{-# LANGUAGE DeriveFoldable         #-}
{-# LANGUAGE DeriveFunctor          #-}
{-# LANGUAGE DeriveTraversable      #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE GADTs                  #-}
{-# LANGUAGE MultiParamTypeClasses  #-}
{-# LANGUAGE OverloadedStrings      #-}
module BiSTLC3 (tests) where

import Bound.ScopeH
import Bound.Var            (Var (..), unvar)
import Control.Monad        (ap)
import Control.Monad.Module
import Data.Bifunctor       (first)
import Data.String          (IsString (..))
import System.FilePath      ((-<.>), (</>))
import Test.Tasty           (TestTree, testGroup)
import Test.Tasty.Golden    (goldenVsString)

import qualified Data.ByteString.Lazy.UTF8 as UTF8
import qualified Data.Text.Short           as TS

import Pretty

-------------------------------------------------------------------------------
-- Types
-------------------------------------------------------------------------------

-- | Types.
data Ty
    = Ty ShortText
    | TUnit
    | Ty :*: Ty
    | Ty :-> Ty
  deriving Eq

infixr 2 :->
infix 4 :*:

instance IsString Ty where
    fromString = Ty . fromString

-------------------------------------------------------------------------------
-- Elimession
-------------------------------------------------------------------------------

-- | Elimerable terms
data Elim a
    -- Variable
    = Var a

    -- :-> Elimination
    | App (Elim a) (Term a)

    -- :*: Elimination-1
    | Fst (Elim a)

    -- :*: Elimination-2
    | Snd (Elim a)

    -- annotated term
    | Ann (Term a) Ty
  deriving (Functor, Foldable, Traversable)

(.:) :: Term a -> Ty -> Elim a
(.:) = Ann
infix 1 .:

-- | Checkable terms
data Term a
    -- Converted term
    = Emb (Elim a)

    -- :-> Introduction
    | Lam (ScopeH () Term Elim a)

    -- :*: Introduction
    | Mul (Term a) (Term a)

  deriving (Functor, Foldable, Traversable)

-------------------------------------------------------------------------------
-- Instances
-------------------------------------------------------------------------------

instance IsString a => IsString (Elim a) where fromString = Var . fromString
instance IsString a => IsString (Term a) where fromString = Emb . fromString

instance Applicative Elim where
    pure = Var
    (<*>) = ap

instance Monad Elim where
    return = Var

    Var x      >>= k = k x
    Ann x t  >>= k = Ann (x >>== k) t
    App f x  >>= k = App (f >>= k) (x >>== k)
    Fst x    >>= k = Fst (x >>= k)
    Snd x    >>= k = Snd (x >>= k)

instance Module Term Elim where
    Emb x    >>== k = Emb (x >>= k)
    Lam b    >>== k = Lam (b >>== k)
    Mul x y  >>== k = Mul (x >>== k) (y >>== k)

instance LiftedModule Term Elim where
    mlift = Emb

lam_ :: Eq a => a -> Term a -> Term a
lam_ x b = Lam (abstract1H x b)

-------------------------------------------------------------------------------
-- Pretty
-------------------------------------------------------------------------------

instance Pretty Ty where
    ppr = return . pprTy

pprTy :: Ty -> Doc
pprTy (Ty t)    = text (TS.unpack t)
pprTy TUnit     = text "Unit"
pprTy (a :*: b) = sexpr (text "prod") [pprTy a, pprTy b]
pprTy (a :-> b) = sexpr (text "->") $ map pprTy $ a : peelArr b

instance Pretty a => Pretty (Elim a) where ppr x = traverse ppr x >>= pprElim
instance Pretty a => Pretty (Term a) where ppr x = traverse ppr x >>= pprTerm

pprElim :: Elim Doc -> PrettyM Doc
pprElim (Var x) = pure x
pprElim (App f x) = case peelApp f of
    (f', xs) -> sexpr
        <$> pprElim f'
        <*> traverse pprTerm (xs ++ [x])
pprElim (Ann x t) = do
    x' <- pprTerm x
    t' <- ppr t
    return $ sexpr (text "the") [t', x']
pprElim (Fst x)  = do
    x' <- pprElim x
    return $ sexpr (text "fst") [x']
pprElim (Snd x)  = do
    x' <- pprElim x
    return $ sexpr (text "snd") [x']

pprTerm :: Term Doc -> PrettyM  Doc
pprTerm (Emb e) = pprElim e
pprTerm (Lam b) = do
    n <- text <$> fresh "x"
    b' <- pprTerm (instantiate1H (Var n) b)
    return $ sexpr (text "fn") [ n, b' ]
pprTerm (Mul x y) = do
    x' <- pprTerm x    
    y' <- pprTerm y
    return $ sexpr (text "pair") [x', y']

-- We output
--   (0 1 2 3)
-- instead of
--   (((0 1) 2) 3)
-- small, but nice improvement!
peelApp :: Elim a -> (Elim a, [Term a])
peelApp (App a b)   = (++ [b]) <$> peelApp a
peelApp e           = (e, [])

peelArr :: Ty -> [Ty]
peelArr (a :-> b) = a : peelArr b
peelArr x         = [x]

-------------------------------------------------------------------------------
-- peelApp
-------------------------------------------------------------------------------

infixl 2 $$

class SApp f g h | h -> f g where
    ($$) :: f a -> g a -> h a

instance SApp Elim Term Elim where ($$) = App
instance SApp Elim Term Term where f $$ x = Emb (f $$ x)

-------------------------------------------------------------------------------
-- Normal form
-------------------------------------------------------------------------------

data NFElim a
    = NFElimNeu (UNeut a)
    | NFElimAnn (NFTerm a) Ty
  deriving (Functor, Foldable, Traversable)

data NFTerm a
    = NFEmb (UNeut a)
    | NFLam (ScopeH () NFTerm NFElim a)
    | NFMul (NFTerm a) (NFTerm a)
  deriving (Functor, Foldable, Traversable)

-- | Upsilon neutral eliminations
data UNeut a
    = NFVar a
    | NFApp (BNeut a) (NFTerm a)
    | NFFst (BNeut a)
    | NFSnd (BNeut a)
    | NFEvalPanic
  deriving (Functor, Foldable, Traversable)

-- | Beta neutral eliminations
data BNeut a
    = BNeutNeu (UNeut a)
    | BNeutAnnEmb (UNeut a) Ty
  deriving (Functor, Foldable, Traversable)

nfVar :: a -> NFElim a
nfVar = NFElimNeu . NFVar

nfApp :: NFElim a -> NFTerm a -> NFElim a
nfApp (NFElimNeu f)                   s =
    NFElimNeu (NFApp (BNeutNeu f) s)
nfApp (NFElimAnn (NFLam t) (a :-> b)) s =
    NFElimAnn (instantiate1H (NFElimAnn s a) t) b
nfApp (NFElimAnn (NFEmb u) ty) s =
    NFElimNeu (NFApp (BNeutAnnEmb u ty) s)
nfApp _ _ = NFElimNeu NFEvalPanic

nfFst :: NFElim a -> NFElim a
nfFst (NFElimNeu e) =
    NFElimNeu (NFFst (BNeutNeu e))
nfFst (NFElimAnn (NFMul t _) (a :*: _)) =
    NFElimAnn t a
nfFst (NFElimAnn (NFEmb u) ty) =
    NFElimNeu (NFFst (BNeutAnnEmb u ty))
nfFst _ = NFElimNeu NFEvalPanic

nfSnd :: NFElim a -> NFElim a
nfSnd (NFElimNeu e) =
    NFElimNeu (NFSnd (BNeutNeu e))
nfSnd (NFElimAnn (NFMul _ s) (_ :*: b)) =
    NFElimAnn s b
nfSnd (NFElimAnn (NFEmb u) ty) =
    NFElimNeu (NFSnd (BNeutAnnEmb u ty))
nfSnd _ = NFElimNeu NFEvalPanic

nfAnn :: NFTerm a -> Ty -> NFElim a
nfAnn = NFElimAnn

nfEmb :: NFElim a -> NFTerm a
nfEmb (NFElimNeu u) = NFEmb u
nfEmb (NFElimAnn t _) = t -- upsilon-reduction

instance Applicative NFElim where
    pure = nfVar
    (<*>) = ap

instance Monad NFElim where
    return = nfVar

    NFElimNeu e   >>= k = substU e k
    NFElimAnn t a >>= k = NFElimAnn (t >>== k) a

substU :: UNeut a -> (a -> NFElim b) -> NFElim b
substU (NFVar x)   k = k x
substU (NFApp f s) k = nfApp (substB f k) (s >>== k)
substU (NFFst e)   k = nfFst (substB e k)
substU (NFSnd e)   k = nfSnd (substB e k)
substU NFEvalPanic _ = NFElimNeu NFEvalPanic

substB :: BNeut a -> (a -> NFElim b) -> NFElim b
substB (BNeutNeu e)       k = substU e k
substB (BNeutAnnEmb e ty) k = nfAnn (nfEmb (substU e k)) ty

instance Module NFTerm NFElim where
    NFEmb u   >>== k = nfEmb (substU u k)
    NFLam b   >>== k = NFLam (b >>== k)
    NFMul t s >>== k = NFMul (t >>== k) (s >>== k)

-------------------------------------------------------------------------------
-- From normal forms to terms
-------------------------------------------------------------------------------

class ToTerm t where toTerm :: t a -> Term a
class ToElim t where toElim :: t a -> Elim a

instance ToTerm Term where toTerm = id
instance ToElim Elim where toElim = id

instance ToElim NFElim where
    toElim (NFElimNeu e)   = toElim e
    toElim (NFElimAnn t a) = Ann (toTerm t) a

instance ToElim BNeut where
    toElim (BNeutNeu e)       = toElim e
    toElim (BNeutAnnEmb e ty) = Ann (Emb (toElim e)) ty

instance ToElim UNeut where
    toElim (NFVar a)   = Var a
    toElim (NFApp f s) = App (toElim f) (toTerm s)
    toElim (NFFst e)   = Fst (toElim e)
    toElim (NFSnd e)   = Snd (toElim e)
    toElim NFEvalPanic = error "eval panic"

instance ToTerm NFTerm where
    toTerm (NFEmb e)   = Emb (toElim e)
    toTerm (NFLam t)   = Lam (toScopeH (toTerm (fromScopeH t)))
    toTerm (NFMul t s) = Mul (toTerm t) (toTerm s)


-------------------------------------------------------------------------------
-- Type-checking
-------------------------------------------------------------------------------

-- infer and check return evaluated values as well.

infer :: (a -> Ty) -> Elim a -> Maybe (NFElim a, Ty)
infer f = infer' . fmap (\x -> (x, f x))

-- No error reporting :)
infer' :: Elim (a, Ty) -> Maybe (NFElim a, Ty)
infer' (Var (a, at)) = Just (nfVar a, at)
infer' (Ann x t) = do
    x' <- check' x t
    Just (nfAnn x' t, t)
infer' (App f x) = do
    (f', ft) <- infer' f
    case ft of
        a :-> b -> do
            x' <- check' x a
            return (nfApp f' x', b)
        _       -> Nothing
infer' (Fst x) = do
    (x', xt) <- infer' x
    case xt of
        (a :*: _) -> do
            return (nfFst x', a)
        _ -> Nothing
infer' (Snd x) = do
    (x', xt) <- infer' x
    case xt of
        (_ :*: b) -> do
            return (nfSnd x', b)
        _ -> Nothing

check' :: Term (a, Ty) -> Ty -> Maybe (NFTerm a)
check' (Lam x) t = case t of
    a :-> b -> do
        let xx = fmap (unvar (\n -> (B n, a)) (first F)) $ fromScopeH x
        xx' <- check' xx b
        return $ NFLam (toScopeH xx')
    _ -> Nothing
check' (Emb x) t = do
    (x', xt) <- infer' x
    if t == xt
    then Just (nfEmb x')
    else Nothing
check' (Mul x y) t = case t of
    a :*: b -> do
        x' <- check' x a
        y' <- check' y b
        return (NFMul x' y')
    _ -> Nothing

-------------------------------------------------------------------------------
-- Examples
-------------------------------------------------------------------------------

demo :: String -> Elim ShortText -> [String]
demo name e = case infer ctx e of
    Nothing ->
        [ name ++ " = " ++ pretty e
        , "DOESN'T TYPECHECK"
        ]
    Just (nf, t) ->
        [ name ++ " : " ++ pretty t
        , name ++ " = " ++ pretty e
        , name ++ " = " ++ pretty (toElim nf)
        ]
  where
    ctx "f"   = "A" :-> "B"
    ctx "a"   = "A"
    ctx "b"   = "B"
    ctx "c" = "C"
    ctx "a2c" = "A" :-> "C"
    ctx "b2c" = "B" :-> "C"
    ctx "ac2d" = "A" :-> "C" :-> "D"
    ctx "bc2d" = "B" :-> "C" :-> "D"
    ctx "aa2b" = "A" :-> "A" :-> "B"
    ctx _     = TUnit

tests :: TestTree
tests = testGroup "Bi-directional STLC 3"
    [ demo' "arr-beta"  $ (lam_ "x" ("f" $$ "x") .: "A" :-> "B") $$ "a"
    , demo' "pair-beta" $ Fst (Mul "a" "b" .: "A" :*: "B")
    ]
  where
    demo' name e = goldenVsString name ("examples" </> name' -<.> "txt")
        $ return $ UTF8.fromString $ unlines
        $ demo name e
      where
        name' = "stlc-3-" ++ name

