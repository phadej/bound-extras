{-# LANGUAGE DeriveFoldable         #-}
{-# LANGUAGE DeriveFunctor          #-}
{-# LANGUAGE DeriveTraversable      #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE GADTs                  #-}
{-# LANGUAGE MultiParamTypeClasses  #-}
{-# LANGUAGE OverloadedStrings      #-}
module BiSTLC2 (tests) where

import Bound.ScopeH
import Bound.Var            (Var (..), unvar)
import Control.Monad        (ap)
import Control.Monad.Module
import Data.Bifunctor       (first)
import Data.String          (IsString (..))
import Data.Void            (Void)
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
    | Ty :+: Ty
    | Ty :*: Ty
    | Ty :-> Ty
  deriving Eq

infixr 2 :->
infix 4 :*:
infix 3 :+:

instance IsString Ty where
    fromString = Ty . fromString

-------------------------------------------------------------------------------
-- Infession
-------------------------------------------------------------------------------

-- | Inferable terms
data Inf ty a
    -- Variable
    = V a

    -- :-> Elimination
    | App (Inf ty a) (Chk ty a)

    -- :*: Elimination-1
    | Fst (Inf ty a)

    -- :*: Elimination-2
    | Snd (Inf ty a)

    -- annotated term
    | Ann (Chk ty a) ty
  deriving (Functor, Foldable, Traversable)

(.:) :: Chk ty a -> ty -> Inf ty a
(.:) = Ann
infix 1 .:

-- | Checkable terms
data Chk ty a
    -- Converted term
    = Inf (Inf ty a)

    -- :-> Introduction
    | Lam (ScopeH () (Chk ty) (Inf ty) a)

    -- :*: Introduction
    | Pair (Chk ty a) (Chk ty a)

    -- :+: Introduction-1
    | Inl (Chk ty a)

    -- :+: Introduction-2
    | Inr (Chk ty a)

    -- :+: Elimination
    | Case (Inf ty a) (ScopeH () (Chk ty) (Inf ty) a) (ScopeH () (Chk ty) (Inf ty) a)

  deriving (Functor, Foldable, Traversable)

-------------------------------------------------------------------------------
-- Instances
-------------------------------------------------------------------------------

instance IsString a => IsString (Inf ty a) where fromString = V . fromString
instance IsString a => IsString (Chk ty a) where fromString = Inf . fromString

instance Applicative (Inf ty) where
    pure = V
    (<*>) = ap

instance Monad (Inf ty) where
    return = V

    V x      >>= k = k x
    Ann x t  >>= k = Ann (x >>== k) t
    App f x  >>= k = App (f >>= k) (x >>== k)
    Fst x    >>= k = Fst (x >>= k)
    Snd x    >>= k = Snd (x >>= k)

instance ty ~ ty' => Module (Chk ty) (Inf ty') where
    Inf x         >>== k = Inf (x >>= k)
    Lam b         >>== k = Lam (b >>== k)
    Pair x y      >>== k = Pair (x >>== k) (y >>== k)
    Inl x         >>== k = Inl (x >>== k)
    Inr y         >>== k = Inr (y >>== k)
    Case e c1 c2  >>== k = Case (e >>= k) (c1 >>== k) (c2 >>== k)

lam_ :: Eq a => a -> Chk ty a -> Chk ty a
lam_ x b = Lam (abstract1H x b)

case_ :: Eq a => Inf ty a -> a -> Chk ty a -> a -> Chk ty a -> Chk ty a
case_ e x c1 y c2 = Case e (abstract1H x c1) (abstract1H y c2)

-------------------------------------------------------------------------------
-- Pretty
-------------------------------------------------------------------------------

instance Pretty Ty where
    ppr = return . pprTy

pprTy :: Ty -> Doc
pprTy (Ty t)    = text (TS.unpack t)
pprTy TUnit     = text "Unit"
pprTy (a :*: b)  = sexpr (text "prod") [pprTy a, pprTy b]
pprTy (a :+: b)  = sexpr (text "sum") [pprTy a, pprTy b]
pprTy (a :-> b) = sexpr (text "->") $ map pprTy $ a : peelArr b

instance (Pretty a, Pretty ty) => Pretty (Inf ty a) where ppr x = traverse ppr x >>= pprInf
instance (Pretty a, Pretty ty) => Pretty (Chk ty a) where ppr x = traverse ppr x >>= pprChk

pprInf :: Pretty ty => Inf ty Doc -> PrettyM Doc
pprInf (V x) = pure x
pprInf (App f x) = case peelApp f of
    (f', xs) -> sexpr
        <$> pprInf f'
        <*> traverse pprChk (xs ++ [x])
pprInf (Ann x t) = do
    x' <- pprChk x
    t' <- ppr t
    return $ sexpr (text "the") [t', x']
pprInf (Fst x)  = do
    x' <- pprInf x
    return $ sexpr (text "fst") [x']
pprInf (Snd x)  = do
    x' <- pprInf x
    return $ sexpr (text "snd") [x']

pprChk :: Pretty ty => Chk ty Doc -> PrettyM  Doc
pprChk (Inf i) = pprInf i
pprChk (Lam b) = do
    n <- text <$> fresh "x"
    b' <- pprChk (instantiate1H (V n) b)
    return $ sexpr (text "fn") [ n, b' ]
pprChk (Pair x y) = do
    x' <- pprChk x    
    y' <- pprChk y
    return $ sexpr (text "pair") [x', y']
pprChk (Inl x)  = do
    x' <- pprChk x
    return $ sexpr (text "inl") [x']
pprChk (Inr x)  = do
    x' <- pprChk x
    return $ sexpr (text "inr") [x']
pprChk (Case e c1 c2) = do
    e' <- pprInf e
    n1 <- text <$> fresh "x"
    n2 <- text <$> fresh "y"
    c1' <- pprChk (instantiate1H (V n1) c1)
    c2' <- pprChk (instantiate1H (V n2) c2)
    return $ sexpr (text "case+") [e', n1, c1', n2, c2']
    


-- We output
--   (0 1 2 3)
-- instead of
--   (((0 1) 2) 3)
-- small, but nice improvement!
peelApp :: Inf ty a -> (Inf ty a, [Chk ty a])
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

instance SApp (Inf ty) (Chk ty) (Inf ty) where ($$) = App
instance SApp (Inf ty) (Chk ty) (Chk ty) where f $$ x = Inf (f $$ x)

-------------------------------------------------------------------------------
-- Normal form
-------------------------------------------------------------------------------

nfApp :: Chk ty a -> Chk ty a -> Maybe (Chk ty a)
nfApp (Inf f) x = Just $ Inf (App f x)
nfApp (Lam b) x        = chkBind (fromScopeH b) (unvar (const x) (Inf . V))
nfApp Pair {} _        = Nothing
nfApp Inl {}  _        = Nothing
nfApp Inr {}  _        = Nothing
nfApp (Case e c1 c2) x = do
    let x' = fmap F x
    c1' <- nfApp (fromScopeH c1) x'
    c2' <- nfApp (fromScopeH c2) x'
    Just $ Case e (toScopeH c1') (toScopeH c2')

nfFst :: Chk ty b -> Maybe (Chk ty b)
nfFst (Inf x)        = Just $ Inf (Fst x)
nfFst (Pair x _)     = Just x
nfFst Lam {}         = Nothing
nfFst Inl {}         = Nothing
nfFst Inr {}         = Nothing
nfFst (Case e c1 c2) = do
    c1' <- nfFst (fromScopeH c1)
    c2' <- nfFst (fromScopeH c2)
    Just $ Case e (toScopeH c1') (toScopeH c2')

nfSnd :: Chk ty b -> Maybe (Chk ty b)
nfSnd (Inf x)        = Just $ Inf (Snd x)
nfSnd (Pair x _)     = Just x
nfSnd Lam {}         = Nothing
nfSnd Inl {}         = Nothing
nfSnd Inr {}         = Nothing
nfSnd (Case e c1 c2) = do
    c1' <- nfSnd (fromScopeH c1)
    c2' <- nfSnd (fromScopeH c2)
    Just $ Case e (toScopeH c1') (toScopeH c2')

nfCase :: Chk ty a -> Chk ty (Var () a) -> Chk ty (Var () a) -> Maybe (Chk ty a)
nfCase (Inf e)        c1 c2 = Just $ Case e (toScopeH c1) (toScopeH c2)
nfCase (Inl x)        c1 _  = chkBind c1 (unvar (const x) (Inf . V))
nfCase (Inr y)        _  c2 = chkBind c2 (unvar (const y) (Inf . V))
nfCase Lam {}         _  _  = Nothing
nfCase Pair {}        _  _  = Nothing
nfCase (Case e d1 d2) c1 c2 = do
    let mkCase c = nfCase c (fmap F $ fromScopeH d1) (fmap F $ fromScopeH d2)
    c1' <- mkCase c1
    c2' <- mkCase c2
    Just $ Case e (toScopeH c1') (toScopeH c2') 

infBind :: Inf ty a -> (a -> Chk ty b) -> Maybe (Chk ty b)
infBind (Ann x _) k = chkBind x k
infBind (V x)     k = Just $ k x
infBind (App f x) k = do 
    f' <- infBind f k
    x' <- chkBind x k
    nfApp f' x'
infBind (Fst x)   k = do
    x' <- infBind x k
    nfFst x'
infBind (Snd x)   k = do
    x' <- infBind x k
    nfSnd x'

chkBind :: Chk ty a -> (a -> Chk ty b) -> Maybe (Chk ty b)
chkBind (Inf a) k = infBind a k
chkBind (Lam b) k = do
    b' <- chkBind (fromScopeH b) (unvar (Inf . V . B) (fmap F . k))
    return $ Lam $ toScopeH b'
chkBind (Pair x y) k = do
    x' <- chkBind x k
    y' <- chkBind y k
    return $ Pair x' y'
chkBind (Inl x) k = do
    x' <- chkBind x k
    return $ Inl x'
chkBind (Inr y) k = do
    y' <- chkBind y k
    return $ Inl y'
chkBind (Case e c1 c2) k = do
    e' <- infBind e k
    c1' <- chkBind (fromScopeH c1) (unvar (Inf . V . B) (fmap F . k))
    c2' <- chkBind (fromScopeH c2) (unvar (Inf . V . B) (fmap F . k))
    nfCase e' c1' c2'

-------------------------------------------------------------------------------
-- Type-checking
-------------------------------------------------------------------------------

infer :: (a -> Ty) -> Inf Ty a -> Maybe (Chk Void a, Ty)
infer f = infer' . fmap (\x -> (x, f x))

-- No error reporting :)
infer' :: Inf Ty (a, Ty) -> Maybe (Chk Void a, Ty)
infer' (V (a, at)) = Just (Inf (V a), at)
infer' (Ann x t) = do
    x' <- check' x t
    Just (x', t)
infer' (App f x) = do
    (f', ft) <- infer' f
    case ft of
        a :-> b -> do
            x' <- check' x a
            t <- nfApp f' x'
            return (t, b)
        _       -> Nothing
infer' (Fst x) = do
    (x', xt) <- infer' x
    case xt of
        (a :*: _) -> do
            t <- nfFst x'
            return (t, a)
        _ -> Nothing
infer' (Snd x) = do
    (x', xt) <- infer' x
    case xt of
        (_ :*: b) -> do
            t <- nfSnd x'
            return (t, b)
        _ -> Nothing

check' :: Chk Ty (a, Ty) -> Ty -> Maybe (Chk Void a)
check' (Lam x) t = case t of
    a :-> b -> do
        let xx = fmap (unvar (\n -> (B n, a)) (first F)) $ fromScopeH x
        xx' <- check' xx b
        return $ Lam (toScopeH xx')
    _ -> Nothing
check' (Inf x) t = do
    (x', xt) <- infer' x
    if t == xt
    then Just x'
    else Nothing
check' (Pair x y) t = case t of
    a :*: b -> do
        x' <- check' x a
        y' <- check' y b
        return (Pair x' y')
    _ -> Nothing
check' (Inl x) t = case t of
    a :+: _ -> do
        x' <- check' x a
        return (Inl x')
    _ -> Nothing
check' (Inr y) t = case t of
    _ :+: b -> do
        y' <- check' y b
        return (Inl y')
    _ -> Nothing
check' (Case e c1 c2) t = do
    (e', et) <- infer' e
    case et of
        a :+: b -> do
            let cc1 = fmap (unvar (\n -> (B n, a)) (first F)) $ fromScopeH c1
            let cc2 = fmap (unvar (\n -> (B n, b)) (first F)) $ fromScopeH c2
            cc1' <- check' cc1 t
            cc2' <- check' cc2 t
            nfCase e' cc1' cc2'
        _ -> Nothing

-------------------------------------------------------------------------------
-- Examples
-------------------------------------------------------------------------------

demo :: String -> Inf Ty ShortText -> [String]
demo name e = case infer ctx e of
    Nothing ->
        [ name ++ " = " ++ pretty e
        , "DOESN'T TYPECHECK"
        ]
    Just (nf, t) ->
        [ name ++ " : " ++ pretty t
        , name ++ " = " ++ pretty e
        , name ++ " = " ++ pretty nf
        ]
  where
    ctx "f"   = "A" :-> "B"
    ctx "a"   = "A"
    ctx "b"   = "B"
    ctx "c" = "C"
    ctx "a2c" = "A" :-> "C"
    ctx "b2c" = "B" :-> "C"
    ctx "aorb" = "A" :+: "B"
    ctx "ac2d" = "A" :-> "C" :-> "D"
    ctx "bc2d" = "B" :-> "C" :-> "D"
    ctx "aa2b" = "A" :-> "A" :-> "B"
    ctx _     = TUnit

tests :: TestTree
tests = testGroup "Bi-directional STLC 2"
    [ demo' "arr-beta"  $ (lam_ "x" ("f" $$ "x") .: "A" :-> "B") $$ "a"
    , demo' "pair-beta" $ Fst (Pair "a" "b" .: "A" :*: "B")
    , demo' "sum-beta"  $ case_ (Inl "a" .: "A" :+: "B") "x" ("a2c" $$ "x") "y" ("b2c" $$ "y") .: "C"
    , demo' "app-delta" $ (case_ "aorb" "x" ("ac2d" $$"x") "y" ("bc2d" $$ "y") .: "C" :-> "D") $$ "c"
    , demo' "redundant-case" $
        (case_ "aorb" "x" (case_ "aorb" "u" ("aa2b" $$ "x" $$ "u") "v" "v") "y" "y".: "B")
    ]
  where
    demo' name e = goldenVsString name ("examples" </> name' -<.> "txt")
        $ return $ UTF8.fromString $ unlines
        $ demo name e
      where
        name' = "stlc-2-" ++ name

