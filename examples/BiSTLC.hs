{-# LANGUAGE DeriveFoldable         #-}
{-# LANGUAGE DeriveFunctor          #-}
{-# LANGUAGE DeriveTraversable      #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE MultiParamTypeClasses  #-}
{-# LANGUAGE OverloadedStrings      #-}
module BiSTLC (tests) where

import Bound.ScopeH
import Control.Monad        (ap)
import Control.Monad.Module
import Data.String          (IsString (..))
import System.FilePath      ((-<.>), (</>))
import Test.Tasty           (TestTree, testGroup)
import Test.Tasty.Golden    (goldenVsString)

import qualified Data.ByteString.Lazy.UTF8 as UTF8

import Pretty

-------------------------------------------------------------------------------
-- Types
-------------------------------------------------------------------------------

-- | Types.
data Ty
    = TBool
    | TNat
    | Ty :-> Ty
  deriving Eq

infixr 2 :->

-------------------------------------------------------------------------------
-- Infession
-------------------------------------------------------------------------------

-- | Inferable terms
data Inf a
    = V a

    -- term abstraction
    | App (Inf a) (Chk a)

    -- annotated term
    | Ann (Chk a) Ty

    -- Booleans
    | TT
    | FF

    -- Numbers
    | Zero
    | Succ (Chk a)
  deriving (Functor, Foldable, Traversable)

(.:) :: Chk a -> Ty -> Inf a
(.:) = Ann
infix 1 .:

-- | Checkable terms
data Chk a
    = Inf (Inf a)
    | Lam (ScopeH () Chk Inf a)

    -- : Bool -> a -> a -> a
    | If (Chk a) (Chk a) (Chk a)

    -- : a -> (a -> a) -> Nat -> a
    | FoldNat (Chk a) (Chk a) (Chk a)
  deriving (Functor, Foldable, Traversable)

-------------------------------------------------------------------------------
-- Instances
-------------------------------------------------------------------------------

instance IsString a => IsString (Inf a) where fromString = V . fromString
instance IsString a => IsString (Chk a) where fromString = Inf . fromString

instance Applicative Inf where
    pure = V
    (<*>) = ap

instance Monad Inf where
    return = V

    V x      >>= k = k x
    Ann x t  >>= k = Ann (x >>== k) t
    App f x  >>= k = App (f >>= k) (x >>== k)

    TT >>= _ = TT
    FF >>= _ = FF

    Zero   >>= _ = Zero
    Succ n >>= k = Succ (n >>== k)

instance Module Chk Inf where
    Inf x         >>== k = Inf (x >>= k)
    Lam b         >>== k = Lam (b >>== k)
    If c t e      >>== k = If (c >>== k) (t >>== k) (e >>== k)
    FoldNat z s n >>== k = FoldNat (z >>== k) (s >>== k) (n >>== k)

instance LiftedModule Chk Inf where
    mlift = Inf

lam_ :: Eq a => a -> Chk a -> Chk a
lam_ x b = Lam (abstract1H x b)

-------------------------------------------------------------------------------
-- Normal form
-------------------------------------------------------------------------------

ann :: Chk a -> Ty -> Inf a
ann (Inf x) _ = x
ann x       t = Ann x t

annNf :: Chk a -> Ty -> Inf a
annNf x t = ann (nfChk x t) t

nf :: Inf a -> Inf a
nf (V x)     = V x
nf (Ann x t) = annNf x t
nf (App f x) = case nf f of
    Ann (Lam f') (a :-> b) -> annNf (instantiate1H (ann x a) f') b
    f'                     -> App f' x -- not normalising, because type unclear

nf TT = TT
nf FF = FF

nf Zero     = Zero
nf (Succ n) = Succ (nfChk n TNat)

nfChk :: Chk a -> Ty -> Chk a
nfChk (Lam x) (_ :-> b) = Lam (toScopeH $ flip nfChk b $ fromScopeH x)
nfChk (Lam x) _         = Lam x -- not simplifying
nfChk (Inf x) _ = case nf x of
    Ann x' _ -> x'
    x'       -> Inf x'
nfChk (If c t e) ty = case nfChk c TBool of
    Inf TT -> nfChk t ty
    Inf FF -> nfChk e ty
    c'     -> If c' t e -- doesn't normalise branches
nfChk (FoldNat z s n) ty = case iter n' of
    Just x  -> nfChk x ty
    Nothing -> FoldNat z s n'
  where
    iter (Inf Zero)       = Just z
    iter (Inf (Succ n'')) = (s' $$) <$> iter n''
    iter _                = Nothing

    n' = nfChk n TNat
    s' = s .: ty :-> ty

-------------------------------------------------------------------------------
-- Pretty
-------------------------------------------------------------------------------

instance Pretty Ty where
    ppr = return . pprTy

pprTy :: Ty -> Doc
pprTy TNat      = text "Nat"
pprTy TBool     = text "Bool"
pprTy (a :-> b) = sexpr (text "->") $ map pprTy $ a : peelArr b

instance Pretty a => Pretty (Inf a) where ppr x = traverse ppr x >>= pprInf
instance Pretty a => Pretty (Chk a) where ppr x = traverse ppr x >>= pprChk

pprInf :: Inf Doc -> PrettyM Doc
pprInf (V x) = pure x
pprInf (App f x) = case peelApp f of
    (f', xs) -> sexpr
        <$> pprInf f'
        <*> traverse pprChk (xs ++ [x])
pprInf (Ann x t) = do
    x' <- pprChk x
    t' <- ppr t
    return $ sexpr (text "the") [t', x']

pprInf TT = return (text "#t")
pprInf FF = return (text "#f")

pprInf Zero     = return (integer 0)
pprInf (Succ n) = case peelNat n of
    Just n' -> return (integer (succ n'))
    Nothing -> sexpr (text "S") . pure <$> pprChk n

pprChk :: Chk Doc -> PrettyM  Doc
pprChk (Inf i) = pprInf i
pprChk (Lam b) = do
    n <- text <$> fresh "x"
    b' <- pprChk (instantiate1H (V n) b)
    return $ sexpr (text "fn") [ n, b' ]
pprChk (If c t e) = sexpr (text "if") <$> traverse pprChk [c, t, e]
pprChk (FoldNat z f n) = sexpr (text "fold-Nat") <$> traverse pprChk [z, f, n]

-- We output
--   (0 1 2 3)
-- instead of
--   (((0 1) 2) 3)
-- small, but nice improvement!
peelApp :: Inf a -> (Inf a, [Chk a])
peelApp (App a b)   = (++ [b]) <$> peelApp a
peelApp e           = (e, [])

peelArr :: Ty -> [Ty]
peelArr (a :-> b) = a : peelArr b
peelArr x         = [x]

peelNat :: Chk a -> Maybe Integer
peelNat (Inf Zero)     = Just 0
peelNat (Inf (Succ n)) = succ <$> peelNat n
peelNat _              = Nothing

-------------------------------------------------------------------------------
-- peelApp
-------------------------------------------------------------------------------

infixl 2 $$

class SApp f g h | h -> f g where
    ($$) :: f a -> g a -> h a

instance SApp Inf Chk Inf where ($$) = App
instance SApp Inf Chk Chk where f $$ x = Inf (f $$ x)

class SBool f where
    tt :: f a
    ff :: f a

instance SBool Inf where
    tt = TT
    ff = FF

instance SBool Chk where
    tt = Inf tt
    ff = Inf ff

-------------------------------------------------------------------------------
-- Type-checking
-------------------------------------------------------------------------------

infer :: (a -> Ty) -> Inf a -> Maybe Ty
infer f = infer' . fmap f

-- No error reporting :)
infer' :: Inf Ty -> Maybe Ty
infer' (V a) = Just a
infer' (App f x) = do
    f' <- infer' f
    case f' of
        a :-> b -> do
            check' x a
            Just b
        _       -> Nothing
infer' (Ann x t) = do
    check' x t
    Just t

infer' TT = Just TBool
infer' FF = Just TBool

infer' Zero     = Just TNat
infer' (Succ n) = do
    check' n TNat
    Just TNat

check' :: Chk Ty -> Ty -> Maybe ()
check' (Lam x) t = case t of
    a :-> b -> check' (instantiate1H (V a) x) b
    _       -> Nothing
check' (Inf x) t = do
    t' <- infer' x
    if t == t'
    then Just ()
    else Nothing
check' (If c t e) ty = do
    check' c TBool
    check' t ty
    check' e ty
check' (FoldNat z f n) ty = do
    check' z ty
    check' f (ty :-> ty)
    check' n TNat

-------------------------------------------------------------------------------
-- Examples
-------------------------------------------------------------------------------

id_ :: Inf ShortText
id_ = lam_ "x" "x" .: TNat :-> TNat

not_ :: Inf ShortText
not_ = lam_ "x" (If "x" ff tt) .: TBool :-> TBool

two_ :: Inf ShortText
two_ = Succ (Inf (Succ (Inf Zero)))

plus_ :: Inf ShortText
plus_ = term .: TNat :-> TNat :-> TNat where
    term = lam_ "n" $ lam_ "m" $ FoldNat "m" s "n"
    s = lam_ "k" $ Inf (Succ "k")

mult_ :: Inf ShortText
mult_ = term .: TNat :-> TNat :-> TNat where
    term = lam_ "n" $ lam_ "m" $ FoldNat (Inf Zero) (plus_ $$ "m") "n"

demo :: String -> Inf ShortText -> [String]
demo name e = case infer (const TBool) e of
    Nothing ->
        [ name ++ " = " ++ pretty e
        , "DOESN'T TYPECHECK"
        ]
    Just t ->
        [ name ++ " : " ++ pretty t
        , name ++ " = " ++ pretty e
        , name ++ " = " ++ pretty (nf e)
        ]

tests :: TestTree
tests = testGroup "Bi-directional STLC"
    [ demo' "id" id_
    , demo' "not-tt"    $ not_ $$ tt
    , demo' "four-plus" $ plus_ $$ Inf two_ $$ Inf two_
    , demo' "four-mult" $ mult_ $$ Inf two_ $$ Inf two_
    ]
  where
    demo' name e = goldenVsString name ("examples" </> name' -<.> "txt")
        $ return $ UTF8.fromString $ unlines
        $ demo name e
      where
        name' = "stlc-" ++ name
