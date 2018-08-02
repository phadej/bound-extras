{-# LANGUAGE DeriveFoldable        #-}
{-# LANGUAGE DeriveFunctor         #-}
{-# LANGUAGE DeriveTraversable     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings     #-}
module SystemF (tests) where

import Bound.Class          ((>>>=))
import Bound.Scope
import Bound.ScopeH
import Bound.Var            (Var (..))
import Control.Monad        (ap)
import Control.Monad.Module
import Data.Bifoldable      (Bifoldable (..))
import Data.Bifunctor       (Bifunctor (..))
import Data.Bitraversable   (Bitraversable (..), bifoldMapDefault, bimapDefault)
import Data.Functor.Classes (Eq1 (..), eq1)
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
--
-- Noteworthy thing is the absence of any /application/.
-- 'TForall' abstract only over types, not type-constructors;
-- so we don't have type application either.
-- In short: everything is well-kinded by construction.
data Ty a
    = TV a
    | Ty a :-> Ty a
    | TForall (Scope () Ty a)
  deriving (Functor, Foldable, Traversable)

infixr 1 :->

instance Applicative Ty where
    pure = TV
    (<*>) = ap

instance Monad Ty where
    return = TV
    TV x      >>= k = k x
    (a :-> b) >>= k = (a >>= k) :-> (b >>= k)
    TForall t >>= k = TForall (t >>>= k)

instance Eq1 Ty where
    liftEq eq (TV a)      (TV a')      = eq a a'
    liftEq eq (a :-> b)   (a' :-> b')  = liftEq eq a a' && liftEq eq b b'
    liftEq eq (TForall a) (TForall a') = liftEq eq a a'

    liftEq _ TV {} _ = False
    liftEq _ (:->) {} _ = False
    liftEq _ TForall {} _ = False

instance Eq a => Eq (Ty a) where (==) = eq1

instance IsString a => IsString (Ty a) where
    fromString = TV . fromString

forall_ :: Eq a => a -> Ty a -> Ty a
forall_ n t = TForall (abstract1 n t)

-------------------------------------------------------------------------------
-- Expression
-------------------------------------------------------------------------------

data Expr b a
    = V a

    -- term abstraction
    | Lam (Ty b) (Scope () (Expr b) a)
    | App (Expr b a) (Expr b a)

    -- type abstraction
    | TyApp (Expr b a) (Ty b)
    | Forall (ScopeH () (Expr' a) Ty b)

instance IsString a => IsString (Expr b a) where
    fromString = V . fromString

{-
-- | In practice we should write Bitraversable instance, and use
-- 'bimapDefault' as Bifunctor implementation.
--
-- That's an argument (not a good one) to omit 'bimapScope' from @bound@.
instance Bifunctor Expr where
    bimap f g = go where
        go (V x) = V (g x)
        go (App a b) = App (go a) (go b)
        go (TyApp a b) = TyApp (go a) (fmap f b)
        go (Lam t b) = Lam (fmap f t) (bimapScope f g b)
        go (Forall (ScopeH b)) = Forall $ ScopeH $
            bimap g (fmap (fmap f)) b
-}

instance Bifunctor  Expr  where bimap     = bimapDefault
instance Bifunctor  Expr' where bimap     = bimapDefault
instance Bifoldable Expr  where bifoldMap = bifoldMapDefault
instance Bifoldable Expr' where bifoldMap = bifoldMapDefault

instance Bitraversable Expr' where
    bitraverse f g = fmap Expr' . bitraverse g f . unExpr'

instance Bitraversable Expr where
    bitraverse f g = go where
        go (V x)       = V <$> g x
        go (App a b)   = App <$> go a <*> go b
        go (TyApp a b) = TyApp <$> go a <*> traverse f b
        go (Lam t b)   = Lam <$> traverse f t <*> bitraverseScope f g b
        go (Forall s)  = Forall <$> bitransverseScopeH (bitraverse g) traverse f s

instance Functor (Expr b) where
    fmap = second

instance Applicative (Expr b) where
    pure = V
    (<*>) = ap

instance Monad (Expr b) where
    return = V

    V x       >>= k = k x
    App a b   >>= k = App (a >>= k) (b >>= k)
    Lam t b   >>= k = Lam t (b >>>= k)
    TyApp a b >>= k = TyApp (a >>= k) b
    Forall b  >>= k = Forall $ ScopeH $ overExpr' (>>= k') $ unscopeH b where
        k' = first (F . TV) . k

-- | @'Flip' 'Expr'@.
newtype Expr' a b = Expr' { unExpr' :: Expr b a }

overExpr :: (Expr' a b -> Expr' a b') -> Expr b a -> Expr b' a
overExpr f = unExpr' . f . Expr'

overExpr' :: (Expr b a -> Expr b' a') -> Expr' a b -> Expr' a' b'
overExpr' f = Expr' . f . unExpr'

instance Functor (Expr' a) where
    fmap f = overExpr' (first f)

instance Module (Expr' c) Ty where
    Expr' (V a) >>== _ = Expr' (V a)

    Expr' (Lam t s) >>== k = Expr' $ Lam (t >>= k) $ hoistScope (overExpr (>>== k)) s
    Expr' (Forall s) >>== k = Expr' $ Forall $ s >>== k

    Expr' (App a b) >>== k = Expr' $ App
        (unExpr' (Expr' a >>== k))
        (unExpr' (Expr' b >>== k))

    Expr' (TyApp a b) >>== k = Expr' $ TyApp
        (unExpr' (Expr' a >>== k))
        (b >>= k)

tyLam_ :: Eq b => b -> Expr b a -> Expr b a
tyLam_ n e = Forall $ abstract1H n (Expr' e)

lam_ :: Eq a => a -> Ty b -> Expr b a -> Expr b a
lam_ x t b = Lam t (abstract1 x b)

-------------------------------------------------------------------------------
-- Normal form
-------------------------------------------------------------------------------

tnf :: Ty b -> Ty b
tnf (TV x) = TV x
tnf (a :-> b) = tnf a :-> tnf b
tnf (TForall a) = TForall (toScope $ tnf $ fromScope a)

nf :: Expr b a -> Expr b a
nf (V x) = V x
nf (Lam t b) = Lam (tnf t) (toScope $ nf $ fromScope b)
nf (App a b) = case nf a of
    Lam _ a' -> nf $ instantiate1 b a'
    a'       -> App a' (nf b)
nf (Forall e) = Forall $ toScopeH $ overExpr' nf $ fromScopeH e
nf (TyApp a b) = case nf a of
    Forall a' -> nf $ unExpr' $ instantiate1H b a'
    a'        -> TyApp a' (tnf b)

-------------------------------------------------------------------------------
-- Pretty
-------------------------------------------------------------------------------

instance Pretty a => Pretty (Ty a) where
    ppr x = traverse ppr x >>= pprTy

pprTy :: Ty Doc -> PrettyM Doc
pprTy (TV x)      = return x
pprTy (a :-> b)   = sexpr (text "->") <$> traverse pprTy [a, b]
pprTy (TForall s) = do
    a <- text <$> fresh "a"
    pprTy (instantiate1 (TV a) s)

instance (Pretty a, Pretty b) => Pretty (Expr b a) where
    ppr x = bitraverse ppr ppr x >>= pprExpr

pprExpr :: Expr Doc Doc -> PrettyM Doc
pprExpr (V x)       = return x
pprExpr (App a b)   = pprApplications $ applications a ++ [Right b]
pprExpr (TyApp a b) = pprApplications $ applications a ++ [Left b]
pprExpr (Lam t b)   = do
    x <- text <$> fresh "x"
    t' <- pprTy t
    b' <- pprExpr $ instantiate1 (V x) b
    return $ sexpr (text "fn") [ sexpr "the" [t', x], b']
pprExpr (Forall b) = do
    t <- text <$> fresh "b"
    b' <- pprExpr $ unExpr' $ instantiate1H (TV t) b
    return $ sexpr (text "poly") [ t , b']

pprApplications :: [Either (Ty Doc) (Expr Doc Doc)] -> PrettyM Doc
pprApplications []       = return $ text "()"
pprApplications (x : xs) = sexpr <$> pp x <*> traverse pp xs
  where
    pp = either pprTy pprExpr

-- We output
--   (0 1 2 3)
-- instead of
--   (((0 1) 2) 3)
-- small, but nice improvement!
applications :: Expr a b -> [Either (Ty a) (Expr a b)]
applications (App a b)   = applications a ++ [Right b]
applications (TyApp a b) = applications a ++ [Left b]
applications e           = [Right e]

-------------------------------------------------------------------------------
-- Applications
-------------------------------------------------------------------------------

infixl 2 $$, @@

($$) :: Expr b a -> Expr b a -> Expr b a
($$) = App

(@@) :: Expr b a -> Ty b -> Expr b a
(@@) = TyApp

-------------------------------------------------------------------------------
-- Type-checking
-------------------------------------------------------------------------------

-- | Type-check assuming that free variables have the similarly named type.
-- In systemf type and term namespaces are different!
check :: Eq a => Expr a a -> Maybe (Ty a)
check = check' . fmap TV

-- No error reporting :)
check' :: Eq a => Expr a (Ty a) -> Maybe (Ty a)
check' (V a) = Just a
check' (App f x) = do
    f' <- check' f
    x' <- check' x
    case f' of
        a' :-> b' | a' == x' -> return b'
        _                    -> Nothing
check' (TyApp x t) = do
    x' <- check' x
    case x' of
        TForall b -> return (instantiate1 t b)
        _         -> Nothing
check' (Lam t b) = do
    b' <- check' (instantiate1 (V t) b)
    return (t :-> b')

check' (Forall b) = do
    let b' = unExpr' $ fromScopeH b
    b'' <- check' (fmap (fmap F) b')
    return $ TForall $ toScope b''

-------------------------------------------------------------------------------
-- Identity function
-------------------------------------------------------------------------------

-- idType_ :: Ty ShortText
-- idType_ = forall_ "n" $ "n" :-> "n"

id_ :: Expr ShortText ShortText
id_ = tyLam_ "a" $ lam_ "x" "a" "x"

-------------------------------------------------------------------------------
-- Church numerals
-------------------------------------------------------------------------------

natType :: Ty ShortText
natType = forall_ "a" $ ("a" :-> "a") :-> "a" :-> "a"

zero :: Expr ShortText ShortText
zero = tyLam_ "a" $ lam_ "f" ("a" :-> "a") $ lam_ "z" "a" "z"

-- sucType :: Ty ShortText
-- sucType = natType :-> natType

suc :: Expr ShortText ShortText
suc
    = lam_ "n" natType
    $ tyLam_ "a" $ lam_ "f" ("a" :-> "a") $ lam_ "z" "a"
    $ "n" @@ "a" $$ "f" $$ ("f" $$ "z")

demo :: String -> Expr ShortText ShortText -> [String]
demo name e = case check e of
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
tests = testGroup "System F"
    [ demo' "id" id_
    , demo' "0" zero
    , demo' "suc" suc
    , demo' "1" (suc $$ zero)
    , demo' "2" (suc $$ (suc $$ zero))
    ]
  where
    demo' name e = goldenVsString name ("examples" </> name' -<.> "txt")
        $ return $ UTF8.fromString $ unlines
        $ demo name e
      where
        name' = "sysf-" ++ name
