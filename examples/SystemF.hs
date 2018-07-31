{-# LANGUAGE DeriveFunctor         #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings     #-}
module Main (main) where

import Bound.Class          ((>>>=))
import Bound.Scope
import Bound.ScopeH
import Bound.Var            (Var (..))
import Control.Monad        (ap)
import Control.Monad.Module
import Data.Bifunctor       (Bifunctor (..))
import Data.Functor.Classes (Eq1 (..), eq1)
import Data.String          (IsString (..))
import Test.Tasty           (defaultMain, testGroup)
import Test.Tasty.Golden    (goldenVsString)
import System.FilePath ((</>), (-<.>))

import qualified Data.ByteString.Lazy.UTF8 as UTF8

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
  deriving Functor

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

bimapScope
    :: Bifunctor t
    => (k -> k') -> (a -> a')
    -> Scope b (t k) a -> Scope b (t k') a'
bimapScope k a (Scope s) = Scope (bimap k (fmap (bimap k a)) s)

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

instance Bifunctor Expr' where
    bimap f g = overExpr' (bimap g f)

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

class SExpr f where
    sexpr :: Int -> (a -> String) -> f a -> Either String [String]

    sexpr' :: Int -> (a -> String) -> f a -> String
    sexpr' i f x = either id (\ws -> "(" ++ unwords ws ++ ")") (sexpr i f x)

instance SExpr Ty where
    sexpr _ f (TV x)      = Left (f x)
    sexpr i f (a :-> b)   = Right ["arr", sexpr' i f a, sexpr' i f b]
    sexpr i f (TForall b) = Right [ "forall", sexpr' (i + 1) f' (fromScope b) ] where
        f' (F x)  = f x
        f' (B ()) = show i

class SExpr2 f where
    sexpr2 :: Int -> (a -> String) -> (b -> String) -> f a b -> Either String [String]

    sexpr2' :: Int -> (a -> String) -> (b -> String) -> f a b -> String
    sexpr2' i f g x = either id (\ws -> "(" ++ unwords ws ++ ")") (sexpr2 i f g x)

instance SExpr2 Expr where
    sexpr2 _ _ g (V x)       = Left (g x)
    sexpr2 i f g (App a b)   = Right
        $ map (either (('@' :) . sexpr' i f) (sexpr2' i f g))
        $ applications a ++ [Right b]
    sexpr2 i f g (TyApp a b) = Right
        $ map (either (('@' :) . sexpr' i f) (sexpr2' i f g))
        $ applications a ++ [Left b]
    sexpr2 i f g (Lam t a)   = Right
        [ "fn"
        , sexpr' (i + 1) f t
        , sexpr2' (i + 1) f g' (fromScope a)
        ]
      where
        g' (F x)  = g x
        g' (B ()) = show i
    sexpr2 i f g (Forall a) = Right
        [ "FN"
        , sexpr2' (i + 1) f' g (unExpr' $ fromScopeH a)
        ]
      where
        f' (F x)  = f x
        f' (B ()) = show i

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

-- idType_ :: Ty String
-- idType_ = forall_ "n" $ "n" :-> "n"

id_ :: Expr String String
id_ = tyLam_ "a" $ lam_ "x" "a" "x"

-------------------------------------------------------------------------------
-- Church numerals
-------------------------------------------------------------------------------

natType :: Ty String
natType = forall_ "a" $ ("a" :-> "a") :-> "a" :-> "a"

zero :: Expr String String
zero = tyLam_ "a" $ lam_ "f" ("a" :-> "a") $ lam_ "z" "a" "z"

-- sucType :: Ty String
-- sucType = natType :-> natType

suc :: Expr String String
suc
    = lam_ "n" natType
    $ tyLam_ "a" $ lam_ "f" ("a" :-> "a") $ lam_ "z" "a"
    $ "n" @@ "a" $$ "f" $$ ("f" $$ "z")

demo :: String -> Expr String String -> [String]
demo name e = case check e of
    Nothing ->
        [ name ++ " = " ++ sexpr2' 0 id id e
        , "DOESN'T TYPECHECK"
        ]
    Just t ->
        [ name ++ " : " ++ sexpr'  0 id t
        , name ++ " = " ++ sexpr2' 0 id id e
        , name ++ " = " ++ sexpr2' 0 id id (nf e)
        ]

main :: IO ()
main = defaultMain $ testGroup "System F"
    [ demo' "id" id_
    , demo' "0" zero
    , demo' "suc" suc
    , demo' "1" (suc $$ zero)
    , demo' "2" (suc $$ (suc $$ zero))
    ]
  where
    demo' name e = goldenVsString name ("examples" </> name -<.> "output")
        $ return $ UTF8.fromString $ unlines
        $ demo name e
