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
import Data.String          (IsString (..))

-------------------------------------------------------------------------------
-- Types
-------------------------------------------------------------------------------

data Ty a
    = TV a
    | TArr (Ty a) (Ty a)
    | TForall (Scope () Ty a)
    | TApp (Ty a) (Ty a)
  deriving Functor

instance Applicative Ty where
    pure = TV
    (<*>) = ap

instance Monad Ty where
    return = TV
    TV x      >>= k = k x
    TArr a b  >>= k = TArr (a >>= k) (b >>= k)
    TApp f x  >>= k = TApp (f >>= k) (x >>= k)
    TForall t >>= k = TForall (t >>>= k)

instance IsString a => IsString (Ty a) where
    fromString = TV . fromString

forall_ :: Eq a => a -> Ty a -> Ty a
forall_ n t = TForall (abstract1 n t)

-------------------------------------------------------------------------------
-- Expression
-------------------------------------------------------------------------------

data Expr b a
    = V a
    -- | T (Ty b)
    -- term abstraction
    | Lam (Ty b) (Scope () (Expr b) a)
    | App (Expr b a) (Expr b a)

    -- type abstraction: this is straight forward
    | TyApp (Expr b a) (Ty b)
    | Forall (ScopeH () (Expr' a) Ty b)

instance IsString a => IsString (Expr b a) where
    fromString = V . fromString

instance Bifunctor Expr where
    bimap f g = go where
        go (V x) = V (g x)
       -- go (T y) = T (fmap f y)
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
    Forall b  >>= k = Forall $ ScopeH $ Expr' $ (>>= k') $ unExpr' $ unscopeH b where
        k' = first (F . TV) . k

-- | @'Flip' 'Expr'@.
newtype Expr' a b = Expr' { unExpr' :: Expr b a }

overExpr :: (Expr' a b -> Expr' a b') -> Expr b a -> Expr b' a
overExpr f = unExpr' . f . Expr'

instance Functor (Expr' a) where
    fmap f = Expr' . first f . unExpr'

instance Bifunctor Expr' where
    bimap f g = Expr' . bimap g f . unExpr'

instance Module (Expr' c) Ty where
    Expr' (V a) >>== _ = Expr' (V a)
    -- Expr' (T b) >>== k = Expr' (T (b >>= k))

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
tnf (TArr a b) = TArr (tnf a) (tnf b)
tnf (TForall a) = TForall (toScope $ tnf $ fromScope a)
tnf (TApp a b) = case tnf a of
    TForall a' -> tnf $ instantiate1 b a'
    a'         -> TApp a' (tnf b)

nf :: Expr b a -> Expr b a
nf (V x) = V x
nf (Lam t b) = Lam (tnf t) (toScope $ nf $ fromScope b)
nf (App a b) = case nf a of
    Lam _ a' -> nf $ instantiate1 b a'
    a'       -> App a' (nf b)
nf (Forall e) = Forall $ toScopeH $ Expr' $ nf $ unExpr' $ fromScopeH e
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
    sexpr i f (TArr a b)  = Right ["arr", sexpr' i f a, sexpr' i f b]
    sexpr i f (TApp a b)  = Right [sexpr' i f a, sexpr' i f b]
    sexpr i f (TForall b) = Right [ "forall", sexpr' (i + 1) f' (fromScope b) ] where
        f' (F x)  = f x
        f' (B ()) = show i

class SExpr2 f where
    sexpr2 :: Int -> (a -> String) -> (b -> String) -> f a b -> Either String [String]

    sexpr2' :: Int -> (a -> String) -> (b -> String) -> f a b -> String
    sexpr2' i f g x = either id (\ws -> "(" ++ unwords ws ++ ")") (sexpr2 i f g x)

instance SExpr2 Expr where
    sexpr2 _ _ g (V x)       = Left (g x)
    -- sexpr2 i f _ (T x)       = sexpr i f x
    sexpr2 i f g (App a b)   = Right [sexpr2' i f g a, sexpr2' i f g b]
    sexpr2 i f g (TyApp a b) = Right [sexpr2' i f g a, sexpr' i f b]
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

-------------------------------------------------------------------------------
-- Applications
-------------------------------------------------------------------------------

infixl 1 $$, @@

($$) :: Expr b a -> Expr b a -> Expr b a
($$) = App

(@@) :: Expr b a -> Ty b -> Expr b a
(@@) = TyApp

-------------------------------------------------------------------------------
-- Church numerals
-------------------------------------------------------------------------------

idType_ :: Ty String
idType_ = forall_ "n" (TArr "n" "n")

id_ :: Expr String String
id_ = tyLam_ "a" $ lam_ "x" "a" "x"

natType :: Ty String
natType = forall_ "a" (TArr (TArr "a" "a") (TArr "a" "a"))

zero :: Expr String String
zero = tyLam_ "a" $ lam_ "f" (TArr "a" "a") $ lam_ "z" "a" "z"

sucType :: Ty String
sucType = TArr natType natType

suc :: Expr String String
suc
    = lam_ "n" natType
    $ tyLam_ "a" $ lam_ "f" (TArr "a" "a") $ lam_ "z" "a"
    $ "n" @@ "a" $$ "f" $$ ("f" $$ "z")

main :: IO ()
main = do
    putStrLn $ "id : " ++ sexpr'  0 id idType_
    putStrLn $ "id = " ++ sexpr2' 0 id id id_

    putStrLn $ "0 : " ++ sexpr' 0 id natType
    putStrLn $ "0 = " ++ sexpr2' 0 id id zero

    putStrLn $ "suc : " ++ sexpr' 0 id sucType
    putStrLn $ "suc = " ++ sexpr2' 0 id id suc
    putStrLn $ "    = " ++ sexpr2' 0 id id (nf suc)

    putStrLn $ "1 = " ++ sexpr2' 0 id id (suc $$ zero)
    putStrLn $ "  = " ++ sexpr2' 0 id id (nf $ suc $$ zero)

    putStrLn $ "2 = " ++ sexpr2' 0 id id (suc $$ (suc $$ zero))
    putStrLn $ "  = " ++ sexpr2' 0 id id (nf $ suc $$ (suc $$ zero))
