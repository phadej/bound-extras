{-# LANGUAGE CPP                   #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RankNTypes            #-}
#if __GLASGOW_HASKELL__ >= 805
{-# LANGUAGE QuantifiedConstraints #-}
#endif
-- For NFData instance
{-# LANGUAGE UndecidableInstances  #-}
-- | 'ScopeT' scope, which allows substitute 'f' into 't f' to get new 't f'.
--
-- Consider using 'Bound.ScopeH.ScopeH', it might be clearer.
module Bound.ScopeT (
    ScopeT (..),
    (>>>>=),
    -- * Abstraction
    abstractT, abstract1T, abstractTEither,
    -- ** Name
    abstractTName, abstract1TName,
    -- * Instantiation
    instantiateT, instantiate1T, instantiateTEither,
    -- * Lifting
    liftScopeT,
    -- * Traditional de Bruijn
    fromScopeT,
    toScopeT,
    -- * Bound variable manipulation
    lowerScopeT,
    splatT,
    bindingsT,
    mapBoundT,
    mapScopeT,
    foldMapBoundT,
    foldMapScopeT,
    traverseBoundT_,
    traverseScopeT_,
    traverseBoundT,
    traverseScopeT,
    bitransverseScopeT,
    ) where

import Bound                (Bound (..), Scope (..), Var (..))
import Bound.Name           (Name (..))
import Control.DeepSeq      (NFData (..))
import Control.Monad.Module (Module (..), LiftedModule (..))
import Data.Bifoldable      (bifoldMap, bitraverse_)
import Data.Bifunctor       (bimap)
import Data.Bitraversable   (Bitraversable (..))
import Data.Foldable        (traverse_)
import Data.Functor.Classes
import Data.Hashable        (Hashable (..))
import Data.Hashable.Lifted (Hashable1 (..), hashWithSalt1)

-- | @'Scope' b f a@ is a @t f@ expression abstracted over @f@,
-- with bound variables in @b@, and free variables in @a@.
--
-- @
-- 'Scope' n f a ~ 'ScopeT' n 'IdentityT' f a
-- 'ScopeT' n t f a ~ t ('Scope' n f) a
-- @
--
newtype ScopeT b t f a = ScopeT { unscopeT :: t f (Var b (f a)) }

-------------------------------------------------------------------------------
-- Instances
-------------------------------------------------------------------------------

instance (Functor (t f), Functor f) => Functor (ScopeT b t f) where
   fmap f (ScopeT a) = ScopeT $ fmap (fmap (fmap f)) a

instance (Foldable (t f), Foldable f) => Foldable (ScopeT b t f) where
    foldMap f (ScopeT a) = foldMap (foldMap (foldMap f)) a
    foldr f z (ScopeT a) = foldr (flip (foldr (flip (foldr f))))  z a

instance (Traversable (t f), Traversable f) => Traversable (ScopeT b t f) where
    traverse f (ScopeT a) = ScopeT <$> traverse (traverse (traverse f)) a

-- | We cannot write @'Bound' ('ScopeT' n t)@ pre-GHC-8.6 (without an auxiliary type class).
(>>>>=) :: (Monad f, Functor (t f)) => ScopeT b t f a -> (a -> f c) -> ScopeT b t f c
ScopeT m >>>>= k = ScopeT $ fmap (fmap (>>= k)) m
{-# INLINE (>>>>=) #-}

#if __GLASGOW_HASKELL__ >= 805
-- | @(>>>=) :: ... => 'ScopeT' n t f a -> (a -> f b) -> 'ScopeT' n t f b@
instance (forall f. Functor f => Functor (t f)) => Bound (ScopeT n t) where
    (>>>=) = (>>>>=)
#endif

instance (Monad f, Functor (t f)) => Module (ScopeT b t f) f where
    (>>==) = (>>>>=)

instance (Monad f, Monad (t f)) => LiftedModule (ScopeT b t f) f where
    mlift = liftScopeT

-- we can define this, as we need Monad (t m).
-- QuantifiedConstraint for transformers would solve that.
-- instance MonadTrans (ScopeT b t) where
--     lift = mlift

instance (Hashable b, Bound t, Monad f, Hashable1 f, Hashable1 (t f)) => Hashable1 (ScopeT b t f) where
    liftHashWithSalt h s m = liftHashWithSalt (liftHashWithSalt h) s (fromScopeT m)
    {-# INLINE liftHashWithSalt #-}

instance (Hashable b, Bound t, Monad f, Hashable1 f, Hashable1 (t f), Hashable a) => Hashable (ScopeT b t f a) where
    hashWithSalt n m = hashWithSalt1 n (fromScopeT m)
    {-# INLINE hashWithSalt #-}

instance NFData (t f (Var b (f a))) => NFData (ScopeT b t f a) where
  rnf scope = rnf (unscopeT scope)

instance (Monad f, Bound t, Eq b, Eq1 (t f), Eq1 f, Eq a) => Eq  (ScopeT b t f a) where (==) = eq1
instance (Monad f, Bound t, Ord b, Ord1 (t f), Ord1 f, Ord a) => Ord  (ScopeT b t f a) where compare = compare1
instance (Show b, Show1 (t f), Show1 f, Show a) => Show (ScopeT b t f a) where showsPrec = showsPrec1
instance (Read b, Read1 (t f), Read1 f, Read a) => Read (ScopeT b t f a) where readsPrec = readsPrec1

-------------------------------------------------------------------------------
-- * transformers 0.5 Data.Functor.Classes
-------------------------------------------------------------------------------

instance (Monad f, Bound t, Eq b, Eq1 (t f), Eq1 f) => Eq1 (ScopeT b t f) where
  liftEq f m n = liftEq (liftEq f) (fromScopeT m) (fromScopeT n)

instance (Monad f, Bound t, Ord b, Ord1 (t f), Ord1 f) => Ord1 (ScopeT b t f) where
  liftCompare f m n = liftCompare (liftCompare f) (fromScopeT m) (fromScopeT n)

instance (Show b, Show1 (t f), Show1 f) => Show1 (ScopeT b t f) where
    liftShowsPrec sp sl d (ScopeT x) = showsUnaryWith
        (liftShowsPrec (liftShowsPrec sp' sl') (liftShowList sp' sl'))
        "ScopeT" d x
      where
        sp' = liftShowsPrec sp sl
        sl' = liftShowList sp sl

instance (Read b, Read1 (t f), Read1 f) => Read1 (ScopeT b t f) where
    liftReadsPrec f g = readsData $ readsUnaryWith
        (liftReadsPrec (liftReadsPrec f' g') (liftReadList f' g'))
        "ScopeT" ScopeT
      where
        f' = liftReadsPrec f g
        g' = liftReadList f g

-------------------------------------------------------------------------------
-- Abstraction
-------------------------------------------------------------------------------

-- | Capture some free variables in an expression to yield a 'ScopeT' with bound variables in @b@.
abstractT :: (Functor (t f), Monad f) => (a -> Maybe b) -> t f a -> ScopeT b t f a
abstractT f e = ScopeT (fmap k e) where
    k y = case f y of
        Just z  -> B z
        Nothing -> F (return y)
{-# INLINE abstractT #-}

-- | Abstract over a single variable.
--
-- >>> abstract1T 'x' (MaybeT (Nothing : map Just "xyz"))
-- ScopeT (MaybeT [Nothing,Just (B ()),Just (F "y"),Just (F "z")])
abstract1T :: (Functor (t f), Monad f, Eq a) => a -> t f a -> ScopeT () t f a
abstract1T a = abstractT (\b -> if a == b then Just () else Nothing)
{-# INLINE abstract1T #-}

-- | Capture some free variables in an expression to yield a 'ScopeT' with bound variables in @b@. Optionally change the types of the remaining free variables.
abstractTEither :: (Functor (t f),  Monad f) => (a -> Either b c) -> t f a -> ScopeT b t f c
abstractTEither f e = ScopeT (fmap k e) where
    k y = case f y of
        Left z -> B z
        Right y' -> F (return y')
{-# INLINE abstractTEither #-}

-------------------------------------------------------------------------------
-- Abstraction with Name
-------------------------------------------------------------------------------

-- | Abstraction, capturing named bound variables.
abstractTName :: (Functor (t f), Monad f) => (a -> Maybe b) -> t f a -> ScopeT (Name a b) t f a
abstractTName f t = ScopeT (fmap k t) where
    k a = case f a of
        Just b  -> B (Name a b)
        Nothing -> F (return a)
{-# INLINE abstractTName #-}

-- | Abstract over a single variable
abstract1TName :: (Functor (t f), Monad f, Eq a) => a -> t f a -> ScopeT (Name a ()) t f a
abstract1TName a = abstractTName (\b -> if a == b then Just () else Nothing)
{-# INLINE abstract1TName #-}

-------------------------------------------------------------------------------
-- Instantiation
-------------------------------------------------------------------------------

-- | Enter a 'ScopeT', instantiating all bound variables
instantiateT :: (Bound t, Monad f) => (b -> f a) -> ScopeT b t f a -> t f a
instantiateT k (ScopeT e) = e >>>= \v -> case v of
    B b -> k b
    F a -> a
{-# INLINE instantiateT #-}

-- | Enter a 'ScopeT' that binds one variable, instantiating it
instantiate1T :: (Bound t, Monad f) => f a -> ScopeT b t f a -> t f a
instantiate1T e = instantiateT (const e)
{-# INLINE instantiate1T #-}

-- | Enter a 'ScopeT', and instantiate all bound and free variables in one go.
instantiateTEither :: (Bound t, Monad f) => (Either b a -> f c) -> ScopeT b t f a -> t f c
instantiateTEither f (ScopeT e) = e >>>= \v -> case v of
    B b -> f (Left b)
    F ea -> ea >>= f . Right
{-# INLINE instantiateTEither #-}

-------------------------------------------------------------------------------
-- Lifting
-------------------------------------------------------------------------------

liftScopeT:: forall t f a b. (Monad (t f)) => f a -> ScopeT b t f a
liftScopeT = ScopeT . return . F
{-# INLINE liftScopeT #-}

-------------------------------------------------------------------------------
-- Traditional de Bruijn
-------------------------------------------------------------------------------

-- | Convert to traditional de Bruijn.
fromScopeT :: (Bound t, Monad f) => ScopeT b t f a -> t f (Var b a)
fromScopeT (ScopeT s) = s >>>= \v -> case v of
    F e -> fmap F e
    B b -> return (B b)

-- | Convert from traditional de Bruijn to generalized de Bruijn indices.
toScopeT :: (Functor (t f), Monad f) => t f (Var b a) -> ScopeT b t f a
toScopeT e = ScopeT (fmap (fmap return) e)

-- | Convert to 'Scope'.
lowerScopeT
    :: (Functor (t f), Functor f)
    => (forall x. t f x -> g x)
    -> (forall x. f x -> g x)
    -> ScopeT b t f a -> Scope b g a
lowerScopeT tf f (ScopeT x) = Scope (tf (fmap (fmap f) x))

-------------------------------------------------------------------------------
-- Extras
-------------------------------------------------------------------------------

-- | Perform substitution on both bound and free variables in a 'ScopeT'.
splatT :: (Bound t, Monad f) => (a -> f c) -> (b -> f c) -> ScopeT b t f a -> t f c
splatT f unbind (ScopeT e) = e >>>= \v -> case v of
    B b -> unbind b
    F ea -> ea >>= f
{-# INLINE splatT #-}

-- | Return a list of occurences of the variables bound by this 'ScopeT'.
bindingsT :: Foldable (t f) => ScopeT b t f a -> [b]
bindingsT (ScopeT s) = foldr f [] s where
    f (B v) vs = v : vs
    f _ vs     = vs
{-# INLINE bindingsT #-}

-- | Perform a change of variables on bound variables.
mapBoundT :: Functor (t f) => (b -> b') -> ScopeT b t f a -> ScopeT b' t f a
mapBoundT f (ScopeT s) = ScopeT (fmap f' s) where
    f' (B b) = B (f b)
    f' (F a) = F a
{-# INLINE mapBoundT #-}

-- | Perform a change of variables, reassigning both bound and free variables.
mapScopeT
    :: (Functor (t f), Functor f)
    => (b -> d) -> (a -> c)
    -> ScopeT b t f a -> ScopeT d t f c
mapScopeT f g (ScopeT s) = ScopeT $ fmap (bimap f (fmap g)) s
{-# INLINE mapScopeT #-}

-- | Obtain a result by collecting information from bound variables
foldMapBoundT :: (Foldable (t f), Monoid r) => (b -> r) -> ScopeT b t f a -> r
foldMapBoundT f (ScopeT s) = foldMap f' s where
    f' (B a) = f a
    f' _     = mempty
{-# INLINE foldMapBoundT #-}

-- | Obtain a result by collecting information from both bound and free
-- variables
foldMapScopeT
    :: (Foldable f, Foldable (t f), Monoid r)
    => (b -> r) -> (a -> r)
    -> ScopeT b t f a -> r
foldMapScopeT f g (ScopeT s) = foldMap (bifoldMap f (foldMap g)) s
{-# INLINE foldMapScopeT #-}

-- | 'traverse_' the bound variables in a 'Scope'.
traverseBoundT_ :: (Applicative g, Foldable (t f)) => (b -> g d) -> ScopeT b t f a -> g ()
traverseBoundT_ f (ScopeT s) = traverse_ f' s where
    f' (B a) = () <$ f a
    f' _     = pure ()
{-# INLINE traverseBoundT_ #-}

-- | 'traverse_' both the variables bound by this scope and any free variables.
traverseScopeT_
    :: (Applicative g, Foldable f, Foldable (t f))
    => (b -> g d) -> (a -> g c)
    -> ScopeT b t f a -> g ()
traverseScopeT_ f g (ScopeT s) = traverse_ (bitraverse_ f (traverse_ g)) s
{-# INLINE traverseScopeT_ #-}

-- | 'traverse' the bound variables in a 'Scope'.
traverseBoundT
    :: (Applicative g, Traversable (t f))
    => (b -> g c) -> ScopeT b t f a -> g (ScopeT c t f a)
traverseBoundT f (ScopeT s) = ScopeT <$> traverse f' s where
    f' (B b) = B <$> f b
    f' (F a) = pure (F a)
{-# INLINE traverseBoundT #-}

-- | 'traverse' both bound and free variables
traverseScopeT
    :: (Applicative g, Traversable f, Traversable (t f))
    => (b -> g d) -> (a -> g c)
    -> ScopeT b t f a -> g (ScopeT d t f c)
traverseScopeT f g (ScopeT s) = ScopeT <$> traverse (bitraverse f (traverse g)) s
{-# INLINE traverseScopeT #-}

-- | If you are looking for 'bitraverseScopeT', this is the monster you need.
bitransverseScopeT
    :: Applicative f
    => (forall x x'. (x -> f x') -> t s x -> f (t' s' x'))  -- ^ 'traverse'-like for @t@
    -> (forall x x'. (x -> f x') -> s x -> f (s' x'))       -- ^ 'traverse'-like for @s@
    -> (a -> f a')
    -> ScopeT b t s a
    -> f (ScopeT b t' s' a')
bitransverseScopeT tauT tauS f = fmap ScopeT . tauT (traverse (tauS f)) . unscopeT
{-# INLINE bitransverseScopeT #-}

-- $setup
-- >>> import Control.Monad.Trans.Maybe
