{-# LANGUAGE CPP                   #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RankNTypes            #-}
{-# LANGUAGE UndecidableInstances  #-}
-- | 'ScopeH' scope, which allows substitute 'f' into 'g' to get new 'g'.
--
-- Compare following signatures:
--
-- @
-- 'instantiate1'  :: ... => m a -> 'Scope'  b   m a -> m a
-- 'instantiate1H' :: ... => m a -> 'ScopeH' b f m a -> f a
-- @
--
-- 'ScopeH' variant allows to encode e.g. Hindley-Milner types, where
-- we diffentiate between @Poly@ and @Mono@-morphic types.
--
-- @
-- specialise :: Poly a -> Mono a -> Poly a
-- specialise (Forall p) m = 'instantiate1H' m p
-- specialise _          _ = error "ill-kinded"
-- @
--
-- Another applications are /bidirectional/ type-systems or representing
-- normal forms with /normal/ and  /neutral/ terms,
-- aka /introduction/ and /elimination/ terms.
--
-- Look into @examples/@ directory for /System F/ and /Bidirectional STLC/
-- implemented with a help of 'ScopeH'.
--
module Bound.ScopeH (
    ScopeH (..),
    -- * Abstraction
    abstractH, abstract1H, abstractHEither,
    -- ** Name
    abstractHName, abstract1HName,
    -- * Instantiation
    instantiateH, instantiate1H, instantiateHEither,
    -- * Traditional de Bruijn
    fromScopeH,
    toScopeH,
    -- * Bound variable manipulation
    lowerScopeH,
    convertFromScope,
    splatH,
    bindingsH,
    mapBoundH,
    mapScopeH,
    foldMapBoundH,
    foldMapScopeH,
    traverseBoundH_,
    traverseScopeH_,
    traverseBoundH,
    traverseScopeH,
    bitraverseScopeH,
    bitransverseScopeH,
    ) where

import Bound                (Scope (..), Var (..))
import Bound.Name           (Name (..))
import Control.DeepSeq      (NFData (..))
import Control.Monad.Module (Module (..))
import Data.Bifoldable      (bifoldMap, bitraverse_)
import Data.Bifunctor       (bimap)
import Data.Bitraversable   (Bitraversable (..))
import Data.Foldable        (traverse_)
import Data.Functor.Classes
import Data.Hashable        (Hashable (..))
import Data.Hashable.Lifted (Hashable1 (..), hashWithSalt1)

-- | @'ScopeH' b f m a@ is a @f@ expression abstracted over @g@,
-- with bound variables in @b@, and free variables in @a@.
--
-- @
-- 'Scope' b f a ~ 'ScopeH' n f f a
-- 'ScopeT' b t f a ~ 'ScopeH' b (t f) f a
-- @
--
newtype ScopeH b f m a = ScopeH { unscopeH :: f (Var b (m a)) }

instance (Functor f, Monad m) => Module (ScopeH b f m) m where
    ScopeH s >>== k = ScopeH $ fmap (fmap (>>= k)) s

-------------------------------------------------------------------------------
-- Instances
-------------------------------------------------------------------------------

instance (Functor f, Functor m) => Functor (ScopeH b f m) where
   fmap f (ScopeH a) = ScopeH $ fmap (fmap (fmap f)) a

instance (Foldable f, Foldable m) => Foldable (ScopeH b f m) where
    foldMap f (ScopeH a) = foldMap (foldMap (foldMap f)) a
    foldr f z (ScopeH a) = foldr (flip (foldr (flip (foldr f))))  z a

instance (Traversable f, Traversable m) => Traversable (ScopeH b f m) where
    traverse f (ScopeH a) = ScopeH <$> traverse (traverse (traverse f)) a

instance (Hashable b, Module f m, Hashable1 f, Hashable1 m) => Hashable1 (ScopeH b f m) where
    liftHashWithSalt h s m = liftHashWithSalt (liftHashWithSalt h) s (fromScopeH m)
    {-# INLINE liftHashWithSalt #-}

instance (Hashable b, Module f m, Hashable1 f, Hashable1 m, Hashable a) => Hashable (ScopeH b f m a) where
    hashWithSalt n m = hashWithSalt1 n (fromScopeH m)
    {-# INLINE hashWithSalt #-}

instance NFData (f (Var b (m a))) => NFData (ScopeH b f m a) where
  rnf scope = rnf (unscopeH scope)

instance (Module f m, Eq b, Eq1 f, Eq1 m, Eq a) => Eq  (ScopeH b f m a) where (==) = eq1
instance (Module f m, Ord b, Ord1 f, Ord1 m, Ord a) => Ord  (ScopeH b f m a) where compare = compare1
instance (Show b, Show1 f, Show1 m, Show a) => Show (ScopeH b f m a) where showsPrec = showsPrec1
instance (Read b, Read1 f, Read1 m, Read a) => Read (ScopeH b f m a) where readsPrec = readsPrec1

-------------------------------------------------------------------------------
-- * transformers 0.5 Data.Functor.Classes
-------------------------------------------------------------------------------

instance (Module f m, Eq b, Eq1 f, Eq1 m) => Eq1 (ScopeH b f m) where
  liftEq f m n = liftEq (liftEq f) (fromScopeH m) (fromScopeH n)

instance (Module f m, Ord b, Ord1 f, Ord1 m) => Ord1 (ScopeH b f m) where
  liftCompare f m n = liftCompare (liftCompare f) (fromScopeH m) (fromScopeH n)

instance (Show b, Show1 f, Show1 m) => Show1 (ScopeH b f m) where
    liftShowsPrec sp sl d (ScopeH x) = showsUnaryWith
        (liftShowsPrec (liftShowsPrec sp' sl') (liftShowList sp' sl'))
        "ScopeH" d x
      where
        sp' = liftShowsPrec sp sl
        sl' = liftShowList sp sl

instance (Read b, Read1 f, Read1 m) => Read1 (ScopeH b f m) where
    liftReadsPrec f g = readsData $ readsUnaryWith
        (liftReadsPrec (liftReadsPrec f' g') (liftReadList f' g'))
        "ScopeH" ScopeH
      where
        f' = liftReadsPrec f g
        g' = liftReadList f g

-------------------------------------------------------------------------------
-- Abstraction
-------------------------------------------------------------------------------

-- | Capture some free variables in an expression to yield a 'ScopeH' with bound variables in @b@.
abstractH :: (Functor f, Monad m) => (a -> Maybe b) -> f a -> ScopeH b f m a
abstractH f e = ScopeH (fmap k e) where
    k y = case f y of
        Just z  -> B z
        Nothing -> F (return y)
{-# INLINE abstractH #-}

-- | Abstract over a single variable.
abstract1H :: (Functor f, Monad m, Eq a) => a -> f a -> ScopeH () f m a
abstract1H a = abstractH (\b -> if a == b then Just () else Nothing)
{-# INLINE abstract1H #-}

-- | Capture some free variables in an expression to yield a 'ScopeH' with bound variables in @b@. Optionally change the types of the remaining free variables.
abstractHEither :: (Functor f,  Monad m) => (a -> Either b c) -> f a -> ScopeH b f m c
abstractHEither f e = ScopeH (fmap k e) where
    k y = case f y of
        Left z -> B z
        Right y' -> F (return y')
{-# INLINE abstractHEither #-}

-------------------------------------------------------------------------------
-- Abstraction with Name
-------------------------------------------------------------------------------

-- | Abstraction, capturing named bound variables.
abstractHName :: (Functor f, Monad m) => (a -> Maybe b) -> f a -> ScopeH (Name a b) f m a
abstractHName f t = ScopeH (fmap k t) where
    k a = case f a of
        Just b  -> B (Name a b)
        Nothing -> F (return a)
{-# INLINE abstractHName #-}

-- | Abstract over a single variable
abstract1HName :: (Functor f, Monad m, Eq a) => a -> f a -> ScopeH (Name a ()) f m a
abstract1HName a = abstractHName (\b -> if a == b then Just () else Nothing)
{-# INLINE abstract1HName #-}

-------------------------------------------------------------------------------
-- Instantiation
-------------------------------------------------------------------------------

-- | Enter a 'ScopeH', instantiating all bound variables
instantiateH :: Module f m => (b -> m a) -> ScopeH b f m a -> f a
instantiateH k (ScopeH e) = e >>== \v -> case v of
    B b -> k b
    F a -> a
{-# INLINE instantiateH #-}

-- | Enter a 'ScopeH' that binds one variable, instantiating it
instantiate1H :: Module f m => m a -> ScopeH b f m a -> f a
instantiate1H e = instantiateH (const e)
{-# INLINE instantiate1H #-}

-- | Enter a 'ScopeH', and instantiate all bound and free variables in one go.
instantiateHEither :: Module f m => (Either b a -> m c) -> ScopeH b f m a -> f c
instantiateHEither f (ScopeH e) = e >>== \v -> case v of
    B b  -> f (Left b)
    F ea -> ea >>= f . Right
{-# INLINE instantiateHEither #-}

-------------------------------------------------------------------------------
-- Traditional de Bruijn
-------------------------------------------------------------------------------

-- | Convert to traditional de Bruijn.
fromScopeH :: Module f m => ScopeH b f m a -> f (Var b a)
fromScopeH (ScopeH s) = s >>== \v -> case v of
    F e -> fmap F e
    B b -> return (B b)

-- | Convert from traditional de Bruijn to generalized de Bruijn indices.
toScopeH :: (Functor f, Monad m) => f (Var b a) -> ScopeH b f m a
toScopeH e = ScopeH (fmap (fmap return) e)

-- | Convert to 'Scope'.
lowerScopeH
    :: (Functor f, Functor f)
    => (forall x. f x -> h x)
    -> (forall x. m x -> h x)
    -> ScopeH b f m a -> Scope b h a
lowerScopeH f m (ScopeH x) = Scope (f (fmap (fmap m) x))

convertFromScope :: Scope b f a -> ScopeH b f f a
convertFromScope (Scope x) = ScopeH x

-------------------------------------------------------------------------------
-- Extras
-------------------------------------------------------------------------------

-- | Perform substitution on both bound and free variables in a 'ScopeH'.
splatH :: Module f m => (a -> m c) -> (b -> m c) -> ScopeH b f m a -> f c
splatH f unbind (ScopeH e) = e >>== \v -> case v of
    B b -> unbind b
    F ea -> ea >>= f
{-# INLINE splatH #-}

-- | Return a list of occurences of the variables bound by this 'ScopeH'.
bindingsH :: Foldable f => ScopeH b f m a -> [b]
bindingsH (ScopeH s) = foldr f [] s where
    f (B v) vs = v : vs
    f _ vs     = vs
{-# INLINE bindingsH #-}

-- | Perform a change of variables on bound variables.
mapBoundH :: Functor f => (b -> b') -> ScopeH b f m a -> ScopeH b' f m a
mapBoundH f (ScopeH s) = ScopeH (fmap f' s) where
    f' (B b) = B (f b)
    f' (F a) = F a
{-# INLINE mapBoundH #-}

-- | Perform a change of variables, reassigning both bound and free variables.
mapScopeH
    :: (Functor f, Functor m)
    => (b -> d) -> (a -> c)
    -> ScopeH b f m a -> ScopeH d f m c
mapScopeH f g (ScopeH s) = ScopeH $ fmap (bimap f (fmap g)) s
{-# INLINE mapScopeH #-}

-- | Obtain a result by collecting information from bound variables
foldMapBoundH :: (Foldable f, Monoid r) => (b -> r) -> ScopeH b f m a -> r
foldMapBoundH f (ScopeH s) = foldMap f' s where
    f' (B a) = f a
    f' _     = mempty
{-# INLINE foldMapBoundH #-}

-- | Obtain a result by collecting information from both bound and free
-- variables
foldMapScopeH
    :: (Foldable f, Foldable m, Monoid r)
    => (b -> r) -> (a -> r)
    -> ScopeH b f m a -> r
foldMapScopeH f g (ScopeH s) = foldMap (bifoldMap f (foldMap g)) s
{-# INLINE foldMapScopeH #-}

-- | 'traverse_' the bound variables in a 'Scope'.
traverseBoundH_ :: (Applicative g, Foldable f) => (b -> g d) -> ScopeH b f m a -> g ()
traverseBoundH_ f (ScopeH s) = traverse_ f' s where
    f' (B a) = () <$ f a
    f' _     = pure ()
{-# INLINE traverseBoundH_ #-}

-- | 'traverse_' both the variables bound by this scope and any free variables.
traverseScopeH_
    :: (Applicative g, Foldable f, Foldable m)
    => (b -> g d) -> (a -> g c)
    -> ScopeH b f m a -> g ()
traverseScopeH_ f g (ScopeH s) = traverse_ (bitraverse_ f (traverse_ g)) s
{-# INLINE traverseScopeH_ #-}

-- | 'traverse' the bound variables in a 'Scope'.
traverseBoundH
    :: (Applicative g, Traversable f)
    => (b -> g c) -> ScopeH b f m a -> g (ScopeH c f m a)
traverseBoundH f (ScopeH s) = ScopeH <$> traverse f' s where
    f' (B b) = B <$> f b
    f' (F a) = pure (F a)
{-# INLINE traverseBoundH #-}

-- | 'traverse' both bound and free variables
traverseScopeH
    :: (Applicative g, Traversable f, Traversable m)
    => (b -> g d) -> (a -> g c)
    -> ScopeH b f m a -> g (ScopeH d f m c)
traverseScopeH f g (ScopeH s) = ScopeH <$> traverse (bitraverse f (traverse g)) s
{-# INLINE traverseScopeH #-}

bitraverseScopeH
    :: (Applicative g, Bitraversable f, Bitraversable m)
    => (k -> g k')
    -> (l -> g l')
    -> (a -> g a')
    -> ScopeH b (f k) (m l) a
    -> g (ScopeH b (f k') (m l') a')
bitraverseScopeH k l = bitransverseScopeH (bitraverse k) (bitraverse l)
{-# INLINE bitraverseScopeH #-}

bitransverseScopeH
    :: Applicative g
    => (forall x x'. (x -> g x') -> f x -> g (f' x'))  -- ^ 'traverse'-like for @f@
    -> (forall x x'. (x -> g x') -> m x -> g (m' x'))  -- ^ 'traverse'-like for @m@
    -> (a -> g a')
    -> ScopeH b f m a
    -> g (ScopeH b f' m' a')
bitransverseScopeH tauF tauM f = fmap ScopeH . tauF (traverse (tauM f)) . unscopeH
{-# INLINE bitransverseScopeH #-}
