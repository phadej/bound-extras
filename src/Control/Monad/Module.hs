{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
-- | Right monad 'Module' type-class.
--
-- Most possible instances are omitted.
-- The primary use-case for 'Module' is to power 'Bound.ScopeH.ScopeH'.
module Control.Monad.Module where

import Bound                     (Scope (..), (>>>=))
import Control.Monad.Trans.Class (MonadTrans (..))
import Data.Functor.Compose      (Compose (..))
import Data.Functor.Identity     (Identity (..))

-- | @f@ is right @m@-module. (according to https://ncatlab.org/nlab/show/module+over+a+monad#modules definitions).
-- We have @'Compose' f m ~> f@ natural transformation.
--
-- === Laws
--
-- @
-- fma '>>==' return    = fma
-- fma '>>==' (f 'Control.Monad.>=>' g) = (fma '>>==' f) '>>==' g
-- @
--
-- === Properties
--
-- For all @'Monad' m@ we can write associated @instance 'Module' m m where ('>>==') = ('>>=')@.
--
-- 'mjoin' and '>>==' are equivalent in power:
--
-- @
-- fa '>>==' amb = 'mjoin' ('fmap' amb fa)
-- @
class (Functor f, Monad m) => Module f m where

    -- | Called 'action'.
    (>>==) :: f a -> (a -> m b) -> f b

infixl 1 >>==

-- | 'Module''s 'join' variant.
mjoin :: Module f m => f (m a) -> f a
mjoin fma = fma >>== id

-- | @'Module' m (t m)@ action's implementation.
transAction :: (MonadTrans t, Monad m, Monad (t m)) => t m a -> (a -> m b) -> t m b
transAction tma amb = tma >>= lift . amb

-- | @'Module' m ('Compose' f m)@ action's implementation.
composeAction :: (Functor f, Monad m) => Compose f m a -> (a -> m b) -> Compose f m b
composeAction (Compose fma) amb = Compose (fmap (>>= amb) fma)

instance Functor f => Module f Identity where
    fa >>== k = fmap (runIdentity . k) fa

instance Monad m => Module (Scope b m) m where
    (>>==) = (>>>=)
