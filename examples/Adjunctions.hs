module Adjunctions where

import Data.Functor.Adjunction (Adjunction (..))

-- Defining 'mjoin' for monad arising from adjunction is easy:
-- every @r f@ is right module of @u f@.
mjoinAdj :: (Functor r, Adjunction f u) => r (f (u (f a))) -> r (f a)
mjoinAdj = fmap counit

-- However 'LiftedModule' is trickier, here we need 
-- to know more.
mliftAdj :: (Functor r, Adjunction f u) => u (f a) -> r (f a)
mliftAdj = error "we need to know about r, f and u"
