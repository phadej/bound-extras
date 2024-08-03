# 0.0.3

- Support GHC-8.6.5...9.10.1

# 0.0.2

- Add `LiftedModule` allowing to lift into 'ScopeH'.

# 0.0.1

- Relax 
  ```diff
  - instance Monad m   => Module m Identity where
  + instance Functor f => Module f Identity where
  ```
