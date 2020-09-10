# 0.0.2

- Add `LiftedModule` allowing to lift into 'ScopeH'.

# 0.0.1

- Relax 
  ```diff
  - instance Monad m   => Module m Identity where
  + instance Functor f => Module f Identity where
  ```
