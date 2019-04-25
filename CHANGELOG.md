# 0.0.1

- Relax 
  ```diff
  - instance Monad m   => Module m Identity where
  + instance Functor f => Module f Identity where
  ```
