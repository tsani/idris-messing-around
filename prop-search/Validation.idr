module Validation
  
%access public export

data Validation : Type -> Type -> Type where
  Ok : a -> Validation e a
  Failed : e -> Validation e a
  
Functor (Validation e) where
  map f (Ok x) = Ok (f x)
  map f (Failed x) = Failed x
  
implementation Semigroup e => Applicative (Validation e) where
  pure x = Ok x
  (<*>) (Ok f) (Ok x) = Ok (f x)
  (<*>) (Failed y) (Ok x) = Failed y
  (<*>) (Ok y) (Failed x) = Failed x
  (<*>) (Failed y) (Failed x) = Failed (y <+> x)
