{-# OPTIONS --cubical #-}

open import Cubical.Foundations.Prelude

infixr 20 _∷_
data LFSet (A : Set) : Set where
  [] : LFSet A
  _∷_ : (x : A) -> (xs : LFSet A) -> LFSet A

  dup : ∀ x xs -> x ∷ x ∷ xs ≡ x ∷ xs
  comm : ∀ x y xs -> x ∷ y ∷ xs ≡ y ∷ x ∷ xs

  trunc : isSet (LFSet A)

infixr 15 _++_
_++_ : ∀ {A} -> (xs ys : LFSet A) -> LFSet A
[] ++ ys = ys
x ∷ xs ++ ys = x ∷ (xs ++ ys)
dup x xs i ++ ys = {!proof i!}
comm x y xs i ++ ys = {!!}
trunc xs xs₁ x y i i₁ ++ ys = {!!}
