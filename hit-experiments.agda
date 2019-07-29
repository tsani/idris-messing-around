
open import Function
open import Cubical.Core.Everything
open import Cubical.Foundations.Prelude

infixr 20 _∷_

data Void : Set where

DecEq : (A : Set) -> Set
DecEq A = (x : A) (y : A) -> Dec (x ≡ y)

data SetList (A : Set) : Set where
  [] : SetList A
  _∷_ : (x : A) -> (xs : SetList A) -> SetList A

  dup : ∀ x xs -> x ∷ x ∷ xs ≡ x ∷ xs
  swap : ∀ x y xs -> x ∷ y ∷ xs ≡ y ∷ x ∷ xs
  trunc : isSet (SetList A)

_++_ : ∀ {A} -> (xs ys : SetList A) -> SetList A
[] ++ ys = ys
(x ∷ xs) ++ ys = x ∷ (xs ++ ys)
dup x xs i ++ ys = dup x (xs ++ ys) i
  -- need (x ∷ x ∷ xs) ++ ys ≡ (x ∷ xs) ++ ys
  -- i.e. x ∷ x ∷ (xs ++ ys) ≡ x ∷ (xs ++ ys)
swap x y xs i ++ ys = swap x y (xs ++ ys) i
  -- need (x ∷ y ∷ xs) ++ ys ≡ (y ∷ x ∷ xs) ++ ys
  -- i.e. x ∷ y ∷ (xs ++ ys) ≡ y ∷ x ∷ (xs ++ ys)
trunc x y p q i j ++ ys = {!!}

module SetListElim {A} {ℓ} {B : SetList A -> Set ℓ}
  ([]* : B [])
  (_∷*_ : (x : A) {xs : SetList A} -> B xs -> B (x ∷ xs))
  (dup* : (x : A) {xs : SetList A} (b : B xs) ->
          PathP (λ i -> B (dup x xs i)) (x ∷* (x ∷* b)) (x ∷* b))
  (swap* : (x y : A) {xs : SetList A} (b : B xs) ->
           PathP (λ i -> B (swap x y xs i)) (x ∷* (y ∷* b)) (y ∷* (x ∷* b)))
  (trunc* : {xs : SetList A} -> isSet (B xs))
           where

  f : (xs : SetList A) -> B xs
  f [] = []*
  f (x ∷ xs) = x ∷* f xs
  f (dup x xs i) = dup* x (f xs) i
  f (swap x y xs i) = swap* x y (f xs) i
  f (trunc x y p q i j) = {!!}

++-assoc : ∀ {A} -> (xs ys zs : SetList A) ->
           xs ++ (ys ++ zs) ≡ (xs ++ ys) ++ zs
++-assoc xs ys zs =
  SetListElim.f {B = λ l -> l ++ (ys ++ zs) ≡ (l ++ ys) ++ zs}
    refl
    (λ x b i → x ∷ b i)
    (λ x b i j → dup x (b j) i)
    (λ x y b i j → swap x y (b j) i)
    {!!}
    xs

infix 30 _∈_
data _∈_ {A} (x : A) : (xs : SetList A) -> Set where
  here : ∀ {xs} -> x ∈ (x ∷ xs)
  skip : ∀ y {xs} -> x ∈ xs -> x ∈ (y ∷ xs)

  dup : ∀ xs -> PathP (λ i -> x ∈ dup x xs i) (skip x here) here
  swap : ∀ y xs -> PathP (λ i -> x ∈ swap x y xs i) here (skip y here)
  trunc : ∀ xs -> isSet (x ∈ xs)
  -- LHS: x ∈ y ∷ x ∷ xs
  -- RHS: x ∈ x ∷ y ∷ xs

module ∈-Elim {A} {x : A} {ℓ} {B : ∀ {xs} -> x ∈ xs -> Set ℓ}
  (here* : ∀ {xs} -> B {xs = x ∷ xs} here)
  (skip* : ∀ {xs} (y : A) {e : x ∈ xs} (b : B e) -> B (skip y e))
  (dup* : ∀ xs -> PathP (λ i -> B (dup xs i)) (skip* x here*) here*)
  (swap* : ∀ {xs} (y : A) ->
           PathP (λ i -> B (swap y xs i)) here* (skip* y here*))
  (trunc* : ∀ {xs} {e : x ∈ xs} -> isSet (B e))
  where

  f : ∀ {xs} (e : x ∈ xs) -> B e
  f here = here*
  f (skip y e) = skip* y (f e)
  f (dup xs i) = dup* xs {!i!}
  f (swap y xs i) = {!!}
  f (trunc xs e e₁ x y i i₁) = {!!}

-- ++-assoc [] ys zs = refl
-- ++-assoc (x ∷ xs) ys zs = cong (x ∷_) (++-assoc xs ys zs)
-- ++-assoc (dup x xs i) ys zs = {!!}
-- ++-assoc (swap x y xs i) ys zs = {!!}

-- _∈_ : ∀ {A} -> (x : A) -> (xs : SetList A) -> Set
-- x ∈ [] = Void
-- x ∈ (x₁ ∷ xs) = {!x ≡ x₁  x ∈ xs!}
-- x ∈ dup x₁ xs i = {!!}
-- x ∈ swap x₁ y xs i = {!!}
