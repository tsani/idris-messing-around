{-# OPTIONS --cubical #-}

module RealShit.QQ where

open import Data.Nat hiding ( pred )
open import Cubical.Foundations.Logic
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Data.Nat
open import Cubical.Data.Empty
open import Cubical.Data.Int renaming ( _+_ to _int+_ )
open import Cubical.Data.Sum
open import Cubical.Core.Everything
open import Cubical.Foundations.Prelude
open import Cubical.Relation.Nullary.DecidableEq
open import Cubical.Relation.Nullary
open import Function

open import RealShit.ZZ

data ℚ : Set where
  _//_ : (num : ℤ) -> (den : ℕ) -> ℚ

  multiple : (num : ℤ) (den k : ℕ) ->
             num // den ≡ (num ℤ* positive k) // (den * k)

  trunc : isSet ℚ
infixl 10 _//_

module ℚ-elim {ℓ} {B : ℚ -> Set ℓ}
  (_//*_ : (num : ℤ) (den : ℕ) -> B (num // den))
  (multiple* : (num : ℤ) (den k : ℕ) ->
               PathP (λ i -> B (multiple num den k i))
                     (num //* den)
                     ((num ℤ* positive k) //* (den * k)))
  (trunc* : (q : ℚ) -> isSet (B q))
  where

  f : (q : ℚ) -> B q
  f (num // den) = num //* den
  f (multiple num den k i) = multiple* num den k i
  f (trunc q₁ q₂ p₁ p₂ i j) =
    isOfHLevel→isOfHLevelDep {n = 2}
      trunc*
      (f q₁) (f q₂)
      (cong f p₁) (cong f p₂)
      (λ i₁ i₂ → trunc q₁ q₂ p₁ p₂ i₁ i₂) i j

module ℚ-elim-prop {ℓ} {B : ℚ -> Set ℓ} (BProp : {q : ℚ} -> isProp (B q))
  (_//*_ : (num : ℤ) (den : ℕ) -> B (num // den))
  where

  f : (q : ℚ) -> B q
  f = ℚ-elim.f
    _//*_
    (λ _ _ _ → toPathP (BProp _ _))
    (λ _ → isProp→isSet BProp)

-- trunc₁ : {A : Set} {q₁ q₂ : ℚ} (x y : A -> q₁ ≡ q₂) -> A -> x ≡ y
-- trunc₁ x y a = trunc _ _ (x a) (y a) {!!} {!!}

module ℚ-rec {ℓ} {B : Set ℓ} (BSet : isSet B)
  (_//*_ : (num : ℤ) (den : ℕ) -> B)
  (multiple* : (num : ℤ) (den k : ℕ) ->
               (num //* den) ≡ ((num ℤ* positive k) //* (den * k)))
  where

  f : ℚ → B
  f = ℚ-elim.f _//*_ multiple* (λ _ → BSet)

ℚ*num : ℚ -> ℤ -> ℚ
ℚ*num (num // den) z = z ℤ* num // den
ℚ*num (multiple num den k i) z = proof num den k z i where
  proof : ∀ num den k z -> z ℤ* num // den ≡ z ℤ* (num ℤ* positive k) // (den * k)
  proof num den k z =
    multiple (z ℤ* num) den k
    ∙ cong (λ p -> p // (den * k)) (ℤ*-assoc z num (positive k))
ℚ*num (trunc q q₁ x y i i₁) z =
  trunc
    (ℚ*num q z) (ℚ*num q₁ z)
    (cong (λ p -> ℚ*num p z) x) (cong (λ p -> ℚ*num p z) y)
    i i₁

ℚ*den : ℚ -> ℕ -> ℚ
ℚ*den (num // den) n = num // (n * den)
ℚ*den (multiple num den k i) n = proof num den k i where
  proof : ∀ num den k -> num // (n * den) ≡ num ℤ* positive k // (n * (den * k))
  proof num den k =
    multiple num (n * den) k
    ∙ cong (λ p -> num ℤ* positive k // p) (*-assoc n den k)
  -- ℚ*den (num // den) n ≡ ℚ*den (num * positive k // den * k) n
  -- num // n * den ≡ num * positive k // n * (den * k)
ℚ*den (trunc q q₁ x y i i₁) n =
  trunc
    (ℚ*den q n) (ℚ*den q₁ n)
    (cong (λ a → ℚ*den a n) x) (cong (λ a → ℚ*den a n) y)
    i i₁

_ℚ*_ : ℚ -> ℚ -> ℚ
q₁ ℚ* (num // den) = ℚ*den (ℚ*num q₁ num) den
q₁ ℚ* multiple num den k i = {!!}
q₁ ℚ* trunc q₂ q₃ x y i i₁ = {!!}

  -- ℚ-rec.f
  -- (λ x y x₁ y₁ i i₁ → trunc x y x₁ y₁ i i₁)
  -- (λ n₁ d₁ -> ℚ-rec.f
  --    (λ x y x₁ y₁ i i₁ → trunc x y x₁ y₁ i i₁)
  --    (λ n₂ d₂ → (n₁ ℤ* n₂) // (d₁ * d₂))
  --    (λ num den k →
  --       multiple (n₁ ℤ* num) (d₁ * den) k
  --         ∙ cong₂ _//_
  --           (ℤ*-assoc n₁ num (positive k))
  --           (*-assoc d₁ den k))
  --    q₁)
  -- (λ num den →
  --   ℚ-rec.f
  --   (λ x y p q i i₁ k i₂ →
  --     trunc {!q₁ ℚ* (x k)!} {!!} {!!} {!!} {!!} {!!})
  --       {!!} {!!} {!!})
