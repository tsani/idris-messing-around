{-# OPTIONS --cubical #-}

module QQ where

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


data ℚ : Set where
  _//_ : (num : ℤ) -> (den : ℕ) -> ℚ

  multiple : (num : ℤ) (den k : ℕ) -> num // den ≡ (num ℤ* positive k) // (den * k)

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
      trunc* (f q₁) (f q₂) (cong f p₁) (cong f p₂) (λ i₁ i₂ → trunc q₁ q₂ p₁ p₂ i₁ i₂) i j

module ℚ-elim-prop {ℓ} {B : ℚ -> Set ℓ} (BProp : {q : ℚ} -> isProp (B q))
  (_//*_ : (num : ℤ) (den : ℕ) -> B (num // den))
  where

  f : (q : ℚ) -> B q
  f = ℚ-elim.f
    _//*_
    (λ _ _ _ → toPathP (BProp _ _))
    (λ _ → isProp→isSet BProp)

module ℚ-rec {ℓ} {B : Set ℓ} (BSet : isSet B)
  (_//*_ : (num : ℤ) (den : ℕ) -> B)
  (multiple* : (num : ℤ) (den k : ℕ) ->
               (num //* den) ≡ ((num ℤ* positive k) //* (den * k)))
  where

  f : ℚ → B
  f = ℚ-elim.f _//*_ multiple* (λ _ → BSet)

ℚ* : ℚ -> ℚ -> ℚ
ℚ* q₁ = ℚ-rec.f
  (λ x y x₁ y₁ i i₁ → trunc x y x₁ y₁ i i₁)
  (λ n₁ d₁ -> ℚ-rec.f
     (λ x y x₁ y₁ i i₁ → trunc x y x₁ y₁ i i₁)
     (λ n₂ d₂ → (n₁ ℤ* n₂) // (d₁ * d₂))
     (λ num den k →
        multiple (n₁ ℤ* num) (d₁ * den) k
          ∙ {!!})
     q₁)
   {!!}
