{-# OPTIONS --cubical #-}

module pie where
  
open import Data.Fin
open import Data.Nat
open import Cubical.Foundations.Prelude hiding ( _,_ )

-- Dependent finite maps
FinDep : ∀ {ℓ} (n : ℕ) -> (Fin n -> Set ℓ) -> Set ℓ
FinDep n P = (i : Fin n) -> P i

-- Simple finite maps
infix 20 _~>_
_~>_ : ∀ {ℓ} (n : ℕ) -> Set ℓ -> Set ℓ
n ~> t = Fin n -> t

infixl 20 _,_
_,_ : ∀ {ℓ k t} -> _~>_ {ℓ} k t -> t -> suc k ~> t
(f , x) zero = x
(f , x) (suc i) = f i

-- The empty finite map.
ε : ∀ {ℓ} {t : Set ℓ} -> zero ~> t
ε = λ ()

mutual
  data Normal (n : ℕ) : Set where
    Lam : Normal (suc n) -> Normal n
    Atom : ℕ -> Normal n
    MkPair : Normal n -> Normal n -> Normal n
    Coe : Neutral n -> Normal n

  data Neutral (n : ℕ) : Set where
    App : Neutral n -> Normal n -> Neutral n
    Var : Fin n -> Neutral n
    Fst : Neutral n -> Neutral n
    Snd : Neutral n -> Neutral n
    _∷_ : Normal n -> (tp : Normal n) -> Neutral n

Ctx : ℕ -> Set
Ctx n = FinDep n (λ i -> {!!})
  
-- mutual
--   data _⊢_

Subst : ℕ -> ℕ -> Set
Subst n k = k ~> Normal n

-- | An environment is a grounding substitution.
Env : ℕ -> Set
Env k = Subst zero k

-- Reduces an expression to weak head normal form
whnf-neutral : ∀ {n} -> Env n -> Neutral n -> Normal n
whnf-neutral ρ (App t x) = {!whnf-neutral (ρ , x) t!}
whnf-neutral ρ (Var x) = {!!}
whnf-neutral ρ (Fst t) = {!!}
whnf-neutral ρ (Snd t) = {!!}
whnf-neutral ρ (x ∷ tp) = {!!}

whnf-normal : ∀ {n} -> Env n -> Normal n -> Normal n
whnf-normal ρ (Lam t) = Lam t
whnf-normal ρ (Atom x) = Atom x
whnf-normal ρ (MkPair t₁ t₂) = MkPair t₁ t₂
whnf-normal ρ (Coe x) = whnf-neutral ρ x

