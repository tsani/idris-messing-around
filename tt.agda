{-# OPTIONS --cubical #-}

open import Cubical.Foundations.Prelude renaming ( _,_ to _,,_ )
open import Data.Nat
open import Data.Fin
-- open import Function

-- this is Thorsten's idea, with explicit substitutions.
-- rather than build in variables as part of the syntax, you recover
-- them.

{-
data Ty : Set where
  Base : Ty
  _=>_ : Ty -> Ty -> Ty

data Ctx : Set where
  · : Ctx
  _,_ : Ctx -> Ty -> Ctx

data Var : Ctx -> Ty -> Set where
  vz : ∀ {Γ A} -> Var (Γ , A) A
  vs : ∀ {Γ A B} -> Var Γ A -> Var (Γ , B) A

data Tm : Ctx -> Ty -> Set
data Subst : Ctx -> Ctx -> Set

data Tm where
  [_] : ∀ {Γ Δ A} -> Subst Γ Δ -> Tm Δ A -> Tm Γ A
  π₂ : ∀ {Γ Δ A} -> Subst Γ (Δ , A) -> Tm Γ A
  app : ∀ {Γ A B} -> Tm Γ (A => B) -> Tm (Γ , A) B
  lam : ∀ {Γ A B} -> Tm (Γ , A) B -> Tm Γ (A => B)
  var : ∀ {Γ A} -> Var Γ A -> Tm Γ A

data Subst where
  ε : ∀ {Γ} -> Subst Γ ·
  _,_ : ∀ {Γ Δ A} -> Subst Γ Δ -> Tm Γ A -> Subst Γ (Δ , A)
  _∘_ : ∀ {Γ₁ Γ₂ Γ'} -> Subst Γ₁ Γ' -> Subst Γ' Γ₂ -> Subst Γ₁ Γ₂
  π₁ : ∀ {Γ Δ A} -> Subst Γ (Δ , A) -> Subst Γ Δ

  -- idl : ∀ {Γ Δ} {σ : Subst Γ Δ} -> idₛ ∘ σ ≡ σ
  -- idr : ∀ {Γ Δ} {σ : Subst Γ Δ} -> σ ∘ idₛ ≡ σ
  ass : ∀ {Γ₁ Γ₂ Γ₃ Γ₄}
        {σ₁ : Subst Γ₁ Γ₂} {σ₂ : Subst Γ₂ Γ₃} {σ₃ : Subst Γ₃ Γ₄} ->
        σ₁ ∘ (σ₂ ∘ σ₃) ≡ (σ₁ ∘ σ₂) ∘ σ₃
  -- ,∘ : ∀ {Γ₁ Γ₂ Γ₃ A}
  --      {σ₁ : Subst Γ₁ (Γ₂ , A)} {σ₂ : Subst (Γ₂ , A) Γ₃} {t : Tm Γ₁ A} ->
  --      (σ₁ , t) ∘ σ₂ ≡ (σ₁ ∘ σ₂) , [ σ₂ ] t
  π₁β : ∀ {Γ₁ Γ₂ A} {t : Tm Γ₁ A} {σ : Subst Γ₁ Γ₂} ->
        π₁ (σ , t) ≡ σ
  πη : ∀ {Γ Δ A} {σ : Subst Γ (Δ , A)} ->
       π₁ σ , π₂ σ ≡ σ
  εη : ∀ {Γ} {σ : Subst Γ ·} -> σ ≡ ε
  
-}

-- This is my idea, just basic metatheory with beta rules thrown in.

open import Function

_~>_ : ℕ -> Set -> Set
n ~> t = Fin n -> t

_,_ : ∀ {n t} -> n ~> t -> t -> suc n ~> t
(f , x) zero = x
(f , x) (suc i) = f i

Renaming : ℕ -> ℕ -> Set
Renaming k n = n ~> Fin k

idᵣ : ∀ {n} -> Renaming n n
idᵣ i = i

weakenᵣ : ∀ {k n} -> Renaming k n -> Renaming (suc k) n
weakenᵣ ρ = suc ∘ ρ 

extendᵣ : ∀ {k n} -> Renaming k n -> Renaming (suc k) (suc n)
extendᵣ ρ = weakenᵣ ρ , zero 

data Tm (n : ℕ) : Set

[_]ᵣ : ∀ {k n} -> Renaming n k -> Tm k -> Tm n

Subst : ℕ -> ℕ -> Set
Subst k n = n ~> Tm k

_r∘s_ : ∀ {n k j} (ρ : Renaming n k) (σ : Subst k j) -> Subst n j
ρ r∘s σ = [ ρ ]ᵣ ∘ σ

idₛ : ∀ {n} -> Subst n n

[_] : ∀ {k n} -> Subst k n -> Tm n -> Tm k

single : ∀ {n} -> Tm n -> Subst n (suc n)
single t = idₛ , t

data Tm n where
  Lam : Tm (suc n) -> Tm n
  _·_ : Tm n -> Tm n -> Tm n
  Var : Fin n -> Tm n
  β : (t : Tm (suc n)) (s : Tm n) -> Lam t · s ≡ [ single s ] t
  trunc : isSet (Tm n)

r∘s-lemma : ∀ {n k j}
            (ρ : Renaming n k) (σ : Subst k j) (t : Tm j) ->
            [ ρ ]ᵣ ([ σ ] t) ≡ [ ρ r∘s σ ] t
idₛ i = Var i

[ ρ ]ᵣ (Lam t) = Lam ([ extendᵣ ρ ]ᵣ t)
[ ρ ]ᵣ (t₁ · t₂) = [ ρ ]ᵣ t₁ · [ ρ ]ᵣ t₂
[ ρ ]ᵣ (Var x) = Var (ρ x)
[ ρ ]ᵣ (trunc t1 t2 p q i j) =
  trunc {!!} {!!} {!!} {!!} {!!} {!!}
[ ρ ]ᵣ (β t s i) =
  -- need to show:
  -- [ ρ ]ᵣ (Lam t · s) ≡ [ ρ ]ᵣ ([ single s ] t)
  -- which we would like to do by β, but we will need a lemma about
  -- single substitutions
  β {![ ρ ]ᵣ t!} ([ ρ ]ᵣ s) i

wk : ∀ {n} -> Renaming (suc n) n
wk = weakenᵣ idᵣ

weakenₜ : ∀ {n} -> Tm n -> Tm (suc n)
weakenₜ = [ wk ]ᵣ

weakenₛ : ∀ {k n} -> Subst k n -> Subst (suc k) n
weakenₛ σ = weakenₜ ∘ σ

extendₛ : ∀ {k n} -> Subst k n -> Subst (suc k) (suc n)
extendₛ σ = weakenₛ σ , Var zero

[ σ ] (Lam t) = Lam ([ extendₛ σ ] t)
[ σ ] (t₁ · t₂) = [ σ ] t₁ · [ σ ] t₂
[ σ ] (Var x) = σ x
[ σ ] (β t s i) = {!!}
[ σ ] (trunc t₁ t₂ x y i j) = {!!}

r-extend-s : ∀ {n k j} (ρ : Renaming n k) (σ : Subst k j) ->
             extendᵣ ρ r∘s extendₛ σ ≡ extendₛ (ρ r∘s σ)
r-extend-s ρ σ = funExt proof where
  proof : (x : Fin _) -> (extendᵣ ρ r∘s extendₛ σ) x ≡ extendₛ (ρ r∘s σ) x
  proof zero = refl
  proof (suc i) = {!proof i!}

_r∘r_ : ∀ {n k j} (ρ₁ : Renaming n k) (ρ₂ : Renaming k j) -> Renaming n j
_r∘r_ ρ₁ ρ₂ = ρ₁ ∘ ρ₂

r-extend-r : ∀ {n k j} (ρ₁ : Renaming n k) (ρ₂ : Renaming k j) ->
             extendᵣ ρ₁ ∘ extendᵣ ρ₂ ≡ extendᵣ (ρ₁ ∘ ρ₂)
r-extend-r ρ₁ ρ₂ = funExt proof where
  proof : (x : Fin _) ->
          (extendᵣ ρ₁ ∘ extendᵣ ρ₂) x ≡ extendᵣ (ρ₁ ∘ ρ₂) x
  proof zero = refl
  proof (suc x) = refl

r∘r-lemma : ∀ {n k j} (ρ₁ : Renaming n k) (ρ₂ : Renaming k j) (t : Tm j) ->
            [ ρ₁ ]ᵣ ([ ρ₂ ]ᵣ t) ≡ [ ρ₁ r∘r ρ₂ ]ᵣ t
r∘r-lemma ρ₁ ρ₂ (Lam t) =
  cong Lam
    (subst
      (λ P ->
        [ extendᵣ ρ₁ ]ᵣ ([ extendᵣ ρ₂ ]ᵣ t) ≡ [ P ]ᵣ t)
      (r-extend-r ρ₁ ρ₂)
      (r∘r-lemma (extendᵣ ρ₁) (extendᵣ ρ₂) t))
r∘r-lemma ρ₁ ρ₂ (t₁ · t₂) =
  cong₂ _·_ (r∘r-lemma ρ₁ ρ₂ t₁) (r∘r-lemma ρ₁ ρ₂ t₂)
r∘r-lemma ρ₁ ρ₂ (Var x) = refl
r∘r-lemma ρ₁ ρ₂ (β t t₁ i) = λ j ->  ?
  -- subst
  --   (λ P ->
  --       (β ([ extendᵣ (ρ₁ ∘ ρ₂) ]ᵣ t) P {!!}
  --       ≡
  --       β ([ extendᵣ (ρ₁ ∘ ρ₂) ]ᵣ t) ([ ρ₁ r∘r ρ₂ ]ᵣ t₁) i))
  --   (r∘r-lemma ρ₁ ρ₂ t₁)
  --   refl

  -- trunc {![ ρ₁ ∘ ρ₂ ]ᵣ t₁!} {!!} {!!} {!!} i

  -- λ j → β ([ extendᵣ (ρ₁ ∘ ρ₂) ]ᵣ t) ([ ρ₁ ∘ ρ₂ ]ᵣ t₁) {!i ∨ j!} -- λ j → {!r∘r-lemma ρ₁ ρ₂ t₁ j!} -- trunc {![ ρ₁ ∘ ρ₂ ]ᵣ t₁!} {![ ρ₁ ∘ ρ₂ ]ᵣ t!} {!!} {!!} 
r∘r-lemma ρ₁ ρ₂ (trunc t t₁ x y i i₁) = {!!}

r∘s-lemma ρ σ (Lam t) =
  cong Lam {!r∘s-lemma (extendᵣ ρ) (extendₛ σ) t!}
r∘s-lemma ρ σ (t · t₁) = {!!}
r∘s-lemma ρ σ (Var x) = {!!}
r∘s-lemma ρ σ (β t t₁ i) = {!!}
r∘s-lemma ρ σ (trunc t t₁ x y i i₁) = {!!}

