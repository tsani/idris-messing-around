{-# OPTIONS --cubical #-}

module hitlam where

open import Cubical.Foundations.Everything hiding ( _,_ ; _∘_ )
open import Function hiding ( id ; _∘_ )
open import Data.Unit
open import Data.Empty

data Tp : Set where
  𝟙 : Tp
  _⇒_ : Tp -> Tp -> Tp
infixr 20 _⇒_

data Ctx : Set where
  ε : Ctx
  _,_ : Ctx -> Tp -> Ctx
infixl 10 _,_

data ⊙ : Set where
  tp : Tp -> ⊙
  ctx : Ctx -> ⊙

data Tm' : (Γ : Ctx) -> ⊙ -> Set

Tm : Ctx -> Tp -> Set
Tm Γ A = Tm' Γ (tp A)

Subst : Ctx -> Ctx -> Set
Subst Δ Γ = Tm' Δ (ctx Γ)

data Tm' where
  ƛ : ∀ {Γ A B} -> Tm (Γ , A) B -> Tm Γ (A ⇒ B)
  u : ∀ {Γ} -> Tm Γ 𝟙
  ▵ : ∀ {Γ A} -> Tm (Γ , A) A
  _·_ : ∀ {Γ A B} -> Tm Γ (A ⇒ B) -> Tm Γ A -> Tm Γ B
  [_] : ∀ {Γ Δ A} -> Subst Γ Δ -> Tm Δ A -> Tm Γ A

  id : ∀ {Γ} -> Subst Γ Γ
  _,,_ : ∀ {Γ Δ A} -> Subst Γ Δ -> Tm Γ A -> Subst Γ (Δ , A)
  _∘_ : ∀ {Γ₁ Γ₂ Γ₃} -> Subst Γ₃ Γ₂ -> Subst Γ₂ Γ₁ -> Subst Γ₃ Γ₁
  ↑ : ∀ {Γ A} -> Subst (Γ , A) Γ

  -- equations for terms
  β : ∀ {Γ A B} (t : Tm (Γ , A) B) (s : Tm Γ A) ->
      ƛ t · s ≡ [ id ,, s ] t
  []app : ∀ {Γ Δ A B} (σ : Subst Γ Δ) (t₁ : Tm Δ (A ⇒ B)) (t₂ : Tm Δ A) ->
          [ σ ] (t₁ · t₂) ≡ [ σ ] t₁ · [ σ ] t₂
  []lam : ∀ {Γ Δ A B} (σ : Subst Γ Δ) (t : Tm (Δ , A) B) ->
          [ σ ] (ƛ t) ≡ ƛ ([ ↑ ∘ σ ,, ▵ ] t)
  [id]▵ : ∀ {Γ A} -> [ id {Γ , A} ] ▵ ≡ ▵
  [,,]▵ : ∀ {Γ Δ A} (σ : Subst Γ Δ) (t : Tm Γ A) -> [ σ ,, t ] ▵ ≡ t
  [][] : ∀ {Γ₃ Γ₁ Γ₂ A} (σ₁ : Subst Γ₃ Γ₂) (σ₂ : Subst Γ₂ Γ₁) (t : Tm Γ₁ A) ->
         [ σ₁ ] ([ σ₂ ] t) ≡ [ σ₁ ∘ σ₂ ] t

  -- equations for substitutions
  ∘id : ∀ {Γ Δ} (σ : Subst Γ Δ) -> σ ∘ id ≡ σ
  id∘↑ : ∀ {Γ A} -> id ∘ ↑ ≡ ↑ {Γ} {A}
  ,,↑ : ∀ {Γ Δ A} (σ : Subst Γ Δ) (t : Tm Γ A) -> (σ ,, t) ∘ ↑ ≡ σ
  ∘ass : ∀ {Γ₁ Γ₂ Γ₃ Γ₄} (σ₁ : Subst Γ₄ Γ₃) (σ₂ : Subst Γ₃ Γ₂) (σ₃ : Subst Γ₂ Γ₁) -> (σ₁ ∘ σ₂) ∘ σ₃ ≡ σ₁ ∘ (σ₂ ∘ σ₃)
  ∘,, : ∀ {Γ Δ Γ' A} (σ : Subst Γ Δ) (ρ : Subst Δ Γ') (t : Tm Δ A) ->
        σ ∘ (ρ ,, t) ≡ σ ∘ ρ ,, [ σ ] t

  trunc : ∀ {Γ α} -> isSet (Tm' Γ α)

infixl 10 _·_
infixl 20 _,,_
infixl 30 _∘_

module Tm-elim {ℓ} {P : {Γ : Ctx} {α : ⊙} -> Tm' Γ α -> Set ℓ}
  -- terms
  (ƛ* : ∀ {Γ A B} {t : Tm (Γ , A) B} ->
        P t -> P (ƛ t))
  (u* : ∀ {Γ} -> P (u {Γ}))
  (▵* : ∀ {Γ A} -> P (▵ {Γ} {A}))
  (_·*_ : ∀ {Γ A B} {t₁ : Tm Γ (A ⇒ B)} {t₂} ->
          P t₁ -> P t₂ -> P (t₁ · t₂))
  ([_]* : ∀ {Γ Δ A} {σ : Subst Γ Δ} {t : Tm Δ A} ->
          P σ -> P t -> P ([ σ ] t))

  -- substitutions
  (id* : ∀ {Γ} -> P (id {Γ}))
  (_,,*_ : ∀ {Γ A Δ} {σ : Subst Δ Γ} {t : Tm Δ A} ->
           P σ -> P t -> P (σ ,, t))
  (_∘*_ : ∀ {Γ₁ Γ₂ Γ₃} {σ₁ : Subst Γ₃ Γ₂} {σ₂ : Subst Γ₂ Γ₁} ->
          P σ₁ -> P σ₂ -> P (σ₁ ∘ σ₂))
  (↑* : ∀ {Γ A} -> P (↑ {Γ} {A}))

  -- equations for terms
  (β* : ∀ {Γ A B} {t : Tm (Γ , A) B} {s : Tm Γ A}
        (t* : P t) (s* : P s) ->
        PathP (λ i -> P (β t s i))
              (ƛ* t* ·* s*)
              ([ id* ,,* s* ]* t*))
  ([]app* : ∀ {Γ Δ A B} {σ : Subst Δ Γ} {t₁ : Tm Γ (A ⇒ B)} {t₂ : Tm Γ A} ->
            (σ* : P σ) (t₁* : P t₁) (t₂* : P t₂) ->
            PathP (λ i -> P ([]app σ t₁ t₂ i))
                  ([ σ* ]* (t₁* ·* t₂*))
                  ([ σ* ]* t₁* ·* [ σ* ]* t₂*))
  ([]lam* : ∀ {Γ Δ A B} {σ : Subst Δ Γ} {t : Tm (Γ , A) B}
            (σ* : P σ) (t* : P t) ->
            PathP (λ i -> P ([]lam σ t i))
                  ([ σ* ]* (ƛ* t*))
                  (ƛ* ([ (↑* ∘* σ*) ,,* ▵* ]* t*)))
  ([id]▵* : ∀ {Γ A} ->
            PathP (λ i -> P ([id]▵ {Γ} {A} i))
                  ([ id* ]* ▵*)
                  ▵*)
  ([,,]▵* : ∀ {Γ Δ A} {σ : Subst Δ Γ} {t : Tm Δ A}
            (σ* : P σ) (t* : P t) ->
            PathP (λ i -> P ([,,]▵ σ t i))
                  ([ σ* ,,* t* ]* ▵*)
                  t*)
  ([][]* : ∀ {Γ₁ Γ₂ Γ₃ A} {σ₁ : Subst Γ₁ Γ₂} {σ₂ : Subst Γ₂ Γ₃} {t : Tm Γ₃ A}
          (σ₁* : P σ₁) (σ₂* : P σ₂) (t* : P t) ->
          PathP (λ i -> P ([][] σ₁ σ₂ t i))
                ([ σ₁* ]* ([ σ₂* ]* t*))
                ([ σ₁* ∘* σ₂* ]* t*))

  -- equations for substitutions
  (∘id* : ∀ {Γ Δ} {σ : Subst Δ Γ}
          (σ* : P σ) ->
          PathP (λ i -> P (∘id σ i))
                (σ* ∘* id*)
                σ*)
  (id∘↑* : ∀ {Γ A} ->
           PathP (λ i -> P (id∘↑ {Γ} {A} i))
                 (id* ∘* ↑*)
                 ↑*)
  (,,↑* : ∀ {Γ Δ A} {σ : Subst Δ Γ} {t : Tm Δ A}
          (σ* : P σ) (t* : P t) ->
          PathP (λ i -> P (,,↑ σ t i))
                ((σ* ,,* t*) ∘* ↑* )
                σ*)
  (∘ass* : ∀ {Γ₁ Γ₂ Γ₃ Γ₄} {σ₁ : Subst Γ₄ Γ₃} {σ₂ : Subst Γ₃ Γ₂} {σ₃ : Subst Γ₂ Γ₁}
           (σ₁* : P σ₁) (σ₂* : P σ₂) (σ₃* : P σ₃) ->
           PathP (λ i -> P (∘ass σ₁ σ₂ σ₃ i))
                 ((σ₁* ∘* σ₂*) ∘* σ₃*)
                 (σ₁* ∘* (σ₂* ∘* σ₃*)))
  (∘,,* : ∀ {Γ Δ Γ' A} {σ : Subst Δ Γ} {ρ : Subst Γ Γ'} {t : Tm Γ A}
          (σ* : P σ) (ρ* : P ρ) (t* : P t) ->
          PathP (λ i -> P (∘,, σ ρ t i))
                (σ* ∘* (ρ* ,,* t*))
                ((σ* ∘* ρ*) ,,* [ σ* ]* t*))
  (trunc* : ∀ {Γ α} (x : Tm' Γ α) -> isSet (P x))
  where

  f : ∀ {Γ α} (x : Tm' Γ α) -> P x
  -- term syntax
  f (ƛ x) = ƛ* (f x)
  f u = u*
  f ▵ = ▵*
  f (x · x₁) = f x ·* f x₁
  f ([ x ] x₁) = [ f x ]* (f x₁)

  -- substitution syntax
  f id = id*
  f (x ,, x₁) = f x ,,* f x₁
  f (x ∘ x₁) = f x ∘* f x₁
  f ↑ = ↑*

  -- term equations
  f (β t s i) = β* (f t) (f s) i
  f ([]app σ t₁ t₂ i) = []app* (f σ) (f t₁) (f t₂) i
  f ([]lam σ t i) = []lam* (f σ) (f t) i
  f ([id]▵ i) = [id]▵* i
  f ([,,]▵ σ t i) = [,,]▵* (f σ) (f t) i
  f ([][] σ₁ σ₂ t i) = [][]* (f σ₁) (f σ₂) (f t) i
  f (∘id σ i) = ∘id* (f σ) i
  f (id∘↑ i) = id∘↑* i
  f (,,↑ σ t i) = ,,↑* (f σ) (f t) i
  f (∘ass σ₁ σ₂ σ₃ i) = ∘ass* (f σ₁) (f σ₂) (f σ₃) i
  f (∘,, σ ρ t i) = ∘,,* (f σ) (f ρ) (f t) i
  f (trunc x₁ x₂ p q i j) =
    isOfHLevel→isOfHLevelDep {n = 2} trunc* (f x₁) (f x₂) (cong f p) (cong f q) (trunc x₁ x₂ p q) i j

module Tm-elim-prop {ℓ} {P : {Γ : Ctx} {α : ⊙} -> Tm' Γ α -> Set ℓ} (PProp : ∀ {Γ α} {x : Tm' Γ α} -> isProp (P x))
  -- terms
  (ƛ* : ∀ {Γ A B} {t : Tm (Γ , A) B} ->
        P t -> P (ƛ t))
  (u* : ∀ {Γ} -> P (u {Γ}))
  (▵* : ∀ {Γ A} ->
        P (▵ {Γ} {A}))
  (_·*_ : ∀ {Γ A B} {t₁ : Tm Γ (A ⇒ B)} {t₂} ->
          P t₁ -> P t₂ -> P (t₁ · t₂))
  ([_]* : ∀ {Γ Δ A} {σ : Subst Γ Δ} {t : Tm Δ A} ->
          P σ -> P t -> P ([ σ ] t))

  -- substitutions
  (id* : ∀ {Γ} -> P (id {Γ}))
  (_,,*_ : ∀ {Γ A Δ} {σ : Subst Δ Γ} {t : Tm Δ A} ->
           P σ -> P t -> P (σ ,, t))
  (_∘*_ : ∀ {Γ₁ Γ₂ Γ₃} {σ₁ : Subst Γ₃ Γ₂} {σ₂ : Subst Γ₂ Γ₁} ->
          P σ₁ -> P σ₂ -> P (σ₁ ∘ σ₂))
  (↑* : ∀ {Γ A} -> P (↑ {Γ} {A}))
  where

  f : ∀ {Γ α} (x : Tm' Γ α) -> P x
  f = Tm-elim.f ƛ* u* ▵* _·*_ [_]* id* _,,*_ _∘*_ ↑*
                (λ _ _ → toPathP (PProp _ _))
                (λ _ _ _ → toPathP (PProp _ _))
                (λ _ _ → toPathP (PProp _ _))
                (toPathP (PProp _ _))
                (λ _ _ → toPathP (PProp _ _))
                (λ _ _ _ → toPathP (PProp _ _))
                (λ _ -> toPathP (PProp _ _))
                (toPathP (PProp _ _))
                (λ _ _ → toPathP (PProp _ _))
                (λ _ _ _ → toPathP (PProp _ _))
                (λ _ _ _ → toPathP (PProp _ _))
                (λ {Γ α} x -> isProp→isSet (PProp {Γ} {α}))

module Tm-rec {ℓ} {P : Type ℓ} (PSet : isSet P)
  -- terms
  (ƛ* : P -> P)
  (u* : P)
  (▵* : P)
  (_·*_ : P -> P -> P)
  ([_]* : P -> P -> P)

  -- substitutions
  (id* : P)
  (_,,*_ : P -> P -> P)
  (_∘*_ : P -> P -> P)
  (↑* : P)

  -- equations for terms
  (β* : (t* : P) (s* : P) -> ƛ* t* ·* s* ≡ [ id* ,,* s* ]* t*)
  ([]app* : (σ* : P) (t₁* : P) (t₂* : P) -> [ σ* ]* (t₁* ·* t₂*) ≡ [ σ* ]* t₁* ·* [ σ* ]* t₂*)
  ([]lam* : (σ* : P) (t* : P) -> [ σ* ]* (ƛ* t*) ≡ ƛ* ([ (↑* ∘* σ*) ,,* ▵* ]* t*))
  ([id]▵* : [ id* ]* ▵* ≡ ▵*)
  ([,,]▵* : (σ* : P) (t* : P) -> [ σ* ,,* t* ]* ▵* ≡ t*)
  ([][]* : (σ₁* : P) (σ₂* : P) (t* : P) -> [ σ₁* ]* ([ σ₂* ]* t*) ≡ [ σ₁* ∘* σ₂* ]* t*)

  -- equations for substitutions
  (∘id* : (σ* : P) -> σ* ∘* id* ≡ σ*)
  (id∘↑* : id* ∘* ↑* ≡ ↑*)
  (,,↑* : (σ* : P) (t* : P) -> (σ* ,,* t*) ∘* ↑* ≡ σ*)
  (∘ass* : (σ₁* : P) (σ₂* : P) (σ₃* : P) -> (σ₁* ∘* σ₂*) ∘* σ₃* ≡ σ₁* ∘* (σ₂* ∘* σ₃*))
  (∘,,* : (σ* : P) (ρ* : P) (t* : P) -> σ* ∘* (ρ* ,,* t*) ≡ (σ* ∘* ρ*) ,,* [ σ* ]* t*)
  where

  f : ∀ {Γ α} -> Tm' Γ α -> P
  f = Tm-elim.f ƛ* u* ▵* _·*_ [_]* id* _,,*_ _∘*_ ↑* β* []app* []lam* [id]▵* [,,]▵* [][]* ∘id* id∘↑* ,,↑* ∘ass* ∘,,* (λ _ → PSet)

-- | No-confusion property for Ctx.
CtxCode : (Γ Δ : Ctx) -> Set
CtxCode ε ε = ⊤
CtxCode ε (Δ , x) = ⊥
CtxCode (Γ , x) ε = ⊥
CtxCode (Γ , x) (Δ , x₁) = ⊤

Ctx→Code : (Γ Δ : Ctx) → (p : Γ ≡ Δ) -> CtxCode Γ Δ
Ctx→Code ε Δ p = J (λ y x → CtxCode ε y) tt p
Ctx→Code (Γ , x) Δ p = J (λ y x₁ → CtxCode (Γ , x) y) tt p

,-not-ε : ∀ {Γ A ℓ} {C : Set ℓ} -> Γ , A ≡ ε → C
,-not-ε p = ⊥-elim (Ctx→Code _ _ p)


{-
open import Data.Fin renaming ( suc to fs ; zero to fz )
open import Data.Nat
open import Data.Empty
open import Data.Unit

module Fin-elim {ℓ} {P : ∀ {n} -> Fin n -> Set ℓ} 
  (zero* : ∀ {n} -> P {suc n} fz)
  (suc* : ∀ {n} {i : Fin n} -> P {n} i -> P {suc n} (fs i))
  where
  
  f : ∀ {n} (i : Fin n) -> P i
  f 0F = zero*
  f (fs i) = suc* (f i)

-- fin-rec : ∀ {ℓ} {P : Set ℓ} -> ∀ {n} -> (ℕ -> P) -> ((n : ℕ) -> Fin n -> P -> P) -> (i : Fin n) -> P
-- fin-rec z s 0F = z
-- fin-rec z s (fs i) = s (fin-rec z s i)

-- foo : ∀ {n} -> Fin n -> Set
-- foo i = fin-rec {P = Set₀} ⊥ (λ x → ⊤) i

Nope : (n m : ℕ) -> Set
Nope 0F 0F = ⊤
Nope 0F (suc m) = ⊥
Nope (suc n) 0F = ⊥
Nope (suc n) (suc m) = Nope n m

Nope-refl : ∀ n -> Nope n n
Nope-refl 0F = tt
Nope-refl (suc n) = Nope-refl n

≡→Nope : ∀ n m -> n ≡ m → Nope n m
≡→Nope 0F m p = J (λ y x → Nope zero y) tt p
≡→Nope (suc n) m p = J (λ y x → Nope (suc n) y) (Nope-refl n) p

Nope→≡ : ∀ n m -> Nope n m → n ≡ m
Nope→≡ 0F 0F c = refl
Nope→≡ (suc n) (suc m) c = cong suc (Nope→≡ n m c)

suc-not-zero : ∀ {n} -> suc n ≡ zero -> ⊥
suc-not-zero p = ≡→Nope _ _ p 

Nope-refl→refl : ∀ n -> Nope→≡ n n (Nope-refl n) ≡ refl
Nope-refl→refl 0F = refl
Nope-refl→refl (suc n) = λ i j → suc (Nope-refl→refl n i j)

Nope→≡→Nope : ∀ n m (p : n ≡ m) -> Nope→≡ n m (≡→Nope n m p) ≡ p
Nope→≡→Nope 0F 0F c = λ i → {!c!}
Nope→≡→Nope 0F (suc m) c = {!!}
Nope→≡→Nope (suc n) m c = {!!}

≡→Nope→≡ : ∀ n m (c : Nope n m) -> ≡→Nope n m (Nope→≡ n m c) ≡ c
≡→Nope→≡ 0F 0F tt = JRefl (λ y x → {!!}) tt
≡→Nope→≡ (suc n) (suc m) c with ≡→Nope→≡ n m c
... | w = {!!}

fin0elim : {A : Set} -> Fin zero -> A
fin0elim {A} i = Fin-elim.f {P = λ {n} x → n ≡ zero → A} (λ x → ⊥-elim (suc-not-zero x)) (λ x x₁ → ⊥-elim (suc-not-zero x₁)) i refl

-}
