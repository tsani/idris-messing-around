{-# OPTIONS --cubical #-}

module WellScoped where

open import Data.Nat
open import Cubical.Foundations.Prelude renaming ( _,_ to _,,_ )
open import Data.Product renaming ( _,_ to _,,_ )

data Fin : ℕ → Set where
  FZ : ∀ {k} → Fin (suc k)
  FS : ∀ {k} → Fin k → Fin (suc k)

-- Dependent finite maps.
FinDep : ∀ {ℓ} (n : ℕ) -> (Fin n -> Set ℓ) -> Set ℓ
FinDep n P = (i : Fin n) -> P i

-- Simply-typed finite maps.
FinMap : ∀ {ℓ} (n : ℕ) → Set ℓ → Set ℓ
FinMap n t = Fin n -> t

ε : ∀ {ℓ} {t : Set ℓ} -> FinMap zero t
ε = λ ()

infixl 50 _·_
data Tm (n : ℕ) : Set where
  C : Tm n
  Var : Fin n → Tm n
  Lam : Tm (suc n) → Tm n
  _·_ : Tm n → Tm n → Tm n

infixr 10 _~>_
data Tp : Set where
  Base : Tp
  _~>_ : Tp → Tp → Tp

-- Simply-typed finite map extension.
-- We can't just use the dependent version all the time because the
-- output type's codomain is slightly different. In particular, if you
-- use `f ,' x` for a simply-typed map, you end up with a
-- `FinMap (suc n) (extend (const t) t)` which is not definitionally
-- equal to `FinMap (suc n) (const t)`.
_,_ : ∀ {n ℓ} {t : Set ℓ} -> FinMap n t -> t -> FinMap (suc n) t
(f , x) FZ = x
(f , _) (FS i) = f i
infixl 8 _,_

-- Dependent finite map extension.
-- Turns out to not be very useful because we need better definitional
-- equalities.
_,'_ : ∀ {ℓ n} {P : FinMap n (Set ℓ)} {t : Set ℓ} ->
       FinDep n P -> t -> FinDep (suc n) (P , t)
(f ,' x) FZ = x
(f ,' _) (FS i) = f i
infixl 8 _,'_

-- A finite map to another finite set.
Renaming : (dst : ℕ) -> (src : ℕ) -> Set
Renaming dst src = FinMap src (Fin dst)

-- Identity renaming.
idᵣ : ∀ {n} -> Renaming n n
idᵣ i = i

-- Elementary function composition.
_∘_ : ∀ {A B C : Set} -> (f : B -> C) (g : A -> B) -> A -> C
(f ∘ g) x = f (g x)

-- Weakening of renamings.
_↑ᵣ : ∀ {n k} -> Renaming n k -> Renaming (suc n) k
(r ↑ᵣ) i = FS (r i)

-- Extension of a renaming, to deal with bound variables.
extendᵣ : ∀ {n k} -> Renaming n k -> Renaming (suc n) (suc k)
extendᵣ r = r ↑ᵣ , FZ

-- Renaming extension distributes over composition.
extendᵣ-∘' : ∀ {n k j} -> (r1 : Renaming n k) -> (r2 : Renaming k j) ->
             (i : Fin (suc j)) ->
             (extendᵣ r1 ∘ extendᵣ r2) i ≡ extendᵣ (r1 ∘ r2) i
extendᵣ-∘' r1 r2 FZ = refl
extendᵣ-∘' r1 r2 (FS _) = refl

-- Renaming extension distributes over composition, extensionally.
extendᵣ-∘ : ∀ {n k j} (r1 : Renaming n k) (r2 : Renaming k j) ->
            extendᵣ r1 ∘ extendᵣ r2 ≡ extendᵣ (r1 ∘ r2)
extendᵣ-∘ r1 r2 = funExt (extendᵣ-∘' r1 r2)

-- Application of a renaming to a term.
[_]ᵣ : ∀ {n k} -> Renaming n k -> Tm k -> Tm n
[_]ᵣ ρ (Var x) = Var (ρ x)
[_]ᵣ ρ (Lam x) = Lam ([ extendᵣ ρ ]ᵣ x)
[_]ᵣ ρ C = C
[_]ᵣ ρ (x · y) = ([ ρ ]ᵣ x) · ([ ρ ]ᵣ y)

-- Composition factors through application of renaming.
apply-∘ᵣ : ∀ {n k j} -> (ρ₁ : Renaming n k) -> (ρ₂ : Renaming k j) ->
          (t : Tm j) ->
          [ ρ₁ ]ᵣ ([ ρ₂ ]ᵣ t) ≡ [ ρ₁ ∘ ρ₂ ]ᵣ t
apply-∘ᵣ ρ₁ ρ₂ (Var x) = refl
apply-∘ᵣ ρ₁ ρ₂ C = refl
apply-∘ᵣ ρ₁ ρ₂ (Lam x) =
  cong Lam
    ( subst (λ p -> [ extendᵣ ρ₁ ]ᵣ ([ extendᵣ ρ₂ ]ᵣ x) ≡ [ p ]ᵣ x)
            (extendᵣ-∘ ρ₁ ρ₂)
            (apply-∘ᵣ (extendᵣ ρ₁) (extendᵣ ρ₂) x))
apply-∘ᵣ ρ₁ ρ₂ (x · y) = cong₂ _·_ (apply-∘ᵣ ρ₁ ρ₂ x) (apply-∘ᵣ ρ₁ ρ₂ y)

apply-∘ᵣ-ext : ∀ {n k j} -> (ρ₁ : Renaming n k) -> (ρ₂ : Renaming k j) ->
               [ ρ₁ ]ᵣ ∘ [ ρ₂ ]ᵣ ≡ [ ρ₁ ∘ ρ₂ ]ᵣ
apply-∘ᵣ-ext ρ₁ ρ₂ = funExt (apply-∘ᵣ ρ₁ ρ₂)

-- Substitution is a finite map to well-scoped terms.
Subst : (dst : ℕ) (src : ℕ) -> Set
Subst dst src = FinMap src (Tm dst)

idₛ : ∀ {n} -> Subst n n
idₛ i = Var i

-- Weakening of a term.
-- Simply apply a weakened identity renaming.
_↑ₜ : ∀ {n} -> Tm n -> Tm (suc n)
t ↑ₜ = [ idᵣ ↑ᵣ ]ᵣ t

-- Weakening of a substitution.
-- Simply weaken the terms that come out of the substitution.
_↑ₛ : ∀ {n k} -> Subst n k -> Subst (suc n) k
(σ ↑ₛ) i = (σ i) ↑ₜ

-- Extend a substitution, to deal with bound variables.
extendₛ : ∀ {n k} -> Subst n k -> Subst (suc n) (suc k)
extendₛ σ = σ ↑ₛ , Var FZ

-- Application of a substitution to a term.
[_]ₛ : ∀ {n k} -> Subst n k -> Tm k -> Tm n
[ σ ]ₛ (Var x) = σ x
[ σ ]ₛ (Lam t) = Lam ([ extendₛ σ ]ₛ t)
[ σ ]ₛ C = C
[ σ ]ₛ (t₁ · t₂) = ([ σ ]ₛ t₁) · ([ σ ]ₛ t₂)

-- Extend distributes over composition with a renaming.
extend-∘ₛᵣ' : ∀ {n k j} (σ : Subst n k) (ρ : Renaming k j) (i : Fin (suc j)) ->
              (extendₛ σ ∘ extendᵣ ρ) i ≡ extendₛ (σ ∘ ρ) i
extend-∘ₛᵣ' σ ρ FZ = refl
extend-∘ₛᵣ' σ ρ (FS i) = refl

-- Extend distributes over composition with a renaming, extensionally.
extend-∘ₛᵣ : ∀ {n k j} (σ : Subst n k) (ρ : Renaming k j) ->
             extendₛ σ ∘ extendᵣ ρ ≡ extendₛ (σ ∘ ρ)
extend-∘ₛᵣ σ ρ = funExt (extend-∘ₛᵣ' σ ρ)

-- Substitution-Renaming composition lemma.
apply-∘ₛᵣ : ∀ {n k j} (σ : Subst n k) (ρ : Renaming k j) (t : Tm j) ->
            [ σ ]ₛ ([ ρ ]ᵣ t) ≡ ([ σ ∘ ρ ]ₛ t)
apply-∘ₛᵣ σ ρ (Var x) = refl
apply-∘ₛᵣ σ ρ C = refl
apply-∘ₛᵣ σ ρ (Lam t) =
  cong Lam (( subst (λ σ' -> [ extendₛ σ ]ₛ ([ extendᵣ ρ ]ᵣ t) ≡ [ σ' ]ₛ t)
            (extend-∘ₛᵣ σ ρ)
            (apply-∘ₛᵣ (extendₛ σ) (extendᵣ ρ) t)))
apply-∘ₛᵣ σ ρ (t₁ · t₂) =  cong₂ _·_ (apply-∘ₛᵣ σ ρ t₁) (apply-∘ₛᵣ σ ρ t₂)

-- Apply a renaming to a substitution
_∘ᵣ_ : ∀ {n k j} (ρ : Renaming n k) (σ : Subst k j) ->
     Subst n j
( ρ ∘ᵣ σ) i = [ ρ ]ᵣ (σ i)

-- Extend distributes over composition of renaming with substitution.
extend-∘ᵣₛ' : ∀ {n k j} (ρ : Renaming n k) (σ : Subst k j) (i : Fin (suc j)) ->
              (extendᵣ ρ ∘ᵣ extendₛ σ) i ≡ extendₛ (ρ ∘ᵣ σ) i
extend-∘ᵣₛ' ρ σ FZ = refl
extend-∘ᵣₛ' ρ σ (FS i) =
  subst ( λ P -> P (σ i) ≡ [ FS ]ᵣ ([ ρ ]ᵣ (σ i)))
        (sym (apply-∘ᵣ-ext (extendᵣ ρ) FS))
        (subst (λ P -> ([ extendᵣ ρ ∘ FS ]ᵣ (σ i)) ≡ P (σ i))
               (sym (apply-∘ᵣ-ext FS ρ))
               refl)

-- Extend distributes over composition of renaming with substitution,
-- extensionally.
extend-∘ᵣₛ : ∀ {n k j} (ρ : Renaming n k) (σ : Subst k j) ->
             extendᵣ ρ ∘ᵣ extendₛ σ ≡ extendₛ (ρ ∘ᵣ σ)
extend-∘ᵣₛ ρ σ = funExt (extend-∘ᵣₛ' ρ σ)

-- Renaming-Substitution composition lemma.
apply-∘ᵣₛ : ∀ {n k j} (ρ : Renaming n k) (σ : Subst k j) (t : Tm j) ->
            [ ρ ]ᵣ ([ σ ]ₛ t) ≡ [ ρ ∘ᵣ σ ]ₛ t
apply-∘ᵣₛ ρ σ (Var x) = refl
apply-∘ᵣₛ ρ σ C = refl
apply-∘ᵣₛ ρ σ (Lam t) =
  cong Lam (( subst (λ ρ' -> [ extendᵣ ρ ]ᵣ ([ extendₛ σ ]ₛ t) ≡ [ ρ' ]ₛ t)
            (extend-∘ᵣₛ ρ σ)
              (apply-∘ᵣₛ (extendᵣ ρ) (extendₛ σ) t)))
apply-∘ᵣₛ ρ σ (t₁ · t₂) = cong₂ _·_ (apply-∘ᵣₛ ρ σ t₁) (apply-∘ᵣₛ ρ σ t₂)

-- Form a substitution to eliminate the head variable.
single : ∀ {n} -> Tm n -> Subst n (suc n)
single t = idₛ , t

-- Contexts are finite maps to types.
Ctx : ℕ -> Set
Ctx n = FinMap n Tp

data _⊢v_of_ {n : ℕ} (Γ : Ctx n) : Fin n -> Tp -> Set where
  Hyp : (i : Fin n) -> Γ ⊢v i of Γ i

-- Term typing judgment.
data _⊢_of_ {n : ℕ} (Γ : Ctx n) : Tm n -> Tp -> Set where
  C : Γ ⊢ C of Base
  Hyp : ∀ {i A} -> Γ ⊢v i of A -> Γ ⊢ Var i of A
  Abs : ∀ {A B t} -> Γ , A ⊢ t of B -> Γ ⊢ Lam t of A ~> B
  App : ∀ {A B s t} ->
        Γ ⊢ s of A ~> B -> Γ ⊢ t of A ->
        Γ ⊢ s · t of B
infix 5 _⊢_of_

_⊢ᵣ_from_ : ∀ {n k} (Γ : Ctx n) (ρ : Renaming n k) (Δ : Ctx k) -> Set
Γ ⊢ᵣ ρ from Δ = FinDep _ λ i -> (Γ ⊢v ρ i of Δ i) × (Γ ∘ ρ) i ≡ Δ i
infix 5 _⊢ᵣ_from_

ctx-weak' : ∀ {k A} {Γ : Ctx k} (i : Fin k) ->
            ((Γ , A) ∘ FS) i ≡ Γ i
ctx-weak' FZ = refl
ctx-weak' (FS f) = refl

ctx-weak : ∀ {k A} {Γ : Ctx k} ->
           ((Γ , A) ∘ FS) ≡ Γ
ctx-weak {A = A} = funExt (ctx-weak' {A = A})

ctx-eq : ∀ {n k} {Γ : Ctx k} {Δ : Ctx n} {ρ : Renaming n k} ->
         Δ ⊢ᵣ ρ from Γ -> Δ ∘ ρ ≡ Γ
ctx-eq dr = funExt (λ i -> snd (dr i))

typing-∘ᵣ : ∀ {n k j} {Γ : Ctx n} {ρ₁ : Renaming n k} {ρ₂ : Renaming k j} {Δ : Ctx k} {Ψ : Ctx j} ->
            Γ ⊢ᵣ ρ₁ from Δ -> Δ ⊢ᵣ ρ₂ from Ψ -> Γ ⊢ᵣ (ρ₁ ∘ ρ₂) from Ψ
typing-∘ᵣ {Γ = Γ} {ρ₁ = ρ₁} {ρ₂ = ρ₂} dr1 dr2 i with (snd (dr1 (ρ₂ i))) ∙ (snd (dr2 i))
... | eq = subst (λ Ψ -> Γ ⊢v (ρ₁ (ρ₂ i)) of Ψ) eq (Hyp (ρ₁ (ρ₂ i))) ,, eq
 
-- Substitution typing is a dependent finite map, from de Bruijn
-- indices to typing derivations on the extracted term.
_⊢_from_ : ∀ {n k} (Γ : Ctx n) (σ : Subst n k) (Δ : Ctx k) -> Set
Γ ⊢ σ from Δ = FinDep _ λ i -> Γ ⊢ σ i of Δ i
infix 2 _⊢_from_

-- Remarkably, the Hyp constructor lifts definitionally to the typing
-- of the identity substitution.
idΓ : ∀ {n} {Γ : Ctx n} -> Γ ⊢ idₛ from Γ
idΓ i = Hyp (Hyp i)

extend-ren : ∀ {n k i A} {Γ : Ctx n} {Δ : Ctx k} {ρ : Renaming n k} ->
             Γ ⊢ᵣ ρ from Δ -> Γ ⊢v i of A -> Γ ⊢ᵣ ρ , i from Δ , A
extend-ren dr (Hyp i) FZ = (Hyp i) ,, refl
extend-ren dr di (FS i) = dr i

extend-subst : ∀ {n k t A} {Γ : Ctx n} {Δ : Ctx k} {σ : Subst n k} ->
               Γ ⊢ σ from Δ -> Γ ⊢ t of A -> Γ ⊢ σ , t from Δ , A
extend-subst ds dt FZ = dt
extend-subst ds dt (FS i) = ds i
-- ^ We would have liked to just use dependent extension (_,'_), but
-- it doesn't give us the desired definitional equality.

single-subst : ∀ {n t A} {Γ : Ctx n} ->
               Γ ⊢ t of A -> Γ ⊢ single t from Γ , A
single-subst dt =  extend-subst idΓ dt

ren-weaken : ∀ {n k A} {Δ : Ctx n} {Γ : Ctx k} {ρ : Renaming k n} ->
             Γ ⊢ᵣ ρ from Δ -> Γ , A ⊢ᵣ ρ ↑ᵣ from Δ
ren-weaken {A = A} {Γ = Γ} {ρ = ρ} dr i =
  subst (λ Δ -> (Γ , A) ⊢v (ρ ↑ᵣ) i of Δ) (snd (dr i)) (Hyp (FS (ρ i))) ,, snd (dr i)

extend-typingᵣ : ∀ {n k A} {Δ : Ctx n} {Γ : Ctx k} {ρ : Renaming n k} ->
                 Δ ⊢ᵣ ρ from Γ -> Δ , A ⊢ᵣ extendᵣ ρ from Γ , A
extend-typingᵣ {ρ = ρ} dr = extend-ren (ren-weaken dr) (Hyp FZ)

ren-lemma : ∀ {n k t A} {Δ : Ctx k} {Γ : Ctx n} {ρ : Renaming k n} ->
            Δ ⊢ᵣ ρ from Γ -> Γ ⊢ t of A -> Δ ⊢ [ ρ ]ᵣ t of A
ren-lemma dr C = C
ren-lemma dr (Hyp (Hyp i)) = Hyp (fst (dr i))
ren-lemma dr (Abs dt) = Abs (ren-lemma (extend-typingᵣ dr) dt)
ren-lemma dr (App dt dt₁) = App (ren-lemma dr dt) (ren-lemma dr dt₁)

term-weaken : ∀ {n A C} {Δ : Ctx n} {t : Tm n} ->
              Δ ⊢ t of A -> Δ , C ⊢ t ↑ₜ of A
term-weaken C = C
term-weaken (Hyp (Hyp i)) = Hyp (Hyp (FS i))
term-weaken (Abs d) = Abs (ren-lemma (extend-typingᵣ (ren-weaken λ i -> Hyp i ,, refl)) d)
term-weaken (App d d₁) = App (term-weaken d) (term-weaken d₁)

subst-weaken : ∀ {n k A} {Δ : Ctx n} {Γ : Ctx k} {σ : Subst n k} ->
                Δ ⊢ σ from Γ -> Δ , A ⊢ σ ↑ₛ from Γ
subst-weaken {n} {k} {A} {Δ} {Γ} {σ} ds i =  term-weaken (ds i)

extend-typingₛ : ∀ {n k A} {Δ : Ctx n} {Γ : Ctx k} {σ : Subst n k} ->
                 Δ ⊢ σ from Γ -> Δ , A ⊢ extendₛ σ from Γ , A
extend-typingₛ d FZ = Hyp (Hyp FZ)
extend-typingₛ d (FS i) = subst-weaken d i 

subst-lemma : ∀ {n k t A} {Δ : Ctx k} {Γ : Ctx n} {σ : Subst k n} ->
              Δ ⊢ σ from Γ -> Γ ⊢ t of A -> Δ ⊢ [ σ ]ₛ t of A
subst-lemma ds C = C
subst-lemma ds (Hyp (Hyp i)) = ds i
subst-lemma ds (Abs dt) = Abs (subst-lemma (extend-typingₛ ds) dt)
subst-lemma ds (App dt dt₁) = App (subst-lemma ds dt) (subst-lemma ds dt₁)

data Value : Tm zero -> Set where
  Lam : ∀ {t} -> Value (Lam t)
  C : Value C

infix 15 _⟶_
data _⟶_ : Tm zero -> Tm zero -> Set where
  Beta : ∀ {t v} -> Value v -> Lam t · v ⟶ [ single v ]ₛ t
  App1 : ∀ {s s' t} -> s ⟶ s' ->
         s · t ⟶ s' · t
  App2 : ∀ {v t t'} -> Value v -> t ⟶ t' ->
         v · t ⟶ v · t'

-- Stepping preserves types.
tps : ∀ {t t' Γ A} -> t ⟶ t' -> Γ ⊢ t of A -> Γ ⊢ t' of A
tps (Beta x) (App (Abs d) d₁) = subst-lemma (single-subst d₁) d
tps (App1 e) (App d d₁) = App (tps e d) d₁
tps (App2 x e) (App d d₁) = App d (tps e d₁)
