{-# OPTIONS --cubical #-}

module LF where

open import Function
open import Data.Maybe
open import Data.Maybe.Categorical renaming ( monad to maybeMonad ; functor to maybeFunctor)
open import Category.Monad
open import Data.Nat
open import Data.Fin hiding ( _+_; _≤_ )
open import Cubical.Foundations.Prelude renaming ( _,_ to _,,_ )
open import Data.Product renaming ( _,_ to _,,_ )
open import Data.Sum

open RawMonad

module MaybeMonad {ℓ : Level} = RawMonad {f = ℓ} maybeMonad

≤-refl : ∀ {n} -> n ≤ n
≤-refl {zero} = z≤n
≤-refl {suc n} = s≤s ≤-refl

-- data Fin : ℕ → Set where
--   FZ : ∀ {k} → Fin (suc k)
--   FS : ∀ {k} → Fin k → Fin (suc k)

-- Dependent finite maps.
FinDep : ∀ {ℓ} (n : ℕ) -> (Fin n -> Set ℓ) -> Set ℓ
FinDep n P = (i : Fin n) -> P i

-- Simply-typed finite maps.
FinMap : ∀ {ℓ} (n : ℕ) → Set ℓ → Set ℓ
FinMap n t = Fin n -> t

-- The empty finite map.
ε : ∀ {ℓ} {t : Set ℓ} -> FinMap zero t
ε = λ ()

-- Uniqueness property of empty finite maps.
ε-unique : ∀ {ℓ} {t : Set ℓ} (f : FinMap zero t) -> f ≡ ε
ε-unique f = funExt (λ ())

-- Simply-typed finite map extension.
-- We can't just use the dependent version all the time because the
-- output type's codomain is slightly different. In particular, if you
-- use `f ,' x` for a simply-typed map, you end up with a
-- `FinMap (suc n) (extend (const t) t)` which is not definitionally
-- equal to `FinMap (suc n) (const t)`.
_,_ : ∀ {n ℓ} {t : Set ℓ} -> FinMap n t -> t -> FinMap (suc n) t
(f , x) zero = x
(f , _) (suc i) = f i
infixl 8 _,_

decompose' : ∀ {n} {ℓ} {t : Set ℓ} (f : Fin (suc n) → t)
               (x : Fin (suc n)) →
             ((λ x₁ → f (suc x₁)) , f zero) x ≡ f x
decompose' f zero = refl
decompose' f (suc i) = refl

decompose : ∀ {n ℓ t} (f : FinMap {ℓ} (suc n) t) -> (f ∘ suc) , f zero ≡ f
decompose f = funExt (decompose' f)

-- Dependent finite map extension.
-- Turns out to not be very useful because we need better definitional
-- equalities.
_,'_ : ∀ {ℓ n} {P : FinMap n (Set ℓ)} {t : Set ℓ} ->
       FinDep n P -> t -> FinDep (suc n) (P , t)
(f ,' x) zero = x
(f ,' _) (suc i) = f i
infixl 8 _,'_

module Renaming where
  -- A finite map to another finite set.
  Renaming : (dst : ℕ) (src : ℕ) -> Set
  Renaming dst src = FinMap src (Fin dst)

  -- Operations on renamings
  -- Note: plain function composition is composition of renamings.

  -- Weakening of renamings.
  _↑ᵣ : ∀ {n k} -> Renaming n k -> Renaming (suc n) k
  (r ↑ᵣ) i = suc (r i)
  
  -- Extension of a renaming, to deal with bound variables.
  extendᵣ : ∀ {n k} -> Renaming n k -> Renaming (suc n) (suc k)
  extendᵣ r = r ↑ᵣ , zero

  -- Special renamings.

  -- Identity renaming.
  idᵣ : ∀ {n} -> Renaming n n
  idᵣ i = i
  
  -- Weakening renaming
  wk : ∀ {n} -> Renaming (suc n) n
  wk = idᵣ ↑ᵣ

  wkₙ : ∀ {n} (k : ℕ) -> Renaming (k + n) n
  wkₙ zero = idᵣ
  wkₙ (suc k) = wkₙ k ↑ᵣ

  wkₙ' : ∀ {n} (k : ℕ) -> Renaming (n + k) n
  wkₙ' k = {! subst wkₙ k !}

  wk-fin : ∀ {n} (i : Fin n) -> Renaming n (n ∸ suc (toℕ i))
  wk-fin zero = wk
  wk-fin (suc i) = wk-fin i ↑ᵣ

  -- Properties of renamings --

  -- Renaming extension distributes over composition.
  extendᵣ-∘' : ∀ {n k j} (r1 : Renaming n k) (r2 : Renaming k j)
               (i : Fin (suc j)) ->
               (extendᵣ r1 ∘ extendᵣ r2) i ≡ extendᵣ (r1 ∘ r2) i
  extendᵣ-∘' r1 r2 zero = refl
  extendᵣ-∘' r1 r2 (suc _) = refl
  
  -- Renaming extension distributes over composition, extensionally.
  extendᵣ-∘ : ∀ {n k j} (r1 : Renaming n k) (r2 : Renaming k j) ->
              extendᵣ r1 ∘ extendᵣ r2 ≡ extendᵣ (r1 ∘ r2)
  extendᵣ-∘ r1 r2 = funExt (extendᵣ-∘' r1 r2)

open Renaming

module Syntax where
  -- Syntax of LF
  mutual
    -- | A spine is a sequence of normal terms.
    data Spine (n : ℕ) : Set where
      Nil : Spine n
      _::_ : Normal n -> Spine n -> Spine n
  
    -- | The head of an application.
    data Head (n : ℕ) : Set where
      BVar : Fin n -> Head n
      -- MVar : Fin m -> Head k n
      Const : ℕ -> Head n
  
    -- Since there's only one neutral form, we don't define neutral
    -- terms separately.
    -- data Neutral (n : ℕ) (m : ℕ) : Set where
    --   App : Head n m -> Spine n m -> Normal n m
      
    data Normal (n : ℕ) : Set where
      Lam : LF-Type n -> Normal (suc n) -> Normal n
      App : Head n -> Spine n -> Normal n
      -- Coe : Neutral n m -> Normal n m
  
    data LF-Type (n : ℕ) : Set where
      Atomic : ℕ -> -- which family in the signature we're using
               Spine n -> LF-Type n
      PiType : LF-Type n -> -- the type we're quantifying over
               LF-Type (suc n) -> -- the body of the Pi
               LF-Type n
    
  data LF-Kind (n : ℕ) : Set where
    Star : LF-Kind n
    PiKind : LF-Type n -> -- the type we're quantifying over
             LF-Kind (suc n) -> -- the body of the Pi
             LF-Kind n

  data LF-Type⁻ : Set where
    Atomic : ℕ -> LF-Type⁻
    _~>_ : LF-Type⁻ -> LF-Type⁻ -> LF-Type⁻
  
  [_]⁻ : ∀ {n} -> LF-Type n -> LF-Type⁻
  [ Atomic x x₁ ]⁻ = Atomic x
  [ PiType A A₁ ]⁻ = [ A ]⁻ ~> [ A₁ ]⁻

open Syntax

-- Application of a renaming for indices in the context
mutual
  [_]ᵣ-head : {n' n : ℕ} (ρ : Renaming n' n) (H : Head n) -> Head n'
  [ ρ ]ᵣ-head (BVar x) = BVar (ρ x)
  -- [ ρ ]ᵣ-head (MVar x) = MVar x
  [ ρ ]ᵣ-head (Const x) = Const x
  
  [_]ᵣ-normal : {n' n : ℕ} (ρ : Renaming n' n) (M : Normal n) -> Normal n'
  [ ρ ]ᵣ-normal (Lam A M) = Lam ([ ρ ]ᵣ-type A) ([ extendᵣ ρ ]ᵣ-normal M)
  [ ρ ]ᵣ-normal (App x x₁) = App ([ ρ ]ᵣ-head x) ([ ρ ]ᵣ-spine x₁)
  
  [_]ᵣ-spine : {n' n : ℕ} (ρ : Renaming n' n) (S : Spine n) -> Spine n'
  [ ρ ]ᵣ-spine Nil = Nil
  [ ρ ]ᵣ-spine (x :: S) = [ ρ ]ᵣ-normal x :: [ ρ ]ᵣ-spine S

  [_]ᵣ-type : {n' n : ℕ} (ρ : Renaming n' n) (T : LF-Type n) -> LF-Type n'
  [ ρ ]ᵣ-type (Atomic x x₁) = Atomic x ([ ρ ]ᵣ-spine x₁)
  [ ρ ]ᵣ-type (PiType T T₁) = PiType ([ ρ ]ᵣ-type T) ([ extendᵣ ρ ]ᵣ-type T₁)

[_]ᵣ-kind : {n' n : ℕ} (ρ : Renaming n' n) (K : LF-Kind n) -> LF-Kind n'
[ ρ ]ᵣ-kind Star = Star
[ ρ ]ᵣ-kind (PiKind x K) = PiKind ([ ρ ]ᵣ-type x) ([ extendᵣ ρ ]ᵣ-kind K)

infix 40 _++-spine_
_++-spine_ : ∀ {n} -> Spine n -> Spine n -> Spine n
Nil ++-spine S' = S'
(x :: S) ++-spine S' = x :: S ++-spine S'

Ctx⁻ : ℕ -> Set
Ctx⁻ n = FinMap n LF-Type⁻

-- Contexts are finite maps to types, which may depend on earlier variables.
Ctx : (n : ℕ) -> Set
Ctx n = FinDep n (λ i -> LF-Type (n ∸ suc (toℕ i)))

[_]⁻-ctx : ∀ {n} -> Ctx n -> Ctx⁻ n
[ Γ ]⁻-ctx i = [ Γ i ]⁻

extend-ctx : ∀ {n} -> Ctx n -> LF-Type n -> Ctx (suc n)
extend-ctx Γ A zero = A
extend-ctx Γ A (suc i) = Γ i

-- Signatures are finite maps to closed types or kinds, which may
-- depend on earlier definitions in the signature.
Sig : Set
Sig = ℕ -> Maybe (LF-Kind zero ⊎ LF-Type zero)

lookup-sig-kind : (Σ : Sig) (n : ℕ) -> Maybe (LF-Kind zero)
lookup-sig-kind Σ n = Σ n MaybeMonad.>>= isInj₁

lookup-sig-type : (Σ : Sig) (n : ℕ) -> Maybe (LF-Type zero)
lookup-sig-type Σ n = Σ n MaybeMonad.>>= isInj₂

lookup-sig-type' : (Σ : Sig) (n : ℕ) -> Maybe LF-Type⁻
lookup-sig-type' Σ n = Data.Maybe.map (λ A -> {!!}) (Σ n)

lookup-ctx : ∀ {n} (Γ : Ctx n) (i : Fin n) -> LF-Type n
lookup-ctx Γ i = [ wk-fin i ]ᵣ-type (Γ i)

module SimpleTyping where
  mutual
    data _,_⊢'_head-of_ {n : ℕ} (Σ : Sig) (Γ : Ctx⁻ n) : Head n -> LF-Type⁻ -> Set where
      BVar : {i : Fin n} -> Σ , Γ ⊢' BVar i head-of Γ i
      Const : {k : ℕ} -> {T : LF-Type⁻} ->
              lookup-sig-type' Σ k ≡ just T ->
              Σ , Γ ⊢' Const k head-of T

    data _,_⊢'_spine-of_↘_ {n : ℕ} (Σ : Sig) (Γ : Ctx⁻ n) : Spine n -> LF-Type⁻ -> LF-Type⁻ -> Set where
      Nil : ∀ {A} -> Σ , Γ ⊢' Nil spine-of A ↘ A
      Cons : ∀ {A B B' M S} ->
             Σ , Γ ⊢' M normal-of A ->
             Σ , Γ ⊢' S spine-of B ↘ B' ->
             Σ , Γ ⊢' M :: S spine-of (A ~> B) ↘ B'

    data _,_⊢'_normal-of_ {n : ℕ} (Σ : Sig) (Γ : Ctx⁻ n) : Normal n -> LF-Type⁻ -> Set where
      Lam : ∀ {A B M} -> 
            Σ , (Γ , [ A ]⁻) ⊢' M normal-of B ->
            Σ , Γ ⊢' Lam A M normal-of ([ A ]⁻ ~> B)

open SimpleTyping

∥_∥ : LF-Type⁻ -> ℕ
∥ Atomic x ∥ = 1
∥ A ~> A₁ ∥ = ∥ A ∥ + ∥ A₁ ∥
  
data Result {n : ℕ} (Σ : Sig) (Γ : Ctx⁻ n) : ℕ -> Set where
  Lam : ∀ {A B p} ->
        (M : Normal (suc n)) ->
        (Σ , Γ ⊢' Lam A M normal-of ([ A ]⁻ ~> B)) ->
        (∥ [ A ]⁻ ∥ + ∥ B ∥ ≤ p) ->
        Result Σ Γ p
  App : (H : Head n) -> (S : Spine n) ->
        -- Σ , Γ ⊢' App H S normal-of A ->
        Result Σ Γ zero

result-size : ∀ {n Σ b} {Γ : Ctx⁻ n} -> Result Σ Γ b -> ℕ
result-size (Lam {p = p} M x x₁) = p
result-size (App H S) = zero

-- Substitution: a finite map to normal objects.
Subst : (Σ : Sig) (n' n : ℕ) (Γ : Ctx⁻ n') -> Set
Subst Σ' n' n Γ = FinMap n (Σ ℕ (λ p -> Result Σ' Γ p))

extend-ctx⁻ : ∀ {n} -> Ctx n -> LF-Type n -> Ctx⁻ (suc n)
extend-ctx⁻ Γ A = [ Γ ]⁻-ctx , [ A ]⁻

∥_∷_∥ : ∀ {n' n Σ} -> (Γ : Ctx⁻ n') -> Subst Σ n' n Γ -> ℕ
∥_∷_∥ {n = zero} Γ σ = zero
∥_∷_∥ {n = suc n} Γ σ with fst (σ zero)
∥_∷_∥ {_} {suc n} Γ σ | x = x +  ∥ Γ ∷ σ ∘ suc ∥

mutual
  ----- SUBSTITUTIONS -----
  
  [_∷ₘ_]ₛ : ∀ {n' n Σ} -> (Γ : Ctx⁻ n') -> (σ : Subst Σ n' n Γ) -> Normal n -> Result Σ Γ ∥ Γ ∷ σ ∥

  [_∷ₛ_]ₛ : ∀ {n' n Σ} -> (Γ : Ctx⁻ n') -> Subst Σ n' n Γ -> Spine n -> Spine n'

  [_∷ₐ_]ₛ : ∀ {n' n Σ} -> (Γ : Ctx⁻ n') -> Subst Σ n' n Γ -> LF-Type n -> LF-Type n'
  [ Γ ∷ₐ σ ]ₛ (Atomic a S) = Atomic a ([ Γ ∷ₛ σ ]ₛ S)
  [ Γ ∷ₐ σ ]ₛ (PiType T T₁) = PiType ([ Γ ∷ₐ σ ]ₛ T) ([ Γ , [ T ]⁻ ∷ₐ extendₛ σ [ T ]⁻ ]ₛ T₁)

  [_∷ₖ_]ₛ : ∀ {n' n Σ} -> (Γ : Ctx⁻ n') -> Subst Σ n' n Γ -> LF-Kind n -> LF-Kind n'
  [ Γ ∷ₖ σ ]ₛ Star = Star
  [ Γ ∷ₖ σ ]ₛ (PiKind T K) = PiKind ([ Γ ∷ₐ σ ]ₛ T) ([ Γ , [ T ]⁻ ∷ₖ extendₛ σ [ T ]⁻ ]ₛ K)

  _,⁻_ : ∀ {n} -> Ctx n -> LF-Type n -> Ctx⁻ (suc n)
  Γ ,⁻ A = [ Γ ]⁻-ctx , [ A ]⁻

  reduce : ∀ {n' n Σ'} (Γ : Ctx⁻ n') -> (σ : Subst Σ' n' n Γ) -> Spine n' ->
           (r : Result Σ' Γ ∥ Γ ∷ σ ∥) ->
           Σ ℕ λ q -> q ≤ result-size r × Result Σ' Γ q
  reduce Γ σ S R with ∥ Γ ∷ σ ∥
  reduce Γ σ Nil (Lam {A} {B} M x lte) | w = _ ,, (≤-refl ,, (Lam M x lte))
  reduce Γ σ (Lam A' M' :: S) (Lam {A} {B} M x lte) | w =
    {!_,,_!}
  reduce Γ σ (App H S₁ :: S) (Lam {A} {B} M x lte) | w with reduce Γ σ S ([ Γ ∷m 
    {!!} ,, ({!!} ,, {!reduce Γ σ ? ?!}) -- ([ Γ ∷ₘ single Γ (App H S₁) ]ₛ M)
  reduce Γ σ S (App H S₁) | .0 = {!!}

  [ Γ ∷ₘ σ ]ₛ (Lam A M) with [ Γ , [ A ]⁻ ∷ₘ extendₛ σ [ A ]⁻ ]ₛ M
  ... | w = {!!}
    -- MkResult
    -- {Γ = extend-ctx _ ([ σ ∷ₐ Γ ]ₛ A)}
    -- (Lam ([ σ ∷ₐ Γ ]ₛ A) M') (Data.Maybe.map (λ B -> Lam {!B!}) B⁻)
  [ Γ ∷ₘ σ ]ₛ (App (BVar x) S) = {!!} -- reduce Γ σ ([ Γ ∷ₛ σ ]ₛ S) {!!}
  [ Γ ∷ₘ σ ]ₛ (App (Const x) S) = {!!} -- with [ Γ ∷ₕ σ ]ₛ H | [ Γ ∷ₛ σ ]ₛ S
  -- [ Γ ∷ₘ σ ]ₛ (App H S) | MkResult (Lam A M) (just P) | w' = {!!}
  -- [ Γ ∷ₘ σ ]ₛ (App H S) | MkResult (Lam A M) nothing | w' = {!!}
  -- [ Γ ∷ₘ σ ]ₛ (App H S) | MkResult (App H' S') A⁻ | S'' = {!!} -- App H' $ S' ++-spine S''

  -- Operations on substitutions
  
  -- Weaken a substitution
  _↑ₛ : ∀ {n' n Γ Σ A} -> Subst Σ n' n Γ -> Subst Σ (suc n') n (Γ , A)
  (σ ↑ₛ) i with σ i
  ... | w = {!!} -- MkResult ([ wk ]ᵣ-normal (fst (σ i))) (snd (σ i))
  
  -- Extend a substitution to go under binders.
  extendₛ : ∀ {n' n Γ Σ} -> Subst Σ n' n Γ -> (A : LF-Type⁻) -> Subst Σ (suc n') (suc n) (Γ , A)
  extendₛ σ A = (σ ↑ₛ) , {!!} -- MkResult (App (BVar zero) Nil) (just {!!}) -- σ ↑ₛ , App (BVar zero) Nil

  -- extendₛ⁻ : ∀ {n' n} -> Subst Σ n' n -> LF-Type n -> Subst (suc n') (suc n)
  -- extendₛ⁻ σ A = extendₛ σ [ A ]⁻

  -- Special substitutions
  
  idₛ : ∀ {n Σ} -> (Γ : Ctx⁻ n) -> Subst Σ n n Γ
  idₛ Γ i = {!!} -- MkResult (App (BVar i) Nil) (just {!!})
  
  single : ∀ {p n Σ} -> (Γ : Ctx⁻ n) -> Result Σ Γ p -> Subst Σ n (suc n) Γ
  single {p} Γ R = idₛ Γ , (p ,, {!!}) -- (MkResult M (just {!!}))

  single⁻ : ∀ {n} {p : ℕ} {Σ : Sig} -> (Γ : Ctx n) -> Result Σ [ Γ ]⁻-ctx p -> Subst Σ n (suc n) [ Γ ]⁻-ctx
  single⁻ Γ R = single [ Γ ]⁻-ctx R

mutual
  infix 20 _,_⊢_head-of_
  data _,_⊢_head-of_ {n : ℕ} (Σ : Sig) (Γ : Ctx n) : Head n -> LF-Type n -> Set where
    BVar : {i : Fin n} -> Σ , Γ ⊢ BVar i head-of (lookup-ctx Γ i)
    Const : {k : ℕ} -> {T : LF-Type zero} ->
            lookup-sig-type Σ k ≡ just T ->
            Σ , Γ ⊢ Const k head-of ([ wkₙ' n ]ᵣ-type T)

  infix 10 _,_⊢_spine-of_↘_
  data _,_⊢_spine-of_↘_ {n : ℕ} (Σ : Sig) (Γ : Ctx n) : Spine n -> LF-Type n -> LF-Type n -> Set where
    Nil : ∀ {A} -> Σ , Γ ⊢ Nil spine-of A ↘ A
    Cons : ∀ {A B B' M S} ->
           Σ , Γ ⊢ M normal-of A ->
           -- Σ , Γ ⊢ S spine-of [ {!!} ∷ₐ single⁻ Γ M A ]ₛ B ↘ B' ->
           Σ , Γ ⊢ M :: S spine-of PiType A B ↘ B'

  infix 20 _,_⊢_normal-of_
  data _,_⊢_normal-of_ {n : ℕ} (Σ : Sig) (Γ : Ctx n) : Normal n -> LF-Type n -> Set where
    Lam : ∀ {A B M} ->
          Σ , (extend-ctx Γ A) ⊢ M normal-of B ->
          Σ , Γ ⊢ Lam A M normal-of (PiType A B)
    -- App : Σ , Γ ⊢ H head-of A -> Σ , Γ ⊢ S spine-of A ↘ B ->
    --       Σ , Γ ⊢ 

-- Application of substitution; we use hereditary substitutions, so we
-- need typing before this.

{-

-}
