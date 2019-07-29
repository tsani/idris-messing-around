{-# OPTIONS --cubical #-}

module cbpv where

open import Cubical.Foundations.Prelude renaming ( _,_ to _,,_ )
open import Data.Nat hiding ( _+_ )
open import Data.Fin hiding ( _+_ ; fold )
open import Function

-- Finite maps
_~>_ : ∀ {ℓ} -> ℕ -> Set ℓ -> Set ℓ
n ~> t = Fin n -> t

_,_ : ∀ {ℓ n} {t : Set ℓ} -> (n ~> t) -> t -> (suc n ~> t)
(f , x) zero = x
(f , x) (suc i) = f i

_~>'_ : (n : ℕ) -> (n ~> Set) -> Set
n ~>' P = (i : Fin n) -> P i

infixr 20 _~>_
infixr 20 _~>'_

cong₃ : {a b c d : Set} -> ∀ {a₁ a₂ b₁ b₂ c₁ c₂} (f : a -> b -> c -> d) ->
        a₁ ≡ a₂ -> b₁ ≡ b₂ -> c₁ ≡ c₂ ->
        f a₁ b₁ c₁ ≡ f a₂ b₂ c₂
cong₃ f p₁ p₂ p₃ i = f (p₁ i) (p₂ i) (p₃ i)

data Tp (n : ℕ) : Set where
  𝟘 : Tp n
  𝟙 : Tp n
  _+_ : Tp n -> Tp n -> Tp n
  _×_ : Tp n -> Tp n -> Tp n
  _⇒_ : Tp n -> Tp n -> Tp n
  μ : Tp (suc n) -> Tp n
  var : Fin n -> Tp n
  cmp : Tp n -> Tp n

infixr 10 _⇒_
infixl 20 _+_
infixl 30 _×_

data Val (n : ℕ) : Set
data Comp (n : ℕ) : Set

data Val n where
  unit : Val n
  
  -- intros for _+_
  injₗ : Val n -> Val n
  injᵣ : Val n -> Val n

  -- intro for _×_
  ⟨_,_⟩ : Val n -> Val n -> Val n

  -- intro for ⇒
  lam : Comp (suc n) -> Val n

  -- variables
  var : Fin n -> Val n

  -- intro for μ
  fold : Val n -> Val n

  delay : Comp n -> Val n

data Comp n where
  -- elim for ⇒
  _·_ : Val n -> Val n -> Comp n

  -- elim for _+_
  case_of_or_ : Val n -> Comp (suc n) -> Comp (suc n) -> Comp n

  -- elim for _×_
  split : Val n -> Comp (suc (suc n)) -> Comp n

  -- elim for μ
  unfold : Val n -> Comp n

  _>>=_ : Val n -> Comp (suc n) -> Comp n

Ren : ℕ -> ℕ -> Set
Ren n k = k ~> Fin n

wk : ∀ {n} -> Ren (suc n) n
wk = suc

weakenᵣ : ∀ {n k} -> Ren n k -> Ren (suc n) k
weakenᵣ = suc ∘_

extendᵣ : ∀ {n k} -> Ren n k -> Ren (suc n) (suc k)
extendᵣ ρ = weakenᵣ ρ , zero

-- Application of renamings

[_]vᵣ : ∀ {n k} -> Ren n k -> Val k -> Val n
[_]cᵣ : ∀ {n k} -> Ren n k -> Comp k -> Comp n

[ ρ ]vᵣ unit = unit
[ ρ ]vᵣ (injₗ v) = injₗ ([ ρ ]vᵣ v)
[ ρ ]vᵣ (injᵣ v) = injᵣ ([ ρ ]vᵣ v)
[ ρ ]vᵣ ⟨ v , v₁ ⟩ = ⟨ ([ ρ ]vᵣ v) , ([ ρ ]vᵣ v₁) ⟩
[ ρ ]vᵣ (lam x) = lam ([ extendᵣ ρ ]cᵣ x)
[ ρ ]vᵣ (var x) = var (ρ x)
[ ρ ]vᵣ (fold v) = fold ([ ρ ]vᵣ v)
[ ρ ]vᵣ (delay x) = delay ([ ρ ]cᵣ x)

[ ρ ]cᵣ (x · x₁) = [ ρ ]vᵣ x · [ ρ ]vᵣ x₁
[ ρ ]cᵣ (case x of c or c₁) =
  case ([ ρ ]vᵣ x)
  of [ extendᵣ ρ ]cᵣ c
  or [ extendᵣ ρ ]cᵣ c₁
[ ρ ]cᵣ (split x c) =
  split ([ ρ ]vᵣ x) ([ extendᵣ (extendᵣ ρ) ]cᵣ c)
[ ρ ]cᵣ (unfold x) = unfold ([ ρ ]vᵣ x)
[ ρ ]cᵣ (x >>= c) = [ ρ ]vᵣ x >>= [ extendᵣ ρ ]cᵣ c

weaken-cₜ : ∀ {n} -> Comp n -> Comp (suc n)
weaken-cₜ = [ wk ]cᵣ

weaken-vₜ : ∀ {n} -> Val n -> Val (suc n)
weaken-vₜ = [ wk ]vᵣ

-- extension distribution lemma
r-extend-r : ∀ {n k j} (ρ₁ : Ren n k) (ρ₂ : Ren k j) ->
             extendᵣ (ρ₁ ∘ ρ₂) ≡ extendᵣ ρ₁ ∘ extendᵣ ρ₂
r-extend-r ρ₁ ρ₂ = funExt proof where
  proof : (i : Fin _) -> extendᵣ (ρ₁ ∘ ρ₂) i ≡ (extendᵣ ρ₁ ∘ extendᵣ ρ₂) i
  proof zero = refl
  proof (suc i) = refl

-- congruence of extension distribution lemma through application
r-extend-r-c : ∀ {n k j} (ρ₁ : Ren n k) (ρ₂ : Ren k j) (c : Comp (suc j)) ->
               [ extendᵣ (ρ₁ ∘ ρ₂) ]cᵣ c ≡ [ extendᵣ ρ₁ ∘ extendᵣ ρ₂ ]cᵣ c
r-extend-r-c ρ₁ ρ₂ c = cong (λ ρ -> [ ρ ]cᵣ c) (r-extend-r ρ₁ ρ₂)

record Foo (P Q R : ℕ -> ℕ -> Set) : Set where
  field
    [_]p : ∀ {n k} -> P n k -> Val k -> Val n
    [_]q : ∀ {n k} -> Q n k -> Val k -> Val n
    [_]r : ∀ {n k} -> R n k -> Val k -> Val n
    extend-P : ∀ {n k} -> P n k -> P (suc n) (suc k)
    extend-Q : ∀ {n k} -> Q n k -> Q (suc n) (suc k)
    extend-R : ∀ {n k} -> R n k -> R (suc n) (suc k)
    _p∘q_ : ∀ {n k j} -> P n k -> Q k j -> R n j
    f-extend-g : ∀ {n k j} (f : P n k) (g : Q k j) -> extend-P f p∘q extend-Q g ≡ extend-R (f p∘q g)
    unit-eq : ∀ {n k j} {f : P n k} {g : Q k j} ->
      ([ f ]p ∘ [ g ]q) unit ≡ [ f p∘q g ]r unit
    var-eq : ∀ {n k j} {f : P n k} {g : Q k j} -> (x : Fin _) ->
      ([ f ]p ∘ [ g ]q) (var x) ≡ [ f p∘q g ]r (var x)

f∘g-lemma-v : {P Q R : ℕ -> ℕ -> Set}
              (T : Foo P Q R) ->
              ∀ {n k j} ->
              (f : P n k) (g : Q k j) (v : Val j) ->
              (T.[ f ]p ∘ T.[ g ]q) v ≡ T.[ f p∘q g ]r v
f∘g-lemma-v T f g unit = {!!}
f∘g-lemma-v T f g (injₗ v) = {!!}
f∘g-lemma-v T f g (injᵣ v) = {!!}
f∘g-lemma-v T f g ⟨ v , v₁ ⟩ = {!!}
f∘g-lemma-v T f g (lam x) = {!!}
f∘g-lemma-v T f g (var x) = {!!}
f∘g-lemma-v T f g (fold v) = {!!}
f∘g-lemma-v T f g (delay x) = {!!}

-- renaming-renaming composition lemmas
r∘r-lemma-v : ∀ {n k j} (ρ₁ : Ren n k) (ρ₂ : Ren k j) (v : Val j) ->
              ([ ρ₁ ]vᵣ ∘ [ ρ₂ ]vᵣ) v ≡ [ ρ₁ ∘ ρ₂ ]vᵣ v

r∘r-lemma-c : ∀ {n k j} (ρ₁ : Ren n k) (ρ₂ : Ren k j) (c : Comp j) ->
              ([ ρ₁ ]cᵣ ∘ [ ρ₂ ]cᵣ) c ≡ [ ρ₁ ∘ ρ₂ ]cᵣ c

r∘r-lemma-c ρ₁ ρ₂ (x · x₁) =
  cong₂ _·_ (r∘r-lemma-v ρ₁ ρ₂ x) (r∘r-lemma-v ρ₁ ρ₂ x₁)
r∘r-lemma-c ρ₁ ρ₂ (case x of c₁ or c₂) =
  cong₃ case_of_or_
    (r∘r-lemma-v ρ₁ ρ₂ x)
    (r∘r-lemma-c (extendᵣ ρ₁) (extendᵣ ρ₂) c₁ ∙ (sym $ r-extend-r-c ρ₁ ρ₂ c₁))
    (r∘r-lemma-c (extendᵣ ρ₁) (extendᵣ ρ₂) c₂ ∙ (sym $ r-extend-r-c ρ₁ ρ₂ c₂))
r∘r-lemma-c ρ₁ ρ₂ (split x c) =
  cong₂ split
    (r∘r-lemma-v ρ₁ ρ₂ x)
    (r∘r-lemma-c (extendᵣ (extendᵣ ρ₁)) (extendᵣ (extendᵣ ρ₂)) c
      ∙ cong (λ ρ → [ ρ ]cᵣ c)
        (sym (r-extend-r (extendᵣ ρ₁) (extendᵣ ρ₂))
          ∙ cong extendᵣ (sym $ r-extend-r ρ₁ ρ₂) ))
r∘r-lemma-c ρ₁ ρ₂ (unfold x) = cong unfold (r∘r-lemma-v ρ₁ ρ₂ x)
r∘r-lemma-c ρ₁ ρ₂ (x >>= c) =
  cong₂ _>>=_
    (r∘r-lemma-v ρ₁ ρ₂ x)
    (r∘r-lemma-c (extendᵣ ρ₁) (extendᵣ ρ₂) c ∙ (sym $ r-extend-r-c ρ₁ ρ₂ c))

r∘r-lemma-v ρ₁ ρ₂ unit = refl
r∘r-lemma-v ρ₁ ρ₂ (injₗ v) = cong injₗ (r∘r-lemma-v ρ₁ ρ₂ v)
r∘r-lemma-v ρ₁ ρ₂ (injᵣ v) = cong injᵣ (r∘r-lemma-v ρ₁ ρ₂ v)
r∘r-lemma-v ρ₁ ρ₂ ⟨ v , v₁ ⟩ =
  cong₂ ⟨_,_⟩ (r∘r-lemma-v ρ₁ ρ₂ v) (r∘r-lemma-v ρ₁ ρ₂ v₁)
r∘r-lemma-v ρ₁ ρ₂ (lam x) =
  cong lam
    (r∘r-lemma-c (extendᵣ ρ₁) (extendᵣ ρ₂) x
      ∙ cong (λ ρ → [ ρ ]cᵣ x) (sym $ r-extend-r ρ₁ ρ₂))
r∘r-lemma-v ρ₁ ρ₂ (var x) = refl
r∘r-lemma-v ρ₁ ρ₂ (fold v) = cong fold (r∘r-lemma-v ρ₁ ρ₂ v)
r∘r-lemma-v ρ₁ ρ₂ (delay x) = cong delay (r∘r-lemma-c ρ₁ ρ₂ x)

r∘r-lemma-c' : ∀ {n k j} (ρ₁ : Ren n k) (ρ₂ : Ren k j) ->
               [ ρ₁ ]cᵣ ∘ [ ρ₂ ]cᵣ ≡ [ ρ₁ ∘ ρ₂ ]cᵣ
r∘r-lemma-c' ρ₁ ρ₂ = funExt (r∘r-lemma-c ρ₁ ρ₂)

r∘r-lemma-v' : ∀ {n k j} (ρ₁ : Ren n k) (ρ₂ : Ren k j) ->
               [ ρ₁ ]vᵣ ∘ [ ρ₂ ]vᵣ ≡ [ ρ₁ ∘ ρ₂ ]vᵣ
r∘r-lemma-v' ρ₁ ρ₂ = funExt (r∘r-lemma-v ρ₁ ρ₂)

-- Substitutions
Subst : ℕ -> ℕ -> Set
Subst n k = k ~> Val n

idₛ : ∀ {n} -> Subst n n
idₛ = var

single : ∀ {n} -> Val n -> Subst n (suc n)
single v = idₛ , v

weakenₛ : ∀ {n k} -> Subst n k -> Subst (suc n) k
weakenₛ = weaken-vₜ ∘_

extendₛ : ∀ {n k} -> Subst n k -> Subst (suc n) (suc k)
extendₛ σ = weakenₛ σ , var zero

-- Application of a substitution
[_]vₛ : ∀ {n k} -> (σ : Subst n k) -> Val k -> Val n
[_]cₛ : ∀ {n k} -> (σ : Subst n k) -> Comp k -> Comp n

[ σ ]vₛ unit = unit
[ σ ]vₛ (injₗ v) = injₗ ([ σ ]vₛ v)
[ σ ]vₛ (injᵣ v) = injᵣ ([ σ ]vₛ v)
[ σ ]vₛ ⟨ v , v₁ ⟩ = ⟨ [ σ ]vₛ v , [ σ ]vₛ v₁ ⟩
[ σ ]vₛ (lam x) = lam ([ extendₛ σ ]cₛ x)
[ σ ]vₛ (var x) = σ x
[ σ ]vₛ (fold v) = fold ([ σ ]vₛ v)
[ σ ]vₛ (delay x) = delay ([ σ ]cₛ x)

[ σ ]cₛ (x · x₁) = ([ σ ]vₛ x) · ([ σ ]vₛ x₁)
[ σ ]cₛ (case x of c or c₁) =
  case ([ σ ]vₛ x) of ([ extendₛ σ ]cₛ c) or ([ extendₛ σ ]cₛ c₁)
[ σ ]cₛ (split x c) = split ([ σ ]vₛ x) ([ extendₛ (extendₛ σ) ]cₛ c)
[ σ ]cₛ (unfold x) = unfold ([ σ ]vₛ x)
[ σ ]cₛ (x >>= c) = ([ σ ]vₛ x) >>= ([ extendₛ σ ]cₛ c)

-- Renaming-substitution composition

_r∘s_ : ∀ {n k j} -> Ren n k -> Subst k j -> Subst n j
_r∘s_ ρ = [ ρ ]vᵣ ∘_

r-extend-s : ∀ {n k j} (ρ : Ren n k) (σ : Subst k j) ->
             extendᵣ ρ r∘s extendₛ σ ≡ extendₛ (ρ r∘s σ)
r-extend-s ρ σ = funExt proof where
  proof : (x : Fin _) ->
          (extendᵣ ρ r∘s extendₛ σ) x ≡ extendₛ (ρ r∘s σ) x
  proof zero = refl
  proof (suc x) =
    r∘r-lemma-v (extendᵣ ρ) wk (σ x)
    ∙
    (sym $ r∘r-lemma-v wk ρ (σ x))

r∘s-lemma-v : ∀ {n k j} (ρ : Ren n k) (σ : Subst k j) (v : Val j) ->
              [ ρ ]vᵣ ([ σ ]vₛ v) ≡ [ ρ r∘s σ ]vₛ v
r∘s-lemma-c : ∀ {n k j} (ρ : Ren n k) (σ : Subst k j) (c : Comp j) ->
              [ ρ ]cᵣ ([ σ ]cₛ c) ≡ [ ρ r∘s σ ]cₛ c

r∘s-lemma-v ρ σ unit = refl
r∘s-lemma-v ρ σ (injₗ v) = cong injₗ (r∘s-lemma-v ρ σ v)
r∘s-lemma-v ρ σ (injᵣ v) = cong injᵣ (r∘s-lemma-v ρ σ v)
r∘s-lemma-v ρ σ ⟨ v , v₁ ⟩ =
  cong₂ ⟨_,_⟩ (r∘s-lemma-v ρ σ v) (r∘s-lemma-v ρ σ v₁)
r∘s-lemma-v ρ σ (lam x) =
  cong lam
    (r∘s-lemma-c (extendᵣ ρ) (extendₛ σ) x
      ∙ cong (λ σ → [ σ ]cₛ x)
        (r-extend-s ρ σ))
r∘s-lemma-v ρ σ (var x) = refl
r∘s-lemma-v ρ σ (fold v) = cong fold (r∘s-lemma-v ρ σ v)
r∘s-lemma-v ρ σ (delay x) = cong delay (r∘s-lemma-c ρ σ x)

r∘s-lemma-c ρ σ (x · x₁) = cong₂ _·_ (r∘s-lemma-v ρ σ x) (r∘s-lemma-v ρ σ x₁)
r∘s-lemma-c ρ σ (case x of c or c₁) =
  cong₃ case_of_or_
    (r∘s-lemma-v ρ σ x)
    (r∘s-lemma-c (extendᵣ ρ) (extendₛ σ) c
      ∙ cong (λ σ → [ σ ]cₛ c) (r-extend-s ρ σ))
    (r∘s-lemma-c (extendᵣ ρ) (extendₛ σ) c₁
      ∙ cong (λ σ → [ σ ]cₛ c₁) (r-extend-s ρ σ))
r∘s-lemma-c ρ σ (split x c) =
  cong₂ split
    (r∘s-lemma-v ρ σ x)
    (r∘s-lemma-c (extendᵣ (extendᵣ ρ)) (extendₛ (extendₛ σ)) c
      ∙ cong (λ σ → [ σ ]cₛ c)
        (r-extend-s (extendᵣ ρ) (extendₛ σ)
          ∙ cong extendₛ
            (r-extend-s ρ σ)))
r∘s-lemma-c ρ σ (unfold x) = cong unfold (r∘s-lemma-v ρ σ x)
r∘s-lemma-c ρ σ (x >>= c) =
  cong₂ _>>=_
    (r∘s-lemma-v ρ σ x)
    (r∘s-lemma-c (extendᵣ ρ) (extendₛ σ) c
      ∙ cong (λ σ -> [ σ ]cₛ c) (r-extend-s ρ σ))

_s∘r_ : ∀ {n k j} -> Subst n k -> Ren k j -> Subst n j
_s∘r_ σ ρ = σ ∘ ρ

s-extend-r : ∀ {n k j} (σ : Subst n k) (ρ : Ren k j) ->
             extendₛ σ s∘r extendᵣ ρ ≡ extendₛ (σ s∘r ρ)
s-extend-r σ ρ = funExt proof where
  proof : (x : Fin _) ->
          (extendₛ σ s∘r extendᵣ ρ) x ≡ extendₛ (σ s∘r ρ) x
  proof zero = refl
  proof (suc x) = refl

s∘r-lemma-v : ∀ {n k j} (σ : Subst n k) (ρ : Ren k j) (v : Val j) ->
              ([ σ ]vₛ ∘ [ ρ ]vᵣ) v ≡ [ σ s∘r ρ ]vₛ v
s∘r-lemma-c : ∀ {n k j} (σ : Subst n k) (ρ : Ren k j) (c : Comp j) ->
              ([ σ ]cₛ ∘ [ ρ ]cᵣ) c ≡ [ σ s∘r ρ ]cₛ c

s∘r-lemma-v σ ρ unit = refl
s∘r-lemma-v σ ρ (injₗ v) = cong injₗ (s∘r-lemma-v σ ρ v)
s∘r-lemma-v σ ρ (injᵣ v) = cong injᵣ (s∘r-lemma-v σ ρ v)
s∘r-lemma-v σ ρ ⟨ v , v₁ ⟩ =
  cong₂ ⟨_,_⟩
    (s∘r-lemma-v σ ρ v)
    (s∘r-lemma-v σ ρ v₁)
s∘r-lemma-v σ ρ (lam x) =
  cong lam
    (s∘r-lemma-c (extendₛ σ) (extendᵣ ρ) x
      ∙ cong (λ σ → [ σ ]cₛ x)
        (s-extend-r σ ρ))
s∘r-lemma-v σ ρ (var x) = refl
s∘r-lemma-v σ ρ (fold v) =
  cong fold (s∘r-lemma-v σ ρ v)
s∘r-lemma-v σ ρ (delay x) = cong delay (s∘r-lemma-c σ ρ x)

s∘r-lemma-c σ ρ (x · x₁) =
  cong₂ _·_
    (s∘r-lemma-v σ ρ x)
    (s∘r-lemma-v σ ρ x₁)
s∘r-lemma-c σ ρ (case x of c or c₁) =
  cong₃ case_of_or_
    (s∘r-lemma-v σ ρ x)
    (s∘r-lemma-c (extendₛ σ) (extendᵣ ρ) c
      ∙ cong (λ σ → [ σ ]cₛ c) (s-extend-r σ ρ))
    (s∘r-lemma-c (extendₛ σ) (extendᵣ ρ) c₁
      ∙ cong (λ σ → [ σ ]cₛ c₁) (s-extend-r σ ρ))
s∘r-lemma-c σ ρ (split x c) =
  cong₂ split
    (s∘r-lemma-v σ ρ x)
    (s∘r-lemma-c (extendₛ (extendₛ σ)) (extendᵣ (extendᵣ ρ)) c
      ∙ cong (λ σ -> [ σ ]cₛ c)
        (s-extend-r (extendₛ σ) (extendᵣ ρ)
          ∙ cong extendₛ (s-extend-r σ ρ)))
s∘r-lemma-c σ ρ (unfold x) = cong unfold {!!}
s∘r-lemma-c σ ρ (x >>= c) = {!!}
