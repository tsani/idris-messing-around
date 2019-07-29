{-# OPTIONS --cubical #-}

module monoid where

open import Cubical.Foundations.Everything
open import Cubical.Data.List
open import Cubical.Relation.Nullary
open import Cubical.Relation.Nullary.DecidableEq

variable
  ℓ : Level

record isMonoid (M : Type ℓ) : Type ℓ where
  constructor Monoid
  field
    m*          : M → M → M
    e*          : M
    -- laws
    assoc*      : (a b c : M) → m* a (m* b c) ≡ m* (m* a b) c
    u1*         : (x : M) → m* x e* ≡ x
    u2*         : (x : M) → m* e* x ≡ x
    -- this is a set
    MonoidIsSet* : isSet M

-- free monoid
data FM {ℓ} (A : Type ℓ) : Type ℓ where
  mon-η : A → FM A
  mon-m : FM A → FM A → FM A
  mon-e : FM A
  mon-assoc : (a b c : FM A) → mon-m a (mon-m b c) ≡ mon-m (mon-m a b) c
  mon-u1 : (x : FM A) → mon-m x mon-e ≡ x
  mon-u2 : (x : FM A) → mon-m mon-e x ≡ x
  FMIsSet : isSet (FM A)

FM-is-Monoid : {A : Type ℓ} → isMonoid (FM A)
FM-is-Monoid = Monoid mon-m mon-e mon-assoc mon-u1 mon-u2 FMIsSet


module FMElim {ℓ a} (A : Type a) (B : FM A → Type ℓ)
  (η* : (a : A) → B (mon-η a))
  (m* : {a b : FM A} → B a → B b → B (mon-m a b))
  (e* : B mon-e)
  (assoc* : {a b c : FM A} → (ba : B a) → (bb : B b) → (bc : B c)
            → PathP (λ i → B (mon-assoc a b c i)) (m* ba (m* bb bc)) (m* (m* ba bb) bc))
  (u1* : {x : FM A} → (b : B x) → PathP (λ i → B (mon-u1 x i)) (m* b e*) b)
  (u2* : {x : FM A} → (b : B x) → PathP (λ i → B (mon-u2 x i)) (m* e* b) b)
  (FMIsSet* : (fg : FM A) → isSet (B fg)) where

  f : (fg : FM A) → B fg
  f (mon-η x) = η* x
  f (mon-m fg fg₁) = m* (f fg) (f fg₁)
  f mon-e = e*
  f (mon-assoc fg fg₁ fg₂ j) = assoc* (f fg) (f fg₁) (f fg₂) j
  f (mon-u1 fg i₁) = u1* (f fg) i₁
  f (mon-u2 fg i₁) = u2* (f fg) i₁
  f (FMIsSet n m₁ p q i₁ j) = isOfHLevel→isOfHLevelDep {n = 2} FMIsSet* (f n) (f m₁) (cong f p) (cong f q) (FMIsSet n m₁ p q) i₁ j

module FMElimProp {ℓ ℓ'} (A : Type ℓ') (B : FM A → Type ℓ) (BProp : ∀ {a} -> isProp (B a))
  (η* : (a : A) → B (mon-η a))
  (m* : {a b : FM A} → B a → B b → B (mon-m a b))
  (e* : B mon-e)
  where

  f : (m : FM A) -> B m
  f = FMElim.f A B η* m* e*
    (λ _ _ _ → toPathP (BProp _ _))
    (λ _ → toPathP (BProp _ _))
    (λ _ → toPathP (BProp _ _))
    (λ fg → isProp→isSet (BProp {fg}))

FMElimRec : {A M : Type ℓ} (MMonoid : isMonoid M) → (A → M) → (FM A → M)
FMElimRec {ℓ} {A} {M} MMonoid f
  = FMElim.f A (λ _ → M) f m* e* assoc* u1* u2* (λ _ → MonoidIsSet*)
  where open isMonoid MMonoid

module _ {ℓ} {A : Type ℓ} (d : isSet (List A)) where
  ListMonoid : isMonoid (List A)
  isMonoid.m* ListMonoid = _++_
  isMonoid.e* ListMonoid = []
  isMonoid.assoc* ListMonoid = λ a b c → sym (++-assoc a b c)
  isMonoid.u1* ListMonoid = ++-unit-r
  isMonoid.u2* ListMonoid = λ x i → refl {x = x} i
  isMonoid.MonoidIsSet* ListMonoid = d
  
  FM→List : FM A -> List A
  FM→List = FMElimRec ListMonoid [_]
  
  List→FM : List A → FM A
  List→FM [] = mon-e
  List→FM (x ∷ l) = mon-m (mon-η x) (List→FM l)
  
  -- hoist monoid multiplication on the left through the isomorphism
  lem1 : ∀ a b ->
         List→FM (FM→List (mon-m a b)) ≡ mon-m a (List→FM (FM→List b))
  lem1 = FMElimProp.f
    _
    (λ x → ∀ b → List→FM (FM→List (mon-m x b)) ≡ mon-m x (List→FM (FM→List b)))
    (λ x y i b → FMIsSet _ _ (x b) (y b) i)
    (λ _ _ → refl)
    (λ {a₁} {b₁} p q b →
      cong (λ r -> List→FM (FM→List r)) (sym (mon-assoc a₁ b₁ b))
      ∙ p (mon-m b₁ b)
      ∙ cong (λ r -> mon-m a₁ r) (q b)
      ∙ mon-assoc a₁ b₁ (List→FM (FM→List b)))
    (λ b → sym (mon-u2 _))
  
  FM→List→FM : (m : FM A) -> List→FM (FM→List m) ≡ m
  FM→List→FM = FMElimProp.f _ _ (FMIsSet _ _)
    (λ a → mon-u1 (mon-η a))
    (λ {a} {b} p q → lem1 a b ∙ cong (λ r → mon-m a r) q)
    refl

  List→FM→List : (l : List A) -> FM→List (List→FM l) ≡ l
  List→FM→List [] = refl
  List→FM→List (x ∷ l) = cong (λ p -> x ∷ p) (List→FM→List l)

  List≅FM : Iso (List A) (FM A)
  Iso.fun List≅FM = List→FM
  Iso.inv List≅FM = FM→List
  Iso.rightInv List≅FM = FM→List→FM
  Iso.leftInv List≅FM = List→FM→List

  List≡FM : List A ≡ FM A
  List≡FM = isoToPath List≅FM 

  normalizeFM : FM A -> FM A
  normalizeFM = List→FM ∘ FM→List

  -- Witnesses the initiality of List A in the category of monoids.
  foldMap : ∀ {M} (MMonoid : isMonoid {ℓ} M) -> (A -> M) -> (List A -> M)
  foldMap = subst (λ X → ∀ {M} (MMonoid : isMonoid {ℓ} M) → (A → M) → X → M)
              (sym List≡FM) FMElimRec

open import RealShit.ZZ

ℤisMonoid : isMonoid ℤ
isMonoid.m* ℤisMonoid = _ℤ+_
isMonoid.e* ℤisMonoid = zero
isMonoid.assoc* ℤisMonoid = λ a b c -> sym (ℤ+-assoc a b c)
isMonoid.u1* ℤisMonoid = ℤ+zero
isMonoid.u2* ℤisMonoid = zeroℤ+
isMonoid.MonoidIsSet* ℤisMonoid = isSetℤ

sum : List ℤ -> ℤ
sum = foldMap (Discrete→isSet (discreteList discreteℤ)) ℤisMonoid (λ x -> x)

example : List ℤ
example = positive 3 ∷ negative 2 ∷ positive 7 ∷ (succ (succ (pred (succ (pred (succ (negative 3))))))) ∷ []
