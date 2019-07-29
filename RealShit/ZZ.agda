{-# OPTIONS --cubical #-}

module RealShit.ZZ where

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

data ℤ : Set where
  zero : ℤ
  succ : ℤ -> ℤ
  pred : ℤ -> ℤ

  succ-pred : ∀ n -> succ (pred n) ≡ n
  pred-succ : ∀ n -> pred (succ n) ≡ n

  trunc : isSet ℤ

succ≅ : Iso ℤ ℤ
Iso.fun succ≅ = succ
Iso.inv succ≅ = pred
Iso.rightInv succ≅ = succ-pred
Iso.leftInv succ≅ = pred-succ

-- A path on ℤ witnessed by the fact that `succ` is an isomorphism.
succ≡ : ℤ ≡ ℤ
succ≡ = isoToPath succ≅

positive : ℕ -> ℤ
positive zero = zero
positive (suc n) = succ (positive n)

negative : ℕ -> ℤ
negative zero = zero
negative (suc n) = pred (negative n)

module ℤ-elim {ℓ} {B : ℤ -> Set ℓ}
  (zero* : B zero)
  (succ* : ∀ {n} -> B n -> B (succ n))
  (pred* : ∀ {n} -> B n -> B (pred n))
  (succ-pred* : ∀ {n} (b : B n) ->
                PathP (λ i -> B (succ-pred n i)) (succ* (pred* b)) b)
  (pred-succ* : ∀ {n} (b : B n) ->
                PathP (λ i -> B (pred-succ n i)) (pred* (succ* b)) b)
  (trunc* : (n : ℤ) -> isSet (B n))
  where

  f : (n : ℤ) -> B n
  f zero = zero*
  f (succ n) = succ* (f n)
  f (pred n) = pred* (f n)
  f (succ-pred n i) = succ-pred* (f n) i
  f (pred-succ n i) = pred-succ* (f n) i
  f (trunc n₁ n₂ p q i j) =
    isOfHLevel→isOfHLevelDep {n = 2} trunc* (f n₁) (f n₂) (cong f p) (cong f q) (trunc n₁ n₂ p q) i j

module ℤ-elim-prop {ℓ} {B : ℤ → Set ℓ} (BProp : {z : ℤ} → isProp (B z))
  (zero* : B zero)
  (succ* : {z : ℤ} → B z → B (succ z))
  (pred* : {z : ℤ} → B z → B (pred z))
  where

  f : (z : ℤ) → B z
  f = ℤ-elim.f zero* succ* pred*
              (λ _ → toPathP (BProp _ _))
              (λ _ → toPathP (BProp _ _))
              (λ _ → isProp→isSet BProp)

module ℤ-rec {ℓ} {B : Set ℓ} (BSet : isSet B)
  (zero* : B)
  (succ* : B -> B)
  (pred* : B -> B)
  (succ-pred* : (b : B) -> succ* (pred* b) ≡ b)
  (pred-succ* : (b : B) -> pred* (succ* b) ≡ b)
  where

  f : ℤ -> B
  f n = ℤ-elim.f zero* succ* pred* succ-pred* pred-succ* (λ _ → BSet) n

-ℤ_ : ℤ → ℤ
-ℤ_ = ℤ-rec.f trunc zero pred succ pred-succ succ-pred

-- computation rules for -ℤ_
-ℤzero : -ℤ zero ≡ zero
-ℤzero = refl

-ℤsucc : ∀ n -> -ℤ (succ n) ≡ pred (-ℤ n)
-ℤsucc n = refl

-ℤpred : ∀ n -> -ℤ (pred n) ≡ succ (-ℤ n)
-ℤpred n = refl

-- properties of -ℤ_
-ℤ-involutive : ∀ n -> -ℤ -ℤ n ≡ n
-ℤ-involutive =
  ℤ-elim-prop.f (trunc _ _) refl (λ p -> cong succ p) λ p -> cong pred p
  
-ℤ≅ : Iso ℤ ℤ
Iso.fun -ℤ≅ = -ℤ_
Iso.inv -ℤ≅ = -ℤ_
Iso.rightInv -ℤ≅ = -ℤ-involutive
Iso.leftInv -ℤ≅ = -ℤ-involutive

ℤ→int : ℤ → Int
ℤ→int zero = pos 0
ℤ→int (succ z) = sucInt (ℤ→int z)
ℤ→int (pred z) = predInt (ℤ→int z)
ℤ→int (succ-pred z i) = sucPred (ℤ→int z) i
ℤ→int (pred-succ z i) = predSuc (ℤ→int z) i
ℤ→int (trunc x y p q i j) =
  isSetInt (ℤ→int x) (ℤ→int y) (cong ℤ→int p) (cong ℤ→int q) i j

int→ℤ : Int → ℤ
int→ℤ (pos n) =  iter n succ zero
int→ℤ (negsuc n) = iter n pred (pred zero)

lem1 : ∀ n → ℤ→int (iter n succ zero) ≡ pos n
lem1 zero    = refl
lem1 (suc n) = cong sucInt (lem1 n)

lem2 : ∀ n → ℤ→int (iter n pred (pred zero)) ≡ negsuc n
lem2 zero    = refl
lem2 (suc n) = cong predInt (lem2 n)

int→ℤ→int : ∀ (z : Int) → ℤ→int (int→ℤ z) ≡ z
int→ℤ→int (pos n)    = lem1 n
int→ℤ→int (negsuc n) = lem2 n

succ-ℤ→int : ∀ n -> sucInt (ℤ→int n) ≡ ℤ→int (succ n)
succ-ℤ→int n = ℤ-elim-prop.f
  {B = λ n -> sucInt (ℤ→int n) ≡ ℤ→int (succ n)}
  (isSetInt _ _)
  refl
  (λ _ → refl)
  (λ _ → refl)
  n

succ-int→ℤ : ∀ n -> succ (int→ℤ n) ≡ int→ℤ (sucInt n)
succ-int→ℤ (pos n) = refl
succ-int→ℤ (negsuc zero) = succ-pred _
succ-int→ℤ (negsuc (suc n)) = succ-pred _

succ-ℤ→int→ℤ : ∀ n -> succ (int→ℤ (ℤ→int n)) ≡ int→ℤ (ℤ→int (succ n))
succ-ℤ→int→ℤ n = succ-int→ℤ (ℤ→int n) ∙ cong int→ℤ (succ-ℤ→int n)

pred-ℤ→int : ∀ n -> predInt (ℤ→int n) ≡ ℤ→int (pred n)
pred-ℤ→int n = ℤ-elim-prop.f
  {B = λ n -> predInt (ℤ→int n) ≡ ℤ→int (pred n)}
  (isSetInt _ _) refl (λ _ → refl) (λ _ → refl) n

pred-int→ℤ : ∀ n -> pred (int→ℤ n) ≡ int→ℤ (predInt n)
pred-int→ℤ (pos zero) = refl
pred-int→ℤ (pos (suc n)) = pred-succ _
pred-int→ℤ (negsuc n) = refl

pred-ℤ→int→ℤ : ∀ n -> pred (int→ℤ (ℤ→int n)) ≡ int→ℤ (ℤ→int (pred n))
pred-ℤ→int→ℤ n = pred-int→ℤ (ℤ→int n) ∙ cong int→ℤ (pred-ℤ→int n)

ℤ→int→ℤ : ∀ n -> int→ℤ (ℤ→int n) ≡ n
ℤ→int→ℤ =
  ℤ-elim-prop.f -- {B = λ x → (int→ℤ ∘ ℤ→int) x ≡ x}
    (trunc _ _) -- (λ x y i j -> trunc _ _ x y i j)
    refl
    (λ {z} x → cong int→ℤ (succ-ℤ→int z) ∙ sym (succ-int→ℤ (ℤ→int z)) ∙ cong succ x)
    (λ {z} x → cong int→ℤ (pred-ℤ→int z) ∙ sym (pred-int→ℤ (ℤ→int z)) ∙ cong pred x)

ℤ≅Int : Iso ℤ Int
Iso.fun ℤ≅Int = ℤ→int
Iso.inv ℤ≅Int = int→ℤ
Iso.rightInv ℤ≅Int = int→ℤ→int
Iso.leftInv ℤ≅Int = ℤ→int→ℤ

ℤ≡Int : ℤ ≡ Int
ℤ≡Int = isoToPath ℤ≅Int

discreteℤ : Discrete ℤ
discreteℤ = subst Discrete (sym ℤ≡Int) discreteInt

-- | A proof that ℤ is a set, obtained from the fact that ℤ is
-- discrete.
isSetℤ : isSet ℤ
isSetℤ = Discrete→isSet discreteℤ

normalizeℤ : ℤ -> ℤ
normalizeℤ n = int→ℤ (ℤ→int n)

abstract
  -- Direct definition of addition on ℤ
  _ℤ+_ : ℤ -> ℤ -> ℤ
  n₁ ℤ+ zero = n₁
  n₁ ℤ+ succ n₂ = succ (n₁ ℤ+ n₂)
  n₁ ℤ+ pred n₂ = pred (n₁ ℤ+ n₂)
  n₁ ℤ+ succ-pred n₂ i = succ-pred (n₁ ℤ+ n₂) i
  n₁ ℤ+ pred-succ n₂ i = pred-succ (n₁ ℤ+ n₂) i
  n₁ ℤ+ trunc n₂ n₃ x y i i₁ = trunc (n₁ ℤ+ n₂) (n₁ ℤ+ n₃) (cong (n₁ ℤ+_) x) (cong (n₁ ℤ+_) y) i i₁
    -- ℤ-rec.f trunc n₁ succ pred succ-pred pred-succ n₂
  infixl 15 _ℤ+_
  
  ℤ+zero : ∀ m -> m ℤ+ zero ≡ m
  ℤ+zero m = refl
  
  ℤ+succ : ∀ m n -> m ℤ+ (succ n) ≡ succ (m ℤ+ n)
  ℤ+succ m n = refl
  
  ℤ+pred : ∀ m n -> m ℤ+ (pred n) ≡ pred (m ℤ+ n)
  ℤ+pred m n = refl
  
  ℤ+-assoc : ∀ n m k -> n ℤ+ m ℤ+ k ≡ n ℤ+ (m ℤ+ k)
  ℤ+-assoc n m zero = refl
  ℤ+-assoc n m (succ k) = cong succ (ℤ+-assoc n m k)
  ℤ+-assoc n m (pred k) = cong pred (ℤ+-assoc n m k)
  ℤ+-assoc n m (succ-pred k i) = cong (λ p -> succ-pred p i) (ℤ+-assoc n m k)
  ℤ+-assoc n m (pred-succ k i) = cong (λ p -> pred-succ p i) (ℤ+-assoc n m k)
  ℤ+-assoc n m (trunc k k₁ p q i j) =
      isOfHLevel→isOfHLevelDep {n = 2} (λ _ → isProp→isSet (trunc _ _))
        (ℤ+-assoc n m k)
        (ℤ+-assoc n m k₁)
        (cong (ℤ+-assoc n m) p)
        (cong (ℤ+-assoc n m) q)
        (trunc k k₁ p q) i j
  
    -- ℤ-elim-prop.f (trunc _ _) refl
    -- (λ x → cong succ x)
    -- (λ x → cong pred x)
  
  zeroℤ+ : ∀ n -> zero ℤ+ n ≡ n
  zeroℤ+ zero = refl
  zeroℤ+ (succ n) = cong succ (zeroℤ+ n)
  zeroℤ+ (pred n) = cong pred (zeroℤ+ n)
  zeroℤ+ (succ-pred n i) = cong (λ p -> succ-pred p i) (zeroℤ+ n) 
  zeroℤ+ (pred-succ n i) = cong (λ p -> pred-succ p i) (zeroℤ+ n)
  zeroℤ+ (trunc n n₁ x y i i₁) =
      isOfHLevel→isOfHLevelDep {n = 2} (λ _ → isProp→isSet (trunc _ _))
        (zeroℤ+ n)
        (zeroℤ+ n₁)
        (cong zeroℤ+ x)
        (cong zeroℤ+ y)
        (trunc n n₁ x y) i i₁
    -- ℤ-elim-prop.f (trunc _ _) refl (λ x → cong succ x) (λ x → cong pred x)
  
  succℤ+ : ∀ m n -> succ m ℤ+ n ≡ succ (m ℤ+ n)
  succℤ+ m =
    ℤ-elim-prop.f (trunc _ _) refl
    (λ x → cong succ x)
    (λ x -> cong pred x ∙ pred-succ _ ∙ sym (succ-pred _))
  
  predℤ+ : ∀ m n -> pred m ℤ+ n ≡ pred (m ℤ+ n)
  predℤ+ m =
    ℤ-elim-prop.f (trunc _ _) refl
    (λ x → cong succ x ∙ succ-pred _ ∙ sym (pred-succ _))
    (λ x -> cong pred x)
  
  ℤ+-comm : ∀ n m -> m ℤ+ n ≡ n ℤ+ m
  ℤ+-comm n =
    ℤ-elim-prop.f (trunc _ _) (zeroℤ+ n)
    (λ {z} x → succℤ+ z n ∙ cong succ x)
    (λ {z} x → predℤ+ z n ∙ cong pred x)
  
  +ℤ-zero : ∀ n -> n ℤ+ -ℤ n ≡ zero
  +ℤ-zero =
    ℤ-elim-prop.f (trunc _ _) refl
    (λ {z} x → succℤ+ _ (-ℤ succ z) ∙ succ-pred _ ∙ x)
    (λ {z} x → predℤ+ _ (-ℤ pred z) ∙ pred-succ _ ∙ x)
  
  -ℤ+zero : ∀ n -> (-ℤ n) ℤ+ n ≡ zero
  -ℤ+zero n = sym (ℤ+-comm (-ℤ n) n) ∙ +ℤ-zero n
  
  -ℤℤ+-ℤ : ∀ n m -> (-ℤ n) ℤ+ (-ℤ m) ≡ -ℤ (n ℤ+ m)
  -ℤℤ+-ℤ n =
    ℤ-elim-prop.f (trunc _ _)
      refl
      (λ {z} x -> cong pred x)
      (λ {z} x -> cong succ x)

ℤ*-lem1 : (m n : ℤ) -> m ℤ+ ((-ℤ m) ℤ+ n) ≡ n
ℤ*-lem1 m n = sym (ℤ+-assoc m (-ℤ m) n) ∙ cong (λ p -> p ℤ+ n) (+ℤ-zero m) ∙ zeroℤ+ n 

ℤ*-lem2 : (m n : ℤ) -> (-ℤ m) ℤ+ (m ℤ+ n) ≡ n
ℤ*-lem2 m n = sym (ℤ+-assoc (-ℤ m) m n) ∙ cong (λ p -> p ℤ+ n) (-ℤ+zero m) ∙ zeroℤ+ n

abstract
  infixl 20 _ℤ*_
  _ℤ*_ : ℤ → ℤ → ℤ
  m ℤ* zero = zero
  m ℤ* succ n = m ℤ+ (m ℤ* n)
  m ℤ* pred n = (-ℤ m) ℤ+ (m ℤ* n)
  m ℤ* succ-pred n i = ℤ*-lem1 m (m ℤ* n) i 
  m ℤ* pred-succ n i = ℤ*-lem2 m (m ℤ* n) i
  m ℤ* trunc n n₁ x y i i₁ = trunc (m ℤ* n) (m ℤ* n₁) (cong _ x) (cong _ y) i i₁
    -- ℤ-rec.f trunc zero (λ n -> m ℤ+ n) (λ n -> (-ℤ m) ℤ+ n)
    -- (λ n -> ℤ*-lem1 m n)
    -- (λ n -> ℤ*-lem2 m n)
  
  ℤ*zero : ∀ m -> m ℤ* zero ≡ zero
  ℤ*zero m = refl
  
  -- m * S Z = m + (m * Z) = m
  ℤ*one : ∀ m -> m ℤ* succ zero ≡ m
  ℤ*one m = ℤ+zero m
  
  ℤ*neg : ∀ m -> m ℤ* pred zero ≡ -ℤ m
  ℤ*neg m = ℤ+zero _
  
  ℤ*pred : ∀ m n -> m ℤ* pred n ≡ (-ℤ m) ℤ+ (m ℤ* n)
  ℤ*pred m =
    ℤ-elim-prop.f
      {B = λ n -> m ℤ* pred n ≡ (-ℤ m) ℤ+ (m ℤ* n)}
      (trunc _ _)
      refl
      (λ _ → refl)
      (λ _ → refl)
  
  ℤ*succ : ∀ m n -> m ℤ* succ n ≡ m ℤ+ (m ℤ* n)
  ℤ*succ m =
    ℤ-elim-prop.f
    (trunc _ _)
    refl
    (λ _ → refl)
    λ _ → refl

ℤ*-ℤ : ∀ n m -> n ℤ* (-ℤ m) ≡ -ℤ (n ℤ* m)
ℤ*-ℤ n =
  ℤ-elim-prop.f (trunc _ _)
    (cong (λ p -> n ℤ* p) -ℤzero
      ∙ ℤ*zero n
      ∙ sym -ℤzero
      ∙ sym (cong -ℤ_ (ℤ*zero n)))
    (λ {z} x →
      cong (λ p -> n ℤ* p) (-ℤsucc z)
      ∙ ℤ*pred n (-ℤ z)
      ∙ cong (λ p -> (-ℤ n) ℤ+ p) x
      ∙ -ℤℤ+-ℤ n (n ℤ* z)
      ∙ sym (cong -ℤ_ (ℤ*succ n z)))
    (λ {z} x →
      cong (λ p -> n ℤ* p) (-ℤpred z)
      ∙ ℤ*succ n (-ℤ z)
      ∙ (cong (λ p -> n ℤ+ p) x
      ∙ sym (cong (λ p -> p ℤ+ (-ℤ (n ℤ* z))) (-ℤ-involutive n))
      ∙ -ℤℤ+-ℤ (-ℤ n) (n ℤ* z))
      ∙ sym (cong -ℤ_ (ℤ*pred n z)))

zeroℤ* : ∀ m -> zero ℤ* m ≡ zero
zeroℤ* = ℤ-elim-prop.f
  {B = λ n -> zero ℤ* n ≡ zero}
  (trunc _ _)
  (ℤ*zero _)
  (λ {z} x → ℤ*succ zero z ∙  zeroℤ+ (zero ℤ* z) ∙ x  )
  (λ {z} x →
     ℤ*pred zero z
     ∙ cong (λ p -> p ℤ+ zero ℤ* z) -ℤzero
     ∙ zeroℤ+ _
     ∙ x)

succℤ* : ∀ m n -> succ m ℤ* n ≡ n ℤ+ (m ℤ* n)
succℤ* m = ℤ-elim-prop.f
  {B = λ n -> succ m ℤ* n ≡ n ℤ+ (m ℤ* n)}
  (trunc _ _)
  (ℤ*zero (succ m) ∙ (sym $ ℤ*zero _) ∙ sym (zeroℤ+ (m ℤ* zero)))
  (λ {z} x →
     ℤ*succ (succ m) z
     ∙ (cong (λ p -> succ m ℤ+ p) x
     ∙ succℤ+ m (z ℤ+ m ℤ* z)
     ∙ cong succ
       (sym (ℤ+-assoc m z (m ℤ* z))
       ∙ sym (cong (λ p -> p ℤ+ m ℤ* z) (ℤ+-comm m z)) 
       ∙ ℤ+-assoc z m (m ℤ* z) )
     ∙ sym (succℤ+ z (m ℤ+ m ℤ* z)))
     ∙ sym (cong (λ p -> succ z ℤ+ p) (ℤ*succ m z)))
  (λ {z} x →
     ℤ*pred (succ m) z
     ∙ cong (λ p -> p ℤ+ succ m ℤ* z) (-ℤsucc m)
     ∙ cong (λ p -> pred (-ℤ m) ℤ+ p) x
     ∙ sym (ℤ+-assoc (pred (-ℤ m)) z (m ℤ* z))
     ∙ cong (λ p -> p ℤ+ m ℤ* z) (predℤ+ (-ℤ m) z)
     ∙ predℤ+ ((-ℤ m) ℤ+ z) (m ℤ* z)
     ∙ cong pred
       ( sym (cong (λ p -> p ℤ+ m ℤ* z) (ℤ+-comm (-ℤ m) z))
         ∙ ℤ+-assoc z (-ℤ m) (m ℤ* z)
       )
     ∙ sym (predℤ+ z ((-ℤ m) ℤ+ m ℤ* z))
     ∙ sym (cong (λ p -> pred z ℤ+ p) (ℤ*pred m z)))

predℤ* : ∀ m n -> pred m ℤ* n ≡ (-ℤ n) ℤ+ (m ℤ* n)
predℤ* m = ℤ-elim-prop.f
  (trunc _ _)
  (ℤ*zero (pred m)
    ∙ sym (ℤ*zero m)
    ∙ sym (zeroℤ+ (m ℤ* zero))
    ∙ sym (cong (λ p -> p ℤ+ m ℤ* zero) -ℤzero))
  (λ {z} x →
     ℤ*succ (pred m) z
     ∙ cong (λ p -> pred m ℤ+ p) x
     ∙ (predℤ+ m ((-ℤ z) ℤ+ m ℤ* z))
     ∙ cong pred
       ( sym (ℤ+-assoc m (-ℤ z) (m ℤ* z))
       ∙ cong (λ p -> p ℤ+ m ℤ* z) (ℤ+-comm (-ℤ z) m)
       ∙ ℤ+-assoc (-ℤ z) m (m ℤ* z)
       )
     ∙ sym (predℤ+ (-ℤ z) (m ℤ+ m ℤ* z))
     ∙ sym (cong (λ p -> pred (-ℤ z) ℤ+ p) (ℤ*succ m z))
     ∙ sym (cong (λ p -> p ℤ+ m ℤ* succ z) (-ℤsucc z))
     )
  (λ {z} x →
     ℤ*pred (pred m) z
     ∙ cong (λ p -> -ℤ pred m ℤ+ p) x
     ∙ cong (λ p -> p ℤ+ ((-ℤ z) ℤ+ m ℤ* z)) (-ℤpred m)
     ∙ succℤ+ (-ℤ m) ((-ℤ z) ℤ+ m ℤ* z)
     ∙ cong succ
       ( sym (ℤ+-assoc (-ℤ m) (-ℤ z) (m ℤ* z))
       ∙ cong (λ p -> p ℤ+ m ℤ* z) (ℤ+-comm (-ℤ z) (-ℤ m))
       ∙ ℤ+-assoc (-ℤ z) (-ℤ m) (m ℤ* z)
       ∙ sym (cong (λ p -> (-ℤ z) ℤ+ p) (ℤ*pred m z))
       )
     ∙ sym (succℤ+ (-ℤ z) (m ℤ* pred z))
     ∙ sym (cong (λ p -> p ℤ+ m ℤ* pred z) (-ℤpred z))
     )

ℤ*-dist : ∀ n m k -> n ℤ* (m ℤ+ k) ≡ n ℤ* m ℤ+ n ℤ* k
ℤ*-dist n m = ℤ-elim-prop.f
  (trunc _ _)
  ( cong (λ p -> n ℤ* p) (ℤ+zero m)
    ∙ sym (ℤ+zero (n ℤ* m))
    ∙ sym (cong (λ p -> n ℤ* m ℤ+ p) (ℤ*zero n))
    )
  (λ {z} x →
     cong (λ p -> n ℤ* p) (ℤ+succ m z)
     ∙ ℤ*succ n (m ℤ+ z)
     ∙ cong (λ p -> n ℤ+ p) x
     ∙ (sym (ℤ+-assoc n (n ℤ* m) (n ℤ* z))
     ∙ cong (λ p -> p ℤ+ n ℤ* z) (ℤ+-comm (n ℤ* m) n)
     ∙ ℤ+-assoc (n ℤ* m) n (n ℤ* z))
     ∙ sym (cong (λ p -> n ℤ* m ℤ+ p) (ℤ*succ n z)))
  (λ {z} x →
     cong (λ p -> n ℤ* p) (ℤ+pred m z)
     ∙ ℤ*pred n (m ℤ+ z)
     ∙ cong (λ p -> (-ℤ n) ℤ+ p) x
     ∙ sym (ℤ+-assoc (-ℤ n) (n ℤ* m) (n ℤ* z))
     ∙ cong (λ p -> p ℤ+ n ℤ* z) (ℤ+-comm (n ℤ* m) (-ℤ n))
     ∙ ℤ+-assoc (n ℤ* m) (-ℤ n) (n ℤ* z)
     ∙ sym (cong (λ p -> n ℤ* m ℤ+ p) (ℤ*pred n z)))

ℤ*-assoc : ∀ n m k -> n ℤ* m ℤ* k ≡ n ℤ* (m ℤ* k)
ℤ*-assoc n m = ℤ-elim-prop.f
  (trunc _ _)
  (ℤ*zero (n ℤ* m) ∙ sym (ℤ*zero n) ∙ sym (cong (λ p -> n ℤ* p) (ℤ*zero m)))
  (λ {z} x →
     ℤ*succ (n ℤ* m) z
     ∙ cong (λ p -> n ℤ* m ℤ+ p) x
     ∙ sym (ℤ*-dist n m (m ℤ* z))
     ∙ sym (cong (λ p -> n ℤ* p) (ℤ*succ m z)))
  (λ {z} x → 
     ℤ*pred (n ℤ* m) z
     ∙ sym (cong (λ p -> p ℤ+ n ℤ* m ℤ* z) (ℤ*-ℤ n m))
     ∙ cong (λ p -> n ℤ* (-ℤ m) ℤ+ p) x
     ∙ sym (ℤ*-dist n (-ℤ m) (m ℤ* z))
     ∙ sym (cong (λ p -> n ℤ* p) (ℤ*pred m z)))

ℤ*-comm : ∀ n m -> n ℤ* m ≡ m ℤ* n
ℤ*-comm n = ℤ-elim-prop.f
  (trunc _ _)
  (ℤ*zero n ∙ sym (zeroℤ* n))
  (λ {z} x →
    ℤ*succ n z
    ∙ cong (λ p -> n ℤ+ p) x
    ∙ sym (succℤ* z n))
  λ {z} x →
    ℤ*pred n z
    ∙ cong (λ p -> (-ℤ n) ℤ+ p) x
    ∙ sym (predℤ* z n)

