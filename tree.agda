{-# OPTIONS --cubical #-}

open import Cubical.Foundations.Everything hiding ( _∨_ )
open import Cubical.Induction.WellFounded
open import Cubical.Data.Sum
open import Cubical.Data.List
open import Cubical.Data.Unit
open import Cubical.Data.Nat
open import Cubical.Data.Nat.Order
open import Cubical.Data.Prod
open import Cubical.Data.Empty
open import Function hiding (case_of_)

_∨_ : ℕ -> ℕ -> ℕ
zero ∨ n = n
suc m ∨ zero = suc m
suc m ∨ suc n = suc (m ∨ n)

infixl 20 _∨_

∨-assoc : ∀ n₁ n₂ n₃ -> n₁ ∨ n₂ ∨ n₃ ≡ n₁ ∨ (n₂ ∨ n₃)
∨-assoc zero n₂ n₃ = refl
∨-assoc (suc n₁) zero n₃ = refl
∨-assoc (suc n₁) (suc n₂) zero = refl
∨-assoc (suc n₁) (suc n₂) (suc n₃) = cong suc (∨-assoc n₁ n₂ n₃)

data Tree : Set where
  ⟨_⟩ : List Tree -> Tree

leaf : Tree
leaf = ⟨ [] ⟩

-- balanced parentheses
data P : ℕ -> Set where
  -- empty string
  done : P zero
  -- open parenthesis
  down : ∀ {n} -> P (suc n) -> P n
  -- close parenthesis
  up : ∀ {n} -> P n -> P (suc n)

-- compute the length of a sequence
∥_∥ₚ : ∀ {n} -> P n -> ℕ
∥ done ∥ₚ = zero
∥ down p ∥ₚ = suc ∥ p ∥ₚ
∥ up p ∥ₚ = suc ∥ p ∥ₚ

-- A parenthesis sequence with an unknown number of extra close-parens.
P' : Set
P' = Σ[ n ∈ ℕ ] P n

-- well-ordering on parenthesis-sequences by ordering their lengths
_≲_ : P' -> P' -> Set
(_ , p) ≲ (_ , q) = ∥ p ∥ₚ < ∥ q ∥ₚ

≲-trans : ∀ {p q r} -> p ≲ q -> q ≲ r -> p ≲ r
≲-trans {_ , p} {(_ , q)} {(_ , r)} a b = <-trans a b

¬-≲-zero : (y : P') -> y ≲ (zero , done) -> ⊥
¬-≲-zero _ p = ¬-<-zero p

-- module WFII {ℓ ℓ' A B}
--   (_<_ : Rel {ℓ} B ℓ')
--   (f : A → B) where
-- 
--   _⊰_ : Rel {ℓ} A ℓ'
--   x ⊰ y = f x < f y
-- 
--   accessible : ∀ {x} → Acc _<_ (f x) → Acc _⊰_ x
--   accessible {x} a = acc (λ y y⊰x → accessible (access a (f y) y⊰x))

-- ≲-split : ∀ {n p} (y : P') → y ≲ (n , down p) →
--           (∥ snd y ∥ₚ < ∥ p ∥ₚ) ⊎ (∥ snd y ∥ₚ ≡ ∥ p ∥ₚ)
-- ≲-split _ e = case <-split e of λ
--   { (inl x) → inl x
--   ; (inr x) → inr x
--   }
-- 
-- ≲-down : ∀ {y n p} → y ≲ (n , down p) → y ≲ (suc n , p)
-- ≲-down {y} y<down-p = case ≲-split y y<down-p of λ
--   { (inl x) → {!!}
--   ; (inr x) → {!!}
--   }
-- 
-- acc-down' : ∀ {n p} → Acc _≲_ (suc n , p) → Acc _≲_ (n , down p)
-- acc-down' a = acc (λ y x → proof y a x) where
--   proof : ∀ {n p} y → Acc _≲_ (suc n , p) → y ≲ (n , down p) → Acc _≲_ y
--   proof y a e = case ≲-split y e of λ
--     { (inl x) → {!access a y!}
--     ; (inr x) → {!!}
--     }
-- 
-- acc-promote : ∀ {n} (p : P n) -> Acc _<_ ∥ p ∥ₚ → Acc _≲_ (_ , p)
-- acc-promote done a = acc (λ y x → ⊥-elim (¬-≲-zero y x))
-- acc-promote (down p) a = acc-down' (acc-promote p (access a _ ≤-refl)) -- where
--  --  proof : ∀ {n p} -> Acc _<_ (∥ p ∥ₚ) → WFRec _≲_ (Acc _≲_) (n , down p)
--  --  proof a (l , q) q<down-p =
--  --    case <-split q<down-p of λ
--  --    { (inl q<p) → acc-promote q (access a _ q<p) 
--  --    ; (inr q≡p) → {!!}
--  --    }
-- acc-promote (up p) a = {!!}
-- 
-- The type `P n` means that the string has `n` unmatched close-parens.
-- `P 0` is a balanced string.

-- weaken : ∀ {n} -> P n -> P (suc n)

-- concat : ∀ {n} -> P n -> P n -> P n

-- depth : Tree -> ℕ
-- depth leaf = zero
-- depth ⟨ l , r ⟩ = depth l ∨ depth r

-- weakens two trees to their max depth
-- ∨-weaken

Trees→P : ∀ {n} -> (ts : List Tree) -> P n -> P n
Trees→P [] p = p
Trees→P (⟨ ts' ⟩ ∷ ts) p =
  down $
  Trees→P ts' $
  up $
  Trees→P ts p

Tree→P : (t : Tree) -> P zero 
Tree→P ⟨ ts ⟩ = Trees→P ts done

P→Trees : ∀ {n} -> (p : P (suc n)) -> Acc _<_ ∥ p ∥ₚ ->
          List Tree × (Σ[ p' ∈ P n ] (_ , p') ≲ (_ , p))
P→Trees (down p) (acc f) with P→Trees p (f _ ≤-refl)
P→Trees (down p) (acc f) | ts , (p' , p'≲p) with P→Trees p' (f _ (≤-suc p'≲p))
P→Trees (down p) (acc f) | ts , (p' , p'≲p) | ts' , (p'' , p''≲p') =
  ⟨ ts ⟩ ∷ ts' , p'' , ≤-suc (<-trans p''≲p' p'≲p)
P→Trees (up p) a = [] , (p , ≤-refl)

P→Trees' : (p : P zero) -> Acc _<_ ∥ p ∥ₚ -> List Tree
P→Trees' done a = []
P→Trees' (down p) (acc f) with P→Trees p (f _ ≤-refl)
P→Trees' (down p) (acc f) | ts , (p' , p'≲p) = ⟨ ts ⟩ ∷ P→Trees' p' (f _ (≤-suc p'≲p))

P→Tree' : (p : P zero) -> Tree
P→Tree' p = ⟨ P→Trees' p (<-wellfounded _) ⟩

example-path : P zero
example-path = down (down (down (up (up (up done)))))

example-tree : Tree
example-tree =
  ⟨ leaf ∷ leaf ∷ [] ⟩

-- P→Tree→P : ∀ {n} (p : P n) (a : Acc _<_ (suc ∥ p ∥ₚ)) →
--            Trees→P (P→Trees' (down p) a) done ≡ down p
-- P→Tree→P (down p) a = {!!}
-- P→Tree→P (up p) a = {!!}
-- 
-- P→Tree→P' : (p : P zero) -> (a : Acc _<_ ∥ p ∥ₚ) ->
--            Trees→P (P→Trees' p a) done ≡ p
-- P→Tree→P' done a = refl
-- P→Tree→P' (down p) a = {!P→Tree→P p a!}

-- P→Tree : P -> Tree Unit
-- P→Tree 
