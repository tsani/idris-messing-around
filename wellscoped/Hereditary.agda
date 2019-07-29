{-# OPTIONS --cubical #-}

module Hereditary where

infixr 20 _⇒_
data Ty : Set where
  𝟙 : Ty
  _⇒_ : Ty -> Ty -> Ty

infixl 20 _,_
data Ctx : Set where
  ε : Ctx
  _,_ : Ctx -> Ty -> Ctx

data Var : Ctx -> Ty -> Set where
  vz : ∀ {Γ σ} -> Var (Γ , σ) σ
  vs : ∀ {τ Γ σ} -> Var Γ σ -> Var (Γ , τ) σ

data Tm (Γ : Ctx) : Ty -> Set where
  var : ∀ {σ} -> Var Γ σ -> Tm Γ σ
  lam : ∀ {σ τ} -> Tm (Γ , σ) τ -> Tm Γ (σ ⇒ τ)
  _·_ : ∀ {σ τ} -> Tm Γ (σ ⇒ τ) -> Tm Γ σ -> Tm Γ τ

infixl 30 _-_
_-_ : ∀ {σ} (Γ : Ctx) -> Var Γ σ -> Ctx
ε - ()
(Γ , σ) - vz = Γ
(Γ , τ) - vs x = Γ - x , τ

wkv : ∀ {Γ τ σ} (x : Var Γ σ) -> Var (Γ - x) τ -> Var Γ τ
wkv vz v = vs v
wkv (vs x) vz = vz
wkv (vs x) (vs v) = vs (wkv x v)

data _≡-var_ {Γ : Ctx} : ∀ {σ τ} -> Var Γ σ -> Var Γ τ -> Set where
  same : ∀ {σ} {x : Var Γ σ} -> x ≡-var x
  diff : ∀ {τ σ} (x : Var Γ σ) (y : Var (Γ - x) τ) ->
         x ≡-var wkv x y

suc-≡-var : ∀ {Γ σ₁ σ₂ τ} {x : Var Γ σ₁} {y : Var Γ σ₂} ->
            x ≡-var y -> vs {τ} x ≡-var vs {τ} y
suc-≡-var same = same
suc-≡-var (diff x y) = diff (vs x) (vs y)

_≡-var?_ : ∀ {Γ σ τ} -> (x : Var Γ σ) -> (y : Var Γ τ) -> x ≡-var y
vz ≡-var? vz = same
vz ≡-var? vs y = diff vz y
vs x ≡-var? vz = diff (vs x) vz
vs x ≡-var? vs y = suc-≡-var (x ≡-var? y)

wkTm : ∀ {Γ σ τ} (x : Var Γ σ) -> Tm (Γ - x) τ -> Tm Γ τ
wkTm x (var x₁) = var (wkv x x₁)
wkTm x (lam t) = lam (wkTm (vs x) t)
wkTm x (t · t₁) = (wkTm x t) · (wkTm x t₁)

_↑ : ∀ {Γ τ τ'} -> Tm Γ τ -> Tm (Γ , τ') τ
t ↑ = wkTm vz t

[_←_]-var : ∀ {Γ σ τ} -> (x : Var Γ σ) -> Tm (Γ - x) σ -> Var Γ τ -> Tm (Γ - x) τ
[ x ← t ]-var v with x ≡-var? v
[ x ← t ]-var .x | same = t
[ x ← t ]-var .(wkv x y) | diff .x y = var y

-- [_/_]-var : ∀ {Γ σ τ} -> Var Γ τ -> (x : Var Γ σ) -> Tm (Γ - x) σ -> Tm (Γ - x) τ
-- [ v / x ]-var t with x ≡-var? v
-- [ v / .v ]-var t | same = t
-- [ .(wkv x y) / x ]-var t | diff .x y = var y

[_←_] : ∀ {Γ σ τ} -> (x : Var Γ σ) -> Tm (Γ - x) σ -> Tm Γ τ -> Tm (Γ - x) τ
[ x ← t ] (var x₁) = [ x ← t ]-var x₁
[ x ← t ] (lam s) = lam ([ vs x ← t ↑ ] s)
[ x ← t ] (s · s₁) = [ x ← t ] s · [ x ← t ] s₁
