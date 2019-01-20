module Renaming
  
import Data.Fin
import Syntax

%default total
  
data Renaming : {dst : Nat} -> {src : Nat} -> (d : Ctx dst) -> (g : Ctx src) -> Type where
  ||| We can weaken the empty context to any context.
  Weaken : (d : Ctx dst) -> Renaming d Nil
  ||| We can extend a renaming from g to d with a new variable
  ||| provided that the types match.
  Cons : {d : Ctx dst} -> Renaming d g -> (f : Fin dst) -> Renaming d (g :: index f d)

||| Weaken a renaming, so its destination context is larger.
weaken : Renaming d g -> Renaming (d :: w) g
weaken (Weaken d) = Weaken _
weaken (Cons r f) = Cons (weaken r) (FS f)

||| Extend a renaming with the same assumption on both sides.
extend : Renaming d g -> Renaming (d :: a) (g :: a)
extend r = Cons (weaken r) FZ

||| The identity renaming for a given context.
id : (g : Ctx n) -> Renaming g g
id [] = Weaken _
id (g :: a) = extend (id g)

%name Renaming r, r', ren, ren'

applyVar : {d : Ctx dst} -> {g : Ctx src} ->
           Renaming d g -> (i : Fin src) -> (j ** index i g = index j d)
applyVar (Weaken _) FZ impossible
applyVar (Weaken _) (FS _) impossible
applyVar (Cons r f) FZ = (f ** Refl)
applyVar (Cons r f) (FS i) = applyVar r i

apply : Renaming d g -> g |- (e, a) -> d |- (e, a)
apply r (Var i) with (applyVar r i)
  apply r (Var i) | (j ** pf) = rewrite pf in Var j
apply _ Unit = Unit
apply r (Lam y) = Lam (apply (extend r) y)
apply r (App y z) = App (apply r y) (apply r z)

namespace Weakening
  weaken : g |- (d, a) -> g :: w |- (d, a)
  weaken {g} t = apply (weaken (id g)) t
