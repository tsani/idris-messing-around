module UList

import Data.Fin

%default total
%access public export

data UVect : Type -> Nat -> Type
data Fresh : a -> UVect a n -> Type

data UVect : Type -> Nat -> Type where
  Nil : UVect a Z
  Cons : (uv : UVect a n) -> (x : a) -> (fresh : Fresh x uv) -> UVect a (S n)
  
data Fresh : a -> UVect a n -> Type where
  FreshNil : (x : a) -> Fresh x Nil
  FreshCons : {x, x' : a} -> Not (x = x') -> (f : Fresh x uv) -> Fresh x (Cons uv x' f')

%name UVect uv, uv'
%name Fresh f, f', fresh, fresh'
  
data Elem : (x : a) -> UVect a n -> Type where
  Here : Elem x (Cons uv x f)
  There : Elem x uv -> Elem x (Cons uv x' f)
  
%name Elem e, e'
  
Uninhabited (Elem s Nil) where
  uninhabited Here impossible
  uninhabited (There _) impossible
  
freshElemAbsurd : Fresh x' ns -> Elem x' ns -> Void
freshElemAbsurd (FreshNil s') e = absurd e
freshElemAbsurd (FreshCons g f) Here = g Refl
freshElemAbsurd (FreshCons g f) (There e) = freshElemAbsurd f e
  
Uninhabited (Fresh s' ns, Elem s' ns) where
  uninhabited (f, e) = freshElemAbsurd f e

||| Accesses a name at a particular index.
index : UVect a n -> Fin n -> a
index Nil i = absurd i
index (Cons n x f) FZ = x
index (Cons n x f) (FS i) = index n i
  
||| If you index into a list, then you get something from the list.
indexElem : (uv : UVect a n) -> (i : Fin n) -> Elem (index uv i) uv
indexElem (Cons ns s fresh) FZ = Here
indexElem (Cons ns s fresh) (FS x) = There (indexElem ns x)
  
elemIndex : {uv : UVect a n} -> Elem x uv -> Fin n
elemIndex Here = FZ
elemIndex (There e) = FS (elemIndex e)
  
||| Elem proofs are unique.
elemUnique : (e1 : Elem x uv) -> (e2 : Elem x uv) -> e1 = e2
elemUnique Here Here {uv = (Cons ns' s f)} = Refl
elemUnique Here (There e) {uv = (Cons ns' s f)} = absurd (f, e)
elemUnique (There e) Here {uv = (Cons ns' s f)} = absurd (f, e)
elemUnique (There e) (There e') {uv = (Cons ns' s' f)} = cong $ elemUnique e e'

||| `elemIndex` is the inverse of `indexElem`.
elemIndexLoop : (uv : UVect a n) -> (i : Fin n) -> elemIndex (indexElem uv i) = i
elemIndexLoop (Cons uv x fresh) FZ = Refl
elemIndexLoop (Cons uv y fresh) (FS x) = cong $ elemIndexLoop uv x

data Lookup : UVect a n -> a -> Type where
  ||| An index was found for the string.
  Found : Elem x uv -> Lookup uv x

  ||| The string is actually fresh in this list.
  NotFound : Fresh x uv -> Lookup uv x
  
||| Looks up a name's index.
lookup : DecEq a => (uv : UVect a n) -> (x : a) -> Lookup uv x
lookup [] s {n=Z} = NotFound (FreshNil s)
lookup (Cons ns x f) s {n=S n} with (decEq s x)
  lookup (Cons ns x f) x {n=S n} | (Yes Refl) = Found Here
  lookup (Cons ns x f) s {n=S n} | (No contra) with (lookup ns s)
    lookup (Cons ns x f) s {n=S n} | (No contra) | (Found e) =
      Found (There e)
    lookup (Cons ns x f) s {n=S n} | (No neq) | (NotFound fresh) =
      NotFound (FreshCons neq fresh)
