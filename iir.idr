-- module InductionInductionRecursion
  
%default covering

-- universe of types
data U : Type
  
-- expressions
data E : U -> Type

interpTy : U -> Type
interpTy' : U -> Type

data U : Type where
  Ty : U
  Prod : U -> U -> U
  Pi : (u : U) -> (interpTy' u -> U) -> U
  Nat : U
  Eq : {u : U} -> interpTy' u -> interpTy' u -> U
  -- allow writing any type, provided that it is the interpretation of
  -- some code
  Embed : {u : U} -> (t : Type) -> {auto prf : t = interpTy' u} -> U
  

interp : E t -> interpTy' t
interp' : E t -> interpTy' t

interpTy (Prod x y) = (interpTy' x, interpTy' y)
interpTy (Pi u f) = (x : interpTy' u) -> interpTy' (f x)
interpTy Nat = Nat
interpTy Ty = Type
interpTy (Eq x y) = x = y
interpTy (Embed t) = t
  
interpTy' x = assert_total (interpTy x)

data E : U -> Type where
  Lam : {f : interpTy' a -> U} -> ((x : interpTy' a) -> E (f x)) -> E (Pi a f)
  App : E (Pi a f) -> (x : E a) -> E (f (interp' x))
  Plus : E Nat -> E Nat -> E Nat
  Refl : E (Eq x x)
  Z : E Nat
  S : E Nat -> E Nat
  Pair : E a -> E b -> E (Prod a b)
  Const : interpTy' a -> E a
  
interp (Lam g) = \x => interp' (g x) -- no guarantee that g x is smaller!!
interp (App f x) = (interp' f) (interp' x)
interp (Plus x y) = interp' x + interp' y
interp Refl = Refl
interp Z = Z
interp (S x) = S (interp' x)
interp (Pair x y) = (interp' x, interp' y)
interp (Const x) = x
  
interp' x = assert_total (interp x)

-- identity function for nats
idNat : E (Pi Nat (\_ => Nat))
idNat = Lam (\x => Const x)
 
-- id : E (Pi Ty (\a => Pi a (\_ => Embed {u = Ty} {prf = Refl} a)))
-- id = Lam (\_ => Lam (\x => Const x))
  
(/=) : (x : a) -> (y : a) -> Type
x /= y = Not (x = y)
  
namespace DList
  data DList : Type -> Type
  data Fresh : a -> DList a -> Type

  data DList : Type -> Type where
    Nil : DList a
    Cons : (x : a) -> (d : DList a) -> {auto prf : Fresh x d} -> DList a

  data Fresh : a -> DList a -> Type where
    -- everything is fresh in the empty list
    FNil : Fresh x Nil
    -- fresh in a cons if fresh in the tail and distinct from the head
    FCons : (x /= y) -> Fresh x ys -> Fresh x (Cons y ys {prf})

  ex : DList Nat
  ex = (Cons Z (Cons (S Z) Nil) {prf = FCons (\Refl impossible) FNil})
