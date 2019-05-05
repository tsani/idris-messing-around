module Min
  
%default total
  
data OrderDec : {ty : Type} -> (R : ty -> ty -> Type) -> (x, y : ty) -> Type where
  ||| The elements are related in the order as they appear in the type.
  AsIs : {R : ty -> ty -> Type} -> R x y -> OrderDec R x y
  ||| The elements are equal.
  Equal : {R : ty -> ty -> Type} -> (x = y) -> OrderDec R x y
  ||| The elemtns are related in the opposite order as they appear in the type.
  Flipped : {R : ty -> ty -> Type} -> R y x -> OrderDec R x y
  
record Order (ty : Type) (R : ty -> ty -> Type) where
  constructor MkOrder
  ||| The ordering must be transitive.
  trans : {x, y, z : ty} -> R x y -> R y z -> R x z
  ||| The order must be reflexive.
  refl : (x : ty) -> R x x
  ||| The order must be total.
  dec : (x, y : ty) -> OrderDec R x y
  
namespace Vect
  data Vect : (n : Nat) -> (a : Type) -> Type where
    Nil : Vect Z a
    (::) : a -> Vect n a -> Vect (S n) a
  
namespace All
  ||| A bundle of proofs over a vector.
  data All : (v : Vect n a) -> (P : a -> Type) -> Type where
    Nil : All Nil p
    (::) : p x -> All v p -> All (x :: v) p
  
  ||| If we can translate proofs without caring about the elements,
  ||| then we can translate a bundle of proofs over a vector.
  map : ({x : a} -> p x -> q x) -> All v p -> All v q
  map _ Nil = Nil
  map f (x :: xs) = f x :: map f xs
  
||| Is `x` a minimal element of `v` according to relation `r`?
||| i.e. for each y in v, we have `r x y`.
IsMinOfBy : (x : a) -> (v : Vect n a) -> (r : a -> a -> Type) -> Type
IsMinOfBy x v r = All v (r x)
  
vmin : Order a r ->
       (v : Vect (S n) a) ->
       (x : a ** IsMinOfBy x v r)
vmin o (x :: Nil) {n = Z} = (x ** [refl o x])
vmin o (x :: v') {n = S n} =
  let (x' ** min) = vmin o v' in
  case dec o x x' of
    -- so min proves that:
    -- for all z in v', x' <= z
    -- Now we know that x <= x',
    -- so by transitivity, we can deduce that x <= z for all z in v'
    -- and furthermore that x <= z for all z in _v_ since v' = x :: v'
    AsIs asIs =>
      (x ** refl o x :: map (trans o asIs) min)
    Equal Refl => (x ** refl o x :: min)
    Flipped flipped => (x' ** flipped :: min)

namespace Leads
  data Leads : (Vect n a) -> (Vect (n + k) a) -> Type where
    ||| The empty vector leads all vectors.
    Nil : Leads Nil v
    ||| We can stick one on.
    (::) : (x : a) -> Leads v w -> Leads (x :: v) (x :: w)
  
  
