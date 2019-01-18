module RTT -- regular tree types
  
import Data.Fin
import Data.Vect
  
%default total
  
namespace Misc
  pairInjective : (x1, x2) = (y1, y2) -> (x1 = y1, x2 = y2)
  pairInjective Refl = (Refl, Refl)
  
namespace Syntax
  ||| A small universe of types, with no functions, but with LFPs.
  ||| The presentation uses well-scoped de Bruijn indices.
  data Reg : Nat -> Type where
    ||| Unit type.
    Top : Reg n
    ||| Empty type.
    Bot : Reg n
    ||| Top variable. The context must be nonempty.
    Var : Reg (S n)
    ||| Weakening.
    Wk : Reg n -> Reg (S n)
    ||| Local definitions.
    Let : Reg n -> Reg (S n) -> Reg n
    ||| Sum types.
    (+) : Reg n -> Reg n -> Reg n
    ||| Product types.
    (*) : Reg n -> Reg n -> Reg n
    ||| Least fixed point.
    Mu : Reg (S n) -> Reg n
  
  %name Reg t, t', s, s'
  
  ||| Embed a value from a finite type into the regular tree type as a
  ||| variable.
  var : Fin n -> Reg n
  var FZ = Var
  var (FS f) = Wk (var f)
  
  ||| Contexts.
  data Tel : Nat -> Type where
    Nil : Tel Z
    (::) : Tel n -> Reg n -> Tel (S n)
  
  %name Tel g, g'
  
  infix 1 |-
  
  ||| Well-typed terms.
  data (|-) : Tel n -> Reg n -> Type where
    VHere : g |- t -> g::t |- Var
    VThere : g |- t -> g::s |- Wk t
    Def : g::s |- t -> g |- Let s t
    InL : g |- s -> g |- s + t
    InR : g |- t -> g |- s + t
    Unit : g |- Top
    Pair : g |- s -> g |- t -> g |- s * t
    In : g :: Mu f |- f -> g |- Mu f
  
-- Example: coding the natural numbers
namespace Nat
  Nat : Reg n
  Nat = Mu (Top + Var)
  
  z : g |- Nat
  z = In (InL Unit)
  
  s : g |- Nat -> g |- Nat
  s n = In (InR (VHere n))
  
  (+) : g |- Nat -> g |- Nat -> g |- Nat
  (In (InL Unit)) + n = n
  (In (InR (VHere x))) + n = s (x + n)
  
-- Interpretation of codes for types
namespace InterpType
  mutual
    ||| Auxiliary datatype used by `interp` for interpreting fixed points.
    data Fix : Vect n Type -> Reg n -> Type where
      MkFix : interp (Fix g (Mu t) :: g) t -> Fix g (Mu t)
  
    ||| Interprets a code with n variables into an Idris Type,
    ||| provided we have n Types associated to those variables.
    interp : (context : Vect n Type) -> (code : Reg n) -> Type
    interp g Top = ()
    interp g Bot = Void
    interp (t :: g) Var = t
    interp (_ :: g) (Wk t) = interp g t
    interp g (Let t t') = interp (interp g t :: g) t'
    interp g (t + t') = Either (interp g t) (interp g t')
    interp g (t * t') = (interp g t, interp g t')
    interp g (Mu t) = Fix g (Mu t)
    -- intuitively, we want to just interp (Mu t), add it to the context, and keep going
    -- but we can't because that's an obvious infinite loop.
    -- The solution is to add an indirection with an auxiliary datatype, Fix.
    -- Fix lets us embed a Mu code inside the universe of Idris type, allowing us
    -- to delay interpreting the type any further, until we need to on the term level.

  unFix : Fix g (Mu t) -> interp (Fix g (Mu t) :: g) t
  unFix (MkFix t') = t'
  
  mkFixInjective : MkFix x = MkFix y -> x = y
  mkFixInjective Refl = Refl
  
namespace InterpCtx
  ||| Interprets a context into an environment.
  interp : Tel n -> Vect n Type
  interp [] = []
  interp (g :: t) = interp (interp g) t :: interp g

namespace InterpTerm
  ||| Interprets a coded term into an Idris term of the appropriate
  ||| type.
  ||| @ g The context of the type.
  ||| @ t The type of the term.
  total
  interp : g |- t -> interp (interp g) t
  interp (VHere x) = interp x
  interp (VThere x) = interp x
  interp (Def x) = interp x
  interp (InL x) = Left (interp x)
  interp (InR x) = Right (interp x)
  interp Unit = ()
  interp (Pair x y) = (interp x, interp y)
  interp (In x) = MkFix (interp x)
  
  total
  interpInjective : {g : Tel n} -> {x : g |- t} -> {y : g |- t} ->
                    interp x = interp y -> x = y
  interpInjective {x = (VHere x)} {y = (VHere y)} prf =
    cong $ interpInjective {x} {y} prf
  interpInjective {x = (VThere x)} {y = (VThere y)} prf =
    cong $ interpInjective {x} {y} prf
  interpInjective {x = (Def x)} {y = (Def y)} prf =
    cong $ interpInjective {x} {y} prf
  interpInjective {x = (InL x)} {y = (InL y)} prf =
    cong $ interpInjective {x} {y} (leftInjective prf)
  interpInjective {x = (InL _)} {y = (InR _)} Refl impossible
  interpInjective {x = (InR _)} {y = (InL _)} Refl impossible
  interpInjective {x = (InR x)} {y = (InR y)} prf = 
    cong $ interpInjective {x} {y} (rightInjective prf)
  interpInjective {x = Unit} {y = Unit} prf = Refl
  interpInjective {x = (Pair x1 x2)} {y = (Pair y1 y2)} prf =
    let (p1, p2) = pairInjective prf in
    let i1 = interpInjective {x=x1} {y=y1} p1 in
    let i2 = interpInjective {x=x2} {y=y2} p2 in
    case (i1, i2) of
      (Refl, Refl) => Refl
  interpInjective {x = (In x)} {y = (In y)} prf =
    cong $ interpInjective {x} {y} (mkFixInjective prf)
  
namespace DecEq
  decEq : (x : g |- t) -> (y : g |- t) -> Dec (x = y)
  decEq (VHere x) (VHere y) with (decEq x y)
    decEq (VHere x) (VHere y) | (Yes prf) = Yes (cong prf)
    decEq (VHere x) (VHere y) | (No contra) =
      No $ \Refl => contra Refl

  decEq (VThere x) (VThere y) with (decEq x y)
    decEq (VThere x) (VThere y) | (Yes prf) = Yes (cong prf)
    decEq (VThere x) (VThere y) | (No contra) =
      No $ \Refl => contra Refl

  decEq (Def x) (Def y) with (decEq x y)
    decEq (Def x) (Def y) | (Yes prf) = Yes (cong prf)
    decEq (Def x) (Def y) | (No contra) =
      No $ \Refl => contra Refl

  decEq (InL x) (InL y) with (decEq x y)
    decEq (InL x) (InL y) | (Yes prf) = Yes (cong prf)
    decEq (InL x) (InL y) | (No contra) =
      No $ \Refl => contra Refl

  decEq (InL x) (InR y) = No $ \Refl impossible
  decEq (InR x) (InL y) = No $ \Refl impossible

  decEq (InR x) (InR y) with (decEq x y)
    decEq (InR x) (InR y) | (Yes prf) = Yes (cong prf)
    decEq (InR x) (InR y) | (No contra) =
      No $ \Refl => contra Refl

  decEq Unit Unit = Yes Refl
  decEq (Pair x1 y1) (Pair x2 y2) with (decEq x1 x2, decEq y1 y2)
    decEq (Pair x2 y2) (Pair x2 y2) | (Yes Refl, Yes Refl) =
      Yes Refl
    decEq (Pair x1 y1) (Pair x2 y2) | (No contra, _) =
      No $ \Refl => contra Refl
    decEq (Pair x1 y1) (Pair x2 y2) | (_, No contra) =
      No $ \Refl => contra Refl

  decEq (In x) (In y) with (decEq x y)
    decEq (In x) (In y) | (Yes prf) = Yes (cong prf)
    decEq (In x) (In y) | (No contra) = No $ \Refl => contra Refl
  
  ||| Equality of interpretations of coded terms is decidable.
  |||
  ||| Follows decidable equality of coded terms, using substitutivity
  ||| and injectivity of interpretation.
  |||
  ||| @ x Code for the left term.
  ||| @ y Code for the right term.
  decEq' : (x : g |- t) -> (y : g |- t) -> Dec (interp x = interp y)
  decEq' x y with (decEq x y) -- decide equality of the codes
    decEq' x y | (Yes prf) = Yes (cong prf)
    decEq' x y | (No contra) = No $ \p => contra (interpInjective p)
    -- contra is a refutation of the equality of the codes
    -- Using injectivity, we transform p from an equality of interpretations
    -- into an equality of codes. This is a contradiction.


