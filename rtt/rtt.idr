module RTT -- regular tree types
  
import Data.Fin
import Data.Vect
  
%default total
  
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
  interp : g |- t -> interp (interp g) t
  interp (VHere x) = interp x
  interp (VThere x) = interp x
  interp (Def x) = interp x
  interp (InL x) = Left (interp x)
  interp (InR x) = Right (interp x)
  interp Unit = ()
  interp (Pair x y) = (interp x, interp y)
  interp (In x) = MkFix (interp x)
