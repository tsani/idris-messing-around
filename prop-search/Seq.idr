module Seq

import Data.Fin
import Data.Vect

%default total
  
data FKind = D | G
%name FKind fk, fk'

data Form : FKind -> Type -> Type where
  Atom : a -> Form fk a
  Top : Form fk a
  Conj : Form fk a -> Form fk a -> Form fk a
  Disj : Form G a -> Form G a -> Form G a
  Imp : Form G a -> Form D a -> Form D a

%name Form phi, phi', phi''

(+) : Form G a -> Form G a -> Form G a
(+) = Disj

(*) : Form fk a -> Form fk a -> Form fk a
(*) = Conj

atom : a -> Form fk a
atom = Atom

infixr 1 ~>
(~>) : Form G a -> Form D a -> Form D a
(~>) = Imp

data Tm : Nat -> Type where
  Var : String -> Tm n
  App : Tm n -> Tm n -> Tm n
  Pair : Tm n -> Tm n -> Tm n
  Unit : Tm n
  Right : Tm n -> Tm n
  Left : Tm n -> Tm n
  Fst : Tm n -> Tm n
  Snd : Tm n -> Tm n
  Subgoal : Fin n -> Tm n
  
weaken : Tm n -> Tm (S n)
weaken (Var x) = Var x
weaken (App x y) = App (weaken x) (weaken y)
weaken (Pair x y) = Pair (weaken x) (weaken y)
weaken Unit = Unit
weaken (Right x) = Right (weaken x)
weaken (Left x) = Left (weaken x)
weaken (Fst x) = Fst (weaken x)
weaken (Snd x) = Snd (weaken x)
weaken (Subgoal x) = Subgoal (FS x)
  
Subgoals : Type -> Nat -> Type
Subgoals a n = Vect n (Form G a)
  
||| A program is a list of terms with no subgoals, each associated
||| with a proven theorem.
Program : Type -> Type
Program a = List (Tm Z, Form D a)
  
mutual
  data State : Type -> Type where
    MkG : (sigma : Program a) -> (term : Tm Z) -> (goal : Form G a) -> State a
    MkD : (sigma : Program a) -> (ctx : Subgoals n) -> (term : Tm n) -> (ty : Form D a) -> (goal : a) ->
          State a
    Solved : (term : Tm Z) -> (ty : Form G a) -> State a
    Fail : State a
  
  data Step : State a -> State a -> Type where
    SolvedPair : 

