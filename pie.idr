module pie
  
import Data.Fin
  
data Subst : Nat -> Nat -> Type where
  Nil : Subst n Z
  (::) : 

data Tm : Fin n -> Type where
  Lam : Tm (S n) -> Tm n
  App : Tm n -> Tm n -> Tm n
  Atom : Nat -> Tm n
  Var : Fin n -> Tm n
  
