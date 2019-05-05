%default total

interface Groupoid t where
  constructor MkGroupoid
  (<+>) : t -> t -> t
  
Groupoid Nat where
  (<+>) = plus
  
-- > :t MkGroupoid
-- (t -> t -> t) -> Groupoid t
  
-- > :printdef Groupoid
-- data Groupoid : Type -> Type where
--   MkGroupoid : (t -> t -> t) -> Groupoid t
  
myGroupoid : Groupoid (Nat, Nat)
myGroupoid = MkGroupoid p where
  p (n11, n12) (n21, n22) = (n11 <+> n21, n12 <+> n22)
  
-- problem: Idris doesn't find myGroupoid implementation for (Nat, Nat) if we just write <+>,
-- so I manually unpack the implementation
example : (Nat, Nat)
example = let (MkGroupoid p) = myGroupoid in p (1, 2) (2, 3)
  
-- alternatively, an implementation declaration does the trick:
Groupoid (Nat, Nat) where
  (n11, n12) <+> (n21, n22) = (n11 <+> n21, n12 <+> n22)
  
  
example2 : (Nat, Nat)
example2 = (1, 2) <+> (2, 3)
  
-- manual unpacking is always an option, if the implementation is named
  
[foo] Groupoid (Nat, Nat) where
  (n11, n12) <+> (n21, n22) = (n11 <+> n21, n12 <+> n22)

example3 : (Nat, Nat)
example3 = let (MkGroupoid p) = foo in p (1, 2) (2, 3)
