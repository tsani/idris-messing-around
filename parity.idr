module Parity

data Parity : Nat -> Type where
  Even : Parity (n + n)
  Odd : Parity (S (n + n))
  
lem : S (S (x + x)) = (S x) + (S x)
lem {x} = cong (plusSuccRightSucc x x)
  
total
parity : (n : Nat) -> Parity n
parity Z = Even {n = Z}
parity (S n) with (parity n)
  parity (S (x + x)) | Even = Odd
  parity (S (S (x + x))) | Odd = replace (sym lem) Even

natToBin : Nat -> List Bool
natToBin n with (parity n)
  natToBin (x + x) | Even = False :: natToBin x
  natToBin (S (x + x)) | Odd = True :: natToBin x

  
foo : (n : Nat) -> (m : Nat) -> (n = m) -> a
foo m m Refl = ?a_1

 
