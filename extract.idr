data So : Bool -> Type where
  Oh : So True
  
noWayJose : So False -> a
noWayJose Oh impossible -- see ?
  
data OrdTuple : Type -> Type where
  MkOrdTuple : Ord t => (x : t) -> (y : t) -> So (x <= y) -> OrdTuple t
  
ex1 : OrdTuple Nat
ex1 = MkOrdTuple 1 4 Oh
  
-- doesn't compile for me:
-- ex2 : OrdTuple Nat
-- ex2 = MkOrdTuple 4 1 Oh
