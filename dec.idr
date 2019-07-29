module dec

data D : (a -> Type) -> Type where
  MkD : Dec (x : a ** p x) -> D p
  
(>>=) : {p : a -> Type} -> {q : a -> Type} ->
        (x : a ** p x) ->
        ({x : a} -> p x -> (y : a ** q y)) ->
        (y : a ** q y)
(>>=) (x ** prf) f = f prf
