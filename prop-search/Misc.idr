module Misc

(/=) : (x, y : a) -> Type
(/=) x y = Not (x = y)
