-- (&&) : Bool -> Bool -> Bool
-- True && True = True
-- _ && _ = False

%default total

all' : (a -> Bool) -> List a -> Bool
all' f [] = True
all' f (x :: xs) = f x && all' f xs

allLemma : f x = True -> all' f xs = True -> all' f (x :: xs) = True
allLemma p1 p2 = rewrite p1 in rewrite p2 in Refl

allFiltered : (f : a -> Bool) -> (xs : List a) -> all' f (filter f xs) = True
allFiltered f [] = Refl
allFiltered f (x :: xs) = lemma (allFiltered f xs) (f x) Refl where
  lemma : all' f (filter f xs) = True -> (b : Bool) -> b = f x -> all' f (filter f (x :: xs)) = True
  lemma p False p2 =
    rewrite sym p2 in p
  lemma p True p2 = rewrite sym p2 in allLemma (sym p2) p
