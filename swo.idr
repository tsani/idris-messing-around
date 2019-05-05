total
decStartsWithOne : (xs : List Nat) -> Maybe (ys : List Nat ** (1 :: ys = xs))
decStartsWithOne ((S Z) :: rest) = Just (rest ** Refl)
decStartsWithOne _ = Nothing
