module Misc
  
%access public export
%default total

cong2 : {f : _} -> (a = b) -> (c = d) -> f a c = f b d
cong2 Refl Refl = Refl

||| If you subtract, then what you get is smaller.
lteMinus : (k, j : _) -> LTE (minus k j) k
lteMinus k Z = rewrite minusZeroRight k in lteRefl
lteMinus Z (S j) = LTEZero
lteMinus (S k) (S j) = lteSuccRight (lteMinus k j)
  
||| lteMinus for two subtractions. Follows from transitivity of LTE.
lteMinus2 : (k, j1, j2 : _) -> LTE (minus (minus k j1) j2) k
lteMinus2 k j1 j2 = lteTransitive (lteMinus (minus k j1) j2) (lteMinus k j1)
  
minusLteLeft : LTE k j -> (l : Nat) -> LTE (minus k l) (minus j l)
minusLteLeft x {k = k} {j = j} Z =
  rewrite minusZeroRight k in
  rewrite minusZeroRight j in
  x
minusLteLeft LTEZero {k = Z} {j = j} (S l) = LTEZero
minusLteLeft (LTESucc x) {k = (S k)} {j = (S j)} (S l) = minusLteLeft x l
  
mmmmpp : (k, j1, j21, j22 : _) ->
         minus (minus (minus k j1) j21) j22 = minus k (plus j1 (plus j21 j22))
mmmmpp k j1 j21 j22 =
  trans (minusMinusMinusPlus (minus k j1) j21 j22) (minusMinusMinusPlus k j1 (plus j21 j22))

minusLteRight : LTE j k -> LTE k l -> LTE j l -> LTE (l - k) (l - j)
minusLteRight LTEZero LTEZero LTEZero {l} =
  rewrite minusZeroRight l in
  lteRefl
minusLteRight LTEZero (LTESucc y) LTEZero {k = S k} {l = S l} =
  lteSuccRight $ lteMinus l k
minusLteRight (LTESucc x) (LTESucc y) (LTESucc z) {l = S l} {k = S k} {j = S j} =
  minusLteRight x y z
  
weakenLtePlus : LTE (n + m) k -> LTE m k
weakenLtePlus x {n = Z} = x
weakenLtePlus (LTESucc x) {n = (S k)} = lteSuccRight $ weakenLtePlus x
  
weakenLtPlus : LT (n + m) k -> LT m k
weakenLtPlus x {n = Z} = x
weakenLtPlus x {n = S n} = weakenLtPlus $ lteSuccLeft x

weakenLtePlusRight : LTE (m + n) k -> LTE m k
weakenLtePlusRight {n} {m} =
  rewrite plusCommutative m n in \x => weakenLtePlus x
  
weakenLtPlusRight : LT (m + n) k -> LT m k
weakenLtPlusRight {m} {n} =
  rewrite plusCommutative m n in \x => weakenLtPlus x
  
succMinus : (k, n : _) -> {smaller : LTE n k} -> S (minus k n) = minus (S k) n
succMinus k Z {smaller = LTEZero} = rewrite minusZeroRight k in Refl
succMinus (S right) (S left) {smaller = (LTESucc x)} = succMinus _ _ {smaller = x}

ltLeftPlusToMinus : (l : LT (m + n) k) -> LT n (minus k m)
ltLeftPlusToMinus (LTESucc x) {m = Z} {n = n} {k = (S right)} = LTESucc x
ltLeftPlusToMinus (LTESucc x) {m = (S m)} {n = n} {k = (S right)} = ltLeftPlusToMinus x

weakenLteMinusLeft : (l : LTE n k) -> (j : Nat) -> LTE (minus n j) k
weakenLteMinusLeft LTEZero j = LTEZero
weakenLteMinusLeft (LTESucc x) Z = LTESucc x
weakenLteMinusLeft (LTESucc x) (S k) =
  lteSuccRight $ weakenLteMinusLeft x k

