module StepIndexed
  
import Data.Fin

import Misc
import Syntax
  
%default total
  
namespace Typing
  infix 1 |-

  data (|-) : Ctx n -> (Tm n, Tp Z) -> Type where
    Lam : g :: a |- (t, b) -> g |- (Lam t, a ~> b)
    T : g |- (T, Top)
    App : g |- (t, a ~> b) -> g |- (s, a) -> g |- (App t s, b)
    Var : (i : Fin n) -> g |- (Var i, index g i)
    Fold : g |- (t, apply (single (Mu a)) a) -> g |- (Fold t, Mu a)
  %name (|-) s, s', t, t'
  
namespace Eval
  ||| Syntactic characterization of values.
  data Value : Tm Z -> Type where
    Lam : Value (Lam t)
    T : Value T
    Fold : Value t -> Value (Fold t)
    
  infix 2 |>
  
  ||| Reduction relation.
  data (|>) : Tm Z -> Tm Z -> Type where
    Beta : Value v ->
           App (Lam t) v |> apply (single v) t
    App1 : t |> t' ->
           App t s |> App t' s
    App2 : Value v -> s |> s' ->
           App v s |> App v s'
    Fold1 : t |> t' ->
            Fold t |> Fold t'
    Unfold1 : t |> t' ->
              Unfold t |> Unfold t'
    Eta : Value v ->
          Unfold (Fold v) |> v

  ||| A small-step reduction sequence between terms, indexed by its length.
  data Steps : Nat -> Tm Z -> Tm Z -> Type where
    Refl : Steps Z t t
    (::) : s' |> s -> Steps n s t -> Steps (S n) s' t
  
namespace LogRel
  data E : (k : Nat) -> (t : Tm Z) -> Tp Z -> Type
  -- data V : (k : Nat) -> (t : Tm Z) -> Tp Z -> Type
  
  V : Nat -> (t : Tm Z) -> Tp Z -> Type
  V k t (a ~> b) = (j : Nat) -> LTE j k -> (t' : Tm Z) -> Value t' -> V j t' a -> E j (App t t') b
  V k t Top = ()
  V k t (Mu a) = (j : Nat) -> LT j k -> E j (Unfold t) (apply (single (Mu a)) a) 
  V k t (Var x) = absurd x
  
  data E : (k : Nat) -> (t : Tm Z) -> Tp Z -> Type where
    MkE : ((j : _) -> {s : _} -> (l : LT j k) -> Value s ->
           Steps j t s -> LogRel.V ((-) k j {smaller=lteSuccLeft l}) s a) ->
          E k t a
  %name E e, e', e''
  
  -- minusDown : {l : LTE j k} -> (-) (S k) (S j) {smaller = LTESucc l} = (-) k j {smaller = l}
  -- minusDown = Refl
  
  data G : (k : Nat) -> Subst Tm n m -> Ctx m -> Type where
    Nil : G k Weaken Nil
    (::) : G k s g -> (Value t, V k t a) -> G k (s :: t) (g :: a)
  %name G g, g', g''
  
  infix 1 |=
  data (|=) : Ctx n -> (Tm n, Tp Z) -> Type where
    Sem : ((k : _) -> (s : _) -> G k s g -> E k (apply s t) a) -> g |= (t, a)
  %name (|=) sem, sem', sem''
  
namespace Lemmas
  valuesDontStep : Value v -> Not (v |> t)
  valuesDontStep (Fold x) (Beta _) impossible
  valuesDontStep (Fold x) (App1 _) impossible
  valuesDontStep (Fold x) (App2 _ _) impossible
  valuesDontStep (Fold x) (Fold1 y) = valuesDontStep x y
  valuesDontStep (Fold x) (Unfold1 _) impossible
  valuesDontStep (Fold x) (Eta _) impossible
  valuesDontStep Lam (Beta _) impossible
  valuesDontStep Lam (App1 _) impossible
  valuesDontStep Lam (App2 _ _) impossible
  valuesDontStep Lam (Fold1 _) impossible
  valuesDontStep Lam (Unfold1 _) impossible
  valuesDontStep Lam (Eta _) impossible
  valuesDontStep T (Beta _) impossible
  valuesDontStep T (App1 _) impossible
  valuesDontStep T (App2 _ _) impossible
  valuesDontStep T (Fold1 _) impossible
  valuesDontStep T (Unfold1 _) impossible
  valuesDontStep T (Eta _) impossible
  
  Uninhabited (Value (App s t)) where
    uninhabited Lam impossible
    uninhabited T impossible
    uninhabited (Fold _) impossible
  
  Uninhabited (Lam t |> s) where
    uninhabited (Beta _) impossible
    uninhabited (App1 _) impossible
    uninhabited (App2 _ _) impossible
    uninhabited (Fold1 _) impossible
    uninhabited (Unfold1 _) impossible
    uninhabited (Eta _) impossible
  
  Uninhabited (Value (Unfold t)) where
    uninhabited Lam impossible
    uninhabited T impossible
    uninhabited (Fold _) impossible

  ||| If a reduction sequence begins at a value, then it goes nowhere.
  valueStepsRefl : Value t -> Steps k t s -> (s = t, k = Z)
  valueStepsRefl v Refl = (Refl, Refl)
  valueStepsRefl v (x :: y) = absurd $ valuesDontStep v x
  
  namespace DC
    namespace Value
      ||| A safe value for `k` steps is safe for any fewer number of steps.
      |||
      ||| This is essentially a lifting of the transitivity property of `LTE`.
      downwardsClosed : (a : Tp Z) -> V k t a -> LTE j k -> V j t a
      downwardsClosed (Mu a) f jLTEk =
        \i, iLTj => f i (lteTransitive iLTj jLTEk)
      downwardsClosed Top _ _ = ()
      downwardsClosed (a ~> b) f jLTEk =
        \i, iLTEj, t, v, val => f i (lteTransitive iLTEj jLTEk) t v val
  
    namespace Context
      ||| Lift the downwards closed lemma from values to contexts.
      downwardsClosed : G k t a -> LTE j k -> G j t a
      downwardsClosed [] x = []
      downwardsClosed (g' :: (v, w)) l = downwardsClosed g' l :: (v, downwardsClosed _ w l)
  
    namespace Expression
      ||| Lift the downwards closed lemma from values to expressions.
      downwardsClosed : E k t a -> LTE j k -> E j t a
      downwardsClosed (MkE f) lte =
        MkE $ \j, l, v, steps =>
          let p = lteTransitive l lte in
          let v' = f j p v steps in
          let prf = minusLteLeft lte _ in
          downwardsClosed _ v' prf
  
    -- ||| Consume one available step of reduction in a safe expression
    -- ||| by adding to its reduction sequence.
    -- forwardsClosed : t |> t' -> E (S k) t a -> E k t' a
    -- forwardsClosed step (MkE f) =
    --   MkE $ \j, l, v, steps => f (S j) (LTESucc l) v (step :: steps)
  
namespace ApplicationReduction
  ||| A term is said to reduce if it steps to a value.
  |||
  ||| This is a notational convenience for definiting AppRed1 and AppRed2
  Reduces : (k : Nat) -> (t : Tm Z) -> (t' : Tm Z) -> Type
  Reduces k t t' = (Steps k t t', Value t')
  
  -- The following datatypes AppRed1 and AppRed2 express the different
  -- phases of the general reduction sequence for applications.
  
  data AppRed1 : (k : Nat) -> (t1 : Tm Z) -> (t2 : Tm Z) -> (s : Tm Z) -> Type where
    MkAppRed1 : Reduces j1 t1 s1 ->
                Steps j2 (App s1 t2) s ->
                AppRed1 (j1 + j2) t1 t2 s
    
  data AppRed2 : (k : Nat) -> (s1 : Tm Z) -> (t2 : Tm Z) -> (s : Tm Z) -> Type where
    MkAppRed2 : Reduces j1 t2 s2 ->
                Steps j2 (App s1 s2) s ->
                AppRed2 (j1 + j2) s1 t2 s
  
  -- the following two lemmas let us split up a reduction sequence for applications
  
  appRed1 : Steps k (App t1 t2) s -> Value s -> AppRed1 k t1 t2 s
  appRed1 Refl v = absurd v
  appRed1 (App1 x :: y) v with (appRed1 y v)
    appRed1 ((App1 x) :: y) v | (MkAppRed1 (steps, v') w) =
      let steps' = x :: steps in
      MkAppRed1 (steps', v') w
  appRed1 (Beta x :: steps') v = MkAppRed1 ( Refl, Lam ) (Beta x :: steps')
  appRed1 (App2 x z :: steps') v = MkAppRed1 ( Refl, x ) (App2 x z :: steps')
  
  appRed2 : Steps k (App s1 t2) s -> Value s1 -> Value s -> AppRed2 k s1 t2 s
  appRed2 Refl vs1 vs = absurd vs
  appRed2 (Beta x :: steps') vs1 vs = MkAppRed2 ( Refl, x ) (Beta x :: steps')
  appRed2 (App1 x :: steps') vs1 vs = absurd $ valuesDontStep vs1 x
  appRed2 (App2 x y :: steps') vs1 vs with (appRed2 steps' vs1 vs)
    appRed2 (App2 x y :: steps') vs1 vs | (MkAppRed2 (steps, v') w) =
      let steps' = y :: steps in
      MkAppRed2 (steps', v') w
  
  ||| Since Fold is a value form, any time we step from a Fold, we must
  ||| eventually return to the Fold.
  foldRedVal : Steps n (Fold t) v -> (v' : Tm Z ** v = Fold v')
  foldRedVal Refl = (_ ** Refl)
  foldRedVal (Fold1 y :: z) = foldRedVal z
  
  ||| Stepping between folds means all the action is happening under the Fold.
  foldRedInv : Steps n (Fold t) (Fold v) -> Steps n t v
  foldRedInv Refl = Refl
  foldRedInv (Fold1 s :: steps) = s :: foldRedInv steps
  
namespace Fundamental
  applySingle : (s : Subst Tm n k) -> (t' : Tm n) -> (t : Tm (S k)) ->
                SubTm.apply (s :: t') t = SubTm.apply (single t') (SubTm.apply (extend s) t)
  applySingle s t' t =
    rewrite subComp (single t') (extend s) t in
    rewrite compWeaken (id _) t' s in
    rewrite compIdLeft s in
    Refl
  
  ||| Extracts a safe value from a safe substitution.
  lookup : {s : Subst Tm _ n} -> (sg : G k s g) -> (i : Fin n) -> (Value (applyVar s i), V k (applyVar s i) (index g i))
  lookup Nil i = absurd i
  lookup (_ :: vx) FZ = vx
  lookup (sg' :: _) (FS y) = lookup sg' y
  
  ||| Horrible part of the fundamental lemma we need to explicitly
  ||| extract into its own function because `case` expressions don't
  ||| do full dependent pattern matching.
  lamE : {sub : Subst Tm Z n} ->
         (ih : Value t1 -> E l (apply (sub :: t1) t) b) ->
         (m : Nat) -> (smaller : LT m l) -> LT m k ->
         Value s1 -> Value t1 ->
         -- V m t1 a -> G m sub g ->
         Steps m (App (Lam (SubTm.apply (extend sub) t)) t1) s1 ->
         LogRel.V ((-) {smaller=lteSuccLeft smaller} l m) s1 b
  lamE _  Z     _    _    s1value _       Refl            = absurd s1value
  lamE _  (S _) _    _    _       _       (App1 x :: _)   = absurd x
  lamE _  (S _) _    _    _       t1value (App2 _ z :: _) = void $ valuesDontStep t1value z
  lamE ih (S n) mLTl mLTk s1value t1value (Beta x :: y) {sub} {t1} {t} {s1} =
    let MkE f = ih x in
    let prf = sym $ applySingle sub t1 t in
    let y' = replace {P = \u => Steps n u s1} prf y in
    let v = f n (lteSuccLeft mLTl) s1value y' in
    let p1 = lteSuccLeft mLTl in
    let p2 = lteSuccLeft p1 in
    let p = minusLteRight (lteSuccRight (lteRefl {n})) p1 p2 in
    downwardsClosed _ v p
  
  ||| Horrible part of the fundamental lemma's case for applications.
  ||| Because of the dependent pattern matchings that result from the calls to the application reduction sequence lemmas,
  ||| this needs to be a separate function.
  appE : E k fn (a ~> b) -> E k arg a -> (j : _) -> (l : LT j k) -> Value s -> Steps j (App fn arg) s ->
         V ((-) {smaller = lteSuccLeft l} k j) s b
  appE {k} e e' j l val steps with (appRed1 steps val)
    appE {k} e e' (j1 + j2) l val steps | (MkAppRed1 (red1, v1) st1) with (appRed2 st1 v1 val)
      appE {k} e e' (j1 + (j21 + j22)) l val steps | (MkAppRed1 (red1, v1) st1) | (MkAppRed2 (red2, v2) st2) =
        let MkE fs = e in
        let MkE xs = e' in
        let l' = weakenLtPlusRight l in
        let l'' = weakenLtPlusRight (weakenLtPlus l) in
        let x = xs _ l'' v2 red2 in
        let l3 = minusLteLeft (lteMinus k j1) j21 in
        let x' = downwardsClosed _ x l3 in
        let MkE ef = fs _ l' v1 red1 _ (lteMinus (minus k j1) j21) _ v2 x' in
        let l4 = ltLeftPlusToMinus (ltLeftPlusToMinus l) in
        rewrite sym $ mmmmpp k j1 j21 j22 in
        ef j22 l4 val st2
  
  ||| Part of the fundamental lemma, for recursive types.
  ||| Needs to be its own function due to dependent pattern matching on the reduction sequence.
  foldE : Value (Fold v') -> Value w -> V (minus k j) v' (apply (single (Mu a)) a) ->
          LT i (minus k j) -> Steps i' (Unfold (Fold v')) w -> V (minus i i') w (apply (single (Mu a)) a)
  foldE val val'   _  _ ((Unfold1 step) :: _) = absurd $ valuesDontStep val step
  foldE val val'   _  _ Refl                  = absurd val'
  foldE val val'   vv l ((Eta v'val) :: steps') with (valueStepsRefl v'val steps')
    foldE val val' vv l ((Eta w) :: steps') | (Refl, Refl) =
      downwardsClosed _ vv (weakenLteMinusLeft l 2)
  
  fundamental : g |- (t, a) -> g |= (t, a)
  fundamental (Lam t') {t=Lam t} =
    let Sem ih = fundamental t' in 
    Sem $ \k, s, sg =>
      MkE $ \j, jLTk, _, steps =>
        case valueStepsRefl Lam steps of
           (Refl, jIsZero) => \l, lLTkj, t1, t1Value, v =>
             -- since j is zero, really lLTkj : LT l k
             -- some fiddling is required to actually get this tho
             -- and its simpler to conclude LT l k by use of the lteMinus lemma
             let p = lteTransitive lLTkj (lteMinus k j) in
             let sg' = \val => downwardsClosed sg p :: (val, v) in
             let ih' = \val => ih l _ (sg' val) in
  
             MkE $ \m, mLTl, resultIsValue, steps' =>
               let mLTk = lteTransitive mLTl (lteTransitive lLTkj (lteMinus k j)) in
               -- pass the relevant parts to lamE which splits on the Steps
               -- and eliminates the impossible cases
               lamE ih' m mLTl mLTk resultIsValue t1Value steps'
  
  fundamental T = Sem $ \k, s, sg => MkE $ \j, l, val, steps => ()
  fundamental (App s' t') =
    let Sem ihS = fundamental s' in
    let Sem ihT = fundamental t' in
    Sem $ \k, s, sg => MkE $ \j, l, val, steps =>
      appE (ihS k s sg) (ihT k s sg) j l val steps

  fundamental {g} (Var i) = Sem $ \k, s, sg => 
    MkE $ \j, l, val, steps =>
      let (val, vx) = lookup sg i in
      case valueStepsRefl val steps of
        (Refl, jIsZero) => downwardsClosed _ vx (lteMinus k j)

  fundamental (Fold s) =
    let Sem ih = fundamental s in
    Sem $ \k, s, sg =>
      let MkE f = ih k s sg in
      MkE $ \j, l, val, steps =>
        case foldRedVal steps of
          (v' ** Refl) =>
            let Fold val' = val in
            let steps' = foldRedInv steps in
            let vv = f j l val' steps' in
            \i, iLTkj =>
            MkE $ \i', i'LTi, val'', steps2 =>
            foldE val val'' vv iLTkj steps2

