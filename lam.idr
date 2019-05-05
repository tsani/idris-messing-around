module Lam
  
import Data.Fin
  
%default total
  
-- namespace Misc
--   lteSucc : LTE n (S n)
--   lteSucc = lteSuccRight lteRefl
--   
--   ||| Like `LTE`, but without a fixed starting point. Instead of "counting up", Diff "counts down".
--   ||| Encodes that `k` is less than `n` by a certain amount (measured by `DS` constructors).
--   data Diff : (k : Nat) -> (n : Nat) -> Type where
--     DZ : Diff n n
--     DS : Diff (S k) n -> Diff k n
--   
--   %name Diff d, d', d'', df, df', df''
--   
--   ||| Every nat is smaller than its successor (by one).
--   diffSucc : Diff k (S k)
--   diffSucc = DS DZ
--   
--   diffSuccLeft : Diff (S k) n -> Diff k n
--   diffSuccLeft d = DS d
--   
--   ||| Like `lteSuccRight`.
--   diffSuccRight : Diff k n -> Diff k (S n)
--   diffSuccRight DZ = diffSucc
--   diffSuccRight (DS d) = DS (diffSuccRight d)
--   
--   ||| 'Based' LTE.
--   data BLTE : Nat -> Nat -> Type where
--     LTEBase : BLTE n n
--     LTESucc : BLTE m n -> BLTE m (S n)
--   
--   %name BLTE b, b', b'', p, p', p''
  
namespace Syntax
  ||| A term occurring under `n` binders.
  ||| Syntax judgment.
  data Tm : (n : Nat) -> Type where
    Unit : Tm n
    Top : Tm m
    Var : Fin n -> Tm n
    App : Tm n -> Tm n -> Tm n
    Lam : Tm (S n) -> Tm n
    ||| The dependent function space. The type `t` is the domain, and
    ||| may refer to any variables already in context.
    ||| The body exists in an extended context and may refer to the new variable.
    Pi : (t : Tm n) -> (body : Tm (S n)) -> Tm n
    ||| The type universe at level `i`.
    Tp : (i : Nat) -> Tm n
  
  %name Tm t, s, t', s', t'', s''

namespace Renaming
  data Renaming : (m : Nat) -> (size : Nat) -> Type where
    Shift : (n : Nat) -> Renaming n Z
    Cons : Renaming n k -> Fin n -> Renaming n (S k)
  
  %name Renaming r, r', r''
  
  weaken : Renaming n k -> Renaming (S n) k
  weaken (Shift n) = Shift (S n)
  weaken (Cons r x) = Cons (weaken r) (FS x)

  applyVar : Renaming n k -> Fin k -> Fin n
  applyVar (Shift _) FZ impossible
  applyVar (Shift _) (FS _) impossible
  applyVar (Cons r y) FZ = y
  applyVar (Cons r y) (FS z) = applyVar r z 
  
  ||| Extends a renaming so it works in an extended context.
  extend : Renaming n k -> Renaming (S n) (S k)
  extend r = Cons (weaken r) FZ
  
  apply : Renaming n k -> Tm k -> Tm n
  apply r (Var x) = Var (applyVar r x)
  apply r (Lam t) = Lam (apply (extend r) t)
  apply r (Pi t body) = Pi (apply r t) (apply (extend r) body)
  apply r Unit = Unit
  apply r Top = Top
  apply r (App t s) = App (apply r t) (apply r s)
  apply r (Tp i) = Tp i
  
  ||| Forms the identity renaming for `k` variables.
  idRen : (k : Nat) -> Renaming k k
  idRen Z = Shift Z
  idRen (S k) = extend (idRen k)
  
namespace Subst
  ||| A simultaneous substitution for `k` variables, using `n` variables.
  ||| In other words, a transformation of k-contexts into n-contexts.
  data Subst : (n : Nat) -> (k : Nat) -> Type where
    Shift : (n : Nat) -> Subst n Z
    Cons : Subst n k -> Tm n -> Subst n (S k)
  
  %name Subst s, s', s'', r, r', r''
  
  namespace WeakenTerm
    ||| For when a term is placed under an additional binder.
    weaken : Tm n -> Tm (S n)
    weaken t = apply (weaken (idRen _)) t
    -- we can just form the identity renaming, which renames each variable to itself,
    -- and then weaken this renaming so that it renames each variable to itself + 1.
  
  namespace WeakenSubst
    ||| Weakening a substitution allows it to be used in an extended context.
    weaken : Subst n k -> Subst (S n) k
    weaken (Shift n) = Shift (S n)
    weaken (Cons s t) = Cons (weaken s) (weaken t)
  
  extendWith : Subst n k -> Tm (S n) -> Subst (S n) (S k)
  extendWith s t = Cons (weaken s) t

  ||| Extends a substitution to move it under a lambda.
  extend : Subst n k -> Subst (S n) (S k)
  extend s = s `extendWith` (Var FZ)
  
  ||| Helper for `apply` to look up a term inside the subtitution.
  applyVar : Subst n k -> Fin k -> Tm n
  applyVar (Shift _) f = FinZElim f
  applyVar (Cons s t) FZ = t
  applyVar (Cons s t) (FS x) = applyVar s x

  ||| Apply a substitution to a term.
  apply : Subst n k -> Tm k -> Tm n
  apply s (Var f) = applyVar s f
  apply s (Lam t) = Lam (apply (extend s) t)
  apply s (Pi t body) = Pi (apply s t) (apply (extend s) body)
  apply s Unit = Unit
  apply s Top = Top
  apply s (App t t') = App (apply s t) (apply s t')
  apply s (Tp i) = Tp i
  
  ||| (y z) (x y)
  exTerm1 : Tm 3
  exTerm1 = App (App (Var 1) (Var 2)) (App (Var 0) (Var 1))

  ||| Constructs the identity substitution for `n` free variables.
  idSub : (k : Nat) -> Subst k k
  idSub Z = Shift Z
  idSub (S k) = extend (idSub k)

  exTerm2 : Tm 2
  exTerm2 = App (Lam exTerm1) Unit
  
namespace SubApply
  ||| Apply a substitution to a substitution.
  ||| Notice that this is transitivity, since the `k` index is squeezed out.
  apply : (s : Subst n k) -> (r : Subst k l) -> Subst n l
  apply _ (Shift _) = Shift _
  apply s (Cons r' t) = Cons (apply s r') (apply s t)
  
namespace SubApplyRen
  apply : (s : Subst n k) -> (r : Renaming k l) -> Subst n l
  apply s (Shift k) = Shift _
  apply s (Cons r x) = Cons (apply s r) (applyVar s x)
  
  swapRenamingVar : (s : Subst k n) -> (x : Fin n) ->
                    apply (weaken (idRen k)) (applyVar s x)
                    =
                    applyVar (extend s) (applyVar (weaken (idRen n)) x)
  swapRenamingVar (Shift k) x = FinZElim x
  swapRenamingVar (Cons s t) FZ = Refl
  swapRenamingVar (Cons s t) (FS x) {n = S n} =
    rewrite swapRenamingVar s x in ?a

  swapRenaming : (s : Subst k n) -> (t : Tm n) ->
                 apply (weaken (idRen k)) (apply s t) = apply (extend s) (weaken t)
  swapRenaming s Unit = Refl
  swapRenaming s Top = Refl
  swapRenaming s (Var x) = swapRenamingVar s x
  swapRenaming s (App t t') = ?a_4
  swapRenaming s (Lam t) = ?a_5
  swapRenaming s (Pi t body) = ?a_8
  swapRenaming s (Tp i) = Refl
  
  distributeWeaken : (s : Subst k n) -> (r : Subst n l) ->
                     weaken (apply s r) = apply (extend s) (weaken r)
  distributeWeaken s (Shift n) = Refl
  distributeWeaken s (Cons r' t) =
    rewrite distributeWeaken s r' in
    rewrite swapRenaming s t in
    Refl
  
  distributeExtend : (s : Subst k n) -> (r : Subst n l) ->
                     extend (apply s r) = apply (extend s) (extend r)
  distributeExtend s (Shift n) = Refl
  distributeExtend s (Cons r' t) =
    rewrite distributeWeaken s r' in
    rewrite swapRenaming s t in
    Refl

  liftExtendVar : (s : Subst k n) -> (r : Subst n l) -> (f : Fin (S l)) ->
                 apply (extend s) (applyVar (extend r) f) = applyVar (apply (extend s) (extend r)) f
  liftExtendVar _ (Shift _) FZ = Refl
  liftExtendVar _ (Shift _) (FS x) = FinZElim x
  liftExtendVar s (Cons r' t) FZ = Refl
  liftExtendVar s (Cons r' t) (FS x) =
    let ih = liftExtendVar s r' x in ?a
  
  liftExtend : (t : Tm (S l)) -> (s : Subst k n) -> (r : Subst n l) ->
               apply (extend s) (apply (extend r) t) = apply (apply (extend s) (extend r)) t
  liftExtend Unit s r = Refl
  liftExtend Top s r = Refl
  liftExtend (App t t') s r =
    rewrite liftExtend t s r in
    rewrite liftExtend t' s r in
    Refl
  liftExtend (Var x) s r = liftExtendVar s r x
  liftExtend (Lam t) s r = ?a_10
  liftExtend (Pi t body) s r = ?a_13
  liftExtend (Tp i) s r = ?a_14
  
  liftApplyVar : (s : Subst k n) -> (r : Subst n l) -> (f : Fin l) ->
                 apply s (applyVar r f) = applyVar (apply s r) f
  liftApplyVar _ (Shift _) f = FinZElim f
  liftApplyVar s (Cons s' t) FZ = Refl
  liftApplyVar s (Cons s' t) (FS x) = ?a --  liftApplyVar s s' x
  
  liftApply : (t : Tm l) ->
              (s : Subst k n) ->
              (r : Subst n l) ->
              apply s (apply r t) = apply (apply s r) t
  liftApply Unit s r = Refl
  liftApply Top s r = Refl
  liftApply (Var x) s r = liftApplyVar s r x
  liftApply (App t t') s r =
    rewrite liftApply t s r in
    rewrite liftApply t' s r in
    Refl
  liftApply (Lam t) s r =
    let ih = liftApply t (extend s) (extend r) in
    rewrite distributeExtend s r in cong ih
  liftApply (Pi t body) s r =
    rewrite liftApply t s r in
    rewrite liftApply body (extend s) (extend r) in
    rewrite distributeExtend s r in
    Refl
  liftApply (Tp i) s r = Refl
  
  liftApplyRenVar : (s : Subst k n) -> (r : Renaming n l) -> (f : Fin l) ->
                    applyVar s (applyVar r f) = applyVar (apply s r) f
  liftApplyRenVar s (Shift n) f = FinZElim f
  liftApplyRenVar s (Cons r x) FZ = Refl
  liftApplyRenVar s (Cons r x) (FS y) = liftApplyRenVar s r y
  
  liftApplyRen : (t : Tm l) -> (s : Subst k n) -> (r : Renaming n l) ->
                 apply s (apply r t) = apply (apply s r) t
  liftApplyRen (Var x) s r = liftApplyRenVar s r x
  liftApplyRen Unit s r = Refl
  liftApplyRen Top s r = Refl
  liftApplyRen (App t t') s r = ?a_9
  liftApplyRen (Lam t) s r = ?a_15
  liftApplyRen (Pi t body) s r = ?a_16
  liftApplyRen (Tp i) s r = ?a_17
  
  renameWeaken : (s : Subst n k) -> (t : Tm n) -> (r : Renaming k l) -> apply (Cons s t) (weaken r) = apply s r
  renameWeaken s t (Shift k) = Refl
  renameWeaken s t (Cons r x) =
    rewrite renameWeaken s t r in
    Refl
  
  applyIdRenRight : (s : Subst n k) -> apply s (idRen k) = s
  applyIdRenRight (Shift n) = Refl
  applyIdRenRight (Cons s t) {k = S k} =
    rewrite renameWeaken s t (idRen k) in
    rewrite applyIdRenRight s in
    Refl
  
  applyWeaken : (s : Subst n k) -> (t : Tm n) -> (r : Subst k l) -> apply (Cons s t) (weaken r) = apply s r
  applyWeaken s t (Shift k) = Refl
  applyWeaken s t (Cons r' t') {k} =
    rewrite liftApplyRen t' (Cons s t) (weaken (idRen k)) in
    rewrite renameWeaken s t (idRen k) in
    rewrite applyIdRenRight s in
    rewrite applyWeaken s t r' in
    Refl
  
  applyIdRight : (s : Subst n k) -> apply s (idSub k) = s
  applyIdRight (Shift n) {k = Z} = Refl
  applyIdRight (Cons s t) {k = S k} =
    rewrite applyWeaken s t (idSub k) in
    rewrite applyIdRight s in
    Refl
  
namespace Eval
  data IsValue : Tm n -> Type where
    Unit : IsValue Unit
    Top : IsValue Top
    Lam : IsValue (Lam t)
    Pi : IsValue s -> IsValue (Pi s t)
    Tp : IsValue (Tp i)
  
  %name IsValue v, v', v''
  
  ||| Forms a substitution to be used for beta reduction, which leaves
  ||| all variables unchanged except for the first, which is
  ||| substituted by the given term.
  single : Tm n -> Subst n (S n)
  single t = Cons (idSub _) t
  
  ||| Perform a beta reduction, substituting `t2` for the head variable of `t1`.
  beta : (t1 : Tm (S n)) -> (t2 : Tm n) -> Tm n
  beta t1 t2 = apply (single t2) t1
  
  ||| Evaluation relation on terms.
  data Eval : Tm n -> Tm n -> Type where
    EvAppLam : Eval (App (Lam body) t) (beta body t)
    EvAppL : Eval t t' -> Eval (App t s) (App t' s)
    EvAppR : Eval s s' -> Eval (App t s) (App t s')
    EvLam : Eval body body' -> Eval (Lam body) (Lam body')
  
  %name Eval e, e', e''
  
namespace SplitApply
  -- splitApplyVar : (x : Fin (S k)) -> (s : Subst n k) -> (t : Tm n) ->
  --                 applyVar (Cons s t) x
  --                 =
  --                 apply (single t) (applyVar (extend s) x)
  -- splitApplyVar FZ s t = Refl
  -- splitApplyVar (FS x) (Shift n) t = FinZElim x
  -- splitApplyVar (FS x) (Cons s t') t = 
  --   let ih = splitApplyVar x s t in ?splitApplyVar_rhs_3

  applySingleWeakenTm : (t : Tm n) -> (t' : Tm n) ->
                        apply (Cons (idSub n) t) (apply (weaken (idRen n)) t') = t'
  applySingleWeakenTm t t' =
    ?applySingleWeakenTm_rhs
  
  applySingleWeaken : (s : Subst n k) -> (t : Tm n) -> apply (single t) (weaken s) = s
  applySingleWeaken (Shift n) t = Refl
  applySingleWeaken (Cons s t') t =
    rewrite applySingleWeaken s t in
    rewrite applySingleWeakenTm t t' in
    Refl
  
  splitApply : (s : Subst n k) -> (t : Tm n) -> Cons s t = apply (single t) (extend s)
  splitApply (Shift n) t = Refl
  splitApply (Cons s t') t = ?splitApply_rhs_2

  -- splitApply : (s : Subst n k) -> (t : Tm n) -> (b : Tm (S k)) ->
  --              apply (Cons s t) b = apply (single t) (apply (extend s) b)
  -- splitApply s t b =
  --   rewrite liftApply b (single t) (extend s) in ?splitApply_rhs
  
namespace Typing
  data Ctx : Nat -> Type where
    Nil : Ctx Z
    (::) : Ctx n -> Tm n -> Ctx (S n)
  
  %name Ctx g, g', g'', ctx, ctx', ctx''
  
  ||| Lookup relation.
  ||| Looking up `f` in `g` gives `t`.
  data Lookup : (g : Ctx n) -> (f : Fin n) -> (t : Tm n) -> Type where
    Here : Lookup (xs :: x) FZ (weaken x)
    There : Lookup xs f t -> Lookup (xs :: s) (FS f) (weaken t)
  
  %name Lookup lk, lk', lk''

  ||| Typing relation on terms.
  ||| In context `g`, term `s` has type `t`.
  data Oft : (g : Ctx n) -> (s : Tm n) -> (t : Tm n) -> Type where
    Unit : Oft g Unit Top
    Top : Oft g Top (Tp 0)
    Pi : Oft g s (Tp i) -> Oft (g :: s) t (Tp j) -> Oft g (Pi s t) (Tp (maximum i j))
    Lam : Oft g s (Tp i) -> Oft (g :: s) body t -> Oft g (Lam body) (Pi s t)
    Tp : Oft g (Tp i) (Tp (S i))
    App : Oft g s (Pi a b) -> Oft g t a -> Oft g (App s t) (apply (Cons (idSub _) t) b)
    Var : Lookup g f t -> Oft g (Var f) t
  
  %name Oft d, d', d''
  
namespace SubstTyping
  ||| A well-typed substitution is a transformation of contexts.
  data SubstOft : Ctx n -> Ctx k -> Subst n k -> Type where
    Nil : SubstOft g Nil (Shift _)
    Cons : SubstOft g d s -> Oft g t a -> SubstOft g (d :: a) (Cons s t)
  
  %name SubstOft sd, sd', sd''
  
namespace SubstLemma
  ||| Substitution lemma.
  ||| Application of a well-typed substitution preserves typing.
  subst : SubstOft g d s -> Oft d t a -> Oft g (apply s t) (apply s a)
  subst sd Unit = Unit
  subst sd Top = Top
  subst sd Tp = Tp
  subst sd (Pi d d') = ?a_6
  subst sd (Lam d d') = ?a_7
  subst sd (Var lk) = ?subst_8
  subst sd {s} (App d d' {t} {b}) =
    let ih1 = subst sd d in
    let ih2 = subst sd d' in
    -- rewrite liftApply b s (single t) in
    -- rewrite applyIdRight s in
    let ideal = App ih1 ih2 in
    ?subst_9
  
  {-
namespace TypePreservation
  pres : Eval t t' -> Oft g t a -> Oft g t' a
  pres EvAppLam (App (Lam t b) d) = ?a
  pres (EvAppL x) d = ?a_2
  pres (EvAppR x) d = ?a_3
  pres (EvLam x) d = ?a_4
  -}
