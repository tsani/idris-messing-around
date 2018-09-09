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

  ||| A context with `n` entries in it.
  data Ctx : (n : Nat) -> Type where
    Nil : Ctx Z
    ||| Adds an entry to the context.
    ||| This entry can refer only to previous entries in the context, which is why their indices match.
    (::) : Tm n -> Ctx n -> Ctx (S n)
  
  %name Ctx g, g', g'', ctx, ctx', ctx''
  
  -- extend : Ctx b n -> Ctx (n + b) m -> Ctx b (m + n)
  -- extend g1 Nil = g1
  -- extend g1 {m=S m} {b} {n} (t :: g2) =
  --   let ih = extend g1 g2 in
  --   let t'' = replace (plusAssociative m n b) {P = \p => Tm p} t in
  --   t'' :: ih
  
  ||| For when a term is placed under an additional binder.
  weaken : Tm n -> Tm (S n)
  weaken Unit = Unit
  weaken Top = Top
  weaken (App t s) = App (weaken t) (weaken s)
  weaken (Lam t) = Lam (weaken t)
  weaken (Var i) = Var (weaken i)
  weaken (Pi t b) = Pi (weaken t) (weaken b)
  weaken (Tp i) = Tp i
  
  namespace Subst
    data Subst : (m : Nat) -> (size : Nat) -> Type where
      Shift : (n : Nat) -> Subst n Z
      Cons : Subst n k -> Tm (S k + n) -> Subst n (S k)
  
    %name Subst s, s', s''
  
    ||| Shift a variable index up by n places.
    shiftVar : (n : Nat) -> Fin k -> Fin (n + k)
    shiftVar Z f = f
    shiftVar (S n) f = FS (shiftVar n f)
  
    applyVar : Subst n k -> Fin k -> Tm (k + n)
    applyVar (Shift m) f =
      rewrite sym (plusZeroRightNeutral m) in Var (shiftVar m f)
    applyVar (Cons s t) FZ {n} {k=S k} = t
    applyVar (Cons s t) (FS y) {n} {k=S k} = weaken (applyVar s y)
  
    apply : Subst n k -> Tm k -> Tm (k + n)
    apply s (Var f) = applyVar s f
    apply s (Lam t) = Lam (apply (Cons s (Var FZ)) t)
    apply s (Pi t body) = Pi (apply s t) (apply (Cons s (Var FZ)) body)
    apply s Unit = Unit
    apply s Top = Top
    apply s (App t t') = App (apply s t) (apply s t')
    apply s (Tp i) = Tp i
  
    ||| (y z) (x y)
    exTerm1 : Tm 3
    exTerm1 = App (App (Var 1) (Var 2)) (App (Var 0) (Var 1))
  
    ||| Constructs the identity substitution for `n` free variables.
    idSub : (n : Nat) -> Subst Z n
    idSub Z = Shift Z
    idSub (S n) = Cons (idSub n) (Var FZ)

    -- shift : (cutoff : Nat) -> (d : Nat) -> Tm n -> Tm (d + n)
    -- shift c d (Var x) = ?a_3
    -- shift c d Unit = ?a_1
    -- shift c d Top = ?a_2
    -- shift c d (App t s) = ?a_4
    -- shift c d (Lam t) = ?a_5
    -- shift c d (Pi t body) = ?a_6
    -- shift c d (Tp i) = ?a_7
  
    -- ||| A substitution of a single term.
    -- ||| @param n The size of the context in which the term is embedded.
    -- data Subst : (n : Nat) -> Type where
    --   MkSubst : -> Subst (S n)
  
    -- applyId : Subst Z -> Tm n -> Tm n
    -- applyId s Unit = Unit
    -- applyId s Top = Top
    -- applyId s (App t t') = App (applyId s t) (applyId s t')
    -- applyId s (Lam t) = let s' = Cons (Var FZ) s in ?a
    -- applyId s (Var x) = ?a_3
    -- applyId s (Pi t body) = ?a_6
    -- applyId s (Tp i) = ?a_7
  
--     ||| The identity substitution for a context.
--     subId : (g : Ctx b n) -> Subst g g
--     subId Nil = Nil
--     subId (t :: g) {b} = Cons (subId g) (t :: Nil) (Var FZ)
--   
--     applySub : {g : Ctx Z n} -> {d : Ctx Z m} -> Subst g d -> Tm n -> Tm m
--     applySub s Unit = Unit
--     applySub s Top = Top
--     applySub s (Var x) = ?a_3
--     applySub s (App t1 t2) = App (applySub s t1) (applySub s t2)
--     applySub s (Lam t) =
--       let s' = Cons (:: Nil) s in
--       ?a  -- Lam (applySub (Cons (Var FZ) s) t)
--     applySub s (Pi t body) = ?a_6
--     applySub s (Tp i) = (Tp i)
--   
--     -- subTrans : {g1 : Ctx b n1} -> {g2 : Ctx b n2} -> {g3 : Ctx b n3} ->
--     --            Subst g1 g2 -> Subst g2 g3 -> Subst g1 g3
--     -- subTrans s [] = s
--     -- subTrans s (Cons {d} s' d' tm) = ?a_2
--   
--   ||| Weaken by multiple steps.
--   weakenTo : Tm k -> Diff k n -> Tm n
--   weakenTo t DZ = t
--   weakenTo t (DS d) = weakenTo (weaken t) d
--   
--   ||| Represents looking up index `i` in context `ctx` with `n` entries to get term `t`
--   ||| referring to `k` earlier variables, where the difference between `k` and `n` is `d`.
--   data Lookup : (i : Fin (n + b)) -> (ctx : Ctx b n) -> (d : Diff (k + b) (n + b)) -> (t : Tm (k + b)) -> Type where
--     Here : Lookup FZ (t :: ctx') diffSucc t
--     There : Lookup f ctx d t -> Lookup (FS f) (s :: ctx) (diffSuccRight d) t
--   
--   -- ||| Looks up a type in the context.
--   -- lookup : (i : Fin (b + n)) -> (ctx : Ctx b n) -> (k : Nat ** t : Tm k ** d : Diff k n ** Lookup i ctx d t)
--   -- lookup FZ (t :: _) = (_ ** t ** diffSucc ** Here)
--   -- lookup (FS f) (_ :: ctx) =
--   --   let (_ ** t' ** d ** l) = lookup f ctx
--   --   in (_ ** t' ** diffSuccRight d ** There l)
--   
-- namespace Typing
--   -- subCtx : Ctx (S n) -> Diff k n -> Tm k -> Ctx n
--   -- subCtx (s :: ctx) DZ t = t
--   -- subCtx (s :: ctx) (DS x) t = ?a_2
-- 
--   ||| Typing assignment.
--   data Oft : Ctx b n -> Tm (n + b) -> Tm (n + b) -> Type where
--     ||| The type universes are contained one in the other.
--     Tp : Oft ctx (Tp n) (Tp (S n))
--     ||| The unit term has the unit type.
--     Unit : Oft ctx Unit Top
--     ||| The unit type is a basic type.
--     Top : Oft ctx Top (Tp 0)
--     ||| Variables get their types from looking up in the context.
--     Var : Lookup f ctx d tp -> Oft ctx (Var f) tp
--     Pi : Oft ctx a (Tp l1) -> Oft (tp :: ctx) b (Tp l2) -> Oft ctx (Pi a b) (Tp (maximum l1 l2))
--     -- ||| Applications get their types by performing substitutions.
--     -- App : Oft ctx t1 (Pi a b) -> Oft ctx t2 a -> Oft ctx (App t1 t2) -> 
--     --       Subst 
--  
