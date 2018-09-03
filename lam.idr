module Lam
  
import Data.Fin
  
%default total
  
namespace Misc
  lteSucc : LTE n (S n)
  lteSucc = lteSuccRight lteRefl
  
  ||| Like `LTE`, but without a fixed starting point. Instead of "counting up", Diff "counts down".
  ||| Encodes that `k` is less than `n` by a certain amount (measured by `DS` constructors).
  data Diff : (k : Nat) -> (n : Nat) -> Type where
    DZ : Diff n n
    DS : Diff (S k) n -> Diff k n
  
  %name Diff d, d', d'', df, df', df''
  
  ||| Every nat is smaller than its successor (by one).
  diffSucc : Diff k (S k)
  diffSucc = DS DZ
  
  diffSuccLeft : Diff (S k) n -> Diff k n
  diffSuccLeft d = DS d
  
  ||| Like `lteSuccRight`.
  diffSuccRight : Diff k n -> Diff k (S n)
  diffSuccRight DZ = diffSucc
  diffSuccRight (DS d) = DS (diffSuccRight d)
  
  ||| 'Based' LTE.
  data BLTE : Nat -> Nat -> Type where
    LTEBase : BLTE n n
    LTESucc : BLTE m n -> BLTE m (S n)
  
  %name BLTE b, b', b'', p, p', p''
  
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

  ||| A context with `n` entries in it, whose entries can access `b`
  ||| outer variables.
  data Ctx : (b : Nat) -> (n : Nat) -> Type where
    Nil : {b : Nat} -> Ctx b Z
    ||| Adds an entry to the context.
    ||| This entry can refer only to previous entries in the context, which is why their indices match.
    (::) : Tm (n + b) -> Ctx b n -> Ctx b (S n)
  
  -- Our contexts are equipped with a "base". What this number refers
  -- to is the number of variables not actually present inside the
  -- context. This way, we have a way of representing free variables
  -- which still keeping a de Bruijn representation.
  
  %name Ctx g, g', g'', ctx, ctx', ctx''
  
  extend : Ctx b n -> Ctx (n + b) m -> Ctx b (m + n)
  extend {m = Z} g1 g2 = g1
  extend {m = S m} g1 {b} {n} (t :: g2) =
    let ih = extend g1 g2 in
    let t'' = replace (plusAssociative m n b) {P = \p => Tm p} t in
    t'' :: ih
  
  namespace Subst
    ||| A substitution is a transformation of contexts.
    data Subst : (g : Ctx b n) -> (d : Ctx b m) -> Type where
      Nil : {b : Nat} -> Subst (Nil {b}) (Nil {b})
      Cons : {g : Ctx b n} ->
             {d : Ctx b m} ->
             {tp : Tm (n + b)} ->
             (s : Subst g d) ->
             (d' : Ctx (m + b) k) -> -- d' introduces k new variables for the term to sub
             (tm : Tm (k + (m + b))) -> -- the term to sub
             Subst (tp :: g) (extend d d')
  
    -- Our substitutions are always *complete*, meaning they give a
    -- term to substitute for *every* variable in the context.
    -- Of course, you can just substitute variables for variables to
    -- get the effect of "incomplete" substitution.
  
    ||| The identity substitution for a context.
    subId : (g : Ctx b n) -> Subst g g
    subId Nil = Nil
    subId (t :: g) {b} = Cons (subId g) (t :: Nil) (Var FZ)
  
    applySub : {g : Ctx b n} -> {d : Ctx b m} -> Subst g d -> Tm (n + b) -> Tm (m + b)
    applySub s Unit = Unit
    applySub s Top = Top
    applySub s (Var x) = ?a_3
    applySub s (App t t') = ?a_4
    applySub s (Lam t) = ?a_5
    applySub s (Pi t body) = ?a_6
    applySub s (Tp i) = ?a_7
  
    -- subTrans : {g1 : Ctx b n1} -> {g2 : Ctx b n2} -> {g3 : Ctx b n3} ->
    --            Subst g1 g2 -> Subst g2 g3 -> Subst g1 g3
    -- subTrans s [] = s
    -- subTrans s (Cons {d} s' d' tm) = ?a_2
  
  ||| For when a term is placed under an additional binder.
  weaken : Tm n -> Tm (S n)
  weaken Unit = Unit
  weaken Top = Top
  weaken (App t s) = App (weaken t) (weaken s)
  weaken (Lam t) = Lam (weaken t)
  weaken (Var i) = Var (weaken i)
  weaken (Pi t b) = Pi (weaken t) (weaken b)
  weaken (Tp i) = Tp i
  
  ||| Weaken by multiple steps.
  weakenTo : Tm k -> Diff k n -> Tm n
  weakenTo t DZ = t
  weakenTo t (DS d) = weakenTo (weaken t) d
  
  ||| Represents looking up index `i` in context `ctx` with `n` entries to get term `t`
  ||| referring to `k` earlier variables, where the difference between `k` and `n` is `d`.
  data Lookup : (i : Fin (n + b)) -> (ctx : Ctx b n) -> (d : Diff (k + b) (n + b)) -> (t : Tm (k + b)) -> Type where
    Here : Lookup FZ (t :: ctx') diffSucc t
    There : Lookup f ctx d t -> Lookup (FS f) (s :: ctx) (diffSuccRight d) t
  
  -- ||| Looks up a type in the context.
  -- lookup : (i : Fin (b + n)) -> (ctx : Ctx b n) -> (k : Nat ** t : Tm k ** d : Diff k n ** Lookup i ctx d t)
  -- lookup FZ (t :: _) = (_ ** t ** diffSucc ** Here)
  -- lookup (FS f) (_ :: ctx) =
  --   let (_ ** t' ** d ** l) = lookup f ctx
  --   in (_ ** t' ** diffSuccRight d ** There l)
  
namespace Typing
  -- subCtx : Ctx (S n) -> Diff k n -> Tm k -> Ctx n
  -- subCtx (s :: ctx) DZ t = t
  -- subCtx (s :: ctx) (DS x) t = ?a_2

  ||| Typing assignment.
  data Oft : Ctx b n -> Tm (n + b) -> Tm (n + b) -> Type where
    ||| The type universes are contained one in the other.
    Tp : Oft ctx (Tp n) (Tp (S n))
    ||| The unit term has the unit type.
    Unit : Oft ctx Unit Top
    ||| The unit type is a basic type.
    Top : Oft ctx Top (Tp 0)
    ||| Variables get their types from looking up in the context.
    Var : Lookup f ctx d tp -> Oft ctx (Var f) tp
    Pi : Oft ctx a (Tp l1) -> Oft (tp :: ctx) b (Tp l2) -> Oft ctx (Pi a b) (Tp (maximum l1 l2))
    -- ||| Applications get their types by performing substitutions.
    -- App : Oft ctx t1 (Pi a b) -> Oft ctx t2 a -> Oft ctx (App t1 t2) -> 
    --       Subst 
 
