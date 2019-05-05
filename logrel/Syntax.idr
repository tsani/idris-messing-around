module Syntax

import Data.Fin

import Misc

%default total
%access public export
  
namespace Types
  infixr 2 ~>
  data Tp : Nat -> Type where
    (~>) : Tp n -> Tp n -> Tp n
    Top : Tp n
    Mu : Tp (S n) -> Tp n
    Var : Fin n -> Tp n
  %name Tp a, b

namespace Contexts
  ||| Typing context for terms.
  data Ctx : Nat -> Type where
    Nil : Ctx Z
    (::) : Ctx n -> Tp Z -> Ctx (S n)
  %name Ctx g, g', g''
  
  index : Ctx n -> Fin n -> Tp Z
  index (_ :: a) FZ = a
  index (g :: _) (FS i) = index g i

namespace Terms
  data Tm : Nat -> Type where
    Lam : Tm (S n) -> Tm n
    App : Tm n -> Tm n -> Tm n
    T : Tm n
    Var : Fin n -> Tm n
    Fold : Tm n -> Tm n
    Unfold : Tm n -> Tm n
  %name Tm t, t', s, s'

namespace Renaming
  data Renaming : (dst : Nat) -> (src : Nat) -> Type where
    Weaken : Renaming n Z
    (::) : Renaming n k -> (f : Fin n) -> Renaming n (S k)
  %name Renaming r, r'

  weaken : Renaming n k -> Renaming (S n) k
  weaken Weaken = Weaken
  weaken (r :: f) = weaken r :: FS f
  
  weakenN : (i : Nat) -> Renaming n k -> Renaming (i + n) k
  weakenN Z r = r
  weakenN (S i) r = weaken (weakenN i r)

  ||| Extends a renaming with x/x
  extend : Renaming n k -> Renaming (S n) (S k)
  extend r = weaken r :: FZ

  ||| The identity renaming for `n` variables.
  id : (n : Nat) -> Renaming n n
  id Z = Weaken
  id (S k) = extend (id k)

  ||| Applies a renaming to a variable.
  applyVar : Renaming n k -> Fin k -> Fin n
  applyVar Weaken i = absurd i
  applyVar (r :: f) FZ = f
  applyVar (r :: f) (FS x) = applyVar r x

  namespace ApplyVarProofs
    ||| Applying a weakened renaming is the same as weakening the
    ||| *result* of applying the original renaming.
    applyVarWeaken : (r : _) -> (i : _) -> applyVar (weaken r) i = FS (applyVar r i)
    applyVarWeaken Weaken i = absurd i
    applyVarWeaken (r :: f) FZ = Refl
    applyVarWeaken (r :: f) (FS x) = applyVarWeaken r x

    ||| Applying an identity renaming does nothing to a variable.
    applyVarIdIsId : (i : _) -> applyVar (id k) i = i
    applyVarIdIsId FZ = Refl
    applyVarIdIsId (FS x) {k=S k} =
      rewrite applyVarWeaken (id k) x in
      cong (applyVarIdIsId x)

  namespace Renaming
    ||| Composition of renamings.
    ||| This effectively applies a renaming to a renaming.
    (.) : Renaming n k -> Renaming k j -> Renaming n j
    (.) r Weaken = Weaken -- this looks wrong to me
    (.) r (r' :: f) = r . r' :: applyVar r f

    namespace RenTp
      apply : Renaming n k -> Tp k -> Tp n
      apply r (a ~> b) = apply r a ~> apply r b
      apply r Top = Top
      apply r (Mu a) = Mu (apply (extend r) a)
      apply r (Var x) = Var (applyVar r x)

    namespace RenTm
      apply : Renaming n k -> Tm k -> Tm n
      apply r (Lam t) = Lam (apply (extend r) t)
      apply r (App t t') = App (apply r t) (apply r t')
      apply r T = T
      apply r (Var x) = Var (applyVar r x)
      apply r (Fold t) = Fold (apply r t)
      apply r (Unfold t) = Unfold (apply r t)

  namespace RenamingProofs
    ||| Weakening distributes over composition of renamings.
    weakenDistributes : (s : Renaming n k) -> (r : Renaming k j) ->
                        weaken (s . r) = extend s . weaken r
    weakenDistributes s Weaken = Refl
    weakenDistributes s (r :: f) =
      rewrite applyVarWeaken s f in
      cong {f=(:: FS (applyVar s f))} $
      weakenDistributes s r

    ||| Extension distributes over composition of renamings.
    extendDistributes : (s : Renaming n k) -> (r : Renaming k j) -> extend (s . r) = extend s . extend r
    extendDistributes s Weaken = Refl
    extendDistributes s (r :: f) =
      cong {f=(:: FZ)} $
      rewrite applyVarWeaken s f in
      cong {f=(:: FS (applyVar s f))} $
      weakenDistributes s r

    ||| Application of a composition renaming for variables is
    ||| composition of application of renamings.
    renCompVar : (s : _) -> (r : _) -> (i : _) -> applyVar s (applyVar r i) = applyVar (s . r) i
    renCompVar s Weaken i = absurd i
    renCompVar s (r :: f) FZ = Refl
    renCompVar s (r :: f) (FS x) = renCompVar s r x

    ||| Applying a composite renaming is the same as composing the
    ||| application of renamings.
    renComp : (s : Renaming n k) -> (r : Renaming k j) -> (t : Tm j) ->
              apply s (apply r t) = apply (s . r) t
    renComp s r (Lam t) =
      cong {f=Lam} $
      rewrite renComp (extend s) (extend r) t in
      rewrite extendDistributes s r in
      Refl
    renComp s r (App t t') = cong2 (renComp s r t) (renComp s r t')
    renComp s r T = Refl
    renComp s r (Var x) = cong (renCompVar s r x)
    renComp s r (Fold t) = cong (renComp s r t)
    renComp s r (Unfold t) = cong (renComp s r t)

    ||| Applying an identity renaming is a no-op.
    idRenIsId : (t : Tm k) -> apply (id k) t = t
    idRenIsId (Lam t) = cong (idRenIsId t)
    idRenIsId (App t t') =
      rewrite idRenIsId t in
      rewrite idRenIsId t' in
      Refl
    idRenIsId T = Refl
    idRenIsId (Var x) = cong $ applyVarIdIsId x
    idRenIsId (Fold t) = cong $ idRenIsId t
    idRenIsId (Unfold t) = cong $ idRenIsId t

    renCompApplyIdRight : (r : Renaming n k) -> (t : Tm k) ->
                     apply (r . id k) t =  apply r t
    renCompApplyIdRight r t {k} =
      rewrite sym $ renComp r (id k) t in
      rewrite idRenIsId t in
      Refl

interface Var (f : Nat -> Type) where
  var : Fin n -> f n

Var Tm where
  var = Var

Var Tp where
  var = Var

interface Weaken (f : Nat -> Type) where
  weaken : f n -> f (S n)

Weaken Tm where
  weaken t = apply (weaken (id _)) t

Weaken Tp where
  weaken a = apply (weaken (id _)) a
  
namespace WeakenN
  weakenN : (i : Nat) -> Tm n -> Tm (i + n)
  weakenN Z t = t
  weakenN (S i) t = weaken (weakenN i t)
  
namespace WeakenProofs
  ||| Weakening a variable means taking its successor.
  weakenVar : (i : Fin n) -> weaken (Var i) = Terms.Var (FS i)
  weakenVar i {n} =
    rewrite applyVarWeaken (id n) i in 
    rewrite applyVarIdIsId i in
    Refl

  compIdWeakenIsWeaken : (r : Renaming n k) -> (weaken (id n) . r) = weaken r
  compIdWeakenIsWeaken Weaken = Refl
  compIdWeakenIsWeaken (r :: f) {n} =
    rewrite applyVarWeaken (id n) f in
    rewrite applyVarIdIsId f in
    rewrite compIdWeakenIsWeaken r in
    Refl

  ||| Applying a weakened renaming is the same this as applying the
  ||| renaming then weakening the term.
  weakenCommutes : (r : Renaming n k) -> (t : Tm k) ->
                    apply (weaken r) t = weaken (apply r t)
  weakenCommutes r t {n} =
    rewrite renComp (weaken (id n)) r t in
    rewrite compIdWeakenIsWeaken r in
    Refl

  weakenApply : (r : Renaming n k) -> (t : Tm k) ->
                weaken (apply r t) = apply (extend r) (weaken t)
  weakenApply r t {n} {k} =
    rewrite renComp (weaken (id n)) r t in
    rewrite compIdWeakenIsWeaken r in
    rewrite renComp (weaken r :: FZ) (weaken (id k)) t in
    rewrite sym $ weakenDistributes r (id k) in
    rewrite weakenCommutes (r . id k) t in
    rewrite renCompApplyIdRight r t in
    rewrite sym $ weakenCommutes r t in
    Refl

  ||| Applying a weakened renaming is the same as applying the
  ||| extended renaming to the weakened term.
  weakenIsExtendWeaken : (r : Renaming n k) -> (t : Tm k) ->
                         apply (weaken r) t = apply (extend r) (weaken t)
  weakenIsExtendWeaken r t = trans (weakenCommutes r t) (weakenApply r t)

namespace Subst
  data Subst : (f : Nat -> Type) -> (dst : Nat) -> (src : Nat) -> Type where
    Weaken : Subst f n Z
    (::) : Subst f n k -> f n -> Subst f n (S k)
  %name Subst s, s', s'', r, r'

  ||| Lifts a renaming to a substitution of variables.
  lift : Var f => Renaming n k -> Subst f n k
  lift Weaken = Weaken
  lift (r :: x) = lift r :: var x

  ||| Weakens a substitution, so it applies in an extended context.
  ||| This simply weakens every term in the substitution.
  weaken : Weaken f => Subst f n k -> Subst f (S n) k
  weaken Weaken = Weaken
  weaken (s :: t) = weaken s :: weaken t
  
  -- weakenN : Weaken f => (i : Nat) -> Subst f n k -> Subst f (i + n) k
  -- weakenN i Weaken = Weaken
  -- weakenN i (s :: t) = weakenN i s :: weakenN i t
  
  weakenN : Weaken f => (i : Nat) -> Subst f n k -> Subst f (i + n) k
  weakenN Z s = s
  weakenN (S i) s = weaken (weakenN i s)

  ||| Extends a substitution with a x/x.
  extend : (Var f, Weaken f) => Subst f n k -> Subst f (S n) (S k)
  extend s = weaken s :: var FZ
  
  ||| Appends substitutions.
  (++) : Subst f n k1 -> Subst f n k2 -> Subst f n (k2 + k1)
  (++) s1 Weaken = s1
  (++) s1 (s :: x) = (s1 ++ s) :: x
  
  ||| The identity substitution replaces variables with identical
  ||| variables.
  ||| It is equal to a lifted identity renaming.
  id : (Var f, Weaken f) => (n : Nat) -> Subst f n n
  id Z = Weaken
  id (S n) = extend (id n)

  ||| Constructs a substitution that replaces the head variable with
  ||| the given term, and lowers all other variables by one.
  single : (Var f, Weaken f) => f n -> Subst f n (S n)
  single t {n} = id n :: t

  ||| Looks up a variable in a substitution.
  applyVar : Subst f n k -> Fin k -> f n
  applyVar Weaken i = absurd i
  applyVar (_ :: t) FZ = t
  applyVar (s :: _) (FS x) = applyVar s x

  namespace ApplyVarProofs
    ||| Weakening commutes with application of substitution.
    applyVarWeaken : (s : Subst Tm n k) -> (i : Fin k) -> applyVar (weaken s) i = weaken (applyVar s i)
    applyVarWeaken Weaken i = absurd i
    applyVarWeaken (s :: x) FZ = Refl
    applyVarWeaken (s :: x) (FS y) = applyVarWeaken s y

    ||| Applying the identity substitution to a variable is the identity.
    applyVarIdIsId : (i : Fin k) -> Subst.applyVar {f=Tm} (id k) i = Var i
    applyVarIdIsId FZ = Refl
    applyVarIdIsId (FS x) {k=S k} = 
      rewrite Subst.ApplyVarProofs.applyVarWeaken (id k) x in
      rewrite Subst.ApplyVarProofs.applyVarIdIsId x in
      rewrite weakenVar x in
      Refl

  namespace SubTm
    ||| Applies a substitution to a term.
    apply : Subst Tm n k -> Tm k -> Tm n
    apply s (Lam t) = Lam (apply (extend s) t)
    apply s (App t t') = App (apply s t) (apply s t')
    apply s (Fold t) = Fold (apply s t)
    apply s (Unfold t) = Unfold (apply s t)
    apply s T = T
    apply s (Var x) = applyVar s x

  namespace SubTp
    ||| Applies a substitution to a type.
    apply : Subst Tp n k -> Tp k -> Tp n
    apply s (a ~> b) = apply s a ~> apply s b
    apply s Top = Top
    apply s (Mu a) = Mu (apply (extend s) a)
    apply s (Var x) = applyVar s x

  ||| Composition of substitutions.
  (.) : Subst Tm n k -> Subst Tm k j -> Subst Tm n j
  (.) s Weaken = Weaken
  (.) s (s' :: x) = s . s' :: apply s x

  namespace RenSubLeft
    (.) : Renaming n k -> Subst Tm k j -> Subst Tm n j
    (.) r Weaken = Weaken
    (.) r (s :: x) = (r . s) :: apply r x

    compId : (s : Subst Tm k j) -> Renaming.id k . s = s
    compId Weaken = Refl
    compId (s :: x) = cong2 (compId s) (idRenIsId x)

    compIdWeakenIsWeaken : (s : Subst Tm n k) -> (weaken (Renaming.id n) . s) = Subst.weaken s
    compIdWeakenIsWeaken Weaken = Refl
    compIdWeakenIsWeaken (s :: x) {n} =
      cong {f=\u => u :: apply (weaken $ Renaming.id n) x } $
      compIdWeakenIsWeaken s

    renSubCompVar : (r : Renaming n k) -> (s : Subst Tm k j) -> (i : Fin j) ->
                    apply r (applyVar s i) = applyVar (r . s) i
    renSubCompVar r Weaken i = absurd i
    renSubCompVar r (s :: x) FZ = Refl
    renSubCompVar r (s :: x) (FS y) = renSubCompVar r s y

    weakenDistributes : (r : Renaming n k) -> (s : Subst Tm k j) ->
                        weaken (r . s) = extend r . weaken s
    weakenDistributes r Weaken = Refl
    weakenDistributes r (s :: x) {n} =
      rewrite weakenDistributes r s in
      cong {f=\u => (weaken r :: FZ) . weaken s :: u} $
      rewrite sym $ weakenApply r x in
      Refl

    renSubComp : (r : Renaming n k) -> (s : Subst Tm k j) -> (t : Tm j) ->
                 apply r (apply s t) = apply (r . s) t
    renSubComp r s (Var x) = renSubCompVar r s x
    renSubComp r s (Lam t) =
      cong {f=Lam} $
      rewrite renSubComp (extend r) (extend s) t in
      rewrite weakenDistributes r s in
      Refl
    renSubComp r s (App t t') = cong2 (renSubComp r s t) (renSubComp r s t')
    renSubComp r s T = Refl
    renSubComp r s (Fold t) = cong (renSubComp r s t)
    renSubComp r s (Unfold t) = cong (renSubComp r s t)

  namespace RenSubRight
    (.) : Subst Tm n k -> Renaming k j -> Subst Tm n j
    (.) s Weaken = Weaken
    (.) s (r :: f) = s . r :: applyVar s f

    renSubCompVar : (s : Subst Tm n k) -> (r : Renaming k j) -> (i : Fin j) ->
                    applyVar s (applyVar r i) = applyVar (s . r) i
    renSubCompVar s Weaken i = absurd i
    renSubCompVar s (r :: f) FZ = Refl
    renSubCompVar s (r :: f) (FS x) = renSubCompVar s r x

    weakenDistributes : (s : Subst Tm n k) -> (r : Renaming k j) ->
                        weaken (s . r) = extend s . weaken r
    weakenDistributes s Weaken = Refl
    weakenDistributes s (r :: f) =
      rewrite weakenDistributes s r in
      cong {f = \u => extend s . weaken r :: u} $
      sym $ applyVarWeaken s f

    renSubComp : (s : Subst Tm n k) -> (r : Renaming k j) -> (t : Tm j) ->
                      apply s (apply r t) = apply (s . r) t
    renSubComp s r (Var x) = renSubCompVar s r x
    renSubComp s r (Lam t) =
      cong {f = Lam} $
      rewrite renSubComp (extend s) (extend r) t in
      rewrite weakenDistributes s r in
      Refl
    renSubComp s r (App t t') = cong2 (renSubComp s r t) (renSubComp s r t')
    renSubComp s r T = Refl
    renSubComp s r (Fold t) = cong $ renSubComp s r t
    renSubComp s r (Unfold t) = cong $ renSubComp s r t
  
    compWeakenRen : (s : Subst Tm n k) -> (t : Tm n) -> (r : Renaming k j) ->
                    (s :: t) . weaken r = s . r
    compWeakenRen s t Weaken = Refl
    compWeakenRen s t (r :: f) =
      cong {f = \u => u :: applyVar s f} $
      compWeakenRen s t r
  
    compId : (s : Subst Tm n k) -> ((s . Renaming.id k) = s)
    compId Weaken = Refl
    compId (s :: t) {k=S k} =
      cong {f = \u => u :: t} $
      rewrite compWeakenRen s t (id k) in
      rewrite RenSubRight.compId s in
      Refl

  namespace SubstProofs
    idSubIsId : (t : Tm n) -> SubTm.apply (id _) t = t
    idSubIsId (Lam t) = cong (idSubIsId t)
    idSubIsId (App t t') = cong2 (idSubIsId t) (idSubIsId t')
    idSubIsId T = Refl
    idSubIsId (Var x) = applyVarIdIsId x
    idSubIsId (Fold t) = cong (idSubIsId t)
    idSubIsId (Unfold t) = cong (idSubIsId t)
  
    compIdLeft : (s : Subst Tm n k) -> Subst.id n . s = s
    compIdLeft Weaken = Refl
    compIdLeft (s :: x) =
      rewrite idSubIsId x in
      cong {f = \u => u :: x} $
      rewrite compIdLeft s in
      Refl
  
    -- idSubAppend : (n : Nat) -> (s : Subst Tm n k) -> (t : Tm (n + k)) -> apply (id n ++ s) t = apply s t

    ||| Applying a weakened substitution is the same as weakening the application.
    weakenCommutes : (s : Subst Tm n k) -> (t : Tm k) ->
                     apply (weaken s) t = weaken (apply s t)
    weakenCommutes s t {n} =
      rewrite renSubComp (weaken (id n)) s t in
      rewrite compIdWeakenIsWeaken s in
      Refl

    mutual -- this is really sketchy
      weakenDistributes : (s1 : Subst Tm n k) -> (s2 : Subst Tm k j) ->
                          weaken (s1 . s2) = extend s1 . weaken s2
      weakenDistributes s1 Weaken = Refl
      weakenDistributes s1 (s2 :: x) =
        rewrite weakenDistributes s1 s2 in
        cong {f = \u => extend s1 . weaken s2 :: u} $
        rewrite weakenApply s1 x in
        Refl

      weakenApply : (s : Subst Tm n k) -> (t : Tm k) ->
                    weaken (apply s t) = apply (extend s) (weaken t)
      weakenApply s t {n} {k} =
        rewrite sym $ RenSubRight.compId s in
        rewrite sym $ weakenCommutes (s . Renaming.id k) t in
        rewrite weakenDistributes s (Renaming.id k) in
        rewrite renSubComp ((extend s . weaken (Renaming.id k)) :: Var FZ) (weaken $ Renaming.id k) t in
        rewrite compWeakenRen (weaken s) (Var FZ) (id k) in
        rewrite RenSubRight.compId (weaken s) in
        rewrite compWeakenRen (weaken s) (Var FZ) (id k) in
        rewrite RenSubRight.compId (weaken s) in
        Refl

    extendDistributes : (s1 : Subst Tm n k) -> (s2 : Subst Tm k j) ->
                        extend s1 . extend s2 = extend (s1 . s2)
    extendDistributes s1 Weaken = Refl
    extendDistributes s1 (s2 :: x) =
      cong {f=(:: Var FZ)} $
      rewrite weakenApply s1 x in
      cong {f=(:: apply (extend s1) (weaken x))} $
      sym (weakenDistributes s1 s2)
      
    subCompVar : (s : Subst Tm n k) -> (r : Subst Tm k j) -> (x : Fin j) ->
                 apply s (applyVar r x) = applyVar (s . r) x
    subCompVar s Weaken x = absurd x
    subCompVar s (s' :: y) FZ = Refl
    subCompVar s (s' :: y) (FS x) = subCompVar s s' x

    subComp : (s : Subst Tm n k) -> (r : Subst Tm k j) -> (t : Tm j) ->
              apply s (apply r t) = apply (s . r) t
    subComp s r (Lam t) =
      cong {f=Lam} $
      rewrite subComp (extend s) (extend r) t in
      rewrite extendDistributes s r in
      Refl
    subComp s r (Var x) = subCompVar s r x
    subComp s r (App t t') = cong2 (subComp s r t) (subComp s r t')
    subComp s r T = Refl
    subComp s r (Fold t) = cong (subComp s r t)
    subComp s r (Unfold t) = cong (subComp s r t)
  
    ||| Substitution composition distributes over substitution append.
    subCompAppend : (s : Subst Tm k n) -> (s1 : Subst Tm n k1) -> (s2 : Subst Tm n k2) ->
                    (s . s1) ++ (s . s2) = s . (s1 ++ s2)
    subCompAppend s s1 Weaken = Refl
    subCompAppend s s1 (s' :: x) =
      cong {f = \u => u :: apply s x} $
      subCompAppend s s1 s'
  
    compWeaken : (s1 : Subst Tm n k) -> (t : Tm n) -> (s2 : Subst Tm k j) ->
                 (s1 :: t) . weaken s2 = s1 . s2
    compWeaken s1 t Weaken = Refl
    compWeaken s1 t (s :: x) =
      rewrite renSubComp (s1 :: t) (weaken $ Renaming.id _) x in
      rewrite compWeakenRen s1 t (Renaming.id _) in
      rewrite RenSubRight.compId s1 in
      rewrite compWeaken s1 t s in
      Refl
