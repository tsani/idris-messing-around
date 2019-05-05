module WellScoped
  
import Data.Fin

namespace Syntax
  infixr 1 ~>
  data Tp : Type where
    Base : Tp
    (~>) : Tp -> Tp -> Tp
    
  data Tm : Nat -> Type where
    Var : Fin n -> Tm n
    Lam : Tm (S n) -> Tm n
    App : Tm n -> Tm n -> Tm n
  
namespace FinMap
  ||| A finite map from `n` to `dst`.
  FinMap : (n : Nat) -> (dst : Type) -> Type
  FinMap n t = Fin n -> t
  
  ||| Adds an entry on the head of a finite map.
  extend : FinMap n t -> t -> FinMap (S n) t
  extend f x FZ = x
  extend f _ (FS i) = f i
  
namespace Context
  Ctx : Nat -> Type
  Ctx n = FinMap n Tp
  
namespace Renumbering
  Renumbering : (dst : Nat) -> (src : Nat) -> Type
  Renumbering dst src = FinMap src (Fin dst)
  
  id : (n : Nat) -> Renumbering n n
  id _ i = i
  
  weaken : Renumbering n k -> Renumbering (S n) k
  weaken r i = FS (r i)
  
  extend : Renumbering n k -> Renumbering (S n) (S k)
  extend r = extend (weaken r) FZ
  
  extendComp : (r1 : Renumbering n k) -> (r2 : Renumbering k j) ->
               (i : Fin (S j)) ->
               extend r1 (extend r2 i) = extend (r1 . r2) i
  extendComp r1 r2 FZ = Refl
  extendComp r1 r2 (FS _) = Refl
  
  extendCompApply : (r1 : Renumbering n k) -> (r2 : Renumbering k j) ->
                    (t : Tm (S j)) ->
                    apply (extend r1 . extend r2) t = apply (extend (r1 . r2)) t
  
  apply : Renumbering n k -> Tm k -> Tm n
  apply r (Var x) = Var (r x)
  apply r (Lam x) = Lam (apply (extend r) x)
  apply r (App x y) = App (apply r x) (apply r y)
  
  renComp : (r1 : Renumbering n k) -> (r2 : Renumbering k j) ->
            (t : Tm j) ->
            apply r1 (apply r2 t) = apply (r1 . r2) t
  renComp r1 r2 (Var x) = Refl
  renComp r1 r2 (Lam x) =
    cong {f = Lam} $
    rewrite renComp (extend r1) (extend r2) x in
    ?a
  renComp r1 r2 (App x y) = ?a_3
  
namespace Subst
  Subst : (dst : Nat) -> (src : Nat) -> Type
  Subst dst src = FinMap src (Tm dst)
  
  
