module Syntax
  
import Data.Fin
import Validation
  
%default total
%access public export
  
namespace Internal
  infixr 2 ~>
  
  data Tp : Type where
    ||| Atomic proposition.
    Top : Tp
    -- ||| Disjunction.
    -- (+) : Tp -> Tp -> Tp
    -- ||| Conjuction.
    -- (*) : Tp -> Tp -> Tp
    ||| Implication.
    (~>) : Tp -> Tp -> Tp
  
  %name Tp a, b, a', b', s, t, s', t'
  
  arrowInjective : a ~> b = a' ~> b' -> (a = a', b = b')
  arrowInjective Refl = (Refl, Refl)
  
  Show Tp where
    show Top = "Unit"
    show (a ~> b) = (showParens True (show a)) ++ " -> " ++ (show a)
  
  DecEq Tp where
    decEq Top Top = Yes Refl
    decEq Top (a ~> b) = No $ \Refl impossible
    decEq (a ~> a') Top = No $ \Refl impossible
    decEq (a ~> a') (b ~> b') with (decEq a b)
      decEq (a ~> a') (b ~> b') | (Yes prf) with (decEq a' b')
        decEq (b ~> b') (b ~> b') | (Yes Refl) | (Yes Refl) = Yes Refl
        decEq (a ~> a') (b ~> b') | (Yes prf) | (No contra) =
          No $ \eq => let (_, p2) = arrowInjective eq in contra p2
      decEq (a ~> a') (b ~> b') | (No contra) =
        No $ \eq => let (p1, _) = arrowInjective eq in contra p1
  
    
  data Ctx : Nat -> Type where
    Nil : Ctx Z
    (::) : Ctx n -> Tp -> Ctx (S n)
    
  ||| Accesses an entry from a context.
  index : Fin n -> Ctx n -> Tp
  index FZ (_ :: x) = x
  index (FS f) (g :: _) = index f g
    
  %name Ctx g, g', d, d'
    
  data Direction = Synth | Check
  
  infix 1 |-
    
  data (|-) : Ctx n -> (Direction, Tp) -> Type where
    Var : (i : Fin n) -> g |- (Synth, index i g)
    Unit : g |- (Synth, Top)
    -- InL : g |- a -> g |- a + b
    -- InR : g |- b -> g |- a + b
    -- Case : g |- a + b -> g :: a |- c -> g :: b |- c -> g |- c
    -- Pair : g |- a -> g |- b -> g |- a * b
    -- Fst : g |- a * b -> g |- a
    -- Snd : g |- a * b -> g |- b
    Lam : g :: a |- (Check, b) -> g |- (Check, a ~> b)
    App : g |- (Check, a ~> b) -> g |- (Synth, a) -> g |- (Check, b)
    Ann : (a : Tp) -> g |- (Check, a) -> g |- (Synth, a)
    Coe : g |- (Synth, a) -> g |- (Check, a)
  
  %name (|-) s, t

namespace External
  data Tm : Type where
    Unit : Tm
    Var : String -> Tm
    Lam : String -> Tm -> Tm
    App : Tm -> Tm -> Tm
    ||| A term with a type annotation.
    Ann : Tm -> Tp -> Tm
  
  %name External.Tm t, t', s, s'

namespace DeBruijn
  data Tm : Direction -> Nat -> Type where
    Unit : Tm Synth n
    Lam : Tm Check (S n) -> Tm Check n
    Var : Fin n -> Tm Synth n
    App : Tm Check n -> Tm Synth n -> Tm Check n
    Ann : Tm Check n -> Tp -> Tm Synth n
    Coe : Tm Synth n -> Tm Check n
  
  ||| Adds a coercion if necessary to make any term checkable.
  coe : Tm d n -> Tm Check n
  coe {d = Synth} t = Coe t
  coe {d = Check} t = t
  
  %name DeBruijn.Tm t, t', s, s'
  
  ||| An ordered collection of names.
  data Names : Nat -> Type where
    Nil : Names Z
    (::) : Names n -> String -> Names (S n)
  
  %name Names ns, ns'
  
  ||| Accesses a name at a particular index.
  index : Names n -> Fin n -> String
  index Nil f = FinZElim f
  index (n :: s) FZ = s
  index (n :: s) (FS f) = index n f
  
  ||| Looks up a name's index.
  name : (ns : Names n) -> (s : String) -> Maybe (i : Fin n ** index ns i = s)
  name [] s = Nothing
  name (ns :: s') s with (decEq s' s)
    name (ns :: s') s | (Yes prf) = Just (FZ ** prf)
    name (ns :: s') s | (No contra) = do
      (f ** prf) <- name ns s
      pure (FS f ** prf)
  
  Bruijnify : Nat -> Type
  Bruijnify n = (d ** Tm d n)

  bruijnify : Names n -> Tm -> Validation (List String) (Bruijnify n)
  bruijnify ns Unit = Ok (_ ** Unit)
  bruijnify ns (Var x) =
    case name ns x of
      Nothing => Failed $ ["variable `" ++ x ++ "` not in scope"]
      Just (i ** p) => Ok (_ ** Var i)
  bruijnify ns (Lam x t) =
    (\(_ ** t) => (_ ** Lam (coe t))) <$> bruijnify (ns :: x) t
  bruijnify {n} ns (App t t') =  rhs <*> bruijnify ns t' where
    rhs = case bruijnify ns t' of
      Ok (Check ** _) => Failed ["RHS of application not synthesizable"]
      Ok (Synth ** s') => Ok (\(_ ** s) => (_ ** App (coe s) s'))
      Failed e => Failed e
  bruijnify {n} ns (Ann t a) = map (\(_ ** s) => (_ ** Ann (coe s) a)) (bruijnify ns t)
  
  ||| Erase an intrisically-typed term to an untyped de bruijn term.
  erase : {g : Ctx n} -> g |- (d, a) -> Tm d n
  erase (Var i) = Var i
  erase Unit = Unit
  erase (Lam s) = Lam (erase s)
  erase (App s t) = App (erase s) (erase t)
  erase (Ann a t) = Ann (erase t) a
  erase (Coe t) = Coe (erase t)
