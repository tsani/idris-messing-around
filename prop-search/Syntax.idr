module Syntax
  
import Data.Fin

import Misc
import UVect
import Validation
  
%default total
%access public export

Names : Nat -> Type
Names n = UVect String n
  
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
    
  %name Ctx g, g', d, d'
    
  ||| Accesses an entry from a context.
  index : Fin n -> Ctx n -> Tp
  index FZ (_ :: x) = x
  index (FS f) (g :: _) = index f g
    
  ||| Whether a term has a checkable type or a synthesizable type.
  data Direction = Synth | Check
  
  infix 1 |-
    
  ||| Well-typed terms, in a context for bound variables and an
  ||| interned collection of names for free variables.
  data (|-) : (Ctx k, Ctx n) -> (Direction, Tp) -> Type where
    Var : (i : Fin n) -> (ns, g) |- (Synth, index i g)
    Unit : (ns, g) |- (Synth, Top)
    -- InL : g |- a -> g |- a + b
    -- InR : g |- b -> g |- a + b
    -- Case : g |- a + b -> g :: a |- c -> g :: b |- c -> g |- c
    -- Pair : g |- a -> g |- b -> g |- a * b
    -- Fst : g |- a * b -> g |- a
    -- Snd : g |- a * b -> g |- b
    Lam : (ns, g :: a) |- (Check, b) -> (ns, g) |- (Check, a ~> b)
    App : (ns, g) |- (Check, a ~> b) -> (ns, g) |- (Synth, a) -> (ns, g) |- (Check, b)
    Ann : (a : Tp) -> (ns, g) |- (Check, a) -> (ns, g) |- (Synth, a)
    Coe : (ns, g) |- (Synth, a) -> (ns, g) |- (Check, a)
    Free : (i : Fin k) -> (ns, g) |- (Synth, index i ns)
  
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
  data Tm : Names k -> Direction -> Nat -> Type where
    Unit : Tm ns Synth n
    Lam : Tm ns Check (S n) -> Tm ns Check n
    Var : Fin n -> Tm ns Synth n
    App : Tm ns Check n -> Tm ns Synth n -> Tm ns Check n
    Ann : Tm ns Check n -> Tp -> Tm ns Synth n
    Coe : Tm ns Synth n -> Tm ns Check n
    Free : {ns : Names k} -> Fin k -> Tm ns Synth n
  
  %name DeBruijn.Tm t, t', s, s'
  
  ||| Adds a coercion if necessary to make any term checkable.
  coe : Tm ns d n -> Tm ns Check n
  coe {d = Synth} t = Coe t
  coe {d = Check} t = t
  
  weakenFree : (fresh : Fresh x uv) -> Tm uv d n -> Tm (Cons uv x fresh) d n
  
  Bruijnify : Nat -> Type
  Bruijnify n = (d ** k ** ns : Names k ** Tm ns d n)

  bruijnify : (bound : Names n) -> (free : Names k) -> Tm ->
              Validation (List String) (Bruijnify n)
  bruijnify ns free Unit = Ok (_ ** _ ** [] ** Unit)
  bruijnify ns free (Var x) = ?a

    -- case lookup ns x of
    --   Nothing => Failed $ ["variable `" ++ x ++ "` not in scope"]
    --   Just (i ** p) => Ok (_ ** Var i)
  -- bruijnify ns (Lam x t) =
  --   (\(_ ** t) => (_ ** Lam (coe t))) <$> bruijnify (ns :: x) t
  bruijnify {n} ns free (App t t') =  rhs <*> bruijnify ns free t' where
    rhs = case bruijnify ns free t' of
      Ok (Check ** _) => Failed ["RHS of application not synthesizable"]
      Ok (Synth ** _ ** ns ** s') => Ok (\(_ ** _ ** ns' ** s) => (_ ** _ ** merge ns ns' ** App (coe s) s'))
      Failed e => Failed e
  bruijnify {n} ns free (Ann t a) = map (\(_ ** s) => (_ ** Ann (coe s) a)) (bruijnify ns free t)
  
  -- ||| Erase an intrisically-typed term to an untyped de bruijn term.
  -- erase : {g : Ctx n} -> g |- (d, a) -> Tm d n
  -- erase (Var i) = Var i
  -- erase Unit = Unit
  -- erase (Lam s) = Lam (erase s)
  -- erase (App s t) = App (erase s) (erase t)
  -- erase (Ann a t) = Ann (erase t) a
  -- erase (Coe t) = Coe (erase t)
