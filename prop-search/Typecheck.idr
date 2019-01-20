module Typecheck

import Data.Vect

import Validation
import Syntax
  
%default total
  
mismatch : (expected : Tp) -> (actual : Tp) -> String
mismatch e a = "expected type " ++ show e ++ "; actual type is " ++ show a

mutual
  ||| Synthesize the type of a synthesizable term.
  typesynth : (g : Ctx n) -> Tm Synth n -> Validation (List String) (a ** g |- (Synth, a))
  typesynth g Unit = Ok (_ ** Unit)
  typesynth g (Var x) = Ok (index x g ** Var x)
  typesynth g (Ann t a) = (\s => (_ ** Ann a s)) <$> typecheck g t a

  ||| Check that in context `g`, the term has the given type.
  typecheck : (g : Ctx n) -> Tm Check n -> (a : Tp) -> Validation (List String) (g |- (Check, a))
  typecheck g (Lam t) (a ~> b) = (\s => Lam s) <$> typecheck (g :: a) t b
  typecheck g (Lam t) a = Failed ["expected function type; given type is " ++ show a]
  typecheck g (App t t') b =
    case typesynth g t' of
      Ok (a ** s') => (\s => App s s') <$> typecheck g t (a ~> b)
      Failed e => Failed e
  typecheck g (Coe t) a =
    case typesynth g t of
      Ok (a' ** s) =>
        case decEq a a' of
          Yes Refl => Ok (Coe s)
          No contra =>
            Failed
              [ "synthesized type `" ++ show a' ++ "`"
                ++ " of coercion does not match expected type `" ++ show a ++ "`"
              ]
      Failed e => Failed e
