module Horn
  
import Data.Fin
import Data.Vect

%default total
  
data FKind = D | G
%name FKind fk, fk'

data Form : FKind -> Type -> Type where
  Atom : a -> Form fk a
  Top : Form fk a
  Conj : Form fk a -> Form fk a -> Form fk a
  Disj : Form G a -> Form G a -> Form G a
  Imp : Form G a -> Form D a -> Form D a

%name Form phi, phi', phi''

(+) : Form G a -> Form G a -> Form G a
(+) = Disj

(*) : Form fk a -> Form fk a -> Form fk a
(*) = Conj

atom : a -> Form fk a
atom = Atom

infixr 1 ~>
(~>) : Form G a -> Form D a -> Form D a
(~>) = Imp
  
data Tm : Nat -> Type where
  Var : String -> Tm n
  App : Tm n -> Tm n -> Tm n
  Pair : Tm n -> Tm n -> Tm n
  Unit : Tm n
  Right : Tm n -> Tm n
  Left : Tm n -> Tm n
  Fst : Tm n -> Tm n
  Snd : Tm n -> Tm n
  Subgoal : Fin n -> Tm n
  
weaken : Tm n -> Tm (S n)
weaken (Var x) = Var x
weaken (App x y) = App (weaken x) (weaken y)
weaken (Pair x y) = Pair (weaken x) (weaken y)
weaken Unit = Unit
weaken (Right x) = Right (weaken x)
weaken (Left x) = Left (weaken x)
weaken (Fst x) = Fst (weaken x)
weaken (Snd x) = Snd (weaken x)
weaken (Subgoal x) = Subgoal (FS x)
 
||| Substitutes the head variable out.
subst : Tm n -> Tm (S n) -> Tm n
  
||| A program is a list of terms with no subgoals, each associated
||| with a proven theorem.
Program : Type -> Type
Program a = List (Tm Z, Form D a)
  
||| A possibly infinite list.
data Colist : Type -> Type where
  Nil : Colist a
  (::) : a -> Inf (Colist a) -> Colist a
  
%name Colist l, l', l''
  
(++) : Colist a -> Colist a -> Colist a
(++) [] l2 = l2
(++) (x :: y) l2 = x :: (y ++ l2)
  
partial 
-- concatMap fails the basic guardedness check since concatMap may not be guarded.
-- Spse `f x = []`. Then `[] ++ concatMap f l = concatMap f l`, which is not guarded.
-- In particular, it will infinite loop `f _ = Nil` and `xs` is infinite.
concatMap : (a -> Colist b) -> (xs : Colist a) -> Colist b
concatMap f [] = []
concatMap f (x :: l) = f x ++ concatMap f l
  
Functor Colist where
  map f [] = []
  map f (x :: y) = f x :: map f y
  
Applicative Colist where
  pure x = [x]
  (<*>) fs xs = assert_total $ concatMap (<$> xs) fs --forgive me
  
Alternative Colist where
  empty = []
  (<|>) = (++)
  
Monad Colist where
  (>>=) m k = assert_total $ concatMap k m --this hurts
  
IsZero : Nat -> Type -> Type -> Type
IsZero Z a b = a
IsZero (S _) a b = b
  
Subgoals : Type -> Nat -> Type
Subgoals a n = Vect n (Form G a)
  
mutual
  Continue : Nat -> Nat -> Type -> Type
  Continue n k a = Maybe (Tm n) -> Either (fk : FKind ** State fk a) (Tm k)
  
  data Phase : FKind -> Type -> Type where
    GPhase : (goal : Form G a) -> Continue Z Z a -> Phase G a
    DPhase : (subgoals : Subgoals a n) ->
             (proofTerm : Tm n) ->
             (proofType : Form D a) ->
             (goal : a) ->
             (continue : Continue n n a) ->
             Phase D a

  record State (fk : FKind) a where
    constructor MkState
    -- solution : Solution fk a n
    phase : Phase fk a
    -- when the termType reaches `DAtom x` and `x = goalProp`, we're
    -- done, and we need to solve the subgoals that were accumulated.
    -- continue : (n ** Solution n) -> State a
  
  %name State s, s', s''
    
  ||| Represents a solution with `n` holes (subgoals).
  ||| Contains a proof term and the type that the term solves.
  record Solution (fk : FKind) a (n : Nat) where
    constructor MkSolution
    subgoals : Subgoals a n
    proofTerm : Tm n
    termType : Form fk a
  
  %name Solution sol, sol', sol''
  
isYes : Dec a -> Bool
isYes (Yes _) = True
isYes (No _) = False

-- mutual
--   covering
--   solveG : DecEq a => Program a -> State G a -> Either (fk : FKind ** State fk a) (Tm Z)
--   solveG p (MkState (GPhase (Atom x) continue)) = tryAll p x continue
--   solveG p (MkState (GPhase Top continue)) = continue (Just Unit)
--   solveG p (MkState (GPhase (Conj phi phi') continue)) = solveG p (MkState (GPhase phi f)) where
--     f : Continue Z Z a
--     f (Just t) = Left (_ ** MkState (GPhase phi' continue))
--     f Nothing = continue Nothing
--   solveG p (MkState (GPhase (Disj phi phi') continue)) = solveG p (MkState (GPhase phi f)) where
--     f : Continue Z Z a
--     f (Just t) = continue (Just t)
--     f Nothing = Left (_ ** MkState (GPhase phi' continue))
--   
--   covering
--   tryAll : DecEq a => Program a -> a -> Continue n n a -> Either (fk : FKind ** State fk a) (Tm n)
--   tryAll p x k = tryAll' p p x k
-- 
--   covering
--   tryAll' : DecEq a => Program a -> Program a -> a -> Continue n n a -> Either (fk : FKind ** State fk a) (Tm n)
--   tryAll' p [] x k = k Nothing
--   tryAll' p ((t, ty) :: xs) x k = solveD p (MkState (DPhase [] t ty x f)) where
--     f : Continue n n a
--     f (Just t') = k (Just t')
--     f Nothing = tryAll' p xs x k
--   
--   covering
--   solveD : DecEq a => Program a -> State D a -> Either (fk : FKind ** State fk a) (Tm n)
--   solveD p (MkState (DPhase subgoals proofTerm proofType goal continue)) = case proofType of
--     (Atom x) => if isYes (decEq x goal) then ?a else ?b
--     Top => continue (Just Horn.Unit)
--     (Conj phi phi') =>
--       solveD p $
--         MkState (DPhase subgoals (Fst proofTerm) phi goal) $ \m => case m of
--           Just t => continue (Just t)
--           Nothing =>
--             solveD p $
--               MkState (DPhase subgoals (Snd proofTerm) phi' goal) continue
--     (Imp phi phi') =>
--       solveD p  $
--         MkState (DPhase (phi :: subgoals) (App (weaken proofTerm) (Subgoal FZ)) phi' goal) $ \m => case m of
--           Just t => Left $ (_ ** MkState (GPhase phi) $ \m => case m of
--             Just t' => continue $ Just (subst t t')
--             Nothing => continue Nothing)
--           Nothing => continue Nothing
  
  -- solveG : DecEq a => Program a -> GForm a -> Colist (Tm Z)
  -- solveG p GTop = [Unit]
  -- solveG p (GConj gf gf') = do
  --   t1 <- solveG p gf
  --   t2 <- solveG p gf'
  --   pure (Pair t1 t2)
  -- solveG p (GDisj gf gf') = (Left <$> solveG p gf) <|> (Right <$> solveG p gf')
  -- solveG p (GAtom x) = ?a -- runStates (map ?a p)
  -- 
  -- solveSubgoals : DecEq a => Subgoals a n -> Tm n -> Either (State a) (Tm Z)
  -- solveSubgoals [] tm = Right tm
  -- solveSubgoals (x :: xs) tm = ?a
  -- 
  -- partial
  -- runState : DecEq a => State a -> Either (State a) (Tm Z)
  -- runState (MkState (MkSolution subgoals tm ty) goal k) =
  --   case ty of
  --     DAtom y =>
  --       if isYes (decEq y goal) then
  --         solveSubgoals subgoals tm
  --       else
  --         Left (k Nothing)
    
--   
--   partial
--   solveD : DecEq a => Program a -> a -> (Tm -> Maybe Tm) -> DForm a -> Tm -> Maybe Tm
--   solveD p x t (DAtom y) with (decEq y x)
--     solveD p x t (DAtom y) | (Yes prf) = \s => t s
--     solveD p x t (DAtom y) | (No contra) = \s => Nothing 
-- 
--   solveD p x t DTop = \s => t s
--   solveD p x t (DConj df df') =
--     \s =>
--     solveD p x (\_ => Fst <$> (t s)) df
--     <|>
--     solveD p x (\_ => Snd <$> (t s)) df'
--   solveD p x t (DImp gf df) =
--     \s => do
--       solveD p x (\s' => App <$> (t s) <*> pure s) df
--       s <- solveG p gf
--       pure
-- 
-- example : Program Nat
-- example = [ atom Z, atom Z ~> atom 1, atom 1 ~> atom 2 ]
 
