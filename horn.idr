module horn
  
import Data.Fin
  
%default total
  
Atom : Type
Atom = Nat
  
namespace Source
  data SGoal : Type where
    GCons : Atom -> SGoal -> SGoal
    GNil : SGoal
  
  data SClause : Type where
    DAtom : Atom -> SClause
    DImp : SGoal -> Atom -> SClause
    DForall : SClause -> SClause
  
  data SProgram : Nat -> Type where
    PNil : SProgram Z
    PCons : SProgram n -> SClause -> SProgram (S n)
  
  index : SProgram n -> Fin n -> SClause
  index PNil i = absurd i
  index (PCons p' c) FZ = c
  index (PCons p' _) (FS i') = index p' i'
  
  mutual
    data SFocus : SProgram n -> SClause -> Atom -> Type where
      SInit : SFocus p (DAtom a) a
      SPick : SFocus p c a -> SFocus p (DForall c) a
      SImp : SSynth p g -> SFocus p (DAtom a') a -> SFocus p (DImp g a') a
    
    data SSynth : SProgram n -> SGoal -> Type where
      SSynNil : SSynth p GNil
      SSynPair : {p : SProgram n} -> (i : Fin n) -> SFocus p (index p i) a -> SSynth p g -> SSynth p (GCons a g)

namespace Target
  data TGoal : Type where
    GAtom : Atom -> TGoal
    GImp : Atom -> TGoal -> TGoal
  
  data TClause : Type where
    DAtom : Atom -> TClause
    DForall : TClause -> TClause
    DGoal : TGoal -> TClause
  
  data TProgram : Nat -> Type where
    PNil : TProgram Z
    PCons : TProgram n -> TClause -> TProgram (S n)
  
  mutual
    data TFocus : SProgram n -> SClause -> Atom -> Type where
      TInit : SFocus p (DAtom a) a
      TPick : SFocus p c a -> SFocus p (DForall c) a
      TGoal : SSynth p g -> SFocus p (DAtom a') a -> SFocus p (DImp g a') a
    
    data TSynth : SProgram n -> SGoal -> Type where
      SSynNil : SSynth p GNil
      SSynPair : {p : SProgram n} -> (i : Fin n) -> SFocus p (index p i) a -> SSynth p g -> SSynth p (GCons a g)

namespace Translation
  transGoal : SGoal -> TGoal -> TGoal
  
  transClause : SClause -> SClause
  
  transProg : SProgram n -> TProgram n
