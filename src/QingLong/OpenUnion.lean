-- open union for use with Eff
import Lean
open Lean Elab Command Term

namespace openunion

def ElemIndex (t : Type → Type) (r : List (Type → Type)) := Nat

def mkElemIndex {t : Type → Type} {r : List (Type → Type)} (x : Nat) : ElemIndex t r := x
def unElemIndex (e : ElemIndex t r) : Nat := e


inductive OU (r : List (Type → Type)) (x : Type) : Type 1 where
| mk : {t : Type → Type} → ElemIndex t r → t x → OU r x


class FindElem (t : Type → Type) (r : List (Type → Type)) where
     eindex : ElemIndex t r

instance : FindElem (t : Type → Type) (List.cons t r) where
     eindex := mkElemIndex 0

instance [FindElem t r] : FindElem t (List.cons t' r) where
     eindex := mkElemIndex (1 + unElemIndex (FindElem.eindex : ElemIndex t r))



class HasEffect (t : Type → Type) (effs : List (Type → Type)) where
   inject  : t v → OU effs v
   project : OU effs v → Option (t v)



-- the freer-simple library used an unsafeCoerce to convert (t v) to (t' v) since it had
-- already verifired (t = t') by looking at the index in the OU. Here we use a typeclass.

class CompareT (t : Type → Type) (t' : Type → Type) where
  areEquiv : t v → Option (t' v)

@[defaultInstance]
instance : CompareT t t where
   areEquiv := fun tv => Option.some tv

instance : CompareT t1 t2 where
   areEquiv := fun _ => Option.none


def rawProject {t : Type → Type} : (ou : OU effs v) → Option (t v)
| @OU.mk effs v t' ix tv => CompareT.areEquiv tv


instance [FindElem t effs] : HasEffect (t : Type → Type) (effs : List (Type → Type)) where
   inject := fun tv => OU.mk (@FindElem.eindex t effs _) tv
   project := rawProject
