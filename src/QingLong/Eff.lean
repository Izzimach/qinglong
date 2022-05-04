-- extensible effect monad "Eff" based on "Free Monads, More Extensible Effects"
-- built on top of the W type

import QingLong.PFunctor
import QingLong.Wtype
import QingLong.OpenUnion

open pfunctor
open Wtype
open openunion

namespace effW

namespace FixHack

variable {α : Sort u} {C : α → Sort v} {r : α → α → Prop}

unsafe def fix'.impl (hwf : WellFounded r) (F : ∀ x, (∀ y, r y x → C y) → C x) (x : α) : C x :=
  F x (fun y _ => impl hwf F y)

set_option codegen false in
@[implementedBy fix'.impl]
def fix' (hwf : WellFounded r) (F : ∀ x, (∀ y, r y x → C y) → C x) (x : α) : C x := hwf.fix F x

end FixHack

-- We manually "compile" the Eff ↔ Arrs mutual inductive here, instead of letting Lean do it. This
-- hopefully allows for better specifying/solving of well found recursion, especially when it
-- enables Lean to automatically apply structural recursion.
--
-- The Bool "chooses" between Eff and Arrs: tt = Eff and ff = Arrs
-- Note that Eff uses one less type index so we just throw Unit in there to fill space.
-- another option might be to duplicate the result type, i.e. change "EffArrs r tt Unit a" to "EffArrs r tt a a"
--
inductive EffArrs (effs : List (Type → Type))  : Bool → Type → Type → Type 1 where
| Pure : α → EffArrs effs true Unit α
| Impure : (x : Type) → OU effs x → EffArrs effs false x α → EffArrs effs true Unit α
| Leaf : (α → EffArrs effs true Unit β) → EffArrs effs false α β
| Node : (x : Type) → EffArrs effs false α x → EffArrs effs false x β → EffArrs effs false α β

def effSize : EffArrs effs b α β → Nat
| EffArrs.Pure _ => 1
| EffArrs.Impure x ou n => effSize n + 1
| EffArrs.Leaf f => 1
| EffArrs.Node x l r => effSize l + effSize r

def effSize2 (y : EffArrs effs b α β) (z : EffArrs effs b' β γ) : Nat :=
    (effSize y * 2) + effSize z


-- don't know why I can't use 'tt' here
def Arr effs a b := a → EffArrs effs true Unit b

section

variable {effs : List (Type → Type)} {α : Type} {β : Type} {γ : Type} {e : Type → Type}

def tsingleton (f : α → EffArrs effs Bool.true Unit β) : EffArrs effs Bool.false α β := EffArrs.Leaf f

def snoc (q : EffArrs effs Bool.false a γ) (f : γ → EffArrs effs Bool.true Unit b) : EffArrs effs Bool.false a b :=
    EffArrs.Node γ q (EffArrs.Leaf f)

def append (q1 : EffArrs effs Bool.false a x) (q2 : EffArrs effs Bool.false x b) : EffArrs effs Bool.false a b :=
    EffArrs.Node x q1 q2

def send {x : Type} [HasEffect e effs] : e x → EffArrs effs Bool.true Unit x :=
    fun tv => EffArrs.Impure x (HasEffect.inject tv) (tsingleton EffArrs.Pure)

end

syntax term "|→" term : term
macro_rules
  | `($s |→ $t) => `(snoc $s $t)

syntax term "><" term : term
macro_rules
  | `($s >< $t) => `(append $s $t)


inductive ViewLL (effs : List (Type → Type)) : Type → Type → Type 1 where
  | VOne : (α → EffArrs effs Bool.true Unit β) → ViewLL effs α β
  | VCons : (x : Type) → (α → EffArrs effs Bool.true Unit x) → EffArrs effs Bool.false x β → ViewLL effs α β

def tviewL' (y : EffArrs effs Bool.false α γ) (z : EffArrs effs Bool.false γ β) : ViewLL effs α β :=
  match y with
  | (EffArrs.Leaf f) => ViewLL.VCons γ f z
  | (EffArrs.Node x f q) => tviewL' f (@EffArrs.Node effs x β γ q z)
  -- the pure/impure nodes are illegal here

def tviewL : EffArrs effs Bool.false α β → ViewLL effs α β
  | EffArrs.Leaf f => ViewLL.VOne f
  | EffArrs.Node e f q => tviewL' f q
  -- the pure/impure nodes are illegal here


-- stil need to prove this well-founded
def qApp (q : EffArrs effs Bool.false β w) (x : β) : EffArrs effs Bool.true Unit w :=
  match (tviewL q) with
  | ViewLL.VOne k => k x
  | ViewLL.VCons e k t => match (k x) with
                          | EffArrs.Pure y => have h : effSize t < effSize q := sorry
                                              qApp t y
                          | EffArrs.Impure x ou n => EffArrs.Impure x ou (n >< t)
  termination_by qApp q x => effSize q
  

instance : Monad (EffArrs effs Bool.true Unit) where
  pure := EffArrs.Pure
  bind := fun m f =>
    match m with
    | EffArrs.Pure a => f a
    | EffArrs.Impure x ou n => EffArrs.Impure x ou (n |→ f)

inductive Reader (i : Type) : Type → Type where
| Get : Reader i i

def ask [HasEffect (Reader i) effs] : EffArrs effs Bool.true Unit i := send Reader.Get

def decomp {effs : List (Type → Type)} {e : Type → Type} {α : Type} : OU (e :: effs) α → Sum (OU effs α) (e α) :=
  fun ou => match ou with
            | @OU.mk (e :: effs) α t' ix tx =>
                match @CompareT.areEquiv t' e _ α tx with
                | Option.none => let ix' := mkElemIndex <| (unElemIndex ix) - 1
                                 Sum.inl <| OU.mk ix' tx
                | Option.some z => Sum.inr z

def qComp (g : EffArrs effs false α β) (h : EffArrs effs true Unit β → EffArrs effs' true Unit γ) : Arr effs' α γ :=
  h ∘ qApp g

def runReader {α : Type} {effs : List (Type → Type)} {i : Type} (inp : i) : EffArrs (Reader i :: effs) true Unit α → EffArrs effs Bool.true Unit α :=
  fun m =>
    match m with
    | EffArrs.Pure a => pure a
    | EffArrs.Impure x ou n =>
        match decomp ou with
        | Sum.inl ou' => EffArrs.Impure x ou' (tsingleton <| qComp n (runReader inp))
        | Sum.inr (Reader.Get) => runReader inp <| qApp n inp
  termination_by runReader i q => effSize q
  decreasing_by sorry



end effW
