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
  F x fun y _ => impl hwf F y

set_option codegen false in
@[implementedBy fix'.impl]
def fix' (hwf : WellFounded r) (F : ∀ x, (∀ y, r y x → C y) → C x) (x : α) : C x := hwf.fix F x

end FixHack


mutual

inductive EffX (r : List (Type → Type)) : Type → Type 1 where
| Pure : a → EffX r a
| Impure : (e : Type) → OU r x → ArrsX r x a → EffX r a

-- ArrsX r a b := FTCQueue (EffX r) a b
inductive ArrsX (r : List (Type → Type)) : Type → Type → Type 1 where
| Leaf : (a → EffX r b) → ArrsX r a b
| Node : (e : Type) → ArrsX r a e → ArrsX r e b → ArrsX r a b

end --mutual

def Arr effs a b := a → EffX effs b

section

variable {r : List (Type → Type)} {α : Type} {β : Type} {γ : Type} {t : Type → Type}

def tsingleton (f : α → EffX r β) : ArrsX r α β := ArrsX.Leaf f

def snoc (q : ArrsX r a γ) (f : γ → EffX r b) : ArrsX r a b := ArrsX.Node γ q (ArrsX.Leaf f)

def append (q1 : ArrsX r a x) (q2 : ArrsX r x b) : ArrsX r a b := ArrsX.Node x q1 q2

def send {v : Type} [HasEffect t r] : t v → EffX r v :=
    fun tv => EffX.Impure v (HasEffect.inject tv) (tsingleton EffX.Pure)

end

syntax term "|→" term : term
macro_rules
  | `($s |→ $t) => `(snoc $s $t)

syntax term "><" term : term
macro_rules
  | `($s >< $t) => `(append $s $t)




inductive ViewLL (r : List (Type → Type)) : Type → Type → Type 1 where
  | VOne : (a → EffX r b) → ViewLL r a b
  | VCons : (e : Type) → (a → (EffX r) e) → ArrsX r e b → ViewLL r a b

-- needs well founded proof
def tviewL' (y : ArrsX r a x) (z : ArrsX r x b) : ViewLL r a b :=
  match y with
  | (ArrsX.Leaf f) => ViewLL.VCons x f z
  | (ArrsX.Node e f q) => tviewL' f (ArrsX.Node x q z)
  termination_by tviewL' y z => 1
  decreasing_by sorry

def tviewL : ArrsX r a b → ViewLL r a b
  | ArrsX.Leaf f => ViewLL.VOne f
  | ArrsX.Node e f q => tviewL' f q

-- this also need well founded proof
-- what a mess
def qApp (q : ArrsX r β w) (x : β) : EffX r w :=
  let bind' {α : Type} : EffX r α → ArrsX r α w → EffX r w :=
    fun ef ar => match ef with
                 | EffX.Pure y => @qApp r α w ar y
                 | EffX.Impure e u q => EffX.Impure e u (q >< ar)
  match (tviewL q) with
  | ViewLL.VOne k => k x
  | ViewLL.VCons e k t => bind' (k x) t
  termination_by qApp q x => 1
  decreasing_by sorry

instance : Monad (EffX r) where
  pure := EffX.Pure
  bind := fun m f =>
    match m with
    | EffX.Pure a => f a
    | EffX.Impure e u ar => EffX.Impure e u (ar |→ f)

inductive Reader (i : Type) : Type → Type where
| Get : Reader i i

def ask [HasEffect (Reader i) effs] : EffX effs i := send Reader.Get

def decomp {effs : List (Type → Type)} {e : Type → Type} {α : Type} : OU (e :: effs) α → Sum (OU effs α) (e α) :=
  fun ou => match ou with
            | @OU.mk (e :: effs) α t' ix tx =>
                match @CompareT.areEquiv t' e _ α tx with
                | Option.none => let ix' := mkElemIndex <| (unElemIndex ix) - 1
                                 Sum.inl <| OU.mk ix' tx
                | Option.some z => Sum.inr z

def qComp (g : ArrsX effs a b) (h : EffX effs b → EffX effs' c) : Arr effs' a c :=
  h ∘ qApp g

def runReader {α : Type} {effs : List (Type → Type)} {i : Type} (inp : i) : EffX (Reader i :: effs) α → EffX effs α :=
  fun m =>
    match m with
    | EffX.Pure a => pure a
    | EffX.Impure e u ar =>
        match decomp u with
        | Sum.inl u' => EffX.Impure e u' (tsingleton <| qComp ar (runReader inp))
        | Sum.inr (Reader.Get) => runReader inp <| qApp ar inp
  termination_by runReader q x => 1
  decreasing_by sorry

end effW
