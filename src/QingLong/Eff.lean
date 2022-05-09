-- extensible effect monad "Eff" based on "Free Monads, More Extensible Effects"
-- built on top of the W type

import QingLong.PFunctor
import QingLong.Wtype
import QingLong.OpenUnion

import Lean
open Lean Elab Command Term --Meta


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

inductive EffX (effs : List (Type → Type)) : Type → Type 1 where
    | Pure : α → EffX effs α
    | Impure : (γ : Type) → OU effs γ → ArrsX effs γ α → EffX effs α

-- ArrsX r a b := FTCQueue (EffX r) a b
inductive ArrsX (effs : List (Type → Type)) : Type → Type → Type 1 where
    | Leaf : (a → EffX effs b) → ArrsX effs a b
    | Node : (e : Type) → ArrsX effs a e → ArrsX effs e b → ArrsX effs a b

end --mutual

def asString (ar : ArrsX r a b) : String :=
    match ar with
    | ArrsX.Leaf f => "Leaf"
    | ArrsX.Node e l r => "Node, l=" ++ asString l ++ ", r=" ++ asString r


instance [ToString α] : ToString (EffX r α) where
    toString ef := match ef with
                   | EffX.Pure a => "Pure " ++ toString a
                   | EffX.Impure e ou n => "Impure (" ++ (asStringOU ou) ++ ") (" ++ asString n ++ ")"


def Arr effs a b := a → EffX effs b

section

variable {r : List (Type → Type)} {α : Type} {β : Type} {γ : Type} {t : Type → Type}

def tsingleton (f : α → EffX r β) : ArrsX r α β := ArrsX.Leaf f

def snoc (q : ArrsX r a γ) (f : γ → EffX r b) : ArrsX r a b := ArrsX.Node γ q (ArrsX.Leaf f)

def append (q1 : ArrsX r a x) (q2 : ArrsX r x b) : ArrsX r a b := ArrsX.Node x q1 q2

def send {v : Type} [HasEffect t r] : t v → EffX r v :=
    fun tv => EffX.Impure v (HasEffect.inject tv) (tsingleton EffX.Pure)

end

-- used in the freer monads paper

syntax term "|→" term : term
macro_rules
  | `($s |→ $t) => `(snoc $s $t)

syntax term "><" term : term
macro_rules
  | `($s >< $t) => `(append $s $t)




inductive ViewLL (r : List (Type → Type)) : Type → Type → Type 1 where
    | VOne : (a → EffX r b) → ViewLL r a b
    | VCons : (e : Type) → (a → (EffX r) e) → ArrsX r e b → ViewLL r a b

def tviewL' (y : ArrsX r a x) (z : ArrsX r x b) : ViewLL r a b :=
    match y with
    | (ArrsX.Leaf f) => ViewLL.VCons x f z
    | (ArrsX.Node e f q) => tviewL' f (ArrsX.Node x q z)

def tviewL : ArrsX r a b → ViewLL r a b
    | ArrsX.Leaf f => ViewLL.VOne f
    | ArrsX.Node e f q => tviewL' f q

-- Application of an effect array
-- this needs well founded proof
-- what a mess
def qApp (q : ArrsX r β w) (x : β) : EffX r w :=
    match (tviewL q) with
    | ViewLL.VOne k => k x
    | ViewLL.VCons e k t =>
        match (k x) with
        | EffX.Pure y => qApp t y
        | EffX.Impure e u q => EffX.Impure e u (q >< t)
    termination_by qApp q x => 1
    decreasing_by sorry

-- Append an effect arrow onto the end of an array of effect arrows.
-- Note this also modifies the stack of effects, and is used in handlers.
def qComp (g : ArrsX effs a b) (h : EffX effs b → EffX effs' c) : Arr effs' a c :=
    h ∘ qApp g

instance : Monad (EffX r) where
    pure := EffX.Pure
    bind := fun m f =>
      match m with
      | EffX.Pure a => f a
      | EffX.Impure e u ar => EffX.Impure e u (ar |→ f)

-- once you have handled all the effects, all you have left is "Eff [] a" and canuse
-- run to extract the a
def run : EffX [] a → a
    | EffX.Pure a => a

-- A version of run that can be applied to a single monad that is
-- left at the bottom of the effect stack. Usually this is IO
def runM {m : Type → Type} [Monad m] : EffX [m] a → m a
    | EffX.Pure a => pure a
    | EffX.Impure e ou ar => 
        match ou with
        | OU.Leaf mb => mb >>= (fun b => runM <| qApp ar b)
    termination_by runM q => 1
    decreasing_by sorry

-- process the top effect of an effect list. You provide the two functions
-- to handle pure and instances of the effect.
def handleRelay {effs : List (Type → Type)} {eff : Type → Type}
    (handlePure : α → EffX effs β)
    (handleEff : ∀ γ, eff γ → Arr effs γ β → EffX effs β)
    : EffX (eff :: effs) α → EffX effs β 
        | EffX.Pure x => handlePure x
        | EffX.Impure e ou next =>
            let k := qComp next (handleRelay handlePure handleEff) 
            match ou with
            | OU.Leaf me => handleEff e me k
            | OU.Cons c => EffX.Impure _ c (tsingleton k)
    termination_by handleRelay e => 1
    decreasing_by sorry

-- A version of handleRelay that threads state through the handler.
-- Useful for state monads and related effects.
def handleRelayS {effs : List (Type → Type)} {eff : Type → Type} {s : Type}
    (state : s)
    (handlePure : s → α → EffX effs β)
    (handleEff : ∀ γ, s → eff γ → (s → Arr effs γ β) → EffX effs β)
    : EffX (eff :: effs) α → EffX effs β 
        | EffX.Pure x => handlePure state x
        | EffX.Impure e ou next =>
            let k := fun st x => handleRelayS st handlePure handleEff <| qApp next x
            match ou with
            | OU.Leaf me => handleEff e state me k
            | OU.Cons c => EffX.Impure _ c (tsingleton <| k state)
    termination_by handleRelayS e => 1
    decreasing_by sorry


def interpretWith {effs : List (Type → Type)} {eff : Type → Type}
    (handleEff: ∀ γ, eff γ → (γ -> EffX effs β) -> EffX effs β)
    : EffX (eff :: effs) β → EffX effs β :=
        fun effVal => handleRelay pure handleEff effVal


def interpret {effs : List (Type → Type)} {eff : Type → Type}
    (handleEff : ∀ γ, (eff γ → EffX effs γ))
    : EffX (eff :: effs) β → EffX effs β :=
        fun effVal => handleRelay pure (fun g ef next => (handleEff g ef) >>= next) effVal

    
--
-- Reader effect
--

inductive ReaderE (i : Type) : Type → Type where
    | Ask : ReaderE i i

instance : ShowEff (ReaderE i) where
    effString := "Reader"

def ask [HasEffect (ReaderE i) effs] : EffX effs i := send ReaderE.Ask

def runReader {α : Type} {effs : List (Type → Type)} {i : Type} (inp : i) : EffX (ReaderE i :: effs) α → EffX effs α :=
    interpret (fun γ r => match r with 
                          | ReaderE.Ask => pure inp)

def addGet : Nat → EffX [ReaderE Nat] Nat :=
    fun x => ask >>= fun i => pure (i+x)

#eval run <| runReader 10 <| addGet 2


--
-- State effect
--

inductive StateE (s : Type) : Type → Type where
    | Get : StateE s s
    | Put : s → StateE s Unit

def get [HasEffect (StateE s) effs]              : EffX effs s   := send StateE.Get
def put [HasEffect (StateE s) effs] (putVal : s) : EffX effs Unit := send <| StateE.Put putVal


def stateGo {s : Type}  (γ : Type) (state : s) (eff : StateE s γ) (next : s → Arr effs γ (α × s)) : EffX effs (α × s) := 
    match eff with
    | StateE.Get => next state state
    | StateE.Put s' => next s' ()

def runState {α : Type} {effs : List (Type → Type)} {s : Type} (state : s) : EffX (StateE s :: effs) α → EffX effs (α × s) :=
    fun effVal => handleRelayS state (fun s x => pure (x,s)) stateGo effVal




end effW
