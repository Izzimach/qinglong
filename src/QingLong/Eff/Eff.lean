-- extensible effect monad "Eff" based on "Free Monads, More Extensible Effects"
--
-- Most of this is converted from the freer-simple library by Alexis King.
-- Many recursive functions aren't shown to be well-founded, so use with caution.
--
-- The monad is built on "Eff effs α" where effs is a list of effects supported by this monad.

import QingLong.Data.OpenUnion

import Lean
open Lean Elab Command Term --Meta


open OpenUnion

namespace Eff




mutual

inductive Eff (effs : List (Type → Type)) : Type → Type 1 where
    | Pure : α → Eff effs α
    | Impure : (γ : Type) → OU effs γ → Arrs effs γ α → Eff effs α

-- Arrs r a b := FTCQueue (Eff r) a b
inductive Arrs (effs : List (Type → Type)) : Type → Type → Type 1 where
    | Leaf : (a → Eff effs b) → Arrs effs a b
    | Node : (e : Type) → Arrs effs a e → Arrs effs e b → Arrs effs a b

end --mutual

def Arr effs a b := a → Eff effs b

section

variable {r : List (Type → Type)} {α : Type} {β : Type} {γ : Type} {t : Type → Type}

def tsingleton (f : α → Eff r β) : Arrs r α β := Arrs.Leaf f

def snoc (q : Arrs r a γ) (f : γ → Eff r b) : Arrs r a b := Arrs.Node γ q (Arrs.Leaf f)

def append (q1 : Arrs r a x) (q2 : Arrs r x b) : Arrs r a b := Arrs.Node x q1 q2

def send {v : Type} [HasEffect t effs] : t v → Eff effs v :=
    fun tv => Eff.Impure v (HasEffect.inject tv) (tsingleton Eff.Pure)

end

-- used in the freer monads paper

syntax term "|→" term : term
macro_rules
  | `($s |→ $t) => `(snoc $s $t)

syntax term "><" term : term
macro_rules
  | `($s >< $t) => `(append $s $t)



-- O(n) dequeue to put/get monads
inductive ViewLL (r : List (Type → Type)) : Type → Type → Type 1 where
    | VOne : (a → Eff r b) → ViewLL r a b
    | VCons : (e : Type) → (a → (Eff r) e) → Arrs r e b → ViewLL r a b

def tviewL' (y : Arrs r a x) (z : Arrs r x b) : ViewLL r a b :=
    match y with
    | (Arrs.Leaf f) => ViewLL.VCons x f z
    | (Arrs.Node e f q) => tviewL' f (Arrs.Node x q z)

def tviewL : Arrs r a b → ViewLL r a b
    | Arrs.Leaf f => ViewLL.VOne f
    | Arrs.Node e f q => tviewL' f q

-- Application of an effect array
-- this needs well founded proof
-- what a mess
def qApp (q : Arrs r β w) (x : β) : Eff r w :=
    match (tviewL q) with
    | ViewLL.VOne k => k x
    | ViewLL.VCons e k t =>
        match (k x) with
        | Eff.Pure y => qApp t y
        | Eff.Impure e u q => Eff.Impure e u (q >< t)
    termination_by qApp q x => 1
    decreasing_by sorry

-- Append an effect arrow onto the end of an array of effect arrows.
-- Note this also modifies the stack of effects, and is used in handlers.
def qComp (g : Arrs effs a b) (h : Eff effs b → Eff effs' c) : Arr effs' a c :=
    h ∘ qApp g


instance : Monad (Eff r) where
    pure := Eff.Pure
    bind := fun m f =>
      match m with
      | Eff.Pure a => f a
      | Eff.Impure e u ar => Eff.Impure e u (ar |→ f)

-- once you have handled all the effects, all you have left is "Eff [] a" and canuse
-- run to extract the a
def run : Eff [] a → a
    | Eff.Pure a => a

-- A version of run that can be applied to a single monad that is
-- left at the bottom of the effect stack. Usually this is IO
def runM {m : Type → Type} [Monad m] : Eff [m] a → m a
    | Eff.Pure a => pure a
    | Eff.Impure e ou ar => 
        match ou with
        | OU.Leaf mb => mb >>= (fun b => runM <| qApp ar b)
    termination_by runM q => 1
    decreasing_by sorry

-- process the top effect of an effect list. You provide the two functions
-- to handle pure and instances of the effect.
def handleRelay {effs : List (Type → Type)} {eff : Type → Type}
    (handlePure : α → Eff effs β)
    (handleEff : ∀ γ, eff γ → Arr effs γ β → Eff effs β)
    : Eff (eff :: effs) α → Eff effs β 
        | Eff.Pure x => handlePure x
        | Eff.Impure e ou next =>
            let k := qComp next (handleRelay handlePure handleEff) 
            match ou with
            | OU.Leaf me => handleEff e me k
            | OU.Cons c => Eff.Impure _ c (tsingleton k)
    termination_by handleRelay e => 1
    decreasing_by sorry

-- A version of handleRelay that threads state through the handler.
-- Useful for state monads and related effects.
def handleRelayS {effs : List (Type → Type)} {eff : Type → Type} {s : Type}
    (state : s)
    (handlePure : s → α → Eff effs β)
    (handleEff : ∀ γ, s → eff γ → (s → Arr effs γ β) → Eff effs β)
    : Eff (eff :: effs) α → Eff effs β 
        | Eff.Pure x => handlePure state x
        | Eff.Impure e ou next =>
            let k := fun st x => handleRelayS st handlePure handleEff <| qApp next x
            match ou with
            | OU.Leaf me => handleEff e state me k
            | OU.Cons c => Eff.Impure _ c (tsingleton <| k state)
    termination_by handleRelayS e => 1
    decreasing_by sorry

def replaceRelay {effs : List (Type → Type)} {eff eff': Type → Type} {α β : Type}
  (handlePure : α → Eff (eff' :: effs) β)
  (handleEff : ∀ γ, eff γ → Arr (eff' :: effs) γ β → Eff (eff' :: effs) β)
  : Eff (eff :: effs) α -> Eff (eff' :: effs) β
      | Eff.Pure x => handlePure x
      | Eff.Impure e ou next =>
            let k := qComp next (replaceRelay handlePure handleEff) 
            match ou with
            | OU.Leaf me => handleEff _ me k
            | OU.Cons c => Eff.Impure _ (weaken c) (tsingleton k)
    termination_by replaceRelay e => 1
    decreasing_by sorry

-- Alexis had this in freer-simple so we have it here too. Sometimes helps to infer types.
def replaceRelayS {effs : List (Type → Type)} {eff eff': Type → Type} {α β s : Type}
  (state : s)
  (handlePure : s → α → Eff (eff' :: effs) β)
  (handleEff : ∀ γ, s → eff γ → Arr (eff' :: effs) γ β → Eff (eff' :: effs) β)
  : Eff (eff :: effs) α -> Eff (eff' :: effs) β
      | Eff.Pure x => handlePure state x
      | Eff.Impure e ou next =>
            let k := qComp next (replaceRelayS state handlePure handleEff) 
            match ou with
            | OU.Leaf me => handleEff _ state me k
            | OU.Cons c => Eff.Impure _ (weaken c) (tsingleton k)
    termination_by replaceRelayS e => 1
    decreasing_by sorry


def interpretWith {effs : List (Type → Type)} {eff : Type → Type}
    (handleEff: ∀ γ, eff γ → (γ -> Eff effs β) -> Eff effs β)
    : Eff (eff :: effs) β → Eff effs β :=
        fun effVal => handleRelay pure handleEff effVal

def interpret {effs : List (Type → Type)} {eff : Type → Type}
    (handleEff : ∀ γ, (eff γ → Eff effs γ))
    : Eff (eff :: effs) β → Eff effs β :=
        fun effVal => handleRelay pure (fun g ef next => (handleEff g ef) >>= next) effVal

-- transform from one effect to another, leaving the remaining effects unmodified
def reinterpret {effs : List (Type → Type)} {eff eff' : Type → Type} {α : Type}
  (reHandle : ∀ γ, eff γ → Eff (eff' :: effs) γ)
  : Eff (eff :: effs) α → Eff (eff' :: effs) α
  := replaceRelay pure (fun a f next => (reHandle a f) >>= next)

-- transform from one effect to another, leaving the remaining effects unmodified
def reinterpretS {effs : List (Type → Type)} {eff eff' : Type → Type} {α : Type}
  (reHandle : ∀ γ, eff γ → Eff (eff' :: effs) γ)
  : Eff (eff :: effs) α → Eff (eff' :: effs) α
  := replaceRelay pure (fun a f next => (reHandle a f) >>= next)

--
-- Reader effect
--

inductive ReaderE (i : Type) : Type → Type where
    | Ask : ReaderE i i

instance : ShowEff (ReaderE i) where
    effString := "Reader"

def ask [HasEffect (ReaderE i) effs] : Eff effs i := send ReaderE.Ask

def runReader {α : Type} {effs : List (Type → Type)} {i : Type} (inp : i) : Eff (ReaderE i :: effs) α → Eff effs α :=
    interpret (fun γ r => match r with 
                          | ReaderE.Ask => pure inp)


--
-- State effect
--

inductive StateE (s : Type) : Type → Type where
    | Get : StateE s s
    | Put : s → StateE s Unit

def get [HasEffect (StateE s) effs]              : Eff effs s
    := send StateE.Get
def put [HasEffect (StateE s) effs] (putVal : s) : Eff effs Unit
    := send <| StateE.Put putVal


def stateGo {s : Type}  (γ : Type) (state : s) (eff : StateE s γ) (next : s → Arr effs γ (α × s)) : Eff effs (α × s) := 
    match eff with
    | StateE.Get => next state state
    | StateE.Put s' => next s' ()

def runState {α : Type} {effs : List (Type → Type)} {s : Type} (state : s) : Eff (StateE s :: effs) α → Eff effs (α × s) :=
    fun effVal => handleRelayS state (fun s x => pure (x,s)) stateGo effVal


end Eff
