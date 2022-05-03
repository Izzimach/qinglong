-- extensible effect monad "Eff" based on "Free Monads, More Extensible Effects"
-- built on top of the W type

import QingLong.PFunctor
import QingLong.Wtype

open pfunctor
open Wtype

namespace effW

inductive Union (effs : List Type) (x : Type) : Type where
| mk : x → Union effs x

class HasEffect (t : Type → Type) (effs : List Type) where
   inject  : t v → Union effs v
   project : Union r v → Option (t v)


inductive ZEffPF (g : Type → Type) (α : Type) : Type 1 where
  | ZPure : α → ZEffPF g α 
  | ZImpure : (x : Type) → g x → ZEffPF g α -- the (x → W ..) part is in the second part of the pfunctor

-- a quick hack to switch type levels
inductive tBump (x : Type) : Type 1
| mk : x → tBump x

def untBump : (tBump x) → x
| tBump.mk x => x


def ZEffBranch {g : Type → Type} {α : Type} : ZEffPF g α → Type
  | ZEffPF.ZPure a => Fin 0 -- can't use False since we need a Type here, not a Prop
  | @ZEffPF.ZImpure g α x gx => x

-- polynomial functor for Eff - combine with W to make a recursive structure
def EffPF (g : Type → Type) (α : Type) : pfunctor := pfunctor.mk (ZEffPF g α) (fun x => tBump <| ZEffBranch x)

def EffW (g : Type → Type) (α : Type) : Type 1 := W (EffPF g α)

def pureEff {α : Type} (a : α) : EffW g α := W.mk ⟨ZEffPF.ZPure a, (fun ux => Fin.elim0 (untBump ux))⟩

def bindEff {α β : Type} (m1 : EffW g α) (m2 : α → EffW g β) : EffW g β :=
  match m1 with
  | ⟨ZEffPF.ZPure a,     _⟩ => m2 a
  | ⟨ZEffPF.ZImpure x gx, bx⟩ => W.mk ⟨ZEffPF.ZImpure x gx, fun x => bindEff (bx x) m2⟩

instance : Monad (EffW g) where
    pure := pureEff
    bind := bindEff





inductive FTCQueue (m : Type → Type 1) : Type → Type →  Type 1 where
  | Leaf : (a → m b) → FTCQueue m a b
  | Node : {x : Type} → FTCQueue m a x → FTCQueue m x b → FTCQueue m a b

-- use a section here to avoid writing a lot of implicit parameters
section

variable (m : Type → Type 1) (a b x : Type)

def tsingleton (x : a → m b) : FTCQueue m a b := FTCQueue.Leaf x

def snoc (q : FTCQueue m a x) (f : x → m b) : FTCQueue m a b := FTCQueue.Node q (FTCQueue.Leaf f)

def append (q1 : FTCQueue m a x) (q2 : FTCQueue m x b) : FTCQueue m a b := FTCQueue.Node q1 q2

end

syntax term "|→" term : term
macro_rules
  | `($s |> $t) => `(snoc $s $t)

syntax term "><" term : term
macro_rules
  | `($s >< $t) => `(append $s $t)

-- left view deconstruction of FTCQueue
inductive ViewL (m : Type → Type 1) : Type → Type → Type 1 where
  | VOne : (a → m b) → ViewL m a b
  | VCons : {x : Type} → (a → m x) → FTCQueue m x b → ViewL m a b

def tview1' : FTCQueue m a x → FTCQueue m x b → ViewL m a b
  | (FTCQueue.Leaf f),    q2 => ViewL.VCons f q2
  | (FTCQueue.Node f q),  q2 => tview1' f (FTCQueue.Node q q2)

def tview1 : FTCQueue m a b → ViewL m a b
  | FTCQueue.Leaf f => ViewL.VOne f
  | FTCQueue.Node f q => tview1' f q

def Arrs r a b := FTCQueue (EffW r) a b
def Arr (r : Type → Type) (a b : Type) : Type 1 := a → EffW r b



mutual

inductive EffX (r : List Type) : Type → Type 1 where
| Pure : a → EffX r a
| Impure : (e : Type) → Union r x → ArrsX r x a → EffX r a

-- ArrsX r a b := FTCQueue (EffX r) a b
inductive ArrsX (r : List Type) : Type → Type → Type 1 where
| Leaf : (a → EffX r b) → ArrsX r a b
| Node : (e : Type) → ArrsX r a e → ArrsX r e b → ArrsX r a b

end --mutual

def snocX (q : ArrsX r a x) (f : x → EffX r b) : ArrsX r a b := ArrsX.Node x q (ArrsX.Leaf f)

def appendX (q1 : ArrsX r a x) (q2 : ArrsX r x b) : ArrsX r a b := ArrsX.Node x q1 q2

#check @ArrsX.below

def ArrX {x : Type} (r : List Type) (a b : Type) : Type 1 := a → EffX r b

def singleK {r : List Type} (arr : a → EffX r b) : ArrsX r a b := ArrsX.Leaf arr

inductive ViewLL (r : List Type) : Type → Type → Type 1 where
  | VOne : (a → (EffX r) b) → ViewLL r a b
  | VCons : (e : Type) → (a → (EffX r) e) → ArrsX r e b → ViewLL r a b


-- needs well founded proof
def tviewL' (y : ArrsX r a x) (z : ArrsX r x b) : ViewLL r a b :=
  match y with
  | (ArrsX.Leaf f) => ViewLL.VCons x f z
  | (ArrsX.Node e f q) => tviewL' f (ArrsX.Node x q z)
  termination_by tviewL' y z => 1
  decreasing_by sorry
  
  --| (ArrsX.Leaf f),    q2 => ViewLL.VCons f q2
  --| (ArrsX.Node f q),  q2 => tviewL' f (ArrsX.Node q q2)

def tviewL : ArrsX r a b → ViewLL r a b
  | ArrsX.Leaf f => ViewLL.VOne f
  | ArrsX.Node e f q => tviewL' f q


def qApp (q : ArrsX r β w) (x : β) : EffX r w :=
  let bind' {α : Type} : EffX r α → ArrsX r α w → EffX r w :=
    fun ef ar => match ef with
                 | EffX.Pure y => @qApp r α w ar y
                 | EffX.Impure e u q => EffX.Impure e u (appendX q ar)
  match (tviewL q) with
  | ViewLL.VOne k => k x
  | ViewLL.VCons e k t => bind' (k x) t
  termination_by qApp q x => 1
  decreasing_by sorry

-- what a mess
instance : Monad (EffX r) where
  pure := EffX.Pure
  bind := fun m f =>
    match m with
    | EffX.Pure a => f a
    | EffX.Impure e u ar => EffX.Impure e u (snocX ar f)


end effW