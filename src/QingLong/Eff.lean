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



mutual

inductive EffX (r : List Type) : Type → Type 1 where
| Pure : a → EffX r a
| Impure : (e : Type) → Union r x → ArrsX r x a → EffX r a

-- ArrsX r a b := FTCQueue (EffX r) a b
inductive ArrsX (r : List Type) : Type → Type → Type 1 where
| Leaf : (a → EffX r b) → ArrsX r a b
| Node : (e : Type) → ArrsX r a e → ArrsX r e b → ArrsX r a b

end --mutual

section

variable {r : List Type} {α : Type} {β : Type} {γ : Type}

def tsingleton (f : α → EffX r β) : ArrsX r α β := ArrsX.Leaf f

def snoc (q : ArrsX r a γ) (f : γ → EffX r b) : ArrsX r a b := ArrsX.Node γ q (ArrsX.Leaf f)

def append (q1 : ArrsX r a x) (q2 : ArrsX r x b) : ArrsX r a b := ArrsX.Node x q1 q2

end

syntax term "|→" term : term
macro_rules
  | `($s |→ $t) => `(snoc $s $t)

syntax term "><" term : term
macro_rules
  | `($s >< $t) => `(append $s $t)




inductive ViewLL (r : List Type) : Type → Type → Type 1 where
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


end effW