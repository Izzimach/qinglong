import Lean
import Lean.Parser.Command
import Lean.Parser.Term

import QingLong.Data.IndexedMonad


-- A general monad to use as the target for a collapser.
-- Usually when running algebraic effects, the monads you end up with are IO and
-- maybe some state. So you can build your collapser to produce a StateIO.

namespace StateIO

open Lean Elab Command Term Meta 
open IndexedMonad

def StateIO (sType : Type) (α : Type) : Type := sType → IO (α × sType)

instance : Monad (StateIO s) where
    pure := fun a s => pure ⟨a, s⟩
    bind := fun m f s => do let ⟨a', s'⟩ ← m s
                            f a' s'

class StateOperator (stateContainer : Type) (name : String) (state : Type) where
    putS : state → stateContainer → stateContainer
    getS : stateContainer → state



structure SomeStuff where (a : Nat) (b : String)

-- should macro-ize these

instance : StateOperator SomeStuff "a" Nat where
    putS := fun v s => {s with a := v}
    getS := fun s => s.a

instance : StateOperator SomeStuff "b" String where
    putS := fun v s => {s with b := v}
    getS := fun s => s.b



set_option hygiene false in
def elabSS (structid : Syntax) (vals : Syntax.SepArray sep) : CommandElabM Unit := do
    let field1 ← `(Lean.Parser.Command.structExplicitBinder| (x : Nat))
    let field2 ← `(Lean.Parser.Command.structExplicitBinder| (y : Nat))
    let fields := #[field1,field2]
    let structDecl ← `(structure $structid where $fields:structExplicitBinder*)
    elabCommand structDecl

elab "mkStateIOStruct" structid:ident vals:ident,+ " @@ " : command => elabSS structid vals

set_option hygiene false in
def elabSI (structid : Syntax) (vals : Syntax.SepArray sep) : CommandElabM Unit := do
  let valArray : Array Syntax := vals
  let valInstance : Syntax → CommandElabM Unit :=
    fun n => do
      let s := Syntax.mkStrLit n.getId.toString
      let c ← `(instance : StateOperator $structid $s Nat where
                  putS := fun v s => { s with $n:ident := v}
                  getS := fun s => s.$n)
      elabCommand c
  Array.forM valInstance valArray

elab "mkStateInterfaces" structid:ident vals:ident,+ " @@ " : command => elabSI structid vals

mkStateIOStruct Blargh x,y @@
mkStateInterfaces Blargh x,y @@

def z : Blargh := { x := 3, y := 6}

#check z

def goP [StateOperator Blargh "x" Nat] : Blargh → Nat := fun b => StateOperator.getS "x" b

#eval goP z


--
-- A monad/effect to read and write from the StateIO.
--
inductive NamedState (n : String) (v : Type) : Type → Type where
  | Get : NamedState n v v
  | Put : v → NamedState n v Unit

def collapseNamedState [StateOperator s n v] : ∀ x, NamedState n v x → StateIO s x :=
  fun x m =>
    match m with
    | .Get => fun s => pure ⟨StateOperator.getS n s,s⟩
    | .Put v' => fun s => pure ⟨(), StateOperator.putS n v' s⟩


def getNamed (n : String) {ix v : Type} {m : Indexer ix → Type → Type 1} [SendableIx (NamedState n v) m] 
  : m (@Indexer.Null ix) v :=
    @send ix (NamedState n v) v m _ <| @NamedState.Get n _

def putNamed (n : String) {ix v : Type} (x : v) {m : Indexer ix → Type → Type 1} [SendableIx (NamedState n v) m]
  : m (@Indexer.Null ix) Unit :=
    @send ix (NamedState n v) Unit m _ <| @NamedState.Put n v x

end StateIO
