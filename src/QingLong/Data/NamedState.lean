import Lean
import Lean.Parser.Command
import Lean.Parser.Term

namespace NamedState

open Lean Elab Command Term Meta TSyntax


--
-- A monad to read/write from multiples state variables, using string lookup.
-- As an example if your state is the struct { z : Nat, y : String } then you
-- can (getNamed "y") or (putNamed "z" 3) in your do block.
-- If using algebraic effects you would need something like [Sendable (NamedState "z" Nat) m]
-- to getNamed/putNamed z.
--

inductive NamedState (n : String) (v : Type) : Type → Type where
  | Get : NamedState n v v
  | Put : v → NamedState n v Unit
  
/-
 A general monad to use as the target for a collapser.
 Usually when running algebraic effects, the monads you end up with are IO and
 some state. So you can build your collapser to produce a StateIO which handles both of these cases.

 Lets' say you have a sum type and freer monad or some equivalent construct. Here we make a freer monad with
 two effects, (NamedState "z" Nat α) and (IO α)

 > mkSumType ExampleCommand >| (NamedState "z" Nat), IO |<
 > mkFreer ExampleMonad ExampleCommand

 This has two sendable instances, IO and (NamedState "z" Nat).

 To interpret this we make a StateIO monad as the final target monad:

 > mkStateIO Blargh (z:Nat),(y:String) @@

 this makes a datatype of type "StateIO Blarghstruct" where Blarghstruct is a struct with fields { z:Nat, y:String }

 Then in the interpreter you can use "collapseNamedState" for example:

 > def interpreter1 := buildInterpreter ExampleCommand OneState (NamedState "z" Nat),IO
 >   [:
 >     collapseNamedState "z" Nat,
 >     collapseIO
 >   :]

-/


def StateIO (sType : Type) (α : Type) : Type := sType → IO (α × sType)

instance : Monad (StateIO s) where
    pure := fun a s => pure ⟨a, s⟩
    bind := fun m f s => do let ⟨a', s'⟩ ← m s
                            f a' s'

class StateOperator (stateContainer : Type) (name : String) (state : Type) where
    putS : state → stateContainer → stateContainer
    getS : stateContainer → state

-- Normally a state monad has a single variable that you access using get/put.
-- This builds a structure representing state, with several fields in it. Each field "x"
-- is a single state that is accessed using putNamed "x"/getNamed "x".
set_option hygiene false in
def elabSS (structid : TSyntax `Lean.Parser.Command.declId) (vals : Syntax.TSepArray `structfield ",") : CommandElabM Unit := do
    let valArray : Array (TSyntax `structfield) := vals
    let valInstance : TSyntax `structfield → CommandElabM (TSyntax `Lean.Parser.Command.structExplicitBinder) :=
      fun n => do
        let id : Ident := TSyntax.mk <| n.raw.getArgs[1]!
        let ftype : Term := TSyntax.mk <| n.raw.getArgs[3]!
        let c ← `(Lean.Parser.Command.structExplicitBinder | ($id : $ftype))
        pure c
    let fields ← Array.sequenceMap valArray valInstance
    let structDecl ← `(structure $structid where $fields:structExplicitBinder*)
    elabCommand structDecl

declare_syntax_cat structfield
syntax " ( " ident " : " term " ) " : structfield

elab "mkStateIOStruct" structid:ident vals:structfield,+ " @@ " : command => elabSS structid vals

-- This makes instances of StateOperator for a particular state container (a structure) and a named
-- field of that structure. There should be an instance generated for each field of the structure.
set_option hygiene false in
def elabSI (structid :Term) (fields : Syntax.TSepArray `structfield ",") : CommandElabM Unit := do
  let fieldArray : Array (TSyntax `structfield) := fields
  let fieldInstance : TSyntax `structfield → CommandElabM Unit :=
    fun n => do
      let id := TSyntax.mk n.raw.getArgs[1]!
      let ftype : Term := TSyntax.mk n.raw.getArgs[3]!
      let s := Syntax.mkStrLit id.getId.toString
      let c ← `(instance : StateOperator $structid $s $ftype where
                  putS := fun v s => { s with $id:ident := v}
                  getS := fun s => s.$id)
      elabCommand c
  Array.forM fieldInstance fieldArray

elab "mkStateInterfaces" structid:term vals:structfield,+ " @@ " : command => elabSI structid vals

-- Makes a complete set of definitions for a StateIO monad, including:
--  A structure with fields to hold all the named states
--  Instances of StateOperator to get/put state
--  A Monad instance
-- You provide the monad name and field names/types.  For a StateIO monad named "x" there is also
-- a State structure named "xstruct" which you can use.
elab "mkStateIO" stateIOname:ident vals:structfield,+ " @@ " : command => do
    let structid : Ident := Lean.mkIdent <| Name.appendAfter stateIOname.getId "struct"
    elabSS structid vals
    elabSI structid vals
    let siodef ← `(def $stateIOname := StateIO $structid)
    elabCommand siodef
    let c ←
        `(instance : Monad $stateIOname where
              pure := fun a s => pure ⟨a, s⟩
              bind := fun m f s => do let ⟨a', s'⟩ ← m s
                                      f a' s')
    elabCommand c


--mkStateIOStruct Blargh (z:Nat),(y:String) @@
--mkStateInterfaces Blargh (z:Nat),(y:String) @@

/-
mkStateIO Blargh (z:Nat),(y:String) @@

def testStruct : Blarghstruct := { z := 3, y := "argh"}

#check testStruct
def goP [StateOperator Blarghstruct "z" Nat] : Blarghstruct → Nat := fun b => StateOperator.getS "z" b
#eval goP testStruct
-/


-- When running the interpreter for a Freer monad that has one or more named state, you typically collapse
-- the monad into a StateIO monad.  For each effect that is a NamedState you can use collapseNamedState.
def collapseNamedState (n : String) (v : Type) [StateOperator s n v] {α : Type} : NamedState n v α → StateIO s α :=
  fun m =>
    match m with
    | .Get => fun s => pure ⟨StateOperator.getS n s,s⟩
    | .Put v' => fun s => pure ⟨(), StateOperator.putS n v' s⟩

-- When running the interpreter for a Freer monad that has one or more named state, you typically collapse
-- the monad into a StateIO monad.  If you have an effect that represents arbitrary IO you can collapse it with collapseIO.
def collapseIO : IO α → StateIO ss α :=
    fun o => fun s => Functor.map (fun x => ⟨x,s⟩) o

end NamedState
