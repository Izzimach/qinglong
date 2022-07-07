import Lean
import Lean.Parser.Command
import Lean.Parser.Term

/-
 A general monad to use as the target for a collapser.
 Usually when running algebraic effects, the monads you end up with are IO and
 maybe some state. So you can build your collapser to produce a StateIO.

 To use:

 > mkStateIO Blargh (z:Nat),(y:String) @@

 Makes a datatype of type "StateIO Blarghstruct" where Blarghstruct is a struct with fields { z:Nat, y:String }

 You'll also need to make a sum type and freer monad (or some equivalent construct):

 > mkSumType ExampleCommand >| (NamedState "z" Nat), IO |<
 > mkFreer ExampleMonad ExampleCommand

 Then in the collapser you can use "collapseNamedState" for example:

 > def interpreter1 := buildInterpreter ExampleCommand OneState (NamedState "z" Nat),IO
 >   [:
 >     collapseNamedState "z" Nat,
 >     collapseIO
 >   :]

-/

namespace StateIO

open Lean Elab Command Term Meta 

def StateIO (sType : Type) (α : Type) : Type := sType → IO (α × sType)

instance : Monad (StateIO s) where
    pure := fun a s => pure ⟨a, s⟩
    bind := fun m f s => do let ⟨a', s'⟩ ← m s
                            f a' s'

class StateOperator (stateContainer : Type) (name : String) (state : Type) where
    putS : state → stateContainer → stateContainer
    getS : stateContainer → state

set_option hygiene false in
def elabSS (structid : Syntax) (vals : Syntax.SepArray sep) : CommandElabM Unit := do
    let valArray : Array Syntax := vals
    let valInstance : Syntax → CommandElabM Syntax :=
      fun n => do
        let id := n.getArgs[1]
        let ftype := n.getArgs[3]
        let s := Syntax.mkStrLit id.getId.toString
        let c ← `(Lean.Parser.Command.structExplicitBinder | ($id : $ftype))
        pure c
    let fields ← Array.sequenceMap valArray valInstance
    let structDecl ← `(structure $structid where $fields:structExplicitBinder*)
    elabCommand structDecl

declare_syntax_cat structfield
syntax " ( " ident " : " term " ) " : structfield

elab "mkStateIOStruct" structid:ident vals:structfield,+ " @@ " : command => elabSS structid vals

set_option hygiene false in
def elabSI (structid : Syntax) (vals : Syntax.SepArray sep) : CommandElabM Unit := do
  let valArray : Array Syntax := vals
  let valInstance : Syntax → CommandElabM Unit :=
    fun n => do
      let id := n.getArgs[1]
      let ftype := n.getArgs[3]
      let s := Syntax.mkStrLit id.getId.toString
      let c ← `(instance : StateOperator $structid $s $ftype where
                  putS := fun v s => { s with $id:ident := v}
                  getS := fun s => s.$id)
      elabCommand c
  Array.forM valInstance valArray

elab "mkStateInterfaces" structid:ident vals:structfield,+ " @@ " : command => elabSI structid vals

elab "mkStateIO" stateIOname:ident vals:structfield,+ " @@ " : command => do
    let structid : Syntax := Lean.mkIdent <| Name.appendAfter stateIOname.getId "struct"
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

--
-- A monad/effect to read and write from the StateIO.
--
inductive NamedState (n : String) (v : Type) : Type → Type where
  | Get : NamedState n v v
  | Put : v → NamedState n v Unit

def collapseNamedState (n : String) (v : Type) [StateOperator s n v] {α : Type} : NamedState n v α → StateIO s α :=
  fun m =>
    match m with
    | .Get => fun s => pure ⟨StateOperator.getS n s,s⟩
    | .Put v' => fun s => pure ⟨(), StateOperator.putS n v' s⟩

def collapseIO : IO α → StateIO ss α :=
    fun o => fun s => Functor.map (fun x => ⟨x,s⟩) o

end StateIO
