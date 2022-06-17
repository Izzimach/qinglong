
import QingLong.Data.OpenUnion
import QingLong.W.FreerIxW

open openunion
open FreerIxW




structure SomeStuff where (a : Nat) (b : String)

-- should macro-ize these

instance : StateOperator SomeStuff "a" Nat where
    putNamed := fun v s => {s with a := v}
    getNamed := fun s => s.a

instance : StateOperator SomeStuff "b" String where
    putNamed := fun v s => {s with b := v}
    getNamed := fun s => s.b





inductive BangTracker : Type → Type where
    | Bang : BangTracker Unit


def goBang {s : Type} [StateOperator s "a" Nat] : (α : Type) → BangTracker Unit → StateIO s Unit := fun x b =>
   match b with
   | .Bang => (fun x => (pure <| StateOperator.getNamed "a" x) 
                        >>= fun b => pure <| Prod.mk () (StateOperator.putNamed "a" (b+1) x))

def liftBang [HasEffect BangTracker effs] : FreerIxW (OU effs) ix α := _