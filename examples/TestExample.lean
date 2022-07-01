import QingLong.Data.IndexedMonad
import QingLong.Data.StateIO
import QingLong.Macro.FreerIxMacro
import QingLong.Macro.SumMacro

open StateIO
open SumMacro
open FreerIx
open IndexedMonad

mkStateIO OneState (z:Nat), (y:String) @@
#check StateIO
#check OneState Nat

mkSumType ExampleCommand >| (NamedState "z" Nat), IO |<

mkFreer ExampleMonad ExampleCommand Nat

def incZ {ix : Type} {m : Indexer ix → Type → Type 1} [SendableIx (NamedState "z" Nat) m] [IxMonad m] :=
  show m _ Nat from   --checkIxDo m ix Nat ∃>
        getNamed "z"
    →→= fun b => putNamed "z" (b+1)
    →→  pure0 6004

#check (incZ : ExampleMonad _ Nat)
#eval getIndex (incZ : ExampleMonad _ Nat)


def interpreter1 := buildInterpreter ExampleCommand OneState (NamedState "z" Nat),IO
    [:
      -- NamedState "z" Nat
      collapseNamedState "z" Nat,
      -- IO
      collapseIO
    :]

def gork := runExampleMonad interpreter1
              incZ -- code
              {z := 3, y := "Argh"} -- initial state


#check gork
#reduce gork
