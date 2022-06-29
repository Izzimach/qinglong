import QingLong.Data.IndexedMonad
import QingLong.Data.StateIO
import QingLong.Macro.FreerIxMacro
import QingLong.Macro.SumMacro

open StateIO
open SumMacro
open FreerIx
open IndexedMonad

mkStateIO OneState (z:Nat) @@
#check StateIO
#check OneState Nat

mkSumType ExampleCommand >| (NamedState "z" Nat), IO |<

def blargh := buildCollapser OneState ExampleCommand (NamedState "z" Nat),IO
    [:
      -- NamedState "z" Nat
      collapseNamedState "z" Nat,
      -- IO
      collapseIO
    :]

mkFreer ExampleMonad ExampleCommand

def incZ {ix : Type} {m : Indexer ix → Type → Type 1} [SendableIx (NamedState "z" Nat) m] [IxMonad m] :=
  show m _ Nat from   --checkIxDo m ix Nat ∃>
        getNamed "z"
    →→= fun b => putNamed "z" (b+1)
    →→  pure0 3

#check (incZ : ExampleMonad _ Nat)


def gork := ExampleMonad_interpret (@incZ Nat _ _ _) blargh {z := 3}

#check gork
#reduce gork
