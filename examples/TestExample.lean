import QingLong.Data.IndexedMonad
import QingLong.Data.StateIO
import QingLong.Macro.FreerIxMacro
import QingLong.Macro.SumMacro

open StateIO
open SumMacro
open FreerIx
open IndexedMonad

#check StateIO

mkStateIO OneState (z:Nat) @@

def incZ {m : Indexer ix → Type → Type 1} [SendableIx (NamedState "z" Nat) m] [IxMonad m] :=
  checkIxDo m ix Nat ∃>
    getNamed "z"
    →→= fun b => putNamed "z" (b+1)
    →→ pure0 3

#check incZ

def nState1 := NamedState "z" Nat
mkSumI ExampleMonad o: nState1,IO :o

mkPrismatic ExampleMonad nState1
mkPrismatic ExampleMonad IO
mkCollapser blargh OneState ExampleMonad nState1,IO
    [:
      -- NamedState "z" Nat
      collapseNamedState "z" Nat,
      -- IO
      collapseIO
    :]
