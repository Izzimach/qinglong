
import QingLong.Data.NamedState
import QingLong.Macro.FreerMacro
import QingLong.Macro.SumMacro

open NamedState
open SumMacro
open Freer


-- Here we build a sum type and freer indexed monad to use. These will eventually get interpreted into a
-- final monad implementing the state and IO
mkSumType ExampleCommand >| (NamedState "z" Nat), IO |<
mkFreer ExampleMonad ExampleCommand

-- some "code" written to use a monad supporting state. This uses the NameState command to increment whatever
-- is in the state labeled "z". m could be ExampleCommand or any other monad that implements (NamedState "z" Nat)
def incZ {m : Type → Type 1} [Sendable (NamedState "z" Nat) m] [Monad m] : m Nat := do
    let z ← getNamed "z"
    putNamed "z" (z+1)
    pure 3

def exampleX [Monad m] [Sendable IO m] [Sendable (NamedState "x" Nat) m]: m Nat := do
    putNamed "x" 4
    Sendable.send <| IO.println 3
    pure 3


-- A monad with two state variables and IO

mkStateIO OneState (z:Nat), (y:String) @@
/-
#check StateIO
#check OneState Nat
-/

-- The interpreter translates code from the abstract-ish ExampleCommand
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
