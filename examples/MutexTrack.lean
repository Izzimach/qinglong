
--
-- Index for monads to track mutex locking/unlocking
--

import QingLong.Data.IndexedMonad

import Lean
import Lean.Parser

open Lean Elab Command Term Meta 
open Parser.Term

open IndexedMonad

inductive MutexStep (maxIndex : Nat) where
| Lock : Fin maxIndex → MutexStep maxIndex
| Unlock : Fin maxIndex → MutexStep maxIndex

inductive MutexSequence (maxIndex : Nat) where
| mk : List (MutexStep maxIndex) → MutexSequence maxIndex

instance : Inhabited (MutexSequence mi) where
    default := MutexSequence.mk []

instance : HAdd (MutexSequence mi) (MutexSequence mi) (MutexSequence mi) where
    hAdd := fun m1 m2 => match m1,m2 with
                         | .mk l1 , .mk l2 => .mk (l1 ++ l2)

inductive MutexCommand (maxIndex : Nat) (a : Type) where
| command : MutexStep maxIndex → MutexCommand maxIndex a


variable {n : Nat} {m : Indexer (MutexStep n) → Type → Type 1}


def lockMutex [SendableIx (MutexCommand n) m] (i : Fin n)
  : m (Indexer.Leaf (MutexStep.Lock i)) Unit :=
    sendIndexed _ (MutexCommand.command (MutexStep.Lock i))
    
def unlockMutex [SendableIx (MutexCommand n) m] (i : Fin n) 
  : m (Indexer.Leaf (MutexStep.Unlock i)) Unit :=
    sendIndexed _ (MutexCommand.command (MutexStep.Unlock i))

--
-- Mapping from strings to mutex indices
--
-- A better route might be to embed the name list into MutexCommand type and use
-- existential types to show inclusion, i.e., (MutexCommand (names : ["argh","ack","ugh"]) Unit)
-- and proofs of the form (∃ i, names[i] = "argh") instead of typeclass instances
--

class NamedMutex (name : String) (m : Nat) where
    lockNamed : MutexStep m
    unlockNamed : MutexStep m

def lockNamedMutex [SendableIx (MutexCommand n) m] [NamedMutex "argh" n] (name : String)
  : m (Indexer.Leaf (NamedMutex.lockNamed "argh")) Unit :=
    sendIndexed _ (MutexCommand.command (@NamedMutex.lockNamed "argh" n _))

def unlockNamedMutex [SendableIx (MutexCommand n) m] [NamedMutex "argh" n] (name : String)
  : m (Indexer.Leaf (NamedMutex.unlockNamed "argh")) Unit :=
    sendIndexed _ (MutexCommand.command (@NamedMutex.unlockNamed "argh" n _))


def elabMutexNames (names : List Syntax) (maxIndex : Nat) (curIndex : Nat) : CommandElabM Unit :=
    -- this doesn't seem right
    let maxI : Syntax := Syntax.mkNumLit <| toString maxIndex
    let curI : Syntax := Syntax.mkNumLit <| toString curIndex
    match names with
    | List.nil => pure ()
    | List.cons h t => do
        let instanceCmd ←
          `(instance  : NamedMutex $h $maxI where
              lockNamed := MutexStep.Lock $curI
              unlockNamed := MutexStep.Unlock $curI)
        elabCommand instanceCmd
        elabMutexNames t maxIndex (curIndex+1)

elab "defineMutexNames" vals:term,+ : command => do
    let valList := Array.toList (vals : Array Syntax)
    let maxIndex := List.length valList
    elabMutexNames valList maxIndex 0

defineMutexNames "argh","ack"

#check @NamedMutex.lockNamed "argh" _ _

