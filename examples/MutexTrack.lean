
--
-- Index for monads to track mutex locking/unlocking
--

import QingLong.Data.IndexedMonad

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

def lockMutex {n : Nat} {m : Indexer (MutexStep n) → Type → Type 1} [SendableIx (MutexCommand n) m] (i : Fin n) 
  : m (Indexer.Leaf (MutexStep.Lock i)) Unit :=
    sendIndexed _ (MutexCommand.command (MutexStep.Lock i))
    
def unlockMutex {n : Nat} {m : Indexer (MutexStep n) → Type → Type 1} [SendableIx (MutexCommand n) m] (i : Fin n) 
  : m (Indexer.Leaf (MutexStep.Unlock i)) Unit :=
    sendIndexed _ (MutexCommand.command (MutexStep.Unlock i))

