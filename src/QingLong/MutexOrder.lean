/- A monad to enforce specific lock/unlock ordering of mutexes, to avoid deadlocking -/

universe u



def MutexPoolSize : Type := { x : Nat // x ≠ 0 }


def LockedSet : Type := List String

def MutexOrderM (poolSize : MutexPoolSize) (lk : LockedSet) (α : Type) : Type := α


def lockMutex (lockId : String) : 