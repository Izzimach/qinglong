import Lean

open Lean Elab Command Term Meta 

namespace IndexedMonad

inductive Indexer (x : Type) : Type where
  | Null : Indexer x
  | Leaf : x → Indexer x
  | Append : Indexer x → Indexer x → Indexer x
    deriving Repr

def evalIndexer {ix : Type} [Inhabited ix] [HAdd ix ix ix] : (i : Indexer ix) → ix
  | .Null => default
  | .Leaf x => x
  | .Append a b => evalIndexer a + evalIndexer b


class IxMonad {ix : Type} (m : Indexer ix → Type → Type 1) where
    pureIx : (i : Indexer ix) → α → m i α
    bindIx : m i₁ α → (α → m i₂ β) → m (Indexer.Append i₁ i₂) β

open IxMonad

def getIndex {ix : Type} {i : Indexer ix} {n : Indexer ix → Type → Type 1} [Inhabited ix] [HAdd ix ix ix] : n i α → ix := 
    fun nia => evalIndexer i


syntax:60 term:60 " →→= " term:61 : term   -- >>= for indexed monads
syntax:60 term:60 " →→ "  term:61 : term   -- >>  for indexed monads

macro_rules
| `($l:term →→= $r:term) => `(bindIx $l $r)
| `($l:term →→  $r:term) => `(bindIx $l (fun _ => $r))

def checkedDo (m : Syntax) (ix : Syntax) (a : Syntax) (monad : Syntax) : TermElabM Expr := do
  let pureAdd ← `((@pureIx $ix $m _ Unit .Null ()) →→ $monad →→= (fun (z : $a) => pureIx .Null z))
  let elabResult ← elabTerm pureAdd Option.none
  let mType ← inferType elabResult
  --logInfo mType
  --logInfo elabResult
  --pure mType
  pure elabResult

elab "checkIxDo" m:ident ix:ident a:ident " ∃> " monad:term : term => checkedDo m ix a monad




class SendableIx (b : Type → Type) (n : Indexer ix → Type → Type 1) where
  sendIx : {x : Type} → {i : Indexer ix} → b x → n i x

def send {m : Indexer ix → Type → Type 1} [SendableIx b m] : b α → m Indexer.Null α := 
  fun ba => @SendableIx.sendIx ix b m _ α Indexer.Null ba

def sendIndexed {m : Indexer ix → Type → Type 1} [SendableIx b m] : (i : ix) → b α → m (Indexer.Leaf i) α := 
  fun i ba => @SendableIx.sendIx ix b m _ α (Indexer.Leaf i) ba

def pure0 {m :Indexer ix → Type → Type 1} [IxMonad m] : α → m Indexer.Null α :=
  fun a => IxMonad.pureIx Indexer.Null a

end IndexedMonad
