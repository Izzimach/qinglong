import Lean

open Lean Elab Command Term Meta 


inductive Indexer (x : Type) : Type where
  | Null : Indexer x
  | Leaf : x → Indexer x
  | Append : Indexer x → Indexer x → Indexer x
    deriving Repr

def evalIndexer {ix : Type} [Inhabited ix] [HAdd ix ix ix] : (i : Indexer ix) → ix
  | .Null => default
  | .Leaf x => x
  | .Append a b => evalIndexer a + evalIndexer b

class ExposeIndex (m : Type → Type 1) (mix : Indexer ix → Type → Type 1) where
  withIndex : m x → mix i x
  withoutIndex : mix i x → m x


def getCtors (typ : Name) : MetaM (List Name) := do
  let env ← getEnv
  match env.find? typ with
  | some (ConstantInfo.inductInfo val) => pure val.ctors
  | _ => pure []


syntax (name := mycs) "cs"  ident  : term 

@[termElab mycs]
def mycselab : TermElab := fun stx typ? =>
  if stx[1].isIdent then do
    let id := stx[1].getId
    let ct ← getCtors id
    match (ct.get? 0) with
    | some c0 => do
      let cVar ← getConstInfoCtor c0
      let ctStr := List.foldl HAppend.hAppend "" <| List.map toString ct
      pure <| mkStrLit ctStr
    | _ => do logInfo "argh"
              throwUnsupportedSyntax
    --elabTerm `($ctStr) typ?
    --pure <| mkStrLit (id.toString)
  else do
    logInfo "unsupported!"
    throwUnsupportedSyntax

inductive SomeI (x : Type) : Type where
| A : x → SomeI x
| B : SomeI x
  deriving Repr

inductive OtherI (y : Type) where
| A 
| C : y → y → OtherI y
  deriving Repr

inductive BothI {ix : Type} (i : Indexer ix) (a : Type) : Type 1 where
| Some : SomeI a → BothI i a
| Other : OtherI a → BothI i a
  deriving Repr

inductive BothI0 {ix : Type} (a : Type) : Type 1 where
| Some : SomeI a → Indexer ix → BothI0 a
| Other : OtherI a → Indexer ix → BothI0 a
  deriving Repr

#check cs SomeI
#check cs OtherI
#check cs BothI
#print SomeI.A


class Sendable (b : Type → Type) (n : Indexer ix → Type → Type 1) where
  send : {x : Type} → {i : Indexer ix} → b x → n i x
  unpack : {x : Type} → {i : Indexer ix} → n i x → Option (b x)

class IxMonad {ix : Type} (m : Indexer ix → Type → Type 1) where
    pureIx : (i : Indexer ix) → α → m i α
    bindIx : m i₁ α → (α → m i₂ β) → m (Indexer.Append i₁ i₂) β
    getIx : m i α → ix

open IxMonad

def getIndex {ix : Type} {i : Indexer ix} {n : Indexer ix → Type → Type 1} [Inhabited ix] [HAdd ix ix ix] : n i α → ix := 
    fun nia => evalIndexer i

instance [Inhabited ix] [HAdd ix ix ix]: IxMonad (@BothI ix) where
    pureIx := fun i a => BothI.Some (SomeI.A a)
    bindIx := fun m f => match m with
                         | BothI.Some (SomeI.A x) => match f x with
                                                     | BothI.Some s => BothI.Some s
                                                     | BothI.Other o => BothI.Other o
                         | _ => BothI.Some (SomeI.B)
    getIx := fun f => getIndex f

open Sendable

instance : Sendable SomeI (@BothI ix) where
  send := fun sx => BothI.Some sx
  unpack := fun bx => match bx with 
                        | BothI.Some sx => Option.some sx
                        | _ => Option.none

def sendNull {m : Indexer ix → Type → Type 1} [Sendable b m] : b α → m Indexer.Null α := 
  fun ba => @Sendable.send ix b m _ α Indexer.Null ba

def sendIndex {m : Indexer ix → Type → Type 1} [Sendable b m] : (i : ix) → b α → m (Indexer.Leaf i) α := 
  fun i ba => @Sendable.send ix b m _ α (Indexer.Leaf i) ba

syntax:60 term:60 " →→= " term:61 : term   -- >>= for indexed monads
syntax:60 term:60 " →→ " term:61 : term   -- >>  for indexed monads

macro_rules
| `($l:term →→= $r:term) => `(bindIx $l $r)
| `($l:term →→  $r:term) => `(bindIx $l (fun _ => $r))


def runBoth {n : Indexer Nat → Type → Type 1} [IxMonad n]  [Sendable SomeI n] :=
       (sendNull <| SomeI.A ())
    →→ (sendNull <| (SomeI.B : SomeI Unit))
    →→ (sendIndex 2 (SomeI.A ()))
    →→ (@pureIx Nat n _ Nat Indexer.Null 3)

def runAuto {n : Indexer Nat → Type → Type 1} [IxMonad n] [Sendable SomeI n] :=
       (@pureIx _ n _ Unit .Null ())
    →→ (sendNull <| SomeI.A ())
    →→ (sendNull <| (SomeI.B : SomeI Unit))
    →→ (sendIndex 2 (SomeI.A ()))
    →→ (pureIx .Null 3)


#eval (@runBoth BothI _ _)
#eval getIndex (@runAuto BothI _ _)

#check elabTerm

def checkedDo (m : Syntax) (ix : Syntax) (a : Syntax) (monad : Syntax) : TermElabM Expr := do
  let pureAdd ← `((@pureIx $ix $m _ Unit .Null ()) →→ $monad →→= (fun (z : $a) => pureIx .Null z))
  let elabResult ← elabTerm pureAdd Option.none
  let mType ← inferType elabResult
  --logInfo mType
  logInfo elabResult
  --pure mType
  pure elabResult

elab "checkIxDo" m:ident ix:ident a:ident " ∃> " monad:term : term => checkedDo m ix a monad

def x {m : Indexer Nat → Type → Type 1} [IxMonad m] [Sendable SomeI m] :=
    checkIxDo m Nat Nat ∃>
        (sendNull <| SomeI.A ())
        →→ (sendIndex 2 (SomeI.A ()))
        →→ (pureIx .Null 3)

#eval getIndex (@x BothI _ _)

def genCollapse (vals : List Syntax) : MetaM Syntax := do
    match vals with
    | List.cons h t => let pt ← genCollapse t
                       `(List.cons $h $pt)
    | List.nil      => `(List.nil)

def elabSumX (ts : Syntax.SepArray sep) : TermElabM Expr := do
    let tsa : Array Syntax := ts
    logInfo "argh"
    --let cx : Constructor := {name := `argh, type := }
    match tsa with
    | Array.mk vals => let collapseStx ← (genCollapse vals)
                       elabTerm collapseStx Option.none

elab "mkSumX " ts:ident,+ " ←| " : term => elabSumX ts

#check mkSumX SomeI, OtherI ←|

def z' := Term.mkConst `Nat.zero

def zx : MetaM Expr := Meta.mkArrow (Lean.mkConst ``Nat) (Lean.mkConst ``String)

def zz : Nat → String := fun _ => "argh"

#eval `(Nat → String) >>= fun x => elabTerm x Option.none >>= fun z => liftMetaM (ppExpr z)

open Lean.Elab.Term in
def whnf' (e : TermElabM Syntax) (md := TransparencyMode.default) : TermElabM Format := do
  let e ← elabTermAndSynthesize (← e) none
  ppExpr (← whnf e)

#eval whnf' `(List.cons "a" List.nil)

def elabSumI (inid : Syntax) (ts : Syntax.SepArray sep) : CommandElabM Unit := do
  let tsa : Array Syntax := ts
  let bd ← `(null)
  let c0 := { ref := default,
              inferMod := false,
              modifiers := default,
              declName := "Blargh",
              binders := Syntax.missing,
              type? := (← `((x : Type) → SomeI x → $inid x))
              }
  let iv1 := { ref := default,
               modifiers := {docString? := "argh"},
               shortDeclName := inid.getId,
               declName := inid.getId,
               levelNames := [],
               binders := Syntax.missing,
               type? := (← `(Type → Type 1)),
               ctors := #[c0],
               derivingClasses := #[]
               }
  let x := #[iv1]
  elabInductiveViews x
  pure ()

elab "mkSumI" inid:ident ts:ident,+ ":∘" : command => elabSumI inid ts

mkSumI Argh SomeI :∘

#print Argh
#check Blargh (SomeI.A 3)

