import Lean
import QingLong.Data.IndexedMonad

open IndexedMonad
open IndexedMonad.IxMonad
open Lean Elab Command Term Meta 



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

--#print SomeI.A

instance [Inhabited ix] [HAdd ix ix ix]: IxMonad (@BothI ix) where
    pureIx := fun i a => BothI.Some (SomeI.A a)
    bindIx := fun m f => match m with
                         | BothI.Some (SomeI.A x) => match f x with
                                                     | BothI.Some s => BothI.Some s
                                                     | BothI.Other o => BothI.Other o
                         | _ => BothI.Some (SomeI.B)


instance : SendableIx SomeI (@BothI ix) where
  sendIx := fun sx => BothI.Some sx
  unpackIx := fun bx => match bx with 
                        | BothI.Some sx => Option.some sx
                        | _ => Option.none




def x {m : Indexer Nat → Type → Type 1} [IxMonad m] [SendableIx SomeI m] :=
    checkIxDo m Nat Nat ∃>
           (send <| SomeI.A ())
        →→ (sendIndexed 2 (SomeI.A ()))
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

