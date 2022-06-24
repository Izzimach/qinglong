import Lean
import Lean.Parser.Term
import QingLong.Data.IndexedMonad

open IndexedMonad
open IndexedMonad.IxMonad
open Lean Elab Command Term Meta 

namespace SumMacro


class Prismatic (e : Type → Type) (u : Type → Type v) where
    inject : e α → u α
    project : u α → Option (e α)

def sumCtorName : Syntax → Syntax → Name := fun sumid subid => sumid.getId ++ Name.appendBefore subid.getId "select"

def elabSumI (sumid : Syntax) (subids : Syntax.SepArray sep) : CommandElabM Unit := do
    let subvals : Array Syntax := subids
    let toCtor : Syntax → CommandElabM CtorView := 
      fun subid => do
        let ty ← `({x : Type} → $subid x → $sumid x)
        pure { ref := default,
                inferMod := false,
                modifiers := default,
                declName := sumCtorName sumid subid,
                binders := Syntax.missing,
                type? := ty
                }
    let subCtors : Array CtorView ← Array.sequenceMap subvals toCtor
    let iv1 := { ref := default,
                  modifiers := {docString? := "argh"},
                  shortDeclName := sumid.getId,
                  declName      := sumid.getId,
                  levelNames := [],
                  binders := Syntax.missing,
                  type? := (← `(Type → Type 1)),
                  ctors := subCtors,
                  derivingClasses := #[]
                  }
    let x := #[iv1]
    elabInductiveViews x

elab "mkSumI" sumid:ident " o: " subids:ident,+ ":o" : command => elabSumI sumid subids



def elabPrismatic (sumid : Syntax) (subid: Syntax) : CommandElabM Unit := do
    let ctorName : Syntax := Lean.mkIdent <| sumCtorName sumid subid
    let instanceCmd ←
      `(instance  : Prismatic $subid $sumid where
          inject := fun sx => $ctorName sx
          project := fun bx => match bx with 
                                | $ctorName sx => Option.some sx
                                | _ => Option.none)
    elabCommand instanceCmd

elab "mkPrismatic" sumid:ident subid:ident : command => elabPrismatic sumid subid



def elabCollapse (collapserid : Syntax) (collapsermonad : Syntax) (sumid : Syntax) (subids: Syntax.SepArray sep) (collapsers : Syntax.SepArray sep) : CommandElabM Unit := do
    let evalBranch : (Syntax × Syntax) → CommandElabM Syntax := fun ⟨subval, collapser⟩ => do
      let ctorName := Lean.mkIdent <| sumCtorName sumid subval
      `(Parser.Term.matchAltExpr| | $ctorName x => $collapser x)
    let branches ← Array.sequenceMap (Array.zip ↑subids collapsers) evalBranch
    let cDef ← `(def $collapserid {α : Type} (sumVal : $sumid α) : $collapsermonad α := match sumVal with $branches:matchAlt*)
    elabCommand cDef
    logInfo "made collapser"

elab "mkCollapser" collapserid:ident collapsermonad:ident sumid:ident subids:ident,+ " [: " collapsers:term,+ " :] " : command =>
    elabCollapse collapserid collapsermonad sumid subids collapsers



inductive SomeI (x : Type) : Type where
  | A : x → SomeI x
  | B : x → SomeI x
    deriving Repr

inductive OtherI (y : Type) where
  | A : y → OtherI y
  | C : y → y → OtherI y
    deriving Repr

mkSumI Argh o: SomeI,OtherI :o
mkPrismatic Argh SomeI
mkPrismatic Argh OtherI
mkCollapser blargh IO Argh SomeI,OtherI
    [:
      (fun s => match s with 
                | SomeI.A z => pure z
                | SomeI.B z => pure z),
      (fun o => match o with
                | OtherI.A y => pure y
                | OtherI.C a b => pure b)
    :]

def aVal : Argh Nat := Prismatic.inject <| SomeI.A 3

#print Argh
#check Argh.selectSomeI (SomeI.A 3)
#check @Prismatic.inject SomeI Argh _ Nat (SomeI.A 3) 
#check (Prismatic.inject (SomeI.A 3) : Argh Nat)
#check blargh aVal



def genCollapse (vals : List Syntax) : MetaM Syntax := do
    match vals with
    | List.cons h t => let pt ← genCollapse t
                       `(List.cons $h $pt)
    | List.nil      => `(List.nil)

def elabSumX (ts : Syntax.SepArray sep) : TermElabM Expr := do
    let tsa : Array Syntax := ts
    logInfo "argh"
    match tsa with
    | Array.mk vals => let collapseStx ← (genCollapse vals)
                       elabTerm collapseStx Option.none

elab "mkSumX " ts:ident,+ " ←| " : term => elabSumX ts



#check mkSumX SomeI, OtherI ←|

#eval `(Nat → String) >>= fun x => elabTerm x Option.none >>= fun z => liftMetaM (ppExpr z)

end SumMacro
