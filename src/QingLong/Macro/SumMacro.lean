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

partial
def compileSubId : Syntax → Name := fun subterm =>
    match subterm with
    | .missing => "missing_"
    | .node info kind args =>
        if kind == strLitKind
        then compileSubId args[0]
        else if kind == ``Lean.Parser.Term.paren
        then compileSubId args[1]
        else if kind == ``Lean.Parser.Term.app
        then
            let fName := compileSubId args[0]
            let argNames := compileSubId args[1]
            fName ++ argNames
        else if args.size > 0
        then Array.foldl (fun x y => 
                              let y' := compileSubId y
                              if x == ""
                              then compileSubId y
                              else if y' == "null"
                              then x
                              else x ++ y') "" args
        else if kind == `null
        then "null"
        else toString kind
    | .atom info val => val
    | .ident info rawVal val _ => val
 
def sumCtorName2 : Syntax → Syntax → Name := fun sumid subterm => sumid.getId ++ Name.appendAfter (compileSubId subterm) "select"

/-
elab "bawk" someid:term : command => do
    logInfo someid.getKind
    if someid.getKind == ``Lean.Parser.Term.paren
    then logInfo <| toString someid.getArgs[1]
    logInfo <| toString someid.getArgs[0]
    logInfo <| compileSubId  someid

bawk (NamedState "z" Nat)
#eval sumCtorName2 (Syntax.mkStrLit "z")
-/

def elabSumI (sumid : Syntax) (subids : Syntax.SepArray sep) : CommandElabM Unit := do
    let subvals : Array Syntax := subids
    let toCtor : Syntax → CommandElabM CtorView := 
      fun subterm => do
        let ty ← `({x : Type} → $subterm x → $sumid x)
        pure { ref := default,
                inferMod := false,
                modifiers := default,
                declName := sumCtorName2 sumid subterm,
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

elab "mkSumI" sumid:ident " o: " subids:term,+ ":o" : command => elabSumI sumid subids



def elabPrismatic (sumid : Syntax) (subterm: Syntax) : CommandElabM Unit := do
    let ctorName : Syntax := Lean.mkIdent <| sumCtorName2 sumid subterm
    let instanceCmd ←
      `(instance  : Prismatic $subterm ($sumid) where
          inject := fun sx => $ctorName sx
          project := fun bx => match bx with 
                                | $ctorName sx => Option.some sx
                                | _ => Option.none)
    elabCommand instanceCmd

elab "mkPrismatic" sumid:ident subid:term : command => elabPrismatic sumid subid

elab "mkSumType" sumid:ident " >| "subids:term,+ " |< " : command => do
    elabSumI sumid subids
    let mkP := fun subterm => elabPrismatic sumid subterm
    Array.forM mkP (subids : Array Syntax)


def elabCollapse (collapsertarget : Syntax) (sumid : Syntax) (subids: Syntax.SepArray sep) (collapsers : Syntax.SepArray sep) : TermElabM Expr := do
    let evalBranch : (Syntax × Syntax) → TermElabM Syntax := fun ⟨subval, collapser⟩ => do
        let ctorName := Lean.mkIdent <| sumCtorName2 sumid subval
        `(Parser.Term.matchAltExpr| | $ctorName x => $collapser x)
    let branches ← Array.sequenceMap (Array.zip ↑subids collapsers) evalBranch
    let collapserFunc ← `(fun {α : Type} (sumVal : $sumid α) => (match sumVal with $branches:matchAlt* : $collapsertarget α))
    elabTerm collapserFunc Option.none

elab "buildInterpreter" commandtype:ident targetmonad:ident subids:term,+ " [: " collapsers:term,+ " :] " : term =>
    elabCollapse targetmonad commandtype subids collapsers

/-
namespace x

inductive OtherI (y : Type) where
  | A : y → OtherI y
  | C : y → y → OtherI y
    deriving Repr

inductive EcksI (x : Type) (y : Type) where
| X : x → y → EcksI x y
-/
/-
mkSumI Argh o: (EcksI Nat),OtherI :o
mkPrismatic Argh (EcksI Nat)
mkPrismatic Argh OtherI


mkSumType Argh >| EcksI Nat, OtherI |<

def collapserArgh := buildInterpreter Argh IO (EcksI Nat),OtherI
    [:
      (fun s => match s with 
                | EcksI.X x y => pure y),
      (fun o => match o with
                | OtherI.A y => pure y
                | OtherI.C a b => pure b)
    :]


open Prismatic

def aVal : Argh Nat := inject <| EcksI.X 3 4
end x

-/

/-#print Argh
#check Argh.EcksI.Natselect (EcksI.X 3 4)
#check @Prismatic.inject (EcksI Nat) Argh _ Nat (EcksI.X 3 5) 
#check (Prismatic.inject (EcksI.X 3 7) : Argh Nat)
#check blargh aVal
-/

end SumMacro
