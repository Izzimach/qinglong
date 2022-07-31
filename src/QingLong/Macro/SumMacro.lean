import Lean
import Lean.Parser.Term

open Lean Elab Command Term Meta 

namespace SumMacro

-- The Prismatic class lets you move between a sum type and its subtypes
-- For instance if you had a sum type X := A | B then
--  > inject goes from A → X or B → X
--  > project goes from X → Option A or X → Option B
class Prismatic (e : Type → Type) (u : Type → Type v) where
    inject : e α → u α
    project : u α → Option (e α)

-- Given a sum type we need a way to label each branch of the sum type.
-- For example given X := A | B we need to generate contructors for A and B.
-- For normal sum types these are usually Left and Right, but one reason to use
-- macros is so that the names are a little more readable.
-- Typically the subtype name is just the name of the subtype, assuming
-- the subtype is just an identifier indicating some type. However, you can
-- actually pass in an expression as a subtype. We need a way to generate
-- an ID for that expression that is (mostly) unique and also repeatable
-- for that expression (thus we can't just generate random names).
partial
def compileSubId : Syntax → Name := fun subterm =>
    match subterm with
    | .missing => "missing_"
    | .node info kind args =>
        if kind == strLitKind
        then compileSubId args[0]
        -- ignore parenthesis
        else if kind == ``Lean.Parser.Term.paren
        then compileSubId args[1]
        -- for parameterized types we merge the function and its argument
        else if kind == ``Lean.Parser.Term.app
        then
            let fName := compileSubId args[0]
            let argNames := compileSubId args[1]
            fName ++ argNames
        -- if we didn't handle the term already we just punt and try
        -- to fold together all the sub nodes, ignoring null or empty values
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

-- to generate the sum type we basically need to generate constructors for each subtype
-- and then tie it all together with an inductive view.
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
    let indView := {
        ref := default,
        modifiers := {docString? := "argh"},
        shortDeclName := sumid.getId,
        declName      := sumid.getId,
        levelNames := [],
        binders := Syntax.missing,
        type? := (← `(Type → Type 1)),
        ctors := subCtors,
        derivingClasses := #[]
        }
    elabInductiveViews #[indView]

-- you can make the sum type directly using mkSumI but typically you use
-- mkSumType which also generates prismatic instances
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


elab "mkSumType" sumid:ident " >| " subids:term,+ " |< " : command => do
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
