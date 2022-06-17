-- open union for use with Eff

-- This is the old version of OpenUnion which is basically a sum type. It is type-safe but
-- requires O(n) access. Most haskell effect libs produce O(1) access by bypassing the normal type
-- system and tracking types with a Nat or Int index, then using unsafeCoerce when the indices indicate matching types.


import Lean
open Lean Elab Command Term Meta

namespace openunion

class ShowEff (t : Type → Type) where
    effString : String


def showType (t : Syntax) : TermElabM Expr := do
    let ty ← elabType t
    match ty with
    | Expr.fvar id d   => pure <| mkStrLit <| toString ty --"Fvar " ++ (toString id.name)
    | Expr.app f arg d => pure <| mkStrLit <| "App " ++ toString f ++ " " ++ toString arg
    | _ => pure <| mkStrLit <| Expr.ctorName ty

elab "reflType" t:term : term => showType t



inductive OU : List (Type → Type) → Type → Type 1 where
    | Leaf : t x → OU (t :: effs) x
    | Cons : OU effs x → OU (t :: effs) x

def weaken {effs : List (Type → Type)} {eff : Type → Type} (u : OU effs x) : OU (eff :: effs) x := OU.Cons u

def asStringOU (ou : OU r α) : String :=
    match ou with
    | .Leaf l => "Leaf"
    | .Cons c => "Node/" ++ asStringOU c

instance [ToString x] : ToString (OU r x) where
    toString := asStringOU

class HasEffect (e : Type → Type) (effs : List (Type → Type)) where
    inject : e α → OU effs α
    project : OU effs α → Option (e α)

instance : HasEffect (r : Type → Type) (r :: effs) where
    inject := fun ea => OU.Leaf ea
    project := fun ou => match ou with
                         | OU.Leaf l => Option.some l
                         | OU.Cons c => Option.none

instance [HasEffect r effs] : HasEffect (r : Type → Type) (x :: effs) where
    inject := fun ea => OU.Cons (HasEffect.inject ea)
    project := fun ou => match ou with
                         | OU.Leaf l => Option.none
                         | OU.Cons c => HasEffect.project c





inductive Collapser (m : Type → Type) : List (Type → Type) → Type 1 where
    | End  : Collapser m []
    | Cons : (∀x, t x → m x) → Collapser m effs → Collapser m (t :: effs)

-- this is the annihilation of a sum type with a product type I always heard about
def collapse {x : Type} {m : Type → Type} {effs : List (Type → Type)} (c : Collapser m (effs)) (ou : OU (effs) x) : m x :=
    match c with
    | .Cons alg n =>
        match ou with
        | .Leaf l => alg x l
        | @OU.Cons effs' x _ ou' => collapse n ou'


#check (Collapser.Cons (fun x v => pure (v : Id x)) (Collapser.Cons (fun x io => (io : IO x)) Collapser.End) : Collapser IO [Id, IO])


def genCollapse (vals : List Syntax) : MetaM Syntax := do
    match vals with
    | List.cons h t => let pt ← genCollapse t
                       `(Collapser.Cons $h $pt)
    | List.nil      => `(Collapser.End)

def elabCollapse (ts : Syntax.SepArray sep) : TermElabM Expr := do
    let tsa : Array Syntax := ts
    match tsa with
    | Array.mk vals => let collapseStx ← (genCollapse vals)
                       elabTerm collapseStx Option.none

elab "mkCollapse " ts:term,+ " o> " : term => elabCollapse ts

#check mkCollapse
    (fun x v  => pure (v : Id x)) ,
    (fun x io => (io : IO x))
    o>

def StateIO (sType : Type) (α : Type) : Type := sType → IO (α × sType)

instance : Monad (StateIO s) where
    pure := fun a s => pure ⟨a, s⟩
    bind := fun m f s => do let ⟨a', s'⟩ ← m s
                            f a' s'

class StateOperator (stateContainer : Type) (name : String) (state : Type) where
    putNamed : state → stateContainer → stateContainer
    getNamed : stateContainer → state




end openunion
