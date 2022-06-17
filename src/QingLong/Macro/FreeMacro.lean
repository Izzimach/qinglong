-- Free monad implemented using macros

import Lean
import Lean.Parser

open Lean Elab Command Term Meta 
open Parser.Term


namespace FreeMacro

inductive FreeL (α : Type) : Type where
| Pure : α → FreeL α
| Impure : List (FreeL α) → FreeL α



def mapL {α : Type} (f : α → β) : FreeL α → FreeL β
| FreeL.Pure a => FreeL.Pure (f a)
| FreeL.Impure List.nil => FreeL.Impure List.nil
| FreeL.Impure (List.cons h t) =>
    let ti := mapL f (FreeL.Impure t)
    match ti with
    | FreeL.Pure b => FreeL.Pure b
    | FreeL.Impure t' => FreeL.Impure (List.cons (mapL f h) t')

set_option hygiene false in
macro "mkFree" freeName:ident f:ident : command =>
  `(inductive $freeName (α : Type u) : Type (u + 1) where 
    | Pure : α → $freeName α 
    | Impure : $f α → $freeName α)

class WfSize (x : Type) where
  wfSize : x → Nat

class WfSubSize (w : Type → Type) where
  wfSubSizeMap : {α β : Type} → [WfSize α] → [WfSize (w α)] → (x : w α) → (f : (a : α) → ( WfSize.wfSize a < WfSize.wfSize x) → β) → w β

def listSizeOf {α : Type} [SizeOf α] : List α → Nat
| List.nil => 1
| List.cons h t => sizeOf h + listSizeOf t

instance [WfSize α ] : WfSize (List α) where
  wfSize := listSizeOf

#print Prod.lex
instance : WfSubSize List where
  wfSubSizeMap :=
    fun l f => match l with
               | List.nil => List.nil
               | List.cons h t => have p : sizeOf h < listSizeOf l := by {}
                                  _
  
set_option hygiene false in
macro "mkFreeSz" freeName:ident f:ident : command => do
  let c1c : Syntax := Lean.mkIdent (freeName.getId ++ "Pure")
  let c2c : Syntax := Lean.mkIdent (freeName.getId ++ "Impure")
  let c1pat ← `(matchAltExpr| | $c1c a  => 1)
  let c2pat ← `(matchAltExpr| | $c2c fa => sizeOf fa + 1)
  let branches := #[c1pat,c2pat]
  `(def arghSz : ($freeName α) → Nat :=
      fun x =>
        match x with $branches:matchAlt*)

set_option hygiene false in
macro "mkFreeSizeOf" freeName:ident f:ident : command => do
  `(instance [SizeOf ($f ($freeName α))] : SizeOf ($freeName α) where
      sizeOf := arghSz)


mkFree argh List
mkFreeSz argh List
mkFreeSizeOf argh List


set_option hygiene false in
macro "mkFmap" freeName:ident fmapName:ident f:ident : command => do
  let pureCtor : Syntax := Lean.mkIdent (freeName.getId ++ "Pure")
  let impureCtor : Syntax := Lean.mkIdent (freeName.getId ++ "Impure")
  let c1pat ← `(matchAltExpr| | $pureCtor a => $pureCtor <| fab a)
  let c2pat ← `(matchAltExpr| | $impureCtor fa => $impureCtor <| Functor.map ($fmapName fab) fa)
  let branches := #[c1pat,c2pat]
  `(def $fmapName [Functor $f] (fab : α → β) (fTree : $freeName α) : $freeName β :=
      match fTree with $branches:matchAlt*)

def arghMap [Functor List] (fab : α → β) (fTree : argh α) : argh β :=
      match fTree with
      | argh.Pure a => argh.Pure <| fab a
      | argh.Impure x fx next => argh.Impure x fx (fun a => arghMap fab (next a))
    termination_by _ _ ft => sizeOf ft

def arghToW [Functor List] (fab : α → β) (fTree : argh α) : freeW.FreeW listPF α :=
      match fTree with
      | argh.Pure a => freeW.pureFree a
      | argh.Impure fa =>
          let n₁ : listPF.A := List.length fa
          Wtype.W_type.mk ⟨freeW.ZFree.ZImpure, fun _ => n₁⟩  _ --⟨Zfree.ZImpure, List.length fa⟩ Functor.map (fun x => arghMap fab x) fa
    termination_by _ _ ft => sizeOf ft

mkFmap argh arghmap List




set_option hygiene false in
macro "mkFunctor" freeName:ident f:ident : command => do
  let c1c : Syntax := Lean.mkIdent (freeName.getId ++ "Pure")
  let c2c : Syntax := Lean.mkIdent (freeName.getId ++ "Impure")
  let c1pat ← `(matchAltExpr| | $c1c a => $c1c <| f a)
  let c2pat ← `(matchAltExpr| | $c2c fa => $c2c (Functor.map (xm f) fa))
  let branches := #[c1pat,c2pat]
  `(instance [Functor $f] : Functor $freeName where
        map := fmapX
        )

set_option hygiene false in
macro "mkMonad" freeName:ident f:ident : command => do
  let c1c : Syntax := Lean.mkIdent (freeName.getId ++ "Pure")
  let c2c : Syntax := Lean.mkIdent (freeName.getId ++ "Impure")
  let c1pat ← `(matchAltExpr| | $c1c a => f a)
  let c2pat ← `(matchAltExpr| | $c2c fa => $c2c (Functor.map (fun x => bind x f) fa))
  let branches := #[c1pat,c2pat]
  `(instance [Functor $f] [Bind $freeName] : Monad $freeName where
        pure := $c1c
        bind := fun m f => match m with $branches:matchAlt*
        )

mkFunctor argh List
mkMonad argh List

#print argh
#check ((pure 3) : argh Nat)
set_option trace.Meta.synthInstance true
#check (inferInstance : Pure argh)
#print Bind
#print Pure


def test' : TermElabM Expr := do
  let discr ← `(List.get? [1,2,3] 0)
  let x ← `(x)
  let p1 ← `( none )
  let p2 ← `( some $x )
  let br1 ← `(matchAltExpr| | $p1 => 3)
  let br2 ← `(matchAltExpr| | $p2 => x)
  let brs := #[br1, br2]
  let e ← `(match $discr:term with $brs:matchAlt*)
  elabTerm e (some (mkConst `Nat))

#eval show TermElabM _ from do
  let e ← withDeclName `foo test'
  Meta.ppExpr e


#print argh

end FreeMacro
