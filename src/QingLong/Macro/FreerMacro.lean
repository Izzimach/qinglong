
import Lean
import Lean.Parser

import QingLong.Data.IndexedMonad

open Lean Elab Command Term Meta 
open Parser.Term

set_option hygiene false in
macro "mkFreerInductive" freerName:ident f:ident : command =>
  `(inductive $freerName (α : Type u) : Type (u + 1) where 
      | Pure : α → $freerName α 
      | Impure : {x : Type} → $f x → (x → $freerName α) → $freerName α)


set_option hygiene false in
macro "mkFmap" freerName:ident fmapName:ident f:ident : command => do
  let pureCtor : Syntax := Lean.mkIdent (freerName.getId ++ "Pure")
  let impureCtor : Syntax := Lean.mkIdent (freerName.getId ++ "Impure")
  let c1pat ← `(matchAltExpr| | $pureCtor a => $pureCtor <| fab a)
  let c2pat ← `(matchAltExpr| | $impureCtor fx next => $impureCtor fx (fun z => $fmapName fab (next z)))
  let branches := #[c1pat,c2pat]
  `(def $fmapName [Functor $f] (fab : α → β) (fTree : $freerName α) : $freerName β :=
       match fTree with $branches:matchAlt*)


set_option hygiene false in
macro "mkFFunctor" freeName:ident fmapName:ident f:ident : command => do
  let c1c : Syntax := Lean.mkIdent (freeName.getId ++ "Pure")
  let c2c : Syntax := Lean.mkIdent (freeName.getId ++ "Impure")
  let c1pat ← `(matchAltExpr| | $c1c a => $c1c <| f a)
  let c2pat ← `(matchAltExpr| | $c2c fa => $c2c (Functor.map (xm f) fa))
  let branches := #[c1pat,c2pat]
  `(instance [Functor $f] : Functor $freeName where
        map := $fmapName
        )

elab "mkFMonad" freeName:ident bindName:ident f:ident : command => do
  let c1c : Syntax := Lean.mkIdent (freeName.getId ++ "Pure")
  let c2c : Syntax := Lean.mkIdent (freeName.getId ++ "Impure")
  let c1pat ← `(matchAltExpr| | $c1c a => f a)
  let c2pat ← `(matchAltExpr| | $c2c fa next => $c2c fa (fun z => $bindName (next z) f))
  let branches := #[c1pat,c2pat]
  let bindF ← `(def $bindName {α β : Type} (m : $freeName α) (f : α → $freeName β) : $freeName β := match m with $branches:matchAlt*)
  elabCommand bindF
  let monadI ←
    `(instance : Monad $freeName where
        pure := $c1c
        bind := $bindName
        )
  elabCommand monadI

elab "mkIxMonad" freeName:ident bindName:ident f:ident : command => do
  let c1c : Syntax := Lean.mkIdent (freeName.getId ++ "Pure")
  let c2c : Syntax := Lean.mkIdent (freeName.getId ++ "Impure")
  let c1pat ← `(matchAltExpr| | $c1c a => f a)
  let c2pat ← `(matchAltExpr| | $c2c fa next => $c2c fa (fun z => $bindName (next z) f))
  let branches := #[c1pat,c2pat]
  let bindF ← `(def $bindName {α β : Type} (m : $freeName α) (f : α → $freeName β) : $freeName β := match m with $branches:matchAlt*)
  elabCommand bindF
  let monadI ←
    `(instance : IxMonad $freeName where
        pureIx := $c1c
        bindIx := $bindName
        )
  elabCommand monadI


elab "mkFreer" freeName:ident f:ident : command => do
  let mapName : Syntax := Lean.mkIdent <| Name.mkSimple <| freeName.getId.toString ++ "mapX"
  let bindName : Syntax := Lean.mkIdent <| Name.mkSimple <| freeName.getId.toString ++ "bindX"
  let m1 ← `(mkFreerInductive $freeName $f)
  elabCommand m1
  let m2 ← `(mkFmap $freeName $mapName $f)
  elabCommand m2
  let m3 ← `(mkFFunctor $freeName $mapName $f)
  elabCommand m3
  let m4 ← `(mkFMonad $freeName $bindName $f)
  elabCommand m4

mkFreer SomeFreer Id

#print SomeFreer
#check (do SomeFreer.Pure (); SomeFreer.Pure 4 : SomeFreer Nat)
#print Bind




def x {m : Indexer Nat → Type → Type 1} [IxMonad m] [SendableIx SomeI m] :=
    checkIxDo m Nat Nat ∃>
           (send <| SomeI.A ())
        →→ (sendIndexed 2 (SomeI.A ()))
        →→ (pureIx .Null 3)

