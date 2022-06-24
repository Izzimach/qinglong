
import Lean
import Lean.Parser

import QingLong.Macro.SumMacro
import QingLong.Data.IndexedMonad

namespace FreerIx

open Lean Elab Command Term Meta 
open Parser.Term

open IndexedMonad


set_option hygiene false in
macro "mkFreerInductive" freerName:ident f:ident : command =>
  `(inductive $freerName {ix : Type} (i : Indexer ix) (α : Type u) : Type (u + 1) where 
      | Pure : α → $freerName i α 
      | Impure : {x : Type} → $f x → (x → $freerName i α) → $freerName i α)


set_option hygiene false in
macro "mkFmap" freerName:ident fmapName:ident f:ident : command => do
  let pureCtor : Syntax := Lean.mkIdent (freerName.getId ++ "Pure")
  let impureCtor : Syntax := Lean.mkIdent (freerName.getId ++ "Impure")
  let c1pat ← `(matchAltExpr| | $pureCtor a => $pureCtor <| fab a)
  let c2pat ← `(matchAltExpr| | $impureCtor fx next => $impureCtor fx (fun z => $fmapName fab (next z)))
  let branches := #[c1pat,c2pat]
  `(def $fmapName (fab : α → β) (fTree : $freerName i α) : $freerName i β :=
       match fTree with $branches:matchAlt*)


set_option hygiene false in
macro "mkFFunctor" freeName:ident fmapName:ident f:ident : command => do
  let c1c : Syntax := Lean.mkIdent (freeName.getId ++ "Pure")
  let c2c : Syntax := Lean.mkIdent (freeName.getId ++ "Impure")
  let c1pat ← `(matchAltExpr| | $c1c a => $c1c a)
  let c2pat ← `(matchAltExpr| | $c2c fa => $c2c (Functor.map (xm f) fa))
  let branches := #[c1pat,c2pat]
  `(instance [Functor $f] : Functor ($freeName i) where
        map := $fmapName
        )

elab "mkFMonad" freeName:ident bindName:ident f:ident : command => do
  let c1c : Syntax := Lean.mkIdent (freeName.getId ++ "Pure")
  let c2c : Syntax := Lean.mkIdent (freeName.getId ++ "Impure")
  let c1pat ← `(matchAltExpr| | $c1c a => f a)
  let c2pat ← `(matchAltExpr| | $c2c fa next => $c2c fa (fun z => $bindName (next z) f))
  let branches := #[c1pat,c2pat]
  let bindF ← `(def $bindName {α β ix : Type} {i : Indexer ix} (m : $freeName i α) (f : α → $freeName i β) : $freeName i β := match m with $branches:matchAlt*)
  elabCommand bindF
  let monadI ←
    `(instance {ix : Type} {i : Indexer ix} : Monad ($freeName i) where
        pure := $c1c
        bind := $bindName
        )
  elabCommand monadI

elab "mkIxMonad" freeName:ident bindName:ident reindexName:ident f:ident : command => do
  let c1c : Syntax := Lean.mkIdent (freeName.getId ++ "Pure")
  let c2c : Syntax := Lean.mkIdent (freeName.getId ++ "Impure")
  let reindex1pat ← `(matchAltExpr| | $c1c a => $c1c a)
  let reindex2pat ← `(matchAltExpr| | $c2c fa next => $c2c fa (fun x => $reindexName (next x)))
  let reindexBranches := #[reindex1pat, reindex2pat]
  let reindexF ← `(def $reindexName {α ix : Type} {i₁ i₂ : Indexer ix} (m : $freeName i₁ α) : $freeName i₂ α := match m with $reindexBranches:matchAlt*)
  elabCommand reindexF
  let c1pat ← `(matchAltExpr| | $c1c a => $reindexName <| f a)
  let c2pat ← `(matchAltExpr| | $c2c fa next => $c2c fa (fun z => $bindName (next z) f))
  let branches := #[c1pat,c2pat]
  let bindF ← `(def $bindName {α β ix : Type} {i₁ i₂ : Indexer ix} (m : $freeName i₁ α) (f : α → $freeName i₂ β) : $freeName (Indexer.Append i₁ i₂) β := match m with $branches:matchAlt*)
  elabCommand bindF
  let monadI ←
    `(instance {ix : Type} : IxMonad (@$freeName ix) where
        pureIx := fun i a => @$c1c ix i _ a
        bindIx := $bindName
        )
  elabCommand monadI


elab "mkSendableIx" freeName:ident f:ident : command => do
  let c1c : Syntax := Lean.mkIdent (freeName.getId ++ "Pure")
  let c2c : Syntax := Lean.mkIdent (freeName.getId ++ "Impure")
  let cd ←
    `(instance {ix : Type} {b : Type → Type} [Prismatic b $f] : SendableIx b (@$freeName ix) where
        sendIx := fun v => $c2c (Prismatic.inject v) $c1c)
  elabCommand cd


elab "mkFreer" freeName:ident f:ident : command => do
  let mapName : Syntax := Lean.mkIdent <| Name.mkSimple <| freeName.getId.toString ++ "mapX"
  let bindName : Syntax := Lean.mkIdent <| Name.mkSimple <| freeName.getId.toString ++ "bindX"
  let bindIxName : Syntax := Lean.mkIdent <| Name.mkSimple <| freeName.getId.toString ++ "bindXX"
  let reindexName : Syntax := Lean.mkIdent <| Name.mkSimple <| freeName.getId.toString ++ "reindexX"
  let m1 ← `(mkFreerInductive $freeName $f)
  elabCommand m1
  let m2 ← `(mkFmap $freeName $mapName $f)
  elabCommand m2
  let m3 ← `(mkFFunctor $freeName $mapName $f)
  elabCommand m3
  let m4 ← `(mkFMonad $freeName $bindName $f)
  elabCommand m4
  let m5 ← `(mkIxMonad $freeName $bindIxName $reindexName $f)
  elabCommand m5
  let m6 ← `(mkSendableIx $freeName $f)
  elabCommand m6

/-
mkFreerInductive SomeFreer Id
mkFmap SomeFreer mapX Id
mkFFunctor SomeFreer mapX Id
mkFMonad SomeFreer bindY Id
mkIxMonad SomeFreer bindIxY reindexIxY Id
mkSendableIx SomeFreer Argh
-/

mkFreer SomeFreer Argh
#print SomeFreer


#check (do SomeFreer.Pure (); SomeFreer.Pure 4 : SomeFreer Indexer.Null Nat)
#check (Prismatic.inject (SomeI.A 3) : Argh Nat)
#check (send (SomeI.A 3) : SomeFreer _ _)

open IxMonad

def x {m : Indexer Nat → Type → Type 1}
  [IxMonad m] [SendableIx SomeI m] :=
    checkIxDo m Nat Nat ∃>
           (send <| SomeI.A ())
        →→ (sendIndexed 2 (SomeI.A ()))
        →→ (pure0 3)

def runSome := @x SomeFreer

#check runSome
#eval getIndex runSome


end FreerIx
