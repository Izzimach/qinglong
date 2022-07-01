
import Lean
import Lean.Parser

import QingLong.Macro.SumMacro
import QingLong.Data.IndexedMonad

namespace FreerIx

open Lean Elab Command Term Meta 
open Parser.Term

open IndexedMonad
open SumMacro


set_option hygiene false in
macro "mkFreerInductive" freerName:ident f:ident : command =>
  `(inductive $freerName {ix : Type} (i : Indexer ix) (α : Type u) : Type (u + 1) where 
      | Pure : α → $freerName i α 
      | Impure : {x : Type} → $f x → (x → $freerName i α) → $freerName i α)

set_option hygiene false in
macro "mkFreerInductiveWithIndex" freerName:ident f:ident ix:term : command =>
  `(inductive $freerName (i : Indexer $ix) (α : Type u) : Type (u + 1) where 
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

def mkFMonadFunc (freeName : Syntax) (bindName : Syntax) (f :Syntax) (oix : Option Syntax) : CommandElabM Unit := do
  let c1c : Syntax := Lean.mkIdent (freeName.getId ++ "Pure")
  let c2c : Syntax := Lean.mkIdent (freeName.getId ++ "Impure")
  let c1pat ← `(matchAltExpr| | $c1c a => f a)
  let c2pat ← `(matchAltExpr| | $c2c fa next => $c2c fa (fun z => $bindName (next z) f))
  let branches := #[c1pat,c2pat]
  let matchTerm ← `(match m with $branches:matchAlt*)
  let bindDecl ← match oix with
                 | Option.none => `(def $bindName {α β ix : Type} {i : Indexer ix} (m : $freeName i α) (f : α → $freeName i β) : $freeName i β := $matchTerm)
                 | Option.some ix => `(def $bindName {α β : Type} {i : Indexer $ix} (m : $freeName i α) (f : α → $freeName i β) : $freeName i β := $matchTerm)
  elabCommand bindDecl
  let monadI ←
      match oix with
      | Option.none =>
            `(instance {ix : Type} {i : Indexer ix} : Monad ($freeName i) where
                pure := $c1c
                bind := $bindName)
      | Option.some ix =>
            `(instance {i : Indexer $ix} : Monad ($freeName i) where
                pure := $c1c
                bind := $bindName)
  elabCommand monadI

elab "mkFMonad" freeName:ident bindName:ident f:ident : command => mkFMonadFunc freeName bindName f Option.none
elab "mkFMonad" freeName:ident bindName:ident f:ident ix:term : command => mkFMonadFunc freeName bindName f (Option.some ix)

def mkIxMonadFunc (freeName : Syntax) (bindName : Syntax) (reindexName : Syntax) (f : Syntax) (oix : Option Syntax) : CommandElabM Unit := do
  let c1c : Syntax := Lean.mkIdent (freeName.getId ++ "Pure")
  let c2c : Syntax := Lean.mkIdent (freeName.getId ++ "Impure")
  let reindex1pat ← `(matchAltExpr| | $c1c a => $c1c a)
  let reindex2pat ← `(matchAltExpr| | $c2c fa next => $c2c fa (fun x => $reindexName (next x)))
  let reindexBranches := #[reindex1pat, reindex2pat]
  let reindexF ←
    match oix with
    | Option.none => `(def $reindexName {α ix : Type} {i₁ i₂ : Indexer ix} (m : $freeName i₁ α) : $freeName i₂ α := match m with $reindexBranches:matchAlt*)
    | Option.some ix => `(def $reindexName {α : Type} {i₁ i₂ : Indexer $ix} (m : $freeName i₁ α) : $freeName i₂ α := match m with $reindexBranches:matchAlt*)
  elabCommand reindexF
  let c1pat ← `(matchAltExpr| | $c1c a => $reindexName <| f a)
  let c2pat ← `(matchAltExpr| | $c2c fa next => $c2c fa (fun z => $bindName (next z) f))
  let branches := #[c1pat,c2pat]
  let bindF ← 
    match oix with
    | Option.none => `(def $bindName {α β ix : Type} {i₁ i₂ : Indexer ix} (m : $freeName i₁ α) (f : α → $freeName i₂ β) : $freeName (Indexer.Append i₁ i₂) β := match m with $branches:matchAlt*)
    | Option.some ix => `(def $bindName {α β : Type} {i₁ i₂ : Indexer $ix} (m : $freeName i₁ α) (f : α → $freeName i₂ β) : $freeName (Indexer.Append i₁ i₂) β := match m with $branches:matchAlt*)
  elabCommand bindF
  let monadI ←
    match oix with
    | Option.none => 
        `(instance {ix : Type} : IxMonad (@$freeName ix) where
            pureIx := fun i a => @$c1c ix i _ a
            bindIx := $bindName)
    | Option.some ix => 
        `(instance : IxMonad $freeName where
            pureIx := fun i a => @$c1c i _ a
            bindIx := $bindName)
  elabCommand monadI


def mkSendableIxFunc (freeName : Syntax) (f : Syntax) (oix : Option Syntax) : CommandElabM Unit := do
  let c1c : Syntax := Lean.mkIdent (freeName.getId ++ "Pure")
  let c2c : Syntax := Lean.mkIdent (freeName.getId ++ "Impure")
  let cd ←
    match oix with
    | Option.none =>
          `(instance {ix : Type} {b : Type → Type} [Prismatic b $f] : SendableIx b (@$freeName ix) where
              sendIx := fun v => $c2c (Prismatic.inject v) $c1c)
    | Option.some ix =>
          `(instance             {b : Type → Type} [Prismatic b $f] : SendableIx b $freeName where
              sendIx := fun v => $c2c (Prismatic.inject v) $c1c)
  elabCommand cd

def mkInterpreterFunc (freeName : Syntax) (sumName : Syntax) (interpretName : Syntax) (oix : Option Syntax) : CommandElabM Unit := do
  let c1c : Syntax := Lean.mkIdent (freeName.getId ++ "Pure")
  let c2c : Syntax := Lean.mkIdent (freeName.getId ++ "Impure")
  let c1pat ← `(matchAltExpr| | $c1c a => pure a)
  let c2pat ← `(matchAltExpr| | $c2c v next => bind (c v) (fun xx => $interpretName c (next xx)))
  let branches := #[c1pat,c2pat]
  let cd ←
    match oix with
    | Option.none =>
          `(def $interpretName {ix α : Type} {i : Indexer ix}  {n : Type → Type} [Monad n] (c : {z : Type} → $sumName z → n z) (m : $freeName i α) : n α :=
              match m with $branches:matchAlt*)
    | Option.some ix =>
          `(def $interpretName {   α : Type} {i : Indexer $ix} {n : Type → Type} [Monad n] (c : {z : Type} → $sumName z → n z) (m : $freeName i α) : n α :=
              match m with $branches:matchAlt*)
  elabCommand cd
  

def mkFreerFunc (freeName : Syntax) (f : Syntax) (oix : Option Syntax) : CommandElabM Unit := do
  let mapName : Syntax := Lean.mkIdent <| Name.mkSimple <| freeName.getId.toString ++ "mapX"
  let bindName : Syntax := Lean.mkIdent <| Name.mkSimple <| freeName.getId.toString ++ "bindX"
  let bindIxName : Syntax := Lean.mkIdent <| Name.mkSimple <| freeName.getId.toString ++ "bindXX"
  let reindexName : Syntax := Lean.mkIdent <| Name.mkSimple <| freeName.getId.toString ++ "reindexX"
  let interpreterName : Syntax := Lean.mkIdent <| Name.mkSimple <| "run" ++ freeName.getId.toString
  let m1 ← match oix with
           | Option.none    => `(mkFreerInductive $freeName $f)
           | Option.some ix => `(mkFreerInductiveWithIndex $freeName $f $ix)
  elabCommand m1
  let m2 ← `(mkFmap $freeName $mapName $f)
  elabCommand m2
  let m3 ← `(mkFFunctor $freeName $mapName $f)
  elabCommand m3
  mkFMonadFunc freeName bindName f oix
  mkIxMonadFunc freeName bindIxName reindexName f oix
  mkSendableIxFunc freeName f oix
  mkInterpreterFunc freeName f interpreterName oix
  /-
  let m7 ← `(mkInterpreter $freeName $f $interpreterName)
  elabCommand m7
  -/

elab "mkFreer" freeName:ident f:ident : command => mkFreerFunc freeName f Option.none
elab "mkFreer" freeName:ident f:ident z:term : command => mkFreerFunc freeName f (Option.some z)

/-
set_option pp.rawOnError true
mkFreer SomeFreer Argh
mkFreer SomeFreerNat Argh Nat
#print SomeFreer
#print SomeFreerNat
#check SomeFreer_interpret

#check (do SomeFreer.Pure (); SomeFreer.Pure 4 : SomeFreer Indexer.Null Nat)
#check (Prismatic.inject (EcksI.X  3 7) : Argh Nat)
#check (send (EcksI.X 1 3) : SomeFreer _ _)



open IxMonad

def x {m : Indexer Nat → Type → Type 1}
  [IxMonad m] [SendableIx (EcksI Nat) m] :=
    checkIxDo m Nat Nat ∃>
           (send <| EcksI.X 1 1)
        →→ (sendIndexed 2 (EcksI.X 22 ()))
        →→ (pure0 3)

def runSome := @x SomeFreer

#check runSome
#eval getIndex runSome
-/

end FreerIx
