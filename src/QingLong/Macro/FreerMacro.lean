
-- we need to instantiate a Sendable instance for getNamed/putNamed
import QingLong.Data.NamedState
-- for the Prismatic class
import QingLong.Macro.SumMacro

import Lean
import Lean.Parser

open Lean Elab Command Term Meta 
open Parser.Term

open NamedState SumMacro

namespace Freer



set_option hygiene false in
macro "mkFreerInductive" freerName:ident f:ident : command =>
  `(inductive $freerName (α : Type u) : Type (u + 1) where 
      | Pure : α → $freerName α 
      | Impure : {x : Type} → $f x → (x → $freerName α) → $freerName α)


set_option hygiene false in
macro "mkFmap" freerName:ident fmapName:ident f:ident : command => do
  let pureCtor := Lean.mkIdent (freerName.getId ++ "Pure")
  let impureCtor := Lean.mkIdent (freerName.getId ++ "Impure")
  let c1pat ← `(matchAltExpr| | $pureCtor a => $pureCtor <| fab a)
  let c2pat ← `(matchAltExpr| | $impureCtor fx next => $impureCtor fx (fun z => $fmapName fab (next z)))
  let branches := #[c1pat,c2pat]
  `(def $fmapName (fab : α → β) (fTree : $freerName α) : $freerName β :=
       match fTree with $branches:matchAlt*)


set_option hygiene false in
macro "mkFFunctor" freerName:ident fmapName:ident f:ident : command => do
  /-let c1c := Lean.mkIdent (freerName.getId ++ "Pure")
  let c2c := Lean.mkIdent (freerName.getId ++ "Impure")
  let c1pat ← `(matchAltExpr| | $c1c a => $c1c a)
  let c2pat ← `(matchAltExpr| | $c2c fa => $c2c (Functor.map (xm f) fa))
  let branches := #[c1pat,c2pat]-/
  `(instance [Functor $f] : Functor $freerName where map := $fmapName)

def mkFMonadFunc (freerName : TSyntax `ident) (bindName : TSyntax `ident) : CommandElabM Unit := do
  let c1c := Lean.mkIdent (freerName.getId ++ "Pure")
  let c2c := Lean.mkIdent (freerName.getId ++ "Impure")
  let c1pat ← `(matchAltExpr| | $c1c a => f a)
  let c2pat ← `(matchAltExpr| | $c2c fa next => $c2c fa (fun z => $bindName (next z) f))
  let branches := #[c1pat,c2pat]
  let matchTerm ← `(match m with $branches:matchAlt*)
  let bindDecl ← `(def $bindName {α β : Type} (m : $freerName α) (f : α → $freerName β) : $freerName β := $matchTerm)
  elabCommand bindDecl
  let monadI ←
      `(instance : Monad $freerName where
          pure := $c1c
          bind := $bindName)
  elabCommand monadI

elab "mkFMonad" freerName:ident bindName:ident : command => mkFMonadFunc freerName bindName


class Sendable (b : Type → Type) (m : Type → Type 1) where
  send : {x : Type} → b x → m x

-- Sometimes getNamed has trouble inferring the type of the variable you are getting. You can help it out
-- with an  explicit call. For instance to get a Nat named "z" : @getNamed "z" Nat _ _
def getNamed (n : String) {v : Type} {m : Type → Type 1} [Sendable (NamedState n v) m] : m v :=
    Sendable.send <| @NamedState.Get n v

def putNamed (n : String) {v : Type} (x : v) {m : Type → Type 1} [Sendable (NamedState n v) m] : m Unit :=
    Sendable.send <| @NamedState.Put n v x


def mkSendableFunc (freerName : TSyntax `ident) (f : TSyntax `ident) : CommandElabM Unit := do
  let c1c := Lean.mkIdent (freerName.getId ++ "Pure")
  let c2c := Lean.mkIdent (freerName.getId ++ "Impure")
  let cd ←
          `(instance {b : Type → Type} [Prismatic b $f] : Sendable b $freerName where
              send := fun v => $c2c (Prismatic.inject v) $c1c)
  elabCommand cd

def mkInterpreterFunc (freerName : TSyntax `ident) (sumName : TSyntax `ident) (interpretName : TSyntax `ident) : CommandElabM Unit := do
  let c1c := Lean.mkIdent (freerName.getId ++ "Pure")
  let c2c := Lean.mkIdent (freerName.getId ++ "Impure")
  let c1pat ← `(matchAltExpr| | $c1c a => pure a)
  let c2pat ← `(matchAltExpr| | $c2c v next => bind (c v) (fun xx => $interpretName c (next xx)))
  let branches := #[c1pat,c2pat]
  let cd ←
          `(def $interpretName {α : Type} {n : Type → Type} [Monad n] (c : {z : Type} → $sumName z → n z) (m : $freerName α) : n α :=
              match m with $branches:matchAlt*)
  elabCommand cd
  

def mkFreerFunc (freerName : TSyntax `ident) (f : TSyntax `ident) : CommandElabM Unit := do
  let mapName := Lean.mkIdent <| Name.mkSimple <| freerName.getId.toString ++ "mapX"
  let bindName := Lean.mkIdent <| Name.mkSimple <| freerName.getId.toString ++ "bindX"
  --let bindIxName : Syntax := Lean.mkIdent <| Name.mkSimple <| freerName.getId.toString ++ "bindXX"
  --let reindexName : Syntax := Lean.mkIdent <| Name.mkSimple <| freerName.getId.toString ++ "reindexX"
  let interpreterName := Lean.mkIdent <| Name.mkSimple <| "run" ++ freerName.getId.toString
  let m1 ← `(mkFreerInductive $freerName $f)
  elabCommand m1
  let m2 ← `(mkFmap $freerName $mapName $f)
  elabCommand m2
  let m3 ← `(mkFFunctor $freerName $mapName $f)
  elabCommand m3
  mkFMonadFunc freerName bindName
  mkSendableFunc freerName f
  mkInterpreterFunc freerName f interpreterName
  /-
  let m7 ← `(mkInterpreter $freerName $f $interpreterName)
  elabCommand m7
  -/

elab "mkFreer" freerName:ident f:ident : command => mkFreerFunc freerName f

end Freer
