-- Free monad implemented using macros

import Lean
import Lean.Parser
import QingLong.PFunctor
import QingLong.Wtype
import QingLong.FreeW
import QingLong.Eff
import QingLong.FixHack

open Lean Elab Command Term Meta 
open Parser.Term


namespace FreeMacro

inductive Argh (α : Type) : Type where
| Poop : α → Argh α
| Blargh : (Argh α) → Argh α
  deriving Repr

def arghSize : (Argh α) → Nat
| Argh.Poop _ => 1
| Argh.Blargh aa => Nat.succ <| arghSize aa

instance : SizeOf (Argh α) where
  sizeOf := arghSize

theorem arghSizeWF (a : Argh α) : arghSize a < arghSize (Argh.Blargh a) := by
    let (h : arghSize (Argh.Blargh a) = Nat.succ (arghSize a)) := by
      unfold arghSize ; simp 
      induction a
      unfold arghSize; simp
      unfold arghSize; simp
      rename_i a_ih
      rw [a_ih]
    rw [h]
    apply Nat.lt_succ_self

def AccNat (x : Nat) (y : Nat) (r : Nat.lt y x) : Acc Nat.lt y := Acc.intro y (AccNat y)

def xx := WellFounded.intro (fun x => Acc.intro x (AccNat x))


def mapArgh (f : α → β) : Argh α → Argh β
| Argh.Poop a => Argh.Poop (f a)
| Argh.Blargh aa => Argh.Blargh <| mapArgh f aa

def algArgh (f : α → β) (x : Argh α) (h : (y : Argh α) → sizeOf y < sizeOf x → Argh β) : Argh β :=
  match x with
  | Argh.Poop a => Argh.Poop (f a)
  | Argh.Blargh aa => h aa (arghSizeWF aa)

#eval FixHack.fix' (measure arghSize).wf (algArgh (fun x => x*3)) (Argh.Poop 3)

set_option hygiene false in
macro "mkFree" freeName:ident f:ident : command =>
  `(inductive $freeName (α : Type u) : Type u where 
    | Pure : α → $freeName α 
    | Impure : $f ($freeName α) → $freeName α)

set_option hygiene false in
macro "mkFreeSz" freeName:ident f:ident : command => do
  let c1c : Syntax := Lean.mkIdent (freeName.getId ++ "Pure")
  let c2c : Syntax := Lean.mkIdent (freeName.getId ++ "Impure")
  let c1pat ← `(matchAltExpr| | $c1c a => 1)
  let c2pat ← `(matchAltExpr| | $c2c fa => sizeOf fa + 1)
  let branches := #[c1pat,c2pat]
  `(def arghSz [SizeOf ($f ($freeName α))] : ($freeName α) → Nat :=
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
      match fTree with $branches:matchAlt*
    termination_by _ _ ft => sizeOf ft)

def arghMap [Functor List] (fab : α → β) (fTree : argh α) : argh β :=
      match fTree with
      | argh.Pure a => argh.Pure <| fab a
      | argh.Impure fa => argh.Impure <| Functor.map (fun x => arghMap fab x) fa
    termination_by _ _ ft => sizeOf ft

def arghToW [Functor List] (fab : α → β) (fTree : argh α) : freeW.FreeW listPF α :=
      match fTree with
      | argh.Pure a => freeW.pureFree a
      | argh.Impure fa =>
          let n₁ : listPF.A := List.length fa
          Wtype.W_type.mk ⟨freeW.ZFree.ZImpure, fun _ => n₁⟩  _ --⟨Zfree.ZImpure, List.length fa⟩ Functor.map (fun x => arghMap fab x) fa
    termination_by _ _ ft => sizeOf ft

#check pfunctor.listPF.A
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
