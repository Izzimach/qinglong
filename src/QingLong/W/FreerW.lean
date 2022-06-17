-- Freer monads using W types and polynomial functors. Similar to FreeW, but we don't need a functor instance
-- of the Monad and also don't compose pfunctors.

import QingLong.PFunctor
import QingLong.Wtype

open pfunctor
open Wtype

namespace freerW

-- The type from "Freer Monads..." was (in Haskell)
--
-- data FFree f a where
--   Pure :: a → FFree f a
--   Impure :: f x → (x → FFree f a) → FFree f a

inductive ZFreerPF (g : Type → Type) (α : Type) : Type 1 where
    | ZPure : α → ZFreerPF g α 
    | ZImpure : (x : Type) → g x → ZFreerPF g α -- the (x → W ..) part is in the second part of the pfunctor

-- a quick hack to switch type levels
inductive tBump (x : Type) : Type 1
    | mk : x → tBump x

def untBump : (tBump x) → x
    | tBump.mk x => x


def ZFreerBranch {g : Type → Type} {α : Type} : ZFreerPF g α → Type
    | ZFreerPF.ZPure a => Fin 0 -- can't use False since we need a Type here, not a Prop
    | ZFreerPF.ZImpure x gx => x

def FreerPF (g : Type → Type) (α : Type) : pfunctor := pfunctor.mk (ZFreerPF g α) (fun v => ULift <| ZFreerBranch v)

def FreerW (g : Type → Type) (α : Type) : Type 1 := W (FreerPF g α)

--
-- FreerW as a Monad
--

-- lift into Free.
-- These universe shifts are annoying!
def liftFreer {α : Type} {g : Type → Type} (ga : g α) : FreerW g α :=
    W.mk <| ⟨ZFreerPF.ZImpure α ga, fun a => W.mk ⟨ZFreerPF.ZPure <| ULift.down a, Fin.elim0 ∘ ULift.down⟩⟩

def pureFreer {α : Type} (a : α) : FreerW g α := W.mk ⟨ZFreerPF.ZPure a, Fin.elim0 ∘ ULift.down⟩


def bindFreer {α β : Type} (m1 : FreerW g α) (m2 : α → FreerW g β) : FreerW g β :=
    match m1 with
    | ⟨ZFreerPF.ZPure a,     _⟩ => m2 a
    | ⟨ZFreerPF.ZImpure x gx, bx⟩ => W.mk ⟨ZFreerPF.ZImpure x gx, fun x => bindFreer (bx x) m2⟩

instance : Monad (FreerW g) where
    pure := pureFreer
    bind := bindFreer

--
-- FreerW as a Functor
--

def FreerMap (f : α → β) (w : FreerW g α) : FreerW g β :=
    let Walg := fun d =>
        match d with
        | ⟨ZFreerPF.ZPure a, _⟩         => pureFreer <| f a
        | ⟨ZFreerPF.ZImpure x gx, next⟩ => W.mk ⟨ZFreerPF.ZImpure x gx, next⟩ -- note, no FreerMap needed here...
    Wtype.elim Walg w

instance : Functor (FreerW f) :=
    { map := FreerMap }


-- catamorphism threaded through the Freer structure
def interpretW {α : Type} {g : Type → Type} (alg : ∀ x, g x → x) (tree : FreerW g α) : α :=
    let Walg := fun zf =>
        match zf with
        | ⟨ZFreerPF.ZPure a, _⟩ => ULift.up a
        | ⟨ZFreerPF.ZImpure x gx, next⟩ => next <| ULift.up <| alg x gx
    ULift.down <| Wtype.elim.{1} Walg tree


inductive FReaderWriter (i : Type) (o : Type) : Type → Type where
    | Get : FReaderWriter i o i
    | Put : o → FReaderWriter i o Unit

def runReaderWriter (val :Nat) (tree : FreerW (FReaderWriter Nat Nat) α) : α :=
  let alg := fun x fr =>
      match fr with
      | FReaderWriter.Get => val
      | FReaderWriter.Put v => ()
  interpretW alg tree

def getW := liftFreer <| @FReaderWriter.Get Nat Nat
def putW (v : Nat) : FreerW (FReaderWriter Nat Nat) Unit := liftFreer <| @FReaderWriter.Put Nat Nat v

#eval runReaderWriter 3 <| do let v ← getW; putW v; pure v

def IT {x : Type} (i o α : Type) := FreerW (FReaderWriter i o) α



end freerW