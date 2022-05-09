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
    | @ZFreerPF.ZImpure g α x gx => x

def FreerPF (g : Type → Type) (α : Type) : pfunctor := pfunctor.mk (ZFreerPF g α) (fun x => tBump <| ZFreerBranch x)

def FreerW (g : Type → Type) (α : Type) := W (FreerPF g α)

def pureFreer {α : Type} (a : α) : FreerW g α := W.mk ⟨ZFreerPF.ZPure a, (fun ux => Fin.elim0 (untBump ux))⟩

def bindFreer {α β : Type} (m1 : FreerW g α) (m2 : α → FreerW g β) : FreerW g β :=
    match m1 with
    | ⟨ZFreerPF.ZPure a,     _⟩ => m2 a
    | ⟨ZFreerPF.ZImpure x gx, bx⟩ => W.mk ⟨ZFreerPF.ZImpure x gx, fun x => bindFreer (bx x) m2⟩

instance : Monad (FreerW g) where
    pure := pureFreer
    bind := bindFreer


inductive FReaderWriter (i : Type) (o : Type) : Type → Type where
    | Get : FReaderWriter i o i
    | Put : o → FReaderWriter i o Unit

def IT {x : Type} (i o α : Type) := FreerW (FReaderWriter i o) α



end freerW