-- extensible effect monad "Eff" based on "Free Monads, More Extensible Effects"
-- built on top of the W type

import QingLong.PFunctor
import QingLong.Wtype

open pfunctor
open Wtype

namespace effW

inductive Union (effs : List Type) (x : Type) : Type where
| mk : x → Union effs x

class HasEffect (t : Type → Type) (effs : List Type) where
   inject  : t v → Union effs v
   project : Union r v → Option (t v)


inductive ZEffPF (g : Type → Type) (α : Type) : Type 1 where
  | ZPure : α → ZEffPF g α 
  | ZImpure : (x : Type) → g x → ZEffPF g α -- the (x → W ..) part is in the second part of the pfunctor

-- a quick hack to switch type levels
inductive tBump (x : Type) : Type 1
| mk : x → tBump x

def untBump : (tBump x) → x
| tBump.mk x => x


def ZEffBranch {g : Type → Type} {α : Type} : ZEffPF g α → Type
  | ZEffPF.ZPure a => Fin 0 -- can't use False since we need a Type here, not a Prop
  | @ZEffPF.ZImpure g α x gx => x

-- polynomial functor for Eff - combine with W to make a recursive structure
def EffPF (g : Type → Type) (α : Type) : pfunctor := pfunctor.mk (ZEffPF g α) (fun x => tBump <| ZEffBranch x)

def EffW (g : Type → Type) (α : Type) := W (EffPF g α)

def pureEff {α : Type} (a : α) : EffW g α := W.mk ⟨ZEffPF.ZPure a, (fun ux => Fin.elim0 (untBump ux))⟩

def bindEff {α β : Type} (m1 : EffW g α) (m2 : α → EffW g β) : EffW g β :=
  match m1 with
  | ⟨ZEffPF.ZPure a,     _⟩ => m2 a
  | ⟨ZEffPF.ZImpure x gx, bx⟩ => W.mk ⟨ZEffPF.ZImpure x gx, fun x => bindEff (bx x) m2⟩

instance : Monad (EffW g) where
    pure := pureEff
    bind := bindEff


end effW