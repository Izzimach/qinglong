-- Free monads built using W types and polynomial functors

import QingLong.PFunctor
import QingLong.Wtype

open pfunctor
open Wtype

namespace pfree

inductive ZFree (α : Type u) : Type u where
| ZPure : α → ZFree α
| ZFree

instance : Functor ZFree where
  map f
  | ZFree.ZPure a => ZFree.ZPure (f a)
  | ZFree.ZFree   => ZFree.ZFree

def ZFreeBranch : ZFree α → Type
| ZFree.ZPure a => Fin 0 -- can't use False since we need a Type here, not a Prop
| ZFree.ZFree   => Unit

def ZFreePF (α : Type) : pfunctor := pfunctor.mk (ZFree α) ZFreeBranch

-- Polynomial functor combining the bare "Free" pfunctor and some other pfunctor f.
-- This is basically a Free Monad without the recursive part.
def FreePF (f : pfunctor) (α : Type) : pfunctor := comp (ZFreePF α) f

/- pfunctor { A := Σ a₂ : ZFree α, ZFreeBranch a₂ → f.A,
              B := fun x => Σ u : ZFreeBranch x.1, f.B (x.2 u)}
   for ZPure: {A := Σ ZPure a, Fin0 → f.A,
               B:= _}  (the second part is never referenced)
       ZFree: {A := Σ Zpure.ZFree, Unit → f.A,
               B := fun x => Σ u : Unit, f.B (x.2 ())}
-/

--def comp (P₂ P₁ : pfunctor.{u}) : pfunctor.{u} :=
--⟨ Σ a₂ : P₂.1, P₂.2 a₂ → P₁.1,
--  fun a₂a₁ => Σ u : P₂.2 a₂a₁.1, P₁.2 (a₂a₁.2 u) ⟩

-- rewrites the Free wrapper around some other object - almost Functor.map
def reFree (f : α → β) (z : obj (ZFreePF α) x) : obj (ZFreePF β) x := 
  match z with
  | ⟨ZFree.ZPure a, n⟩ => ⟨ZFree.ZPure (f a), n⟩
  | ⟨ZFree.ZFree,   n⟩ => ⟨ZFree.ZFree      , n⟩


-- The recursive structure of a Free Monad
-- Uses the W type invoked with the poynomial functor FreePF, which combines the Free pfunctor and some pfunctor f
def FreeW (pf : pfunctor) (α : Type) := W (FreePF pf α)

def FreeMap (f : α → β) (w : FreeW pf α) : FreeW pf β :=
  let alg := fun d =>
                -- unpack into Free and pf parts, apply map to the Free part, then re-pack into a FreeW
                let x1 := comp.get (ZFreePF α) pf d
                let x2 := reFree f x1
                let x3 := comp.mk (ZFreePF β) pf x2
                W.mk x3
  Wtype.elim alg w

instance : Functor (FreeW f) :=
  { map := FreeMap }

def rawFree {pf : pfunctor} {α : Type} (a : α) : (FreePF pf α).obj (W (FreePF pf α)) :=
  -- FreePF is a composite pfunctor, so obj is a nested sigma type
  ⟨ ⟨ZFree.ZPure a, Fin.elim0⟩ , (fun x => Fin.elim0 x.1) ⟩

def pureFree {pf : pfunctor} (a : α) : FreeW pf α := W.mk <| rawFree a

def bindFree {pf : pfunctor} {α β : Type} (m1 : FreeW pf α) (m2 : α → FreeW pf β) : FreeW pf β :=
  match m1 with
  | W_type.mk ⟨ZFree.ZPure a, _⟩   _    => m2 a
  | W_type.mk ⟨ZFree.ZFree,   x⟩   next => W_type.mk ⟨ZFree.ZFree, x⟩ (fun a => bindFree (next a) m2)


instance : Monad (FreeW pf) where
  pure := pureFree
  bind := bindFree

-- catamorphism wrapped around the Free structure
def interpret (alg : pf.obj α → α) (tree : FreeW pf α) : α :=
  let Walg := fun zf =>
                let ⟨a,f⟩ := comp.get (ZFreePF α) pf zf
                match a with
                | ZFree.ZPure a => a
                | ZFree.ZFree   => alg <| f ()
  Wtype.elim Walg tree


end pfree