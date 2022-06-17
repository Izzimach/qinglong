-- Free monads built using W types and polynomial functors

import QingLong.Data.PFunctor
import QingLong.Data.Wtype

open pfunctor
open Wtype

namespace freeW

inductive ZFree (α : Type u) : Type u where
    | ZPure : α → ZFree α
    | ZImpure

instance : Functor ZFree where
    map f
    | ZFree.ZPure a => ZFree.ZPure (f a)
    | ZFree.ZImpure => ZFree.ZImpure

def ZFreeBranch : ZFree α → Type
    | ZFree.ZPure a => Fin 0 -- can't use False since we need a Type here, not a Prop
    | ZFree.ZImpure => Unit

def ZImpurePF (α : Type) : pfunctor := pfunctor.mk (ZFree α) ZFreeBranch

-- Polynomial functor combining the bare "Free" pfunctor and some other pfunctor f.
-- This is basically a Free Monad without the recursive part.
def FreePF (pf : pfunctor) (α : Type) : pfunctor := comp (ZImpurePF α) pf

/- pfunctor { A := Σ a₂ : ZImpure α, ZImpureBranch a₂ → f.A,
              B := fun x => Σ u : ZImpureBranch x.1, f.B (x.2 u)}
   for ZPure: {A := Σ ZPure a, Fin0 → f.A,
               B:= _}  (the second part is never referenced)
       ZImpure: {A := Σ Zpure.ZImpure, Unit → f.A,
               B := fun x => Σ u : Unit, f.B (x.2 ())}
-/

--def comp (P₂ P₁ : pfunctor.{u}) : pfunctor.{u} :=
--⟨ Σ a₂ : P₂.1, P₂.2 a₂ → P₁.1,
--  fun a₂a₁ => Σ u : P₂.2 a₂a₁.1, P₁.2 (a₂a₁.2 u) ⟩

-- rewrites the Free wrapper around some other object - basically Functor.map on ZImpurePF when it's embedded in FreePF
def reFree (f : α → β) (z : obj (ZImpurePF α) x) : obj (ZImpurePF β) x := 
    match z with
    | ⟨ZFree.ZPure a, n⟩ => ⟨ZFree.ZPure (f a), n⟩
    | ⟨ZFree.ZImpure, n⟩ => ⟨ZFree.ZImpure      , n⟩


-- The recursive structure of a Free Monad
-- Uses the W type invoked with the poynomial functor FreePF, which combines the Free pfunctor and some pfunctor f
def FreeW (pf : pfunctor) (α : Type) := W (FreePF pf α)

def FreeMap (f : α → β) (w : FreeW pf α) : FreeW pf β :=
    let alg := fun d =>
        -- unpack into Free and pf parts, apply map to the Free part, then re-pack into a FreeW
        let x1 := comp.get (ZImpurePF α) pf d
        let x2 := reFree f x1
        let x3 := comp.mk (ZImpurePF β) pf x2
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
    | W_type.mk ⟨ZFree.ZImpure, x⟩   next => W_type.mk ⟨ZFree.ZImpure, x⟩ (fun a => bindFree (next a) m2)


instance : Monad (FreeW pf) where
    pure := pureFree
    bind := bindFree

-- catamorphism threaded through the Free structure
def interpretW (alg : pf.obj α → α) (tree : FreeW pf α) : α :=
    let Walg := fun zf =>
        let ⟨a,f⟩ := comp.get (ZImpurePF α) pf zf
        match a with
        | ZFree.ZPure a => a
        | ZFree.ZImpure => alg <| f ()
    Wtype.elim Walg tree

-- lift into Free
def liftF {pf :pfunctor} {α :Type} (p : pf.obj α) : FreeW pf α :=
    W.mk <| comp.mk (ZImpurePF α) pf ⟨ZFree.ZImpure, fun _ => Functor.map pureFree p⟩

-- state command has two functions, one from s → s and one from s → α
-- These get combined into the usual s → α × s we see in normal state monads

def StatePF (s : Type) := pfunctor.mk (s → s) (fun _ => s)

def get                  : FreeW (StatePF s) s    := liftF <| Sigma.mk id id
def put {s : Type} (x:s) : FreeW (StatePF s) Unit := liftF <| Sigma.mk (fun _ => x) (fun _ => ())

-- should rewrite interpret so that runStateW can be expressed in terms of interpretW
def runStateW (m : FreeW (StatePF s) α) : (s → α × s) :=
    let Walg := fun zf =>
        let ⟨x,f⟩ := comp.get (ZImpurePF α) (StatePF s) zf
        match x with
        | ZFree.ZPure a => fun s => ⟨a,s⟩
        | ZFree.ZImpure => let ⟨fs,fm⟩ := f ()
                           fun s => (fm s) (fs s)
    Wtype.elim Walg m



/-
#check (put 3) >>= (fun _ => get)
#reduce runStateW (do put 3; get) 2
#reduce runStateW (do put 3; put 4) 2
#reduce runStateW (get) 2
-/

end freeW