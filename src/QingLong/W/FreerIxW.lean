
--
-- Freer indexed monads built on the W-type
--
-- If you don't need the index consider FreerW instead
--


import QingLong.Data.PFunctor
import QingLong.Data.Wtype

open pfunctor
open Wtype

namespace FreerIxW

--
-- ix should work like a Haskell Monoid. Here we used Inhabitied and HAdd for this functionality.
--
-- data FFree g ix a where
--   Pure :: {ix} → a → FFree g ix a
--   Impure :: {ix} → g x → (x → FFree g a) → FFree g ix a

inductive FreerIxA (g : Type → Type) (α : Type) : Type 1 where
    | Pure : α → FreerIxA g α 
    | Impure : (x : Type) → g x → FreerIxA g α -- the (x → W ..) part is in the second part of the pfunctor



def FreerIxB {g : Type → Type} {α : Type} : FreerIxA g α → Type
    | FreerIxA.Pure a => Fin 0 -- can't use False since we need a Type here, not a Prop
    | FreerIxA.Impure x gx => x

def FreerIxPF (g : Type → Type) (α : Type) : pfunctor := pfunctor.mk (FreerIxA g α) (fun v => ULift <| FreerIxB v)

structure FreerIxW {ix : Type} (g : Type → Type) (i : ix) (α : Type) : Type 1 where
   val : W (FreerIxPF g α)

--
-- FreerW as a Monad
--

-- lift into Free.
-- These universe shifts are annoying!
def liftFreer {α : Type} {g : Type → Type} {ix : Type} (i : ix) (ga : g α) : FreerIxW g i α :=
    FreerIxW.mk <| ⟨FreerIxA.Impure α ga, fun a => W.mk ⟨FreerIxA.Pure <| ULift.down a, Fin.elim0 ∘ ULift.down⟩⟩

def pureFreer {α : Type} {ix : Type} [Inhabited ix] (i : ix) (a : α) : FreerIxW g i α := FreerIxW.mk ⟨FreerIxA.Pure a, Fin.elim0 ∘ ULift.down⟩

def bindFreerW {α β : Type} : W (FreerIxPF g α) → (α → W (FreerIxPF g β)) → W (FreerIxPF g β) := fun m1 m2 =>
    match m1 with
    | ⟨FreerIxA.Pure a,     _⟩ => m2 a
    | ⟨FreerIxA.Impure x gx, bx⟩ =>W.mk ⟨FreerIxA.Impure x gx, fun x => (@bindFreerW g α β (bx x) m2)⟩

def bindFreer {α β ix : Type} [HAdd ix ix ix] {ix₁ ix₂ : ix}
  : FreerIxW g ix₁ α → (α → FreerIxW g ix₂ β) → FreerIxW g (ix₁ + ix₂) β := fun m1 m2 =>
    -- we just strip off the FreerIxW wrapper and recurse
    FreerIxW.mk <| bindFreerW m1.val (fun x => (m2 x).val)

class IxMonad {ix : Type} (m : ix → Type → Type 1) where
    pureIx : (i : ix) → α → m i α
    bindIx [HAdd ix ix ix] : m i₁ α → (α → m i₂ β) → m (i₁ + i₂) β

open IxMonad

instance {ix : Type} [Inhabited ix] : @IxMonad ix (FreerIxW g) where
    pureIx := fun i a => @pureFreer g _ ix _ i a
    bindIx := bindFreer



--
-- FreerIxW as a Functor
--

def FreerIxMap {ix : Type} {i : ix} (f : α → β) (w : FreerIxW g i α) : FreerIxW g i β :=
    let Walg := fun d =>
        match d with
        | ⟨FreerIxA.Pure a, z⟩         => W.mk ⟨FreerIxA.Pure (f a), z⟩
        | ⟨FreerIxA.Impure x gx, next⟩ => W.mk ⟨FreerIxA.Impure x gx, next⟩
    FreerIxW.mk <| Wtype.elim Walg w.val

instance : Functor (FreerIxW f i) :=
    { map := FreerIxMap }


-- catamorphism threaded through the Freer structure
def interpretW {ix : Type} {i : ix} {α : Type} {g : Type → Type} (alg : ∀ x, g x → x) (tree : FreerIxW g i α) : α :=
    let Walg := fun zf =>
        match zf with
        | ⟨FreerIxA.Pure a, _⟩ => ULift.up a
        | ⟨FreerIxA.Impure x gx, next⟩ => next <| ULift.up <| alg x gx
    ULift.down <| Wtype.elim.{1} Walg tree.val

def interpretM {ix : Type} {i : ix} {α : Type} {m g : Type → Type} [Monad m] (alg : ∀ x, g x → m x) (tree : FreerIxW g i α) : m α :=
    let Walg := fun zf =>
        match zf with
        | ⟨FreerIxA.Pure a, _⟩ => ULift.up (pure a)
        | ⟨FreerIxA.Impure x gx, next⟩ => let a := do let z ← alg x gx
                                                      ULift.down (next <| ULift.up z)
                                          ULift.up a
    ULift.down <| Wtype.elim.{1} Walg tree.val


inductive FReaderWriter (i : Type) (o : Type) : Type → Type where
    | Get : FReaderWriter i o i
    | Put : o → FReaderWriter i o Unit

def runReaderWriter (val :Nat) (tree : FreerIxW (FReaderWriter Nat Nat) i α) : α :=
  let alg := fun x fr =>
      match fr with
      | FReaderWriter.Get => val
      | FReaderWriter.Put v => ()
  interpretW alg tree

def getW : FreerIxW (FReaderWriter Nat Nat) 0 Nat := liftFreer _ <| @FReaderWriter.Get Nat Nat
def putW (v : Nat) : FreerIxW (FReaderWriter Nat Nat) 1 Unit := liftFreer _ <| @FReaderWriter.Put Nat Nat v

def evalIx {g : Type → Type} {ix : Type} {i : ix} {α : Type} : FreerIxW g i α → ix := fun _ => i

#eval runReaderWriter 4 <| bindIx (bindIx (getW) (fun x => putW x)) (fun _ => putW 3)
#eval evalIx            <| bindIx (bindIx (getW) (fun x => putW x)) (fun _ => putW 3)


-- can't use normal do notation, so we make up a separate syntax for indexed monads

syntax:60 term:60 " ::→ " term:61 : term   -- >>= for indexed monads
syntax:60 term:60 " **→ " term:61 : term   -- >>  for indexed monads

macro_rules
| `($l:term ::→ $r:term) => `(bindIx $l $r)
| `($l:term **→ $r:term) => `(bindIx $l (fun _ => $r))

-- run the monad and output result
#eval runReaderWriter 6 <| getW ::→ putW **→ putW 3 **→ getW

-- should count # of putW's in the monad
#eval evalIx            <| getW ::→ putW **→ putW 3

