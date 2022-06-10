
--
-- Algebraic effects with indices, using the W-type
--
-- If you don't need the index consider Eff instead
--


import QingLong.PFunctor
import QingLong.Wtype
import QingLong.OpenUnion

open pfunctor
open Wtype
open openunion

namespace EffIx

--
-- ix should work like a Haskell Monoid. Here we used Inhabitied and HAdd for this functionality.
--
--inductive Eff (effs : List (Type → Type)) : Type → Type 1 where
--    | Pure : α → Eff effs α
--    | Impure : (γ : Type) → OU effs γ → (γ → Eff effs α) → Eff effs α

inductive EffIxA (effs : List (Type → Type)) (α : Type) : Type 1 where
    | Pure : α → EffIxA effs α 
    | Impure : (x : Type) → OU effs x → EffIxA effs α -- the (x → W ..) part is in the second part of the pfunctor



def EffIxB {effs : List (Type → Type)} {α : Type} : EffIxA effs α → Type
    | .Pure a      => Fin 0 -- can't use False since we need a Type here, not a Prop
    | .Impure x gx => x

def EffIxPF (effs : List (Type → Type)) (α : Type) : pfunctor := pfunctor.mk (EffIxA effs α) (fun v => ULift <| EffIxB v)

structure EffIxW {ix : Type} (effs : List (Type → Type)) (i : ix) (α : Type) : Type 1 where
   val : W (EffIxPF effs α)


-- lift into Eff.
-- These universe shifts are annoying!
def sendEff {α : Type} {g : Type → Type} {effs : List (Type → Type)} [HasEffect g effs] {ix : Type} (i : ix) (ga : g α) : EffIxW effs i α :=
    EffIxW.mk <| ⟨EffIxA.Impure α (HasEffect.inject ga), fun a => W.mk ⟨EffIxA.Pure <| ULift.down a, Fin.elim0 ∘ ULift.down⟩⟩

def pureEff {α : Type} {ix : Type} [Inhabited ix] (i : ix) (a : α) : EffIxW effs i α := EffIxW.mk ⟨EffIxA.Pure a, Fin.elim0 ∘ ULift.down⟩

def bindEffW {effs : List (Type → Type)} {α β : Type} : W (EffIxPF effs α) → (α → W (EffIxPF effs β)) → W (EffIxPF effs β) := fun m1 m2 =>
    match m1 with
    | ⟨EffIxA.Pure a,     _⟩ => m2 a
    | ⟨EffIxA.Impure x ou, bx⟩ => W.mk ⟨EffIxA.Impure x ou, fun x => (@bindEffW effs α β (bx x) m2)⟩

def bindEff {α β ix : Type} [HAdd ix ix ix] {ix₁ ix₂ : ix}
  : EffIxW g ix₁ α → (α → EffIxW g ix₂ β) → EffIxW g (ix₁ + ix₂) β := fun m1 m2 =>
    -- we just strip off the FreerIxW wrapper and recurse
    EffIxW.mk <| bindEffW m1.val (fun x => (m2 x).val)


class IxMonad {ix : Type} (m : ix → Type → Type 1) where
    pureIx : (i : ix) → α → m i α
    bindIx [HAdd ix ix ix] : m i₁ α → (α → m i₂ β) → m (i₁ + i₂) β

open IxMonad

instance {ix : Type} [Inhabited ix] : @IxMonad ix (EffIxW effs) where
    pureIx := fun i a => @pureEff effs _ ix _ i a
    bindIx := bindEff



--
-- EffIxW as a Functor
--

def EffIxMap {ix : Type} {i : ix} (f : α → β) (w : EffIxW effs i α) : EffIxW effs i β :=
    let Walg := fun d =>
        match d with
        | ⟨EffIxA.Pure a, z⟩         => W.mk ⟨EffIxA.Pure (f a), z⟩
        | ⟨EffIxA.Impure x gx, next⟩ => W.mk ⟨EffIxA.Impure x gx, next⟩
    EffIxW.mk <| Wtype.elim Walg w.val

instance : Functor (EffIxW effs i) :=
    { map := EffIxMap }



-- Use the given collapser to convert an algebraic EffIxW monad into a static monad of type m. m is typically
-- IO or StateIO s. For a pure result you could use Id for m.
def interpretM {ix : Type} {i : ix} {α : Type} {m : Type → Type} [Monad m] (c : Collapser m effs) (tree : EffIxW effs i α) : m α :=
    let Walg := fun zf =>
        match zf with
        | ⟨EffIxA.Pure a, _⟩ => ULift.up (pure a)
        | ⟨EffIxA.Impure x gx, next⟩ => let a := do let z ← collapse c gx
                                                    ULift.down (next <| ULift.up z)
                                        ULift.up a
    ULift.down <| Wtype.elim.{1} Walg tree.val






inductive FReaderWriter (i : Type) (o : Type) : Type → Type where
    | Get : FReaderWriter i o i
    | Put : o → FReaderWriter i o Unit

def collapseReaderWriter [StateOperator s "tag" Nat] (val : Nat) : ∀ x, FReaderWriter Nat Nat x → StateIO s x :=
    fun x fr =>
        match fr with
        | FReaderWriter.Get => pure val
        | FReaderWriter.Put v => fun s => pure ⟨(), StateOperator.putNamed "tag" v s⟩

def getW [HasEffect (FReaderWriter Nat Nat) effs] : EffIxW effs 0 Nat := sendEff _ <| @FReaderWriter.Get Nat Nat
def putW [HasEffect (FReaderWriter Nat Nat) effs] (v : Nat) : EffIxW effs 1 Unit := sendEff _ <| @FReaderWriter.Put Nat Nat v

def evalIx {effs : List (Type → Type)} {ix : Type} {i : ix} {α : Type} : EffIxW effs i α → ix := fun _ => i

-- if you have the collapser you can provide it to evalIx in order to help typeclass inference
def evalIxC {effs : List (Type → Type)} {ix : Type} {i : ix} {α : Type} (c : Collapser m effs) (w : EffIxW effs i α) : ix := evalIx w

structure StateTag where (tag : Nat)
  deriving Repr

instance : StateOperator StateTag "tag" Nat where
  putNamed := fun n s => {s with tag := n}
  getNamed := fun s => s.tag

def rwCollapser {s : Type} [StateOperator s "tag" Nat] : Collapser (StateIO s) [FReaderWriter Nat Nat] :=
    mkCollapse
      @collapseReaderWriter s _ 3
      o>

def xCollapser := @rwCollapser StateTag _

def xProg := bindIx (bindIx (getW) (fun x => putW 1)) (fun _ => @putW [FReaderWriter Nat Nat] _ 5)

def x : StateIO StateTag Unit := (@interpretM _ _ _ Unit (StateIO StateTag) _ xCollapser <| xProg)

def runX : StateTag → StateIO StateTag Unit → IO Nat :=
  fun x s => do let ⟨a,s'⟩ ← s x
                pure s'.tag

#eval runX {tag := 2} x

#eval evalIx <| xProg


-- can't use normal do notation, so we make up a separate syntax for indexed monads

syntax:60 term:60 " →→= " term:61 : term   -- >>= for indexed monads
syntax:60 term:60 " →→ " term:61 : term   -- >>  for indexed monads

macro_rules
| `($l:term →→= $r:term) => `(bindIx $l $r)
| `($l:term →→ $r:term) => `(bindIx $l (fun _ => $r))

-- run the monad and output result
#eval runX {tag := 2} <| interpretM xCollapser <| getW →→= putW →→ putW 3 →→ getW →→= putW

-- should count # of putW's in the monad
#eval evalIxC xCollapser <| getW →→= putW →→ getW →→= putW →→ putW 3

