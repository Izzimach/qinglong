
--
-- Algebraic effects with indices, using the W-type
--
-- If you don't need the index consider Eff instead
--


import QingLong.Data.PFunctor
import QingLong.Data.Wtype
import QingLong.Data.OpenUnion

open pfunctor
open Wtype
open openunion

namespace EffIx

inductive Indexer (x : Type) : Type where
  | Null : Indexer x
  | Leaf : x → Indexer x
  | Append : Indexer x → Indexer x → Indexer x

def evalIndexer {ix : Type} [Inhabited ix] [HAdd ix ix ix] : (i : Indexer ix) → ix
  | .Null => default
  | .Leaf x => x
  | .Append a b => evalIndexer a + evalIndexer b

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

structure EffIxW {ix : Type} (effs : List (Type → Type)) (i : Indexer ix) (α : Type) : Type 1 where
   val : W (EffIxPF effs α)


-- lift into Eff, explicitly specifying the index
def sendEffIx {α : Type} {g : Type → Type} {effs : List (Type → Type)} [HasEffect g effs] {ix : Type} (i : Indexer ix) (ga : g α) : EffIxW effs i α :=
    EffIxW.mk <| ⟨EffIxA.Impure α (HasEffect.inject ga), fun a => W.mk ⟨EffIxA.Pure <| ULift.down a, Fin.elim0 ∘ ULift.down⟩⟩

-- lift into Eff. Use the default value for the monad index
def sendEff {α : Type} {g : Type → Type} {effs : List (Type → Type)} [HasEffect g effs] {ix : Type} (ga : g α) := @sendEffIx α g effs _ ix Indexer.Null ga

-- pure for Eff with explicit index
def pureEffIx {α : Type} {ix : Type} (i : Indexer ix) (a : α) : EffIxW effs i α := EffIxW.mk ⟨EffIxA.Pure a, Fin.elim0 ∘ ULift.down⟩

-- Uses the default index for the monad
def pureEff {α : Type} {effs : List (Type → Type)} {ix : Type} (a : α) := @pureEffIx effs α ix Indexer.Null a


def bindEffW {effs : List (Type → Type)} {α β : Type} : W (EffIxPF effs α) → (α → W (EffIxPF effs β)) → W (EffIxPF effs β) := fun m1 m2 =>
    match m1 with
    | ⟨EffIxA.Pure a,     _⟩ => m2 a
    | ⟨EffIxA.Impure x ou, bx⟩ => W.mk ⟨EffIxA.Impure x ou, fun x => (@bindEffW effs α β (bx x) m2)⟩

def bindEff {α β ix : Type} {ix₁ ix₂ : Indexer ix}
  : EffIxW g ix₁ α → (α → EffIxW g ix₂ β) → EffIxW g (Indexer.Append ix₁ ix₂) β := fun m1 m2 =>
    -- we just strip off the FreerIxW wrapper and recurse
    EffIxW.mk <| bindEffW m1.val (fun x => (m2 x).val)



class IxMonad {ix : Type} (m : Indexer ix → Type → Type 1) where
    pureIx : (i : Indexer ix) → α → m i α
    bindIx : m i₁ α → (α → m i₂ β) → m (Indexer.Append i₁ i₂) β

open IxMonad

instance {ix : Type} : @IxMonad ix (EffIxW effs) where
    pureIx := fun i a => @pureEffIx effs _ ix i a
    bindIx := bindEff



--
-- EffIxW as a Functor
--

def EffIxMap {ix : Type} {i : Indexer ix} (f : α → β) (w : EffIxW effs i α) : EffIxW effs i β :=
    let Walg := fun d =>
        match d with
        | ⟨EffIxA.Pure a, z⟩         => W.mk ⟨EffIxA.Pure (f a), z⟩
        | ⟨EffIxA.Impure x gx, next⟩ => W.mk ⟨EffIxA.Impure x gx, next⟩
    EffIxW.mk <| Wtype.elim Walg w.val

instance : Functor (EffIxW effs i) :=
    { map := EffIxMap }



-- Use the given collapser to convert an algebraic EffIxW monad into a static monad of type m. m is typically
-- IO or StateIO s. For a pure result you could use Id for m.
def interpretM {ix : Type} {i : Indexer ix} {α : Type} {m : Type → Type} [Monad m] (c : Collapser m effs) (tree : EffIxW effs i α) : m α :=
    let Walg := fun zf =>
        match zf with
        | ⟨EffIxA.Pure a, _⟩ => ULift.up (pure a)
        | ⟨EffIxA.Impure x gx, next⟩ => let a := do let z ← collapse c gx
                                                    ULift.down (next <| ULift.up z)
                                        ULift.up a
    ULift.down <| Wtype.elim.{1} Walg tree.val







inductive NamedState (n : String) (v : Type) : Type → Type where
  | Get : NamedState n v v
  | Put : v → NamedState n v Unit

def collapseNamedState [StateOperator s n v] : ∀ x, NamedState n v x → StateIO s x :=
  fun x m =>
    match m with
    | .Get => fun s => pure ⟨StateOperator.getNamed n s,s⟩
    | .Put v' => fun s => pure ⟨(), StateOperator.putNamed n v' s⟩


def getW (n : String) {ix v : Type} {effs : List (Type → Type)} 
    [HasEffect (NamedState n v) effs] : EffIxW effs (@Indexer.Null ix) v := sendEffIx (@Indexer.Null ix) <| @NamedState.Get n _

def putW (n : String) {ix v : Type} (x : v) {effs : List (Type → Type)}
    [HasEffect (NamedState n v) effs] : EffIxW effs (@Indexer.Null ix) Unit := sendEffIx (@Indexer.Null ix) <| @NamedState.Put n v x

#check HAppend

def evalIx {effs : List (Type → Type)} {ix : Type} [Inhabited ix] [HAdd ix ix ix] {i : Indexer ix} {α : Type} : EffIxW effs i α → ix := fun _ => evalIndexer i

-- if you have the collapser you can provide it to evalIx in order to help typeclass inference
def evalIxC {effs : List (Type → Type)} {ix : Type} [Inhabited ix] [HAdd ix ix ix] {i : Indexer ix} {α : Type} (c : Collapser m effs) (w : EffIxW effs i α) : ix := evalIx w

/-structure StateTag where (tag : Nat)
    deriving Repr

instance : StateOperator StateTag "tag" Nat where
    putNamed := fun n s => {s with tag := n}
    getNamed := fun s => s.tag

def rwCollapser {s : Type} [StateOperator s "tag" Nat] : Collapser (StateIO s) [NamedState "tag" Nat] :=
    mkCollapse
      @collapseNamedState s "tag" Nat _
      o>

def xCollapser := @rwCollapser StateTag _

  
def xProg {ix : Type} {i : Indexer ix} {effs : List (Type → Type)} [HasEffect (NamedState "tag" Nat) effs] :=
    getW "tag"
    --bindIx (bindIx (@getW "tag" ix Nat effs _) (fun x => putW "tag" 2)) (fun _ => @putW "tag" ix Nat 3 effs _)

def x : StateIO StateTag Unit := (@interpretM _ _ _ Unit (StateIO StateTag) _ xCollapser <| xProg)

def runX : StateTag → StateIO StateTag Unit → IO Nat :=
  fun x s => do let ⟨a,s'⟩ ← s x
                pure s'.tag

#eval runX {tag := 2} x

#eval evalIxC xCollapser xProg


-- run the monad and output result
#eval runX {tag := 2} <| interpretM xCollapser <| getW →→= putW →→ putW 3 →→ getW →→= putW

-- should count # of putW's in the monad
#eval evalIxC xCollapser <| getW →→= putW →→ getW →→= putW →→ putW 3

-/