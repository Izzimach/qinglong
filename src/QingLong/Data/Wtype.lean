import QingLong.Data.PFunctor

open pfunctor

-- Contains the basic W type "W_type" as well as "W" which builds a W-type using a polynomial functor P

universe u

namespace Wtype

-- The basic W type
inductive W_type {α : Type u} (β : α → Type u) where
| mk (a : α) (f : β a → W_type β) : W_type β

def to_sigma {α : Type u} {β : α → Type u} : W_type β → (Σ a:α, β a → W_type β)
| ⟨a, f⟩ => ⟨a, f⟩

def of_sigma {α : Type u} {β : α → Type u} : (Σ a:α, β a → W_type β) → W_type β
| ⟨a, f⟩ => W_type.mk a f

-- W Catamorphism using an algebra on Sigma values
def elim {α : Type u} {β : α → Type u} {γ : Type u} (alg : (Σ a:α, β a → γ) → γ) : W_type β → γ
| ⟨a, f⟩ => alg ⟨a, fun b => elim alg (f b)⟩


-- W type for polynomial functors. "W P" is a tree where P describes the branching.
def W (P : pfunctor) := W_type P.B

/-- root element  of a W tree -/
def W.head : W P → P.A
| ⟨a, f⟩ => a

/-- children of the root of a W tree -/
def W.children : (x : W P) → (P.B (W.head x) → W P)
| ⟨a, f⟩ => f

/-- destructor for W-types -/
def W.dest : W P → P.obj (W P)
| ⟨a, f⟩ => ⟨a, f⟩

/-- constructor for W-types -/
def W.mk : P.obj (W P) → W P
| ⟨a, f⟩ => ⟨a, f⟩

-- typeclass to convert another type to/from a W-type
class IsoW (f : Type → Type) where
    pf : Type → pfunctor
    toW : {α : Type} → f α → W (pf α)
    fromW : {α : Type} → W (pf α) → f α


inductive ListA (α : Type u) : Type u where
    | Nil : ListA α
    | Cons : α → ListA α

instance : Functor ListA where
    map f
    | ListA.Nil => ListA.Nil
    | ListA.Cons h => ListA.Cons (f h)

def ListABranch : ListA α → Type
    | ListA.Nil => Fin 0 -- can't use False since we need a Type here, not a Prop
    | ListA.Cons _ => Unit

def ListPF (α : Type) : pfunctor := pfunctor.mk (ListA α) ListABranch

-- list as a W-type
def ListW (α : Type) := W (ListPF α)

-- convert list to a ListW
def ListToW {α : Type} : (l : List α) → ListW α
  | List.nil => ⟨ListA.Nil, Fin.elim0⟩
  | List.cons h t => ⟨ListA.Cons h, (fun _ => ListToW t)⟩
  
def WToList {α : Type} : (lw : ListW α) → List α
  | ⟨ListA.Nil, _⟩ => List.nil
  | ⟨ListA.Cons h, f⟩ => List.cons h (WToList (f ()))

instance : IsoW List where
  pf := ListPF
  toW := ListToW
  fromW := WToList


end Wtype
