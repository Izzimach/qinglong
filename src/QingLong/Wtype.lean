import QingLong.PFunctor

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

end Wtype
