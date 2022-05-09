-- stolen from mathlib3

universe u v


structure pfunctor :=
(A : Type u) (B : A → Type u)


namespace pfunctor

variable (P : pfunctor) {α β : Type u}

-- for a given functor F, you would build the corresponding structure "F α" such as
-- "List α" or "Option α" but for a given polynomial functor P, you instead
-- build the structure "P.obj α"
def obj (α : Type u) := Σ x : P.A, P.B x → α

def map (f : α → β) : P.obj α → P.obj β := fun ⟨a, g⟩ => ⟨a, f ∘ g⟩

-- The inhabited instance just defers default to the relevant shape and payload types
instance [Inhabited P.A] [Inhabited α] : Inhabited (P.obj α) :=
  ⟨ ⟨ default, fun _ => default ⟩ ⟩

instance : Functor P.obj :=
  {map := P.map}

-- an "identity" pfunctor
def pfunctor0 : pfunctor := pfunctor.mk Unit (fun _ => Unit)
def pfunctor0.mk {α :Type u} (a : α) : pfunctor0.obj α := ⟨ () , fun () => a ⟩

/-- functor composition for polynomial functors -/
def comp (P₂ P₁ : pfunctor.{u}) : pfunctor.{u} :=
⟨ Σ a₂ : P₂.1, P₂.2 a₂ → P₁.1,
  fun a₂a₁ => Σ u : P₂.2 a₂a₁.1, P₁.2 (a₂a₁.2 u) ⟩

/-- constructor for composition -/
def comp.mk (P₂ P₁ : pfunctor.{u}) {α : Type} (x : P₂.obj (P₁.obj α)) : (comp P₂ P₁).obj α :=
⟨ ⟨ x.1, Sigma.fst ∘ x.2 ⟩, fun a₂a₁ => (x.2 a₂a₁.1).2 a₂a₁.2  ⟩

/-- destructor for composition -/
def comp.get (P₂ P₁ : pfunctor.{u}) {α : Type} (x : (comp P₂ P₁).obj α) : P₂.obj (P₁.obj α) :=
⟨ x.1.1, fun a₂ => ⟨x.1.2 a₂, fun a₁ => x.2 ⟨a₂,a₁⟩ ⟩ ⟩


--
-- Here we prove LawfulFunctor for the a given polynomial P, or specifically we prove for
-- it's functor form P.obj
--

protected theorem map_eq (f : α → β) (a : P.A) (g : P.B a → α) :
  @Functor.map P.obj _ _ _ f ⟨a, g⟩ = ⟨a, f ∘ g⟩ := rfl

protected theorem id_map : ∀ x : P.obj α, id <$> x = id x :=
  fun ⟨a, b⟩ => rfl

protected theorem comp_map {γ : Type u} (f : α → β) (g : β → γ) :
  ∀ x : P.obj α, (g ∘ f) <$> x = g <$> (f <$> x) :=
    fun ⟨a, b⟩ => rfl

protected theorem map_const : (Functor.mapConst : α → P.obj β → P.obj α) = Functor.map ∘ Function.const β :=
  rfl

instance : LawfulFunctor P.obj where
    map_const := @pfunctor.map_const P
    id_map    := @pfunctor.id_map P
    comp_map  := @pfunctor.comp_map P



end pfunctor

