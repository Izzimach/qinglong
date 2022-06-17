/- A State monad with Hoare Logic style pre/post invariants -/


-- Hoare logic pre and post invariants
def Pre (s : Type) : Type := s → Prop
def Post (s α : Type) : Type := s → α → s → Prop

-- Hoare Logic State monad returns a (s × α × post) structure
structure HLOut (s α : Type) (postCondition : Post s α) (stateIn : s) where
  (stateOut : s) (retVal : α) (postInvariant : postCondition stateIn retVal stateOut)

-- state monad with pre/post invariants
def HLStateM (s : Type) (pre : Pre s) (α : Type) (post : Post s α) : Type := 
  (s₁ : s) → pre s₁ → HLOut s α post s₁


def Top {s : Type} : Pre s  := fun _ => True



def HLreturn (s α : Type) : ∀ x, @HLStateM s Top α (fun i y f => i = f ∧ y = x) :=
  fun retVal =>
    -- s → preCondition → HLO
    fun state hPre => HLOut.mk state retVal (And.intro rfl rfl)

--
-- From "The Hoare State Monad" by Wouter Swierstra
--
def HLBind {s α β : Type} {pre1 : Pre s} {pre2 : α → Pre s} {post1 : Post s α} {post2 : α → Post s β} :
  (@HLStateM s pre1 α post1) →
  ((x : α) → @HLStateM s (pre2 x) β (post2 x)) →
  @HLStateM s 
    (fun (s₁ : s) => pre1 s₁ ∧ (∀ (x :α) (s₂ : s), post1 s₁ x s₂ → pre2 x s₂))
    β
    (fun (s₁ : s) (y : β) (s₃ :s) => ∃ (x : α), ∃ (s₂ : s), post1 s₁ x s₂ ∧ post2 x s₂ y s₃) := 
      fun c₁ c₂ s₁ pb =>
        have pre₁ : pre1 s₁ := pb.left
        match c₁ s₁ pre₁ with
        | HLOut.mk s₂ x p₁ => 
          have pre₂ : pre2 x s₂ := pb.right x s₂ p₁
          match c₂ x s₂ pre₂ with
          | HLOut.mk s₃ b p₃ =>
            have post₂ : ∃ x s₂, post1 s₁ x s₂ ∧ post2 x s₂ b s₃ := Exists.intro x (Exists.intro s₂ (And.intro p₁ p₃))
            HLOut.mk s₃ b post₂

def HLget {s : Type} : HLStateM s Top s (fun i x f => i = f ∧ x = i) :=
  fun state hPre => HLOut.mk state state (And.intro rfl rfl)

def HLput {s : Type} (x : s) : @HLStateM (s : Type) Top Unit (fun _ _ f => f = x) :=
  fun _     hPre => HLOut.mk x () rfl

def preSimp : Prop → Prop := sorry


def putget : HLStateM Nat Top Nat (fun i x f => x = 3) :=
  let x := HLBind (HLput 3) (fun _ => HLget)
  x
