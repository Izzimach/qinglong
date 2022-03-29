universe u v

def Top {s : Type} : s → Prop := fun _ => True


structure BaseMonad (α : Type) where
  (output : α)

inductive MonadResultIs {α : Type} : α → BaseMonad α → Prop where
| mk : (z : α) → (mz : BaseMonad α) → (mz.output = z) → MonadResultIs z mz

def MRret {α : Type} (a : α) := MonadResultIs.mk a (BaseMonad.mk a) rfl

def MRbind {α : Type} {a b : α} {ma mb : BaseMonad α} : MonadResultIs a ma → (α → MonadResultIs b mb) → MonadResultIs b mb :=
  fun m1 m2 => match m1 with
               | MonadResultIs.mk z mz zp => m2 z

def MRrun {α : Type} {z : α} {mz : BaseMonad α} (d : MonadResultIs z mz) : α :=
  match d with
  | MonadResultIs.mk r _ hp => r


#check MRret 3
#check MRrun (MRret 3)
-- here we try to run the monad and enforce a return value that is wrong, should produce and error
#check @MRrun Nat 4 _ (MRret 3)

inductive Eeek {α : Type} : α → α → Prop where
| EeekRaf : (z : α) → Eeek z z

def raff {α : Type} {a : α} : Eeek a a:= Eeek.EeekRaf a

#check show Eeek 3 3 by apply raff



structure DijkstraMonad {p₁ p₂ : Prop} (α : Type) (z : (α → p₁) → p₂) where
  (output : α)

def DMonad {α : Type} {p₁ p₂ : Prop} (x : α) (wp : (α → p₁) → p₂) := ∀ (p : α → p₁), p₂ → p₁

def DMret {α : Type} {p₁ p₂ : Prop} (x : α) { wp : (α → p₁) → p₁} : DMonad x wp :=
  fun p p2 => p x

def DMrun {α : Type} {p₁ p₂ : Prop} {x : α} {wp : (α → p₁) → p₂} (d : DMonad x wp) (post : α → p₁) : p₂ := wp post

#check DMret 2
#reduce DMrun (DMret 2) (fun a => show ∀ a, a = 2 → true by simp)

def apple {α : Type} {p₁ :Prop} (x : α) (z : α → p₁) : p₁ := z x

def lit (x : Nat) : ∃ b, b = x :=
  Exists.intro x rfl

def lit2 {p₁ : Prop} {x : α → Prop} (z : ∀ a, x a → p₁) (b : Exists x) : p₁ := Exists.elim b z

def lit3 {p₁ : Prop} (x : α → Prop) (hp : p₁): ∀ a, x a → p₁ :=
  fun (a : α) _ => show p₁ from hp

def lit4 (a : α) (x : α → Prop) {hp : x a} : Exists x := Exists.intro a hp

def DJRet {α : Type} {p₁ : Prop} {z : (α → p₁) → p₁} (x: α) : DijkstraMonad α := DijkstraMonad.mk x

def DJBind {α β : Type} {p₁ p₂ p₃ : Prop} {wp1 : (α → p₂) → p₃} {wp2 : α → (β → p₁) → p₂} :
  DijkstraMonad α wp1 → ( (x:α) → DijkstraMonad β (wp2 x)) → DijkstraMonad β (fun p => wp1 (fun x => wp2 x p)) :=
    fun m1 m2 => let a := DijkstraMonad.output m1
                 let b := DijkstraMonad.output (m2 a)
                 DijkstraMonad.mk b

def DJRun {α : Type} {p₁ p₂ :Prop} {wp : (α → p₁) → p₂} (d : DijkstraMonad α wp) (post : α → p₁) : p₂ := wp post

example : ∃ x : Nat, x = 3 :=
  have h : 3=3 := by rfl
  Exists.intro 3 h

example (h₁ : ∃ x : Nat, x = 3) (z : ∀ x, x = 3 → a > 1) : a > 1 :=
  Exists.elim h₁ z

#check (@DJRun Nat (1=1) (1=1) (fun hp => show 1=1 by rfl) (@DJRet Nat (1=1) (fun hp => hp 2) 2) (fun a => show 1=1 by rfl))
#check @DJRet Nat (1=1) (fun hp => hp 2) 2
#reduce DJRun (DJRet 2) (fun a => show 1=1 by rfl)
#check (lit 3)
#check ∃ x, x = 3
#check ∀ (a : Nat), a = 3 → true
#check @Exists
#check lit2 (lit3 (fun a => a < 3) (show 3=3 by rfl)) (Exists.intro 2 (show (fun a => a < 3) 2 by simp))
#check lit4 (fun a => a < 3) 2
#check ∃ a, a < 3