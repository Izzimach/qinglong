universe u v

--
-- Model of Dijkstra monads, which combine a base monad (usually representing code) with a second
-- monad that is a predicate or prop/proof about the monad behavior.  This monad product is represented by
-- "MonadWithPredicate"
--

structure BaseMonad (α : Type) where
  (output : α)

inductive MonadResultIs {α : Type} : α → Type where
| mk : (mz : BaseMonad α) → MonadResultIs (mz.output)

def MRret {α : Type} (a : α) := MonadResultIs.mk (BaseMonad.mk a)

def MRbind {α : Type} {a b : α} {ma mb : BaseMonad α} : MonadResultIs a → (α → MonadResultIs b) → MonadResultIs b :=
  fun m1 m2 => match m1 with
               | MonadResultIs.mk mz => m2 (mz.output)

def MRrun {α : Type} {z : α} {mz : BaseMonad α} (d : MonadResultIs z) : α :=
  match d with
  | MonadResultIs.mk mz => mz.output


#check MRret 3
#reduce MRrun (MRret 3)
#reduce MRrun (MRbind (MRret 2) (fun _ => MRret 3))
-- here we try to run the monad and enforce a return value (4) that is wrong (actually returns 3).  This should produce and error
#check @MRrun Nat 4 _ (MRret 4)


def dPred (α : Type) : Type := α → Prop

def retEqPred {α : Type} (v : α) : dPred α := fun y => y = v
def retEqProof {α : Type} (v : α) : retEqPred v v := show v = v by rfl

def bindPred {α β : Type} (p : dPred α) (f : α → dPred β) : dPred β := fun b => ∃ (a:α), p a ∧ f a b

inductive MonadWithPredicate (α : Type) : dPred α → Type where
| mk : (mz : BaseMonad α) → (pf : p mz.output) → MonadWithPredicate α p

def retMW {α : Type} {p : dPred α} (v : α) (pf : p v) := MonadWithPredicate.mk (BaseMonad.mk v) pf

-- bind that just uses the predicate of the most recent monad. All monads need to use the same predicate here.
def bindMW {α : Type} {p : dPred α} {a b : α} {ma mb : BaseMonad α} : MonadWithPredicate α p → (α → MonadWithPredicate α p) → MonadWithPredicate α p :=
  fun m1 m2 => match m1 with
               | MonadWithPredicate.mk mz1 pf1 => m2 mz1.output

-- bind that combines (using AND) the predicates of both monads
def bindMWAnd {α : Type} {p₁ p₂ : dPred α} : MonadWithPredicate α p₁ → (α → MonadWithPredicate α p₂) → MonadWithPredicate α (fun b => ∃x, p₁ x ∧ (p₂ b)) :=
  fun m1 m2 => match m1 with
               | MonadWithPredicate.mk mz1 pf1 =>
                 match (m2 mz1.output) with
                 | MonadWithPredicate.mk mz2 pf2 =>
                     MonadWithPredicate.mk mz2 (show ∃ x, p₁ x ∧ p₂ mz2.output from Exists.intro mz1.output (And.intro pf1 pf2))

def runPred {α : Type} (p : dPred α) (m : MonadWithPredicate α p) : ∃ x, p x :=
  match m with
  | MonadWithPredicate.mk b pf => Exists.intro b.output pf


#check show ∃ x, x=3 from Exists.intro 3 (_ : 3=3)
#reduce (retMW 3 _ : MonadWithPredicate Nat (retEqPred 3))
#reduce (retMW 3 (retEqProof 3) : MonadWithPredicate Nat (retEqPred 3))
#reduce (runPred (retEqPred 3) (retMW 3 _))
#reduce (runPred _ (bindMW (retMW 3 (retEqProof 3)) (fun _ => retMW 3 (retEqProof 3))))
#reduce (runPred _ (bindMWAnd (retMW 3 (retEqProof 3)) (fun _ => retMW 4 (retEqProof 4))))

def runProg := runPred (retEqPred 3) (retMW 3 (retEqProof 3))
def runProg2 := (runPred _ (bindMWAnd (retMW 3 (retEqProof 3)) (fun (x : Nat) => retMW 4 (retEqProof 4))))


#check @runProg2
#check Exists.intro 3 rfl
#check (show (∃ x, x = 3) from (Exists.intro 3 rfl))
#check (show (∀ a, a = 3 → retEqPred 3 3) from (fun a (_:a=3) => _))
#check Exists.elim (show (∃ x, x = 3) from (Exists.intro 3 rfl)) (show (∀ a, a = 3 → retEqPred 3 3) from (fun a (_:a=3) => _))


example (h: ∃ x, retEqPred 3 x ∧ retEqPred 4 4) : retEqPred 3 3 := by
  let hx : ∀ a, retEqPred 3 a ∧ retEqPred 4 4 → retEqPred 3 3 := show ∀a, retEqPred 3 a ∧ retEqPred 4 4 → retEqPred 3 3 from (fun a x => show _ from rfl)
  apply Exists.elim h hx

-- forward transforming predicate

def fPred (α : Type) : Type := Prop → α → Prop

def simpleFP {α : Type} (v : α) : fPred α := fun (pre:Prop) (a : α) => pre ∧ a = v


inductive MonadFwdPredicate {α : Type} : Prop → fPred α → Type where
| mk : (mz : BaseMonad α) → (pf : ∀ (hpre : pre), p pre mz.output) → MonadFwdPredicate pre p


def retFP {α : Type} (v : α) {pre :Prop} : MonadFwdPredicate pre (@simpleFP α v) :=
  let bm := BaseMonad.mk v
  MonadFwdPredicate.mk bm (fun (hpre : pre) => show simpleFP v pre bm.output from (And.intro hpre rfl))

def bindFP {α :Type} {pre1 : Prop} {p₁ p₂ : fPred α} :
  MonadFwdPredicate pre1 p₁ → (α → MonadFwdPredicate (∃a, p₁ pre1 a) p₂) → MonadFwdPredicate pre1 (fun pre z => p₂ (∃a, p₁ pre a) z) :=
    fun m f => match m with 
               | MonadFwdPredicate.mk z1 pf1 =>
                   match (f z1.output) with
                   | MonadFwdPredicate.mk z2 pf2 =>
                       MonadFwdPredicate.mk z2 (fun pre => (pf2 (Exists.intro z1.output (pf1 pre))))


def runFP {α : Type} {pre1 :Prop} {p₁ : fPred α} (m : MonadFwdPredicate pre1 p₁) : pre1 → ∃ a, p₁ pre1 a :=
  fun p1 => match m with 
            | MonadFwdPredicate.mk ma pf => Exists.intro ma.output (pf p1)

def sampleProg := runFP (bindFP (retFP 3) (fun _ => bindFP (retFP 5) (fun _ => retFP 4))) (rfl : 2=2)


-- backward transforming predicate

def bPred (α : Type) : Type := (α → Prop) → Prop

-- for backward transformers we need to map pointwise under the transformer when binding monads.
-- This also restricts transformers to be monotonic
class MonoBackward (w : bPred α) where
  monoMap {p₁ p₂ : α → Prop} : (∀ a , p₁ a → p₂ a) → w p₁ → w p₂

def simpleBP {α : Type} (v : α) : bPred α := fun (post : α → Prop) => post v

instance {α : Type} {v : α}: MonoBackward (simpleBP v) where
  monoMap  {p₁ p₂ : α → Prop} :=  fun f wp1 => f v wp1

inductive MonadBwdPredicate {α : Type} : bPred α → (α → Prop) → Type where
| mk : (mz : BaseMonad α) → (pf : p post) → MonadBwdPredicate p post



def retBP {α : Type} (v : α) {post : α → Prop} {postpf: post v} : MonadBwdPredicate (@simpleBP α v) post:=
  let bm := BaseMonad.mk v
  MonadBwdPredicate.mk bm postpf

def bindBP {α : Type} {post1 post2 : α → Prop} {p₁ p₂ p₃ : bPred α} [MonoBackward p₁] :
  MonadBwdPredicate p₁ post1 → (α → MonadBwdPredicate p₂ post2) → MonadBwdPredicate (fun (p : α → Prop) => p₁ (fun a => post1 a ∧ p₂ post2)) post2 :=
    fun m f => match m with
               | MonadBwdPredicate.mk z1 pf1 =>
                 match (f z1.output) with
                 | MonadBwdPredicate.mk z2 pf2 =>
                     MonadBwdPredicate.mk z2 (let hx : ∀ a, post1 a → post1 a ∧ p₂ post2 := fun a p1 => And.intro p1 pf2
                                              MonoBackward.monoMap hx pf1)

def runBP {α : Type} {post1 : α → Prop} {p₁ : bPred α} (m : MonadBwdPredicate p₁ post1) : p₁ post1 :=
  match m with | MonadBwdPredicate.mk ma pf => pf

#check retBP 3

def sampleBack := @runBP Nat (fun x => 3 = x → Eq 3 3) (simpleBP 3) (@retBP Nat 3 _ id)
def sampleBack2 : simpleBP 3 fun x => 3 = x → 3 = 3 := runBP (@retBP Nat 3 _ id)


-- backward predicate for state monad

def Top {x : Type} : x → Prop  := fun _ => True

def bSPred (s α : Type) : Type := (α × s → Prop) → s → Prop

def StatePM (s : Type) (α : Type) : Type := s → (α × s)

inductive MonadBwdState (s : Type) (α: Type) (p : bSPred s α) : Type where
| mk : (ms : StatePM s α) → (pf : ∀ post s, p post s → post (ms s)) → MonadBwdState s α p


def retBS {s α : Type} (a : α) : MonadBwdState s α (fun post s0 => post ⟨a, s0⟩) :=
  let md : StatePM s α := fun s => ⟨a,s⟩
  MonadBwdState.mk md (fun post s_1 => by
                          intro pst
                          let (h : md s_1 = (a, s_1)) := by simp
                          rw [h]
                          assumption
                       )

-- monadic bind of backward state transformers
def bindWBS {s α β : Type} (wc : bSPred s α) (wf : α → bSPred s β) : bSPred s β :=
  fun p s0 => wc (fun ⟨a,s1⟩ => wf a p s1) s0


def bindBS {s α β : Type} {wc : bSPred s α} {wf : α → bSPred s β} :
           MonadBwdState s α wc → ((x : α) → MonadBwdState s β (wf x)) → MonadBwdState s β (bindWBS wc wf) :=
  fun m1 f =>
    match m1 with
    | MonadBwdState.mk ms1 pf1 =>
        let mm  := fun s₁ =>
                        let mo1:= ms1 s₁
                        let m2 := f mo1.1
                        match m2 with
                        | MonadBwdState.mk ms2 pf2 => ms2 mo1.2
        let pf3 := fun post s₁ bindW =>
                        let mo1 := ms1 s₁
                        let m2 := f mo1.1
                        let ms2 := m2.1
                        let pf2 := m2.2
                        let ⟨a₂,s₃⟩ := mm s₁  -- actual results from monad running
                        let postX := fun (a,s) => wf a post s
                        let postXrfl : postX = (fun (a,s) => wf a post s) := by simp
                        let postT₁ := pf1 postX s₁
                        let postT₂ := pf2 post mo1.2
                        let hh : wc postX s₁ := by unfold bindWBS at bindW; assumption
                        let pf12 := postT₁ hh
                        let hpf12 : postX (ms1 s₁) = wf mo1.1 post mo1.2 := by simp
                        let hh2 : wf mo1.1 post mo1.2 := by rw [hpf12] at pf12; assumption
                        let pf3 := postT₂ hh2
                        let hme : ms2 = (f (ms1 s₁).fst).1 := by simp
                        let hh3 : ms2 mo1.2 = mm s₁:= by simp
                        by rewrite [←hh3]; assumption
        MonadBwdState.mk mm pf3

