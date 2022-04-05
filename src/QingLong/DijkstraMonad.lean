universe u v

--
-- a simple monad along with a proof that the monad returns a specific value
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
#check @MRrun Nat 4 _ (MRret 3)


def dPred (α : Type) : Type := α → Prop

def retEqPred {α : Type} (v : α) : dPred α := fun y => y = v
def retEqProof {α : Type} (v : α) : retEqPred v v := show v = v by rfl

def bindPred {α β : Type} (p : dPred α) (f : α → dPred β) : dPred β := fun b => ∃ (a:α), p a ∧ f a b

inductive MonadWithPredicate {α : Type} : α → dPred α → Type where
| mk : (mz : BaseMonad α) → (pf : p mz.output) → MonadWithPredicate (mz.output) p

def retMW {α : Type} {p : dPred α} (v : α) (pf : p v) := MonadWithPredicate.mk (BaseMonad.mk v) pf

-- bind that just uses the predicate of the most recent monad. All monads need to use the same predicate here.
def bindMW {α : Type} {p : dPred α} {a b : α} {ma mb : BaseMonad α} : MonadWithPredicate a p → (α → MonadWithPredicate b p) → MonadWithPredicate b p :=
  fun m1 m2 => match m1 with
               | MonadWithPredicate.mk mz1 pf1 => m2 mz1.output

-- bind that combines (using AND) the predicates of both monads
def bindMWAnd {α : Type} {p₁ p₂ : dPred α} {a b : α} : MonadWithPredicate a p₁ → (α → MonadWithPredicate b p₂) → MonadWithPredicate b (fun b => ∃x, p₁ x ∧ (p₂ b)) :=
  fun m1 m2 => match m1 with
               | MonadWithPredicate.mk mz1 pf1 =>
                 match (m2 mz1.output) with
                 | MonadWithPredicate.mk mz2 pf2 =>
                     MonadWithPredicate.mk mz2 (show ∃ x, p₁ x ∧ p₂ mz2.output from Exists.intro mz1.output (And.intro pf1 pf2))

def runPred {α : Type} {a : α} (p : dPred α) (m : MonadWithPredicate (a : α) p) : p a :=
  match m with
  | MonadWithPredicate.mk b pf => pf


#check show ∃ x, x=3 from Exists.intro 3 (_:3=3)
#reduce (retMW 3 _ : MonadWithPredicate 3 (retEqPred 3))
#reduce (retMW 3 (retEqProof 3) : MonadWithPredicate 3 (retEqPred 3))
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


inductive MonadFwdPredicate {α : Type} : Prop → α → fPred α → Type where
| mk : (mz : BaseMonad α) → (pf : ∀ (hpre : pre), p pre mz.output) → MonadFwdPredicate pre (mz.output) p


def retFP {α : Type} (v : α) {pre :Prop} : MonadFwdPredicate pre v (@simpleFP α v) :=
  let bm := BaseMonad.mk v
  MonadFwdPredicate.mk bm (fun (hpre : pre) => show simpleFP v pre bm.output from (And.intro hpre rfl))

def bindFP {α :Type} {a b : α} {pre1 : Prop} {p₁ p₂ : fPred α} :
  MonadFwdPredicate pre1 a p₁ → (α → MonadFwdPredicate (p₁ pre1 a) b p₂) → MonadFwdPredicate pre1 b (fun pre z => ∃ a, p₂ (p₁ pre a) z) :=
    fun m f => match m with 
               | MonadFwdPredicate.mk z1 pf1 =>
                   match (f z1.output) with
                   | MonadFwdPredicate.mk z2 pf2 =>
                       MonadFwdPredicate.mk z2 (fun pre => Exists.intro z1.output (pf2 (pf1 pre)))


def runFP {α : Type} {pre1 :Prop} {a : α} {p₁ : fPred α} (m : MonadFwdPredicate pre1 a p₁) : pre1 → p₁ pre1 a :=
  fun p1 => match m with 
            | MonadFwdPredicate.mk ma pf => pf p1

def sampleProg := runFP (bindFP (retFP 3) (fun _ => bindFP (retFP 5) (fun _ => retFP 4))) (rfl : 2=2)

-- backward transforming predicate

def bPred (α : Type) : Type := (α → Prop) → Prop

-- for backward transformers we need to map pointwise under the transformer. This also restricts transformers to be monotonic
class MonoBackward (w : bPred α) where
  monoMap {p₁ p₂ : α → Prop} : (∀ a , p₁ a → p₂ a) → w p₁ → w p₂

def simpleBP {α : Type} (v : α) : bPred α := fun (post : α → Prop) => post v

instance {α : Type} {v : α}: MonoBackward (simpleBP v) where
  monoMap  {p₁ p₂ : α → Prop} :=  fun f wp1 => f v wp1

inductive MonadBwdPredicate {α : Type} : α → bPred α → (α → Prop) → Type where
| mk : (mz : BaseMonad α) → (pf : ∀ x, x = mz.output → p post) → MonadBwdPredicate (mz.output) p post



def retBP {α : Type} (v : α) {post : α → Prop} (postpf: post v) : MonadBwdPredicate v (@simpleBP α v) post:=
  let bm := BaseMonad.mk v
  MonadBwdPredicate.mk bm (fun x (he : x = bm.output) => postpf)

def bindBP {α : Type} {a b : α} {post1 : α → Prop} {p₁ p₂ : bPred α} [MonoBackward p₁] :
  MonadBwdPredicate a p₁ (fun x => ∀ post2, x = a → post2) → (α → MonadBwdPredicate b p₂ post1) → MonadBwdPredicate b (fun post => p₁ (fun x => b = x → p₂ post)) post1 :=
    fun m f => match m with
               | MonadBwdPredicate.mk z1 pf1 =>
                 match (f z1.output) with
                 | MonadBwdPredicate.mk z2 pf2 =>
                     MonadBwdPredicate.mk z2 (fun x he =>
                                                    let (hp : ∃ x, x = z1.output) := Exists.intro z1.output (show _ by rfl)
                                                    let hx : p₁ fun x => ∀ post2 , x = z1.output → post2 := Exists.elim hp pf1
                                                    let tx :  ∀ (a : α), (∀ (postx : Prop), a = z1.output → postx) → z2.output = a → p₂ post1 :=
                                                      fun a postx eq =>
                                                        let eq' := show _ from Eq.symm eq
                                                        pf2 a eq'
                                                    MonoBackward.monoMap tx hx
                     )

def runBP {α : Type} {post1 : α → Prop} {a : α} {p₁ : bPred α} (m : MonadBwdPredicate a p₁ post1) : ∀ x, x = a → p₁ post1 :=
  fun a => match m with
           | MonadBwdPredicate.mk ma pf => pf a

#check retBP 3 rfl

def sampleBack := runBP (retBP 3 rfl) 3