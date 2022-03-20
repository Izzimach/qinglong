
universe u v

--
-- Conor McBride's indexed monads based on indexed types

-- an index-preserving function : (s :→ t)  =  (∀ i, s i → t i)
-- I can be in any type universe, even 0 (Props), so we make it 'Sort u'
def NatTransf {ix : Sort u} (s t : ix → Type v) : Sort (max u (v+1)) := ∀ i, s i → t i

syntax term ":→" term : term
macro_rules
| `($s :→ $t) => `(NatTransf $s $t) -- `(∀ i, $s i → $t i)


-- functional composition. `ComposeNT f g` is  `g . f` for the category :→
def ComposeNT {a b c : ix → Type u} (f : a :→ b) (g : b :→ c) : a :→ c := 
  fun (i : ix) (v : a i) => g i (f i v)


class IFunctor {ix : Sort u} (f : (ix → Type u) → (ox → Type u)) where
  imap {s t : ix → Type u} : (s :→ t) → f s :→ f t


inductive VerifiedValue (α : Type) : Bool → Type u where
| VVal : α → {x : Bool} → VerifiedValue α x

def liftVV : (α → β) → VerifiedValue α :→ VerifiedValue β :=
  fun (f : α → β) {i : Bool} (s : VerifiedValue α i) =>
    match s with
    | (VerifiedValue.VVal a) => VerifiedValue.VVal (f a)


inductive LockedIndex {ix : Sort u} (α : Type u) : ix → ix → Type u where
| LockAt : α → (x : ix) → LockedIndex α x x

inductive LockProp {ix : Sort u} (α : Type u) : (ix → Prop) → ix → Type u where
| LockProp : α → (p : ix → Prop) → (x :ix) → LockProp α p x

syntax term ";=;" term : term
macro_rules
| `($a ;=; $k) => `(LockedIndex $a $k)


-- 加油!
class IMonad {ix : Sort u} (m : (ix → Type u) → ix → Type u) where
  iskip {p : ix → Type u} : p :→ m p
  iextend {p q : ix → Type u} : (p :→ m q) → (m p :→ m q)


def iseq {ix : Sort u} {m : (ix → Type u) → ix → Type u} [IMonad m] {p q r : ix → Type u} :
         (p :→ m q) → (q :→ m r) → (p :→ m r) :=
  fun f g => ComposeNT f (IMonad.iextend g)

def demonicBind {ix : Sort u} {m : (ix → Type u) → ix → Type u} [IMonad m] {p q r : ix → Type u} {i : ix} :
         m p i → (p :→ m q) → m q i :=
  fun mpi mpq => (IMonad.iextend mpq i) mpi

def angelicBind {ix : Sort u} {m : (ix → Type u) → ix → Type u} [IMonad m] {p q r : ix → Type u} {i j : ix} :
         m (a ;=; j) i → (a → m q j) → m q i :=
  fun mai mqj => @demonicBind ix m _ (a ;=; j) q r i mai 
                    (fun j' v => match v with
                                 | (LockedIndex.LockAt a j') => mqj a)



def akReturn {ix : Sort u} {i : ix} {m : (ix → Type u) → ix → Type u} [IMonad m] (α : Type u) (a : α) : m (α ;=; i) i := 
  @IMonad.iskip ix m _ (@LockedIndex ix α i) i (LockedIndex.LockAt a i)



inductive FileState : Type where
| FileOpen
| FileClosed

inductive FileState1 : Type 1 where
| FileOpen1
| FileClosed1

inductive Unit1 : Type 1 where
| U1

inductive StateTransition {ix : Sort u} (p q r : ix → Type u) : ix → Type u where
| STr : p i → (q :→ r) → StateTransition p q r i

instance {ix : Sort u} {p q r : ix → Type u} : IFunctor (StateTransition p q) where
  imap h := fun (i:ix) pk =>
              match pk with
              | StateTransition.STr pi qr => StateTransition.STr pi (ComposeNT qr h)

#check StateTransition (@LockedIndex FileState FileState1 FileState.FileOpen)
#check (StateTransition (@LockedIndex FileState Unit1 FileState.FileOpen) (@LockedIndex FileState Unit1 FileState.FileClosed))

inductive FH {ix : Sort u} : ((p : ix → Type u) → (q : ix) → Type u) → Type u where
| FHI : (s₁ : ix) → (s₂ :ix) → FH (StateTransition (@LockedIndex ix PUnit s₁) (@LockedIndex ix PUnit s₂))

#check FH.FHI FileState.FileOpen FileState.FileClosed


