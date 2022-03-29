
universe u v

--
-- Conor McBride's indexed monads based on indexed types

-- an index-preserving function : (s :→ t)  =  (∀ i, s i → t i)
-- I can be in any type universe, even 0 (Props), so we make it 'Sort u'
def NatTransf {ix : Type u} (s t : ix → Type v) : Type (max u v) := ∀ i, s i → t i

syntax term ":→" term : term
macro_rules
| `($s :→ $t) => `(NatTransf $s $t) -- `(∀ i, $s i → $t i)


-- functional composition. `ComposeNT f g` is  `g . f` for the category :→
def ComposeNT {a b c : ix → Type u} (f : a :→ b) (g : b :→ c) : a :→ c := 
  fun (i : ix) (v : a i) => g i (f i v)


class IFunctor {ix : Type u} (f : (ix → Type u) → (ox → Type u)) where
  imap {s t : ix → Type u} : (s :→ t) → f s :→ f t


inductive VerifiedValue (α : Type) : Bool → Type u where
| VVal : α → {x : Bool} → VerifiedValue α x

def liftVV : (α → β) → VerifiedValue α :→ VerifiedValue β :=
  fun (f : α → β) {i : Bool} (s : VerifiedValue α i) =>
    match s with
    | (VerifiedValue.VVal a) => VerifiedValue.VVal (f a)


inductive LockedIndex {ix : Type u} (α : Type u) : ix → ix → Type u where
| LockAt : α → (x : ix) → LockedIndex α x x

inductive LockProp {ix : Type u} (α : Type u) : (ix → Prop) → ix → Type u where
| LockProp : α → (p : ix → Prop) → (x :ix) → LockProp α p x

syntax term ";=;" term : term
macro_rules
| `($a ;=; $k) => `(LockedIndex $a $k)


-- keep going! 加油！
class IMonad {ix : Type u} (m : (ix → Type u) → ix → Type u) where
  iskip {p : ix → Type u} : p :→ m p
  iextend {p q : ix → Type u} : (p :→ m q) → (m p :→ m q)


def iseq {ix : Type u} {m : (ix → Type u) → ix → Type u} [IMonad m] {p q r : ix → Type u} :
         (p :→ m q) → (q :→ m r) → (p :→ m r) :=
  fun f g => ComposeNT f (IMonad.iextend g)

def demonicBind {ix : Type u} {m : (ix → Type u) → ix → Type u} [IMonad m] {p q r : ix → Type u} {i : ix} :
         m p i → (p :→ m q) → m q i :=
  fun mpi mpq => (IMonad.iextend mpq i) mpi

def angelicBind {ix : Type u} {m : (ix → Type u) → ix → Type u} [IMonad m] {p q r : ix → Type u} {i j : ix} :
         m (a ;=; j) i → (a → m q j) → m q i :=
  fun mai mqj => @demonicBind ix m _ (a ;=; j) q r i mai 
                    (fun j' v => match v with
                                 | (LockedIndex.LockAt a j') => mqj a)



def akReturn {ix : Type u} {i : ix} {m : (ix → Type u) → ix → Type u} [IMonad m] (α : Type u) (a : α) : m (α ;=; i) i := 
  @IMonad.iskip ix m _ (@LockedIndex ix α i) i (LockedIndex.LockAt a i)


-- Identity as an indexed functor
inductive IxId {ix : Type u} (p : ix → Type u) : ix → Type u where
| IxId : (f : p i) → IxId p i

instance {ix : Type u} : IFunctor (@IxId ix) where
  imap h := fun (i : ix) v =>
              match v with
              | IxId.IxId f => IxId.IxId (h i f)

-- IxId as a function synonym instead
def IdentityX {ix : Type u} : (ix → Type u) → ix → Type u := id

instance {ix : Type u} : IFunctor (@IdentityX ix) where
  imap h := fun (i : ix) f => h i f


-- Index holder is a simple indexed datatype (ix → Type u)
inductive IndexHolder {ix : Type u} : ix → Type u where
| IDH : (i : ix) → IndexHolder i

#check IndexHolder.IDH 3
#check IdentityX IndexHolder true

inductive FileState : Prop where
| FileOpen
| FileClosed

inductive FileState0 : Type 0 where
| FileOpen0
| FileClosed0

inductive FileState1 : Type 1 where
| FileOpen1
| FileClosed1

inductive Unit1 : Type 1 where
| U1

inductive StateTransition {ix : Type u} (p q r : ix → Type u) : ix → Type u where
| STr : p i → (q :→ r) → StateTransition p q r i

instance {ix : Type u} {p q r : ix → Type u} : IFunctor (StateTransition p q) where
  imap h := fun (i:ix) pk =>
              match pk with
              | StateTransition.STr pi qr => StateTransition.STr pi (ComposeNT qr h)

#check StateTransition (@LockedIndex FileState0 FileState0 FileState0.FileOpen0)
#check (StateTransition (@LockedIndex FileState0 Unit FileState0.FileOpen0) (@LockedIndex FileState0 Unit FileState0.FileClosed0))
#check @LockedIndex Bool PUnit 


def FHF : (FileState0 → Type) → FileState0 → Type := (StateTransition (@LockedIndex FileState0 Unit FileState0.FileOpen0) (@LockedIndex FileState0 Unit FileState0.FileClosed0))

inductive FH {ix : Type u} (f : (ix → Type u) → ix → Type u) (p : ix → Type u) : ix → Type u where
| FHX : (x : f p i) → FH f p i

#check (IdentityX IndexHolder true)
#check @FH.FHX FileState0 IdentityX IndexHolder FileState0.FileOpen0 (IndexHolder.IDH FileState0.FileOpen0)
#print PUnit

instance {ix : Type u} {p : (ix → Type u) → ix → Type u} [IFunctor p]: IFunctor (@FH ix p) where
  imap h := fun (i : ix) fhp =>
              match fhp with 
              | FH.FHX x => FH.FHX (IFunctor.imap h i x)

def FHOpen : Type := sorry

