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


inductive LockedValue {ix : Type u} (α : Type u) : ix → ix → Type u where
| LockAt : α → (x : ix) → LockedValue α x x

inductive UnlockedValue {ix : Type u} (α : Type u) : ix → Type u where
| Ret : α → UnlockedValue α x 

inductive LockProp {ix : Type u} (α : Type u) : (ix → Prop) → ix → Type u where
| LockProp : α → (p : ix → Prop) → (x :ix) → LockProp α p x

syntax term ";=;" term : term
macro_rules
| `($a ;=; $k) => `(LockedValue $a $k)


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
                                 | (LockedValue.LockAt a j') => mqj a)



def returnLocked {ix : Type u} {i : ix} {m : (ix → Type u) → ix → Type u} [IMonad m] (α : Type u) (a : α) : m (α ;=; i) i := 
  @IMonad.iskip ix m _ (@LockedValue ix α i) i (LockedValue.LockAt a i)

def returnUnlocked {ix : Type u} {i : ix} {m : (ix → Type u) → ix → Type u} [IMonad m] (α : Type u) (a : α) : m (UnlockedValue α) i :=
  @IMonad.iskip ix m _ (@UnlockedValue ix α) i (@UnlockedValue.Ret ix α i a)


-- Identity as an indexed functor
inductive IxId (p : ix → Type u) : ix → Type u where
| IxId : p i → IxId p i

instance {ix : Type u} : IFunctor (@IxId ix) where
  imap h := fun (i : ix) v =>
              match v with
              | IxId.IxId f => IxId.IxId (h i f)

instance : @IMonad ix IxId where
  iskip := fun i pi => IxId.IxId pi
  iextend := fun pq ip pip => match pip with
                              | IxId.IxId f => pq ip f

--  Indexed Identity as a function synonym instead
def IdentityX {ix : Type u} : (ix → Type u) → ix → Type u := id

instance {ix : Type u} : IFunctor (@IdentityX ix) where
  imap h := fun (i : ix) f => h i f

instance : @IMonad ix IdentityX where
  iskip := fun i pi => pi
  iextend := fun pq ip pip => pq ip pip


inductive IndexLessThan (ixlt : Nat) : Nat → Type where
| mk : (ix < ixlt) → IndexLessThan ixlt ix



structure PredicatedValue (pred : Nat → Prop) : Type where
    (val : Nat) (proof : pred val)
    deriving Repr

def LimitedUse (n : Nat) : Nat → Prop := (fun s => s < n)

def ResourceUse (n : Nat) : Type := PredicatedValue (LimitedUse n)

def CombineResourceUse (a : ResourceUse n) (b : ResourceUse m) : ResourceUse (n + m) :=
    let h1 : a.val < n := a.proof
    let h2 : b.val < m := b.proof
    PredicatedValue.mk (a.val + b.val) (show (a.val + b.val < n + m) from Nat.add_lt_add h1 h2)

def m1 := IdentityX ResourceUse 1
def m2 := IdentityX ResourceUse 3


def bump1 (h : ResourceUse n) : ResourceUse (n+1) :=
    PredicatedValue.mk (h.val + 1) (Nat.succ_lt_succ h.proof)

def weaken' (h : ResourceUse n) {h2 : n <= m}: ResourceUse m :=
    let pf₃ : h.val <  m := Nat.lt_of_lt_of_le h.proof h2
    PredicatedValue.mk h.val pf₃

def rBind (m1: IdentityX ResourceUse n) (m2 : IdentityX ResourceUse m) : IdentityX ResourceUse (n + m) :=
  PredicatedValue.mk (m1.val + m2.val) (show m1.val+m2.val < n + m from Nat.add_lt_add m1.proof m2.proof)

syntax "|↑" term : term
macro_rules
  | `(|↑ $t) => `(@weaken' _ _ $t (by simp))

#check Exists.elim


#eval (|↑ (bump1 (PredicatedValue.mk 1 (show 1 < 2 by simp))) : ResourceUse 3)
#print Bind

