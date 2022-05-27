universe u v


--
-- Conor McBride's indexed monads based on indexed types

-- an index-preserving function : (s :→ t)  =  (∀ i, s i → t i)
-- I can be in any type universe, even 0 (Props), so we make it 'Sort u'
def NatTransf {ix : Sort u} (s t : ix → Sort v) : Sort (imax u v) := ∀ i, s i → t i

syntax term ":→" term : term
macro_rules
| `($s :→ $t) => `(NatTransf $s $t)

-- As NatTransf, but with two indices
def DoubleIndexed {ix₁ ix₂ : Sort u} (s t : ix₁ → ix₂ → Sort v) : Sort (imax u u v) := ∀ i₁ i₂, s i₁ i₂ → t i₁ i₂

syntax term "::→" term : term
macro_rules
| `($s ::→ $t) => `(DoubleIndexed $s $t)


-- natural transformation composition. `ComposeNT f g` is  `g . f` for the category :→
def ComposeNT {a b c : ix → Sort u} (f : a :→ b) (g : b :→ c) : a :→ c := 
  fun (i : ix) (v : a i) => g i (f i v)


class IFunctor {ix : Sort u} (f : (ix → Sort v) → (ix → Sort v)) where
  imap {s t : ix → Sort v} : (s :→ t) → f s :→ f t


class IMonad {ix : Sort u} (m : (ix → Sort v) → ix → Sort v) where
  iskip {p : ix → Sort v} : p :→ m p
  iextend {p q : ix → Sort v} : (p :→ m q) → (m p :→ m q)


inductive LockedValue {ix : Sort u} (α : Sort v) : ix → ix → Type (max u v) where
| LockAt : α → (x : ix) → LockedValue α x x


inductive UnlockedValue {ix : Sort u} (α : Sort v) : ix → Type (max u v) where
| Ret : α → UnlockedValue α x 

inductive LockProp {ix : Sort u} (α : Sort v) : (ix → Prop) → ix → Type (max u v) where
| LockProp : α → (p : ix → Prop) → (x :ix) → LockProp α p x

syntax term ";=;" term : term
macro_rules
| `($a ;=; $k) => `(LockedValue $a $k)

inductive IndexLessThan (ixlt : Nat) : Nat → Type u where
| mk : (ix < ixlt) → IndexLessThan ixlt ix


def returnLocked {ix : Sort u} {i : ix} {m : (ix → Type (max u v)) → ix → Type (max u v)} [IMonad m] (α : Sort v) (a : α) : m (α ;=; i) i := 
  @IMonad.iskip ix m _ (@LockedValue ix α i) i (LockedValue.LockAt a i)

def returnUnlocked {ix : Sort u} {i : ix} {m : (ix → Type (max u v)) → ix → Type (max u v)} [IMonad m] (α : Sort v) (a : α) : m (UnlockedValue α) i :=
  @IMonad.iskip ix m _ (@UnlockedValue ix α) i (@UnlockedValue.Ret ix α i a)


-- compose and binds

def iseq {ix : Sort u} {m : (ix → Type u) → ix → Type u} [IMonad m] {p q r : ix → Type u} :
         (p :→ m q) → (q :→ m r) → (p :→ m r) :=
  fun f g => ComposeNT f (IMonad.iextend g)

def demonicBind {ix : Sort u} {m : (ix → Type u) → ix → Type u} [IMonad m] {p q : ix → Type u} {i : ix} :
         m p i → (p :→ m q) → m q i :=
  fun mpi mpq => (IMonad.iextend mpq i) mpi

def angelicBind {ix : Sort u} {a : Sort v} {m : (ix → Type (max u v)) → ix → Type (max u v)} [IMonad m] {p q : ix → Type (max u v)} {i j : ix} :
         m (a ;=; j) i → (a → m q j) → m q i :=
         -- we manually apply demonicBind here to avoid type-hackery
  fun mai mqj => IMonad.iextend (fun j' v => match v with | (LockedValue.LockAt a j') => mqj a) i <| mai

-- Identity as an indexed functor
inductive IxId {ix : Sort u} (p : ix → Type u) : ix → Type u where
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
def IdentityX {ix : Sort u} : (ix → Type u) → ix → Type u := id

instance {ix : Type u} : IFunctor (@IdentityX ix) where
  imap h := fun (i : ix) f => h i f

instance : @IMonad ix IdentityX where
  iskip := fun i pi => pi
  iextend := fun pq ip pip => pq ip pip


def needsLessThan : IndexLessThan 3 :→ IdentityX (UnlockedValue String) := fun i ilt => returnUnlocked String "argh"

def processLT := demonicBind (IndexLessThan.mk (show 1 < 3 by simp)) needsLessThan



--
-- Freer monad as a functor/monad and indexed functor/monad
--

inductive Free (f : Sort u → Type v) (α : Sort u) : Type (max u v) where
| Pure : α → Free f α
| Impure {x : Sort u} : (x → Free f α) → f x → Free f α

def freeMap (k : α → β) : Free f α → Free f β
| Free.Pure a => Free.Pure (k a)
| Free.Impure next v => Free.Impure (fun x => freeMap k <| next x) v

instance : Functor (Free f) where
  map := freeMap

def freePure {α : Type u} : (a : α) → Free f α := Free.Pure

def freeBind (m : Free f α) (k : α → Free f β) : Free f β :=
    match m with
    | Free.Pure a => k a
    | Free.Impure next v => Free.Impure (fun x => freeBind (next x) k) v

instance : Monad (Free f) where
  pure := freePure
  bind := freeBind

class IFunctor1 (f : (Sort u → Type v) → (Sort u → Type v)) where
  imap {s t : Sort u → Type v} : (s :→ t) → f s :→ f t

class IMonad1 (m : (Sort u → Type u) → Sort u → Type u) where
  iskip {p : Sort u → Type u} : p :→ m p
  iextend {p q : Sort u → Type u} : (p :→ m q) → (m p :→ m q)

def fImap (f : s :→ t) (i : Sort u) : Free s i → Free t i
| Free.Pure a => Free.Pure a
| Free.Impure next v => Free.Impure (fun xx => fImap f _ (next xx)) (f _ v)

instance : IFunctor1 Free where
  imap := fImap

def freeExtend (f : p :→ Free q) : (Free p :→ Free q) :=
  fun ix fpi => match fpi with
      | Free.Pure a => Free.Pure a
      | Free.Impure next v => (f _ v) >>= (fun x => freeExtend f _ <| next x) 

instance : IMonad1 Free where
  iskip := fun i pi => Free.Impure Free.Pure pi
  iextend := freeExtend



--
-- Free Monad of indexed types
--
class IndexedMonoid (ix : Type v) where
   pureIndex : ix
   bindIndex : ix → ix → ix

inductive FreeIx {ix : Type v} (w : ix → Sort u → Type u) : ix → Sort u → Type (max v u) where
| Pure : α → FreeIx w i α
| Impure {x : Sort u} {j : ix} : (x → FreeIx w i α) → w j x → FreeIx w i α


def freeixMap {w : (ix → Sort u → Type u)} (k : α → β) : FreeIx w i α → FreeIx w i β
| FreeIx.Pure a => FreeIx.Pure (k a)
| FreeIx.Impure next v => FreeIx.Impure (fun x => freeixMap k <| next x) v
  termination_by freeixMap k f => 1
  decreasing_by sorry

instance : Functor (FreeIx w ix) where
  map := freeixMap

def ffreePure {α : Sort u} {ix : Type v} {w : ix → Sort u → Type u}  [IndexedMonoid ix] : (a : α) → FreeIx w IndexedMonoid.pureIndex α := FreeIx.Pure

def combine {ix : Type v} [IndexedMonoid ix] (i j : ix) : ix := IndexedMonoid.bindIndex i j

def reIndex : FreeIx w i₁ α → FreeIx w i₂ α
| FreeIx.Pure a => FreeIx.Pure a
| FreeIx.Impure next v => FreeIx.Impure (fun x => reIndex <| next x) v

def ffreeBind {ix : Type v} {i j : ix} {w : ix → Sort u → Type u } [IndexedMonoid ix] (m : FreeIx w i α) (k : α → FreeIx w j β) : FreeIx w (combine i j) β :=
    match m with
    | FreeIx.Pure a => match k a with
                       | FreeIx.Pure a' => FreeIx.Pure a'
                       | FreeIx.Impure next' v' => reIndex <| FreeIx.Impure next' v'
    | FreeIx.Impure next v => FreeIx.Impure (fun x => ffreeBind (next x) k) v
  termination_by ffreeBind k f => 1
  decreasing_by sorry




