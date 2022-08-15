
import QingLong.Macro.SumMacro
import QingLong.Macro.FreerMacro
import QingLong.Data.NamedState

import QingLong.Macro.Deconstruct

import Lean
import Lean.Parser.Term

open Lean Elab Expr Command Term Meta 

open Freer SumMacro NamedState
open Deconstruct

inductive Concurrent (mutexIx : Type) : Type → Type where
| Lock : mutexIx → Concurrent mutexIx Unit
| Unlock : mutexIx → Concurrent mutexIx Unit

def collapseConcurrent (v : Type) {α : Type}: Concurrent v α → StateIO s α :=
  fun m =>
    match m with
    | .Lock ix => fun s => pure ⟨(),s⟩
    | .Unlock ix => fun s => pure ⟨(), s⟩

partial
def loopUntilResult {m : Type u → Type (u+1)} {α : Type u} [Inhabited α] [Monad m] : m (Option α) → m α :=
   fun moa => do
     let x ← moa
     match x with
     | Option.none => loopUntilResult moa
     | Option.some x => pure <| x


-- Here we build a sum type and freer indexed monad to use. These will eventually get interpreted into a
-- final monad implementing the state and IO
mkSumType ExampleCommand >| (NamedState "z" Nat), (Concurrent Nat), IO |<
mkFreer ExampleMonad ExampleCommand

-- some "code" written to use a monad supporting state. This uses the NameState command to increment whatever
-- is in the state labeled "z". m could be ExampleCommand or any other monad that implements (NamedState "z" Nat)
def incZ {m : Type → Type 1} [Sendable (NamedState "z" Nat) m] [Monad m] : m Nat := do
    let z ← getNamed "z"
    putNamed "z" (z+1)
    pure 3

def exampleX [Monad m] [Sendable IO m] [Sendable (NamedState "z" Nat) m]: m Nat := do
    putNamed "z" 4
    Sendable.send <| IO.println 3
    pure 3


-- A StateIO monad with two state variables and IO. Used as the collapse target of the following interpreter.
mkStateIO OneState (z:Nat), (y:String) @@

/-
#check StateIO
#check OneState Nat
-/

-- The interpreter translates code from the abstract-ish ExampleCommand monad into the concrete OneState monad
def interpreter1 := buildInterpreter ExampleCommand OneState (NamedState "z" Nat),(Concurrent Nat),IO
    [:
      -- NamedState "z" Nat
      collapseNamedState "z" Nat,
      -- Concurrent Nat
      collapseConcurrent Nat,
      -- IO
      collapseIO
    :]

def gork := runExampleMonad interpreter1
              exampleX -- code
              {z := 3, y := "Argh"} -- initial state

#check gork

def blargh : t → t := fun x => x

def x : ExampleMonad Nat := loopUntilResult <| do
        putNamed "z" 5
        --let (z:Nat) ← @getNamed "z" Nat _ _
        pure <| Option.some 3



#eval walkExpr ((do blargh <| putNamed "z" 5; pure 3) : ExampleMonad Nat)

-- given a parameterized type, strip off the last parameter so it's (Type → Type)
-- and compare to a monad type that is already of the form Type → Type
def monadMatch : Expr → Expr → MetaM Bool := fun t m =>
    match t with
    | app m2 _ _ => isDefEq m m2
    | forallE n a b _ => monadMatch b m
    | _ => pure false

-- Checks if some type is one of the monad types in the provided list. If it is, returns some
-- Expr value. If not, returns Option.none
-- So if the list was t := [⟨IO,"IO"⟩,⟨Free Id,"Free"⟩] then
--   > checkAgainstMonads (IO a) t => Option.some "IO"
--   > checkAgainstMonads Nat t    => Option.none
--   > checkAgainstMonads (Free Id Nat) t => Option.some "Free"
def checkAgainstMonads : Expr → List (Expr × Expr) → MetaM (Option Expr) := fun t l =>
    match l with
    | List.nil => pure Option.none
    | List.cons head tail => do
        let m ← monadMatch t head.1
        if m
        then pure (Option.some head.2)
        else do
            checkAgainstMonads t tail


def dispatchSend (converters : List (Expr × Expr)) (targetType : Expr) (argStack : List Expr) : TermElabM Expr := do
    let m := argStack.get! 4
    let et ← inferType m
    --goExpr sending 0
    let m ← checkAgainstMonads et converters
    --logInfo argStack
    match m with
    | Option.none => pure <| Lean.mkAppN (Lean.mkConst ``FreerSkeleton.Error) #[targetType, Lean.mkStrLit "no match for send"]--(argStack.get! 4)))
    | Option.some f => pure <| Lean.mkAppN (Lean.mkConst ``FreerSkeleton.Command) #[targetType, Lean.mkAppN f #[argStack.get! 3, argStack.get! 4]]


set_option hygiene false in
elab "magicSendSkeleton" skelName:ident " $: " target:term ">: " transforms:doElem " :$ " : command => do
    let skelCommand ← 
        `(@[termElab skeletonize]
          def $skelName : TermElab := fun stx oxe => do
              let e ← elabTerm (Syntax.getArg stx 1) Option.none
              let t ← $transforms
              magicSkeleton (stdMonadSkeleton ``String ++ [⟨"send",fun args mk => dispatchSend t $target args⟩]) [] e
         )
    elabCommand skelCommand

def tx : TermElabM (List (Expr × Expr)) := do
    let tm : List (Prod (TermElabM Syntax) (TermElabM Syntax)) :=
        [⟨`(IO),
              `(fun (a : Type) (z : IO a) => "IO")⟩,
         ⟨`(NamedState "z" Nat),
              `(fun (a : Type) (x : NamedState "z" Nat a) => match x with 
                                      | NamedState.Get => "Get"
                                      | NamedState.Put x => "Put " ++ toString x)⟩]
    let runProd : TermElabM Syntax × TermElabM Syntax → TermElabM (Expr × Expr) :=
        fun ⟨n,t⟩ => do
           let nE ← elabTerm (← n) Option.none
           let tE ← elabTerm (← t) Option.none
           pure <| ⟨nE,tE⟩
    List.mapM runProd tm

syntax (name := skeletonize) "goSkeleton" term " ::: " term : term

magicSendSkeleton freerSkel $: Lean.mkConst ``String >: tx :$    

#check Sendable.send


def yx : Nat → FreerSkeleton String := fun buzz => goSkeleton 
    (do Sendable.send <| IO.println "argh"
        putNamed "z" 3
        match buzz with
        | 0 => pure 3
        | 1 => pure 5
        | _ => pure 7
        : ExampleMonad Nat)
    ::: 7

#eval toString <| yx 5

#check goSkeleton (do Sendable.send <| IO.println "argh"; putNamed "z" 3; pure () : ExampleMonad Unit) ::: 7

