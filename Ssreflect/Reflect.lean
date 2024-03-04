import Lean
import Lean.Elab.Tactic
import Std.Lean.Meta.UnusedNames
import Ssreflect.Utils
import Std.Tactic.Omega

open Lean Lean.Expr Lean.Meta
open Lean Elab Command Term Meta Tactic


@[simp] def evenb : Nat -> Bool
  | 0 => true
  | 1 => false
  | n +2=> evenb n

inductive even : Nat -> Prop where
  | zero : even 0
  | add2 (n : Nat) : even n -> even (n + 2)

class inductive Reflect (P : Prop) (b : outParam Bool) : Type
  | T (_ : P) (_:b) : Reflect P b
  | F (_ : ¬ P) (_:b=false) : Reflect P b

@[inline] abbrev Reflect.toProp (b : Bool) {P : Prop} [Reflect P b] : Prop := P

theorem toPropEq (eq : b1 = b2) [inst1:Reflect P1 b1] [inst2:Reflect P2 b2] :
  @Reflect.toProp b1 _ inst1 = @Reflect.toProp b2 _ inst2 := by
  simp [Reflect.toProp]
  cases inst1 <;> cases inst2 <;> simp_all

-- #check Expr

@[simp↑] theorem decide_decidable_of_bool {P} : @decide p (decidable_of_bool b P) = b := by
  by_cases h : p <;> simp_all
  { apply Eq.symm; rw [P]; simp_all }
  cases b <;> simp_all

def reflect_of_equiv : (b = true <-> P) -> Reflect P b := by
  cases b <;> simp <;> intro p
  { apply Reflect.F; assumption; rfl }
  constructor; assumption; trivial

def equiv_of_reflect : Reflect P b -> (b = true <-> P) := by
  intro r; cases r <;> simp_all

-- instance reflect_of_decide [Decidable P] : Reflect P (decide P) := by

instance [Reflect P b] : Decidable P := by
  eapply decidable_of_bool
  apply equiv_of_reflect
  assumption

def reflect_of_decide [inst1: Decidable P] : b = decide P -> Reflect P b := by
  intros r; apply reflect_of_equiv; rw [r]
  cases inst1 <;> simp_all

macro "reflect" n:num : attr =>
  `(attr| default_instance 1000+$n)

macro "reflect" : attr =>
  `(attr| default_instance 1000)

@[reflect 1]
instance ReflectEven (n: Nat) : Reflect (even n) (evenb n) :=
  match n with
  | 0 => by simp <;> repeat constructor
  | 1 => by simp; apply Reflect.F; intro r; cases r; trivial
  | n + 2 => by
    simp; cases (ReflectEven n)
    { apply Reflect.T <;> try assumption
      constructor; assumption }
    apply Reflect.F <;> try assumption
    intro n; cases n; contradiction

@[reflect]
instance : Reflect True true := by apply Reflect.T <;> simp_all
@[reflect]
instance ReflectFalse : Reflect False false := by apply Reflect.F <;> simp_all
@[reflect 1]
instance ReflectAnd : [Reflect P1 b1] -> [Reflect P2 b2] -> Reflect (P1 /\ P2) (b1 && b2) := by
  intros i1 i2; apply reflect_of_decide
  by_cases h : P1 <;> cases i1 <;> simp_all


-- #reduce Reflect.toProp (evenb 0)

def generatePropSimp (np nb : Expr) : TermElabM Unit := do
  let (some np, some nb) := (np.constName?, nb.constName?) | throwError s!"Not a constant"
  -- let .some eqs := (eqnsExt.getState (env) |>.map.find? nb) | failure
  let some eqs <- getEqnsFor? nb | throwError s!"No reduction rules for {nb}"
  let mut names : Array Name := #[]
  for eq in eqs do
    -- dbg_trace "Bool:{eq}"
    let env <- getEnv
    let some c := env.find? eq | throwError s!"No reduction rule with name {eq}"
    let cT := c.type
    let name <- forallTelescopeReducing cT fun args cT => do
      let rhsb := cT.getAppArgs[1]!
      let lhsb := cT.getAppArgs[2]!

      let rhsbs <- PrettyPrinter.delab rhsb
      let t <- `(term| Reflect.toProp $rhsbs)
      let rhs <- Term.elabTermAndSynthesize t none

      let lhsbs <- PrettyPrinter.delab lhsb
      let t <- `(term| Reflect.toProp $lhsbs)
      let lhs <- elabTermAndSynthesize t none
      let rhs <- withTransparency (mode := TransparencyMode.reducible) <| reduce rhs (skipProofs := false) (skipTypes := false)
      let lhs <- withTransparency (mode := TransparencyMode.reducible) <| reduce lhs (skipProofs := false) (skipTypes := false)
      let type <- mkForallFVars args $ <- mkEq rhs lhs
      let value <- lambdaTelescope c.value! fun args _ => do
        let thm <- mkAppOptM c.name (args.map Option.some)

        let thms <- PrettyPrinter.delab thm
        let t <- `(term| toPropEq $thms)
        let body <- elabTermAndSynthesize t none

        mkLambdaFVars args body
      let name := c.name ++ "_Prop"
      addDecl <| Declaration.thmDecl {
        name, type, value
        levelParams := c.levelParams
      }
      -- dbg_trace "Prop:{name}"
      let env <- getEnv
      let s := simpExtension.getState env
      let s <- s.addConst name
      modifyEnv (fun env => simpExtension.modifyState env (fun _ => s))
      return name
    names := names.push name
    modifyEnv (fun env => simpExtension.modifyState env (·.registerDeclToUnfoldThms np names))

elab "#reflect" ip:ident ib:ident : command => liftTermElabM <| do
  let ip <- Term.elabTerm ip none
  let ib <- Term.elabTerm ib none
  generatePropSimp ip ib

#reflect even evenb

-- @[simp] def leb' : Nat -> Nat -> Bool
--   | n+1, m+1 => leb' n m
--   | 0, _ => true
--   | _, _ => false

-- example n : leb' (.succ n) (.succ n) := by dsimp; sorry

-- @[reflect 2]
-- instance (n m : Nat) : Reflect (LE.le n m) (leb' n m) := by sorry
-- #reflect Nat.le leb'

-- set_option pp.raw true

-- example (n m : Nat) : (Nat.succ n) <= (Nat.succ m) := by
--   simp
