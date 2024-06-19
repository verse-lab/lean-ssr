import Lean
import Lean.Elab.Tactic
import Batteries.Lean.Meta.UnusedNames
import Ssreflect.Utils
-- import Batteries.Tactic.Omega

open Lean Lean.Expr Lean.Meta
open Lean Elab Command Term Meta Tactic

class inductive Reflect (P : Prop) (b : outParam Bool) : Prop
  | T (_ : P) (_:b) : Reflect P b
  | F (_ : ¬ P) (_:b=false) : Reflect P b

@[inline] abbrev Reflect.toProp b {P} [Reflect P b] := P

theorem toPropEq (_: b1 = b2) [inst1:Reflect P1 b1] [inst2:Reflect P2 b2] :
  P1 = P2 := by
  simp [Reflect.toProp]
  cases inst1 <;> cases inst2 <;> simp_all

-- #check Expr

theorem decide_decidable_of_bool {P} : @decide p (decidable_of_bool b P) = b := by
  by_cases h : p <;> simp_all
  cases b <;> simp_all

def reflect_of_equiv : (b = true <-> P) -> Reflect P b := by
  cases b <;> simp <;> intro p
  { apply Reflect.F; assumption; rfl }
  constructor; assumption; trivial

def equiv_of_reflect : Reflect P b -> (b = true <-> P) := by
  intro r; cases r <;> simp_all

instance [Reflect P b] : Decidable P := by
  apply decidable_of_bool
  apply equiv_of_reflect
  assumption

def reflect_of_decide [inst1: Decidable P] : b = decide P -> Reflect P b := by
  intros r; apply reflect_of_equiv; rw [r]
  cases inst1 <;> simp_all

macro "reflect" n:num : attr =>
  `(attr| default_instance $n)

-- macro "reflect" "-" n:num : attr =>
--   `(attr| default_instance 1001-$n)

macro "reflect" : attr =>
  `(attr| default_instance)

def generatePropSimp (np nb : Expr) : CommandElabM Unit := liftTermElabM do
  let (some np, some nb) := (np.getAppFn.constName?, nb.getAppFn.constName?) | throwError s!"Either {np} or {nb} is not a function application"
  let some eqs <- getEqnsFor? (nonRec := true) nb | throwError s!"No reduction rules for {nb}"
  let rs <- getReducibilityStatus nb
  setReducibilityStatus nb .irreducible
  let mut names : Array Name := #[]
  for eq in eqs, i in [0:eqs.size] do
    let env <- getEnv
    let some c := env.find? eq | throwError s!"No reduction rule with name {eq}"
    let cT := c.type
    trace[reflect_names] c.name ++ " : " ++ c.type
    let name <- forallTelescopeReducing cT fun args cT => do
      let rhsb := cT.getAppArgs[1]!
      let lhsb := cT.getAppArgs[2]!

      let rhsbs <- PrettyPrinter.delab rhsb
      let t <- `(term| Reflect.toProp $rhsbs)
      let rhs <- Term.elabTermAndSynthesize t none

      let lhsbs <- PrettyPrinter.delab lhsb
      let t <- `(term| Reflect.toProp $lhsbs)
      let lhs <- withTransparency (mode := TransparencyMode.reducible) <| elabTermAndSynthesize t none
      -- IO.println s! "{rhs}"
      -- dbg_trace "lhs:{lhs}"
      let rhs <- withTransparency (mode := TransparencyMode.reducible) <| reduce rhs (skipProofs := false) (skipTypes := false)
      let lhs <- withTransparency (mode := TransparencyMode.reducible) <| reduce lhs (skipProofs := false) (skipTypes := false)
      let type <- mkForallFVars args $ <- mkEq rhs lhs
      let value <- lambdaTelescope c.value! fun args _ => do
        let thm <- mkAppOptM c.name (args.map Option.some)

        let thms <- PrettyPrinter.delab thm
        let t <- `(term| toPropEq $thms)
        let body <- elabTermAndSynthesize t none

        mkLambdaFVars args body
      let name := `eq_ ++ np ++ (s!"{i}").toName
      addDecl <| Declaration.thmDecl {
        name, type, value
        levelParams := c.levelParams
      }
      trace[reflect] c.type ++ "\n ~~> \n" ++ type
      trace[reflect_names] name ++ " : " ++ type
      -- TODO: configure if the simp theorem is local or global
      addSimpTheorem simpExtension name (post := true) (inv := false) AttributeKind.global (eval_prio default)
      return name
    names := names.push name
    modifyEnv (fun env => simpExtension.modifyState env (·.registerDeclToUnfoldThms np names))
    setReducibilityStatus nb rs

elab "#reflect" ip:term:max ib:term : command => do
  let ip <- liftTermElabM <| Term.elabTerm ip none
  let ib <- liftTermElabM <| Term.elabTerm ib none
  generatePropSimp ip ib

@[reflect]
instance trueP : Reflect True true := by apply Reflect.T <;> simp_all
@[reflect]
instance talseP : Reflect False false := by apply Reflect.F <;> simp_all
@[reflect]
instance andP : [Reflect P1 b1] -> [Reflect P2 b2] -> Reflect (P1 ∧ P2) (b1 && b2) := by
  intros i1 i2; apply reflect_of_decide
  by_cases h : P1 <;> cases i1 <;> simp_all [decide_decidable_of_bool]
@[reflect]
instance orP : [Reflect P1 b1] -> [Reflect P2 b2] -> Reflect (P1 ∨ P2) (b1 || b2) := by
  intros i1 i2; apply reflect_of_decide
  by_cases h : P1 <;> cases i1 <;> simp_all [decide_decidable_of_bool]
@[default_instance]
instance ifP [Reflect P1 b1] [Reflect P2 b2] [Decidable P] :
  Reflect (if P then P1 else P2) (if P then b1 else b2) := by
  by_cases P <;> simp_all
@[reflect]
instance decideP : [Decidable P] -> Reflect P (decide P) := by
  intros; apply reflect_of_decide; trivial

-- Examples

-- @[simp] def evenb : Nat -> Bool
--   | 0 => true
--   | 1 => false
--   | n + 2=> evenb n

-- inductive even : Nat -> Prop where
--   | zero : even 0
--   | add2 : ∀ n, even n -> even (n + 2)

/- False /\ P = False -/
/- True /\ P = P -/

/- false && b = b -/

-- @[reflect]
-- instance ReflectEven (n: Nat) : Reflect (even n) (evenb n) :=
--   match n with
--   | 0 => by simp <;> repeat constructor
--   | 1 => by simp; apply Reflect.F; intro r; cases r; trivial
--   | n + 2 => by
--     simp; cases (ReflectEven n)
--     { apply Reflect.T <;> try assumption
--       constructor; assumption }
--     apply Reflect.F <;> try assumption
--     intro n; cases n; contradiction

-- -- set_option trace.reflect true
-- #reflect even evenb

-- theorem even_eq : even n -> even (m + n) = even m := by
--   intro ev
--   induction ev with
--   | zero => { intros; rfl }
--   | add2 n ev n_ih => rw [<-Nat.add_assoc, <-n_ih]; simp



-- def leb' : Nat -> Nat -> Bool
--   | n+1, m+1 => leb' n m
--   | 0, _ => true
--   | _, _ => false

-- def leb : Nat -> Nat -> Bool
--   | n + 1, m + 1 => leb n m
--   | 0, _ => true
--   | _, _ => false

-- @[reflect]
-- instance lebP (n m : Nat) : Reflect (n <= m) (leb n m) := by
--   sorry
-- #reflect Nat.le leb

-- def ltb (n m : Nat) := leb (n + 1) m

-- @[reflect]
-- instance (n m : Nat) : Reflect (n < m) (ltb n m) := by
--   sorry

-- #reflect Nat.lt ltb

-- example (n : Nat) : even 0 /\ even 1 /\ even (n + 2) := by
--   simp

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
