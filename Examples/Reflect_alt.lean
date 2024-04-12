import Mathlib

namespace DecTest

set_option autoImplicit true

instance (p : Prop) : CoeOut (Decidable p) Bool := ⟨@decide p⟩

@[inline] def dtrue {p : Prop} (h : p := by aesop) : Decidable p := isTrue h
@[inline] def dfalse {p : Prop} (h : ¬ p := by aesop) : Decidable p := isFalse h
@[inline] def decide_by {p : Prop} (q : Prop) [Decidable q] (h : q ↔ p := by aesop) : Decidable p :=
  decidable_of_iff q h

@[inline] def decide_by' {p : Prop} (q : Prop) [Decidable q] (h : q ↔ p) : Decidable p :=
  decidable_of_iff q h

inductive Even : Nat -> Prop where
  | zero : Even 0
  | add2 : ∀ n, Even n -> Even (n+2)

attribute [simp] Even.zero Even.add2
attribute [aesop safe cases] Even

instance evend : DecidablePred Even
  | 0 => dtrue
  | 1 => dfalse
  | n+2 => decide_by (evend n)

theorem decide_prop (p : Prop) [Decidable p] : p = decide p := by simp only [decide_eq_true_eq]

theorem decide_decide_by (p q : Prop) {dq : Decidable q} (h : q ↔ p) :
    @decide p (decide_by q h) ↔ q := by simp [h]

theorem decide_ite {t e : Decidable p} [Decidable b] :
    @decide p (ite b t e) = ite b (decide t) (decide e)  := by sorry

section
open Lean Meta Elab

private def getSimpUnfoldContext : MetaM Simp.Context :=
   return {
      congrTheorems := (← getSimpCongrTheorems)
      config        := Simp.neutralConfig
   }

def reflect_unfold (e : Expr) (declName : Name) : MetaM Simp.Result := do
  (·.1) <$> Simp.main e (← getSimpUnfoldContext) (methods := { pre := pre })
where
  pre (e : Expr) : SimpM Simp.Step := do
    if e.isAppOf ``Decidable.decide then return .done {expr := e}
    unless e.isAppOf declName do return .continue
    let inst ← try synthInstance (← mkAppM ``Decidable #[e]) catch _ => return .continue
    let some inst ← withDefault <| unfoldDefinition? inst | return .continue
    let eq ← mkAppOptM ``decide_prop #[e, inst]
    let eqTy := (← inferType eq).eq?.get!
    return .done {expr := eqTy.2.2, proof? := eq}

elab "reflect_unfold' " declNameId:ident : tactic => do
  let declName ← resolveGlobalConstNoOverloadWithInfo declNameId
  Tactic.liftMetaTactic1 fun mvarId => do
    let target ← instantiateMVars (← mvarId.getType)
    let r ← reflect_unfold target declName
    if r.expr == target then throwError "\
      tactic 'reflect_unfold' failed to unfold '{declName}' at{indentExpr target}"
    applySimpResultToTarget mvarId target r

macro "reflect_unfold " declNameId:ident : tactic =>
  `(tactic| (reflect_unfold' $declNameId ; try simp only [decide_decide_by, decide_ite]; try simp))

end

example (h : Even n) : Even (m + n) ↔ Even m := by
  induction h
  · rfl
  · rw [← Nat.add_assoc]
    /-
    a_ih✝ : Even (m + n✝) ↔ Even m
    ⊢ Even (m + n✝ + 2) ↔ Even m
    -/
    reflect_unfold Even
    /-
    a_ih✝ : Even (m + n✝) ↔ Even m
    ⊢ Even (m + n✝) ↔ Even m
    -/
    assumption

namespace HasTest

variable (a : α -> Prop) [DecidableEq α] [DecidablePred a]

abbrev has (s : List α) : Prop := ∃ (x : α), x ∈ s ∧ a x

instance hasd :  DecidablePred (has a)
  | [] => decide_by False (by simp [has])
  | x :: s =>
    if a x then
      decide_by True (by sorry)
    else decide_by (hasd s) (by sorry)

instance hasd' :  DecidablePred (has a)
  | [] => decide_by False (by simp [has])
  | x :: s =>
    @decide_by _ (a x ∨ has a s) (@Or.decidable _ _ (decide_by (a x)) (decide_by (hasd s))) (by sorry)


example x (xs : List α) : has a (x :: xs) = (a x ∨ has a xs) := by
  reflect_unfold has
  /- ¬a x → has a xs ↔ a x ∨ has a xs -/
  sorry


end HasTest
