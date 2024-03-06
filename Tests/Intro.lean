import Ssreflect.Lang
import Std.Tactic.GuardMsgs

-- (1) Named introduction
theorem named_intro : ∀ (x : Nat), x = x := by
  move=>x
  trivial

-- (2) Unnamed introduction
theorem unnamed_intro : ∀ (x : Nat), x = x := by
  move=>?
  trivial

-- (3) Ignore introduction
theorem ignore_intro : ∀ (x : Nat), True := by
  move=>_
  trivial

-- (4) Multiple unnamed introduction
theorem multiple_unnamed_intro : ∀ (x : Nat) (y : List Nat) (z : Nat), True := by
  move=>*
  trivial

-- (5) Dependent introduction: works for multiple binders
/-- error:
unsolved goals
x : Nat
y : List Nat
⊢ Nat → x = x ∧ y = y
-/
#guard_msgs in
theorem dependent_intro1 : ∀ (x : Nat) (y : List Nat) (z : Nat), x = x ∧ y = y := by
  move=>>;

-- (6) Dependent introduction: stops at first binder that is not used
/-- error:
unsolved goals
x : Nat
⊢ List Nat → ∀ (z : Nat), x = x ∧ z = z
-/
#guard_msgs in
theorem dependent_intro2 : ∀ (x : Nat) (y : List Nat) (z : Nat), x = x ∧ z = z := by
  move=>>;
