import Ssreflect.Lang
import Std.Tactic.GuardMsgs

-- Named introduction
/-- info:
z : Nat
⊢ z = z
-/
#guard_msgs in
theorem named_intro : ∀ (x : Nat), x = x := by
  move=>z
  trace_state
  trivial

-- Unnamed introduction
theorem unnamed_intro : ∀ (x : Nat), x = x := by
  move=>?
  trivial

-- Ignore introduction
/--
info: ⊢ True
-/
#guard_msgs in
theorem ignore_intro : ∀ (x : Nat), True := by
  move=>_
  trace_state
  trivial

-- Multiple unnamed introduction
theorem multiple_unnamed_intro : ∀ (x : Nat) (y : List Nat) (z : Nat), True := by
  move=>*
  trivial

-- Dependent introduction: works for multiple binders
/-- error:
unsolved goals
x : Nat
y : List Nat
⊢ Nat → x = x ∧ y = y
-/
#guard_msgs in
theorem dependent_intro1 : ∀ (x : Nat) (y : List Nat) (z : Nat), x = x ∧ y = y := by
  move=>>;

-- Dependent introduction: stops at first binder that is not used
/-- error:
unsolved goals
x : Nat
⊢ List Nat → ∀ (z : Nat), x = x ∧ z = z
-/
#guard_msgs in
theorem dependent_intro2 : ∀ (x : Nat) (y : List Nat) (z : Nat), x = x ∧ z = z := by
  move=>>;

-- Right rewrite: single
/-- info:
x y : Nat
⊢ y = y + 5 - 5
-/
#guard_msgs in
theorem rrw_intro_1 : ∀ (x y : Nat), x = y + 5 → y = x - 5 := by
  move=>x y ->;
  trace_state
  trivial

-- Right rewrite: multiple sequentially
/-- info:
x y z : Nat
⊢ y = z → z = y
-/
#guard_msgs in
theorem rrw_intro_2 : ∀ (x y z : Nat), x = y → y = z → z = x  := by
  move=>x y z ->
  trace_state
  move=>->

-- Right rewrite: multiple sequentially in a single line
theorem rrw_intro_3 : ∀ (x y z : Nat), x = y → y = z → z = x  := by
  move=>x y z -> ->

-- Right rewrite: the rewrite failing leaves the goal unchanged
/--
info: x y z : Nat
⊢ x = y → z = z
---
info: x y z : Nat
⊢ x = y → z = z
-/
#guard_msgs(info, drop error) in
theorem rrw_intro_fail_unchaged : ∀ (x y z : Nat), x = y → z = z := by
  move=>x y z;
  trace_state
  move=>->;
  trace_state
  sby move=>_

-- Left rewrite
/-- info:
x y z : Nat
⊢ x = z → z = x
-/
#guard_msgs in
theorem lrw_intro_1 : ∀ (x y z : Nat), x = y → y = z → z = x := by
  move=>x y z <-
  trace_state
  move=>->;

-- Left rewrite: the rewrite failing leaves the goal unchanged
/--
info: x y z : Nat
⊢ x = y → z = z
---
info: x y z : Nat
⊢ x = y → z = z
-/
#guard_msgs(info, drop error) in
theorem lrw_intro_fail_unchaged : ∀ (x y z : Nat), x = y → z = z := by
  move=>x y z;
  trace_state
  move=><-
  trace_state
  sby move=>_;
