import Ssreflect.Lang
import Std.Tactic.GuardMsgs
import Std.Data.List

-- Named revert
/-- info:
⊢ ∀ (z : Nat), z = z
-/
#guard_msgs in
theorem named_revert : ∀ (x : Nat), x = x := by
  move=>z; move: z;
  trace_state
  sdone

-- Elim on Nat: works with no errors
#guard_msgs in
theorem subnDA (m n p : Nat) : n - (m + p) = (n - m) - p := by
  elim: m;
  move=>//;
  omega

-- Elim on Nat
/-- info:
case succ
m n p : Nat
⊢ Nat.succ p + m - (Nat.succ p + n) = p + m - (p + n)
-/
#guard_msgs in
theorem subnDl (p m n : Nat) : (p + m) - (p + n) = m - n := by
  elim: p=>//=p <-
  trace_state
  omega

-- Induction on lists
theorem length_cons (x : α) (xs : List α) :
  List.length xs ≤ List.length (x :: xs) := by
  elim: xs=>//=

-- Case-split of DecidablePred
#guard_msgs in
theorem length_filter (s : List α) (f : α → Prop) [dp : DecidablePred f] :
  List.length (List.filter f s) ≤ List.length s := by
  elim: s=>//==x xs Ih; srw List.filter;
  scase: [f x];
  { move=>?//= }
  { move=>h//==; omega }

-- Revert theorem application
/--
info: α : Type
x y : α
xs : List α
⊢ List.length (y :: xs) ≤ List.length (x :: y :: xs) → List.length (y :: xs) ≤ List.length (x :: y :: xs)
-/
#guard_msgs in
theorem length_cons_1 {α : Type} (x : α) (y : α) (xs : List α) :
 List.length (y :: xs) ≤ List.length (x :: y :: xs) := by
 move: (length_cons x (y :: xs))
 trace_state
 move=>//=;

-- Revert with hypothesis application
/--
info: α : Type
x y : α
xs : List α
⊢ List.length (y :: xs) ≤ List.length (x :: y :: xs) → List.length (y :: xs) ≤ List.length (x :: y :: xs)
-/
#guard_msgs in
theorem length_cons_2 {α : Type} (x : α) (y : α) (xs : List α) :
  List.length (y :: xs) ≤ List.length (x :: y :: xs) := by
  have H: ∀ (x : α) (xs : List α), List.length xs ≤ List.length (x :: xs)
    := by apply length_cons
  move: (H x (y :: xs))
  clear H
  trace_state
  move=>//=;
