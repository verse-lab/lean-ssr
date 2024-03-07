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

-- FAILING test case: what is going on here??
/-- error:
(kernel) declaration has metavariables 'subnDA'
-/
theorem subnDA (m n p : Nat) : n - (m + p) = (n - m) - p := by
  elim: m;
  move=>//;

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

-- Induction on lists and case-split of DecidablePred
#guard_msgs in
theorem length_filter (s : List α) (f : α → Prop) [dp : DecidablePred f] :
  List.length (List.filter f s) <= List.length s := by
  elim: s=>//==x xs Ih
  srw List.filter;
  scase: [f x];
  { move=>?//= }
  { move=>h//==; omega }
