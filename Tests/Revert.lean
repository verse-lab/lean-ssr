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

-- set_option trace.reflect true
-- set_option pp.all true

theorem length_filter (s : List α) (f : α → Prop) [dp : DecidablePred f] :
  List.length (List.filter f s) <= List.length s := by
  elim: s=>//==x xs Ih
  srw List.filter;
  -- have dx: _ := by apply (dp x)
  scase: [f x];
  { move=>?//= }
  { move=>h//==; omega }
