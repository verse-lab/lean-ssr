import Ssreflect.Lang
import Std.Tactic.Omega

section nat
variable {α : Type}

def eqn (m n : Nat) :=
  match m, n with
  | Nat.zero, Nat.zero => true
  | Nat.succ m, Nat.succ n => eqn m n
  | _, _ => false

@[simp] theorem addSn (m n : Nat) : (Nat.succ m + n) = Nat.succ (m + n) := by omega

@[simp] def iter (n : Nat) (f : α → α) (x : α) : α :=
  match n with
  | 0 => x
  | i + 1 => f (iter i f x)

-- def iter (n : Nat) (f : α → α) (x : α) :=
--   loop n
--   where loop m :=
--     match m with
--     | 0 => x
--     | i + 1 => f (loop i)

theorem iterS (n : Nat) (f : α → α) (x : α) : iter (n + 1) f x = f (iter n f x) := by sdone
theorem iterD (n m : Nat) (f : α → α) (x : α) : iter (n + m) f x = iter n f (iter m f x) := by
  elim: n => //=

end nat
