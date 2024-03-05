import Ssreflect.Lang
import Std.Tactic.Omega

section nat
variable {α : Type}

@[simp] def eqn (n m : Nat) :=
  match n, m with
  | 0, 0 => true
  | n + 1, m + 1 => eqn n m
  | _, _ => false

-- <= is Defined as a inductive predicate on ℕ. But we want to behave as `leb` defined below
-- This `leb` defintion exactly follows the one defined in mathcomp/ssrnat.v
-- In particula we want `n+1 <= m+1` to be always simplified to `n <= m`
-- To achive such behaviour we simply `#reflect` two Definitions
@[simp] def leb : Nat -> Nat -> Bool
  | n + 1, m + 1 => leb n m
  | 0, _ => true
  | _, _ => false

@[reflect]
instance lebP (n m : Nat) : Reflect (n <= m) (leb n m) := by
  apply reflect_of_equiv
  elim: n m=> //== ?/[swap][]//=?->
  omega
#reflect Nat.le leb

def ltb (n m : Nat) := leb (n + 1) m

@[reflect]
instance (n m : Nat) : Reflect (n < m) (ltb n m) := by
  apply reflect_of_equiv; srw ltb
  srw (equiv_of_reflect (lebP ..))
  omega
set_option trace.reflect true
#reflect Nat.lt ltb

@[simp] theorem eqSS (m n : Nat) : (Nat.succ m == Nat.succ n) = (m == n) := by rfl
@[simp] theorem addSn (m n : Nat) : (Nat.succ m + n) = Nat.succ (m + n) := by omega

@[simp] def iter (n : Nat) (f : α → α) (x : α) : α :=
  match n with
  | 0 => x
  | i + 1 => f (iter i f x)
theorem iterS (n : Nat) (f : α → α) (x : α) : iter (n + 1) f x = f (iter n f x) := by sdone
theorem iterD (n m : Nat) (f : α → α) (x : α) : iter (n + m) f x = iter n f (iter m f x) := by
  elim: n => //=

end nat
