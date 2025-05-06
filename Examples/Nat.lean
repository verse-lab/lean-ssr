import Ssreflect.Lang
-- import Batteries.Tactic.Omega

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
  elim: n m=> //== ?/[swap][]//=
#reflect Nat.le leb

def ltb (n m : Nat) := leb (n + 1) m

@[reflect]
instance (n m : Nat) : Reflect (n < m) (ltb n m) := by
  apply reflect_of_equiv; srw ltb
  srw (equiv_of_reflect (lebP ..))
  omega
set_option trace.reflect true
#reflect Nat.lt ltb

@[simp] theorem eqSS (m n : Nat) : (Nat.succ m == Nat.succ n) = (m == n) := by simp
@[simp] theorem addSn (m n : Nat) : (Nat.succ m + n) = Nat.succ (m + n) := by omega

@[simp] def iter (n : Nat) (f : α → α) (x : α) : α :=
  match n with
  | 0 => x
  | i + 1 => f (iter i f x)
theorem iterS (n : Nat) (f : α → α) (x : α) : iter (n + 1) f x = f (iter n f x) := by sdone
theorem iterD (n m : Nat) (f : α → α) (x : α) : iter (n + m) f x = iter n f (iter m f x) := by
  elim: n => //=

@[simp] def nat_of_bool (b : Bool) := if b then 1 else 0

theorem posnP : n = 0 ∨ 0 < n := by omega

example (m n : Nat): n <= m ->
  m - n + n = m := by
   elim: n m=> [| n IHm [|m]] //==
   move=> ?
   srw -[2](IHm m) //

namespace Even
@[simp] def evenb : Nat -> Bool
  | 0 => true | 1 => false
  | n + 2 => evenb n

inductive even : Nat -> Prop where
  | zero : even 0
  | add2 : ∀ n, even n -> even (n+2)

@[reflect]
instance evP n : Reflect (even n) (evenb n):=
  match n with
  | 0 => by sdone
  | 1 => by simp; apply Reflect.F; intro r; cases r; trivial
  | n + 2 => by
    simp; cases (evP n)
    { apply Reflect.T <;> try assumption
      constructor; assumption }
    apply Reflect.F <;> try assumption
    intro n; cases n; contradiction

-- theorem foo : evenb n -> evenb (m + n) = evenb m := by

  -- move=> /(equiv_of_reflect (evP ..))
  -- elim=> [//|] -- n _ <-
  -- simp only [evenb]
  -- sorry
  -- simp_all

#reflect even evenb

-- def even_ind n := if even n then 1 else 0

-- @[inline] abbrev Reflect.toBool (P : Prop) [Reflect P b] : Bool := P

-- -- theorem foo (P : Prop) [Reflect P b] : P = Reflect.toProp (Reflect.toBool P) := by sorry

-- @[simp]

-- example : even n -> even (m + n) = even m := by
--   rw [foo (even (m+n))]
--   sorry
  -- elim=> // n _ <-
  -- simp only [even]
     --srw -Nat.add_assoc /==
end Even





end nat
