import Ssreflect.Lang
import Std.Data.List
import Std.Tactic.Omega
import Examples.Nat
-- import Lean.Elab.Tactic
-- import Lean

notation "Seq" => List

namespace seq

variable {α : Type} [DecidableEq α]

@[simp] def size : Seq α -> Nat
  | [] => 0
  | _ :: xs => Nat.succ $ size xs

theorem size0nil (s : Seq α) : 0 = size s -> s = [] := by
  sby scase: s

@[simp] def beq : Seq α -> Seq α -> Bool
  | [], [] => true
  | x :: xs, y :: ys => x = y /\ beq xs ys
  | _, _ => false

def nilp (s : Seq α) : Bool := size s = 0

-- Lemma nilP s : reflect (s = [::]) (nilp s).

def ohead : Seq α -> Option α
  | [] => none
  | x :: _ => some x

def head [Inhabited α] : Seq α -> α
  | [] => default
  | x :: _ => x

def behead : Seq α -> Seq α
  | [] => []
  | _ :: xs => xs

theorem size_behead (s : Seq α) : size (behead s) = size s - 1 := by
  sby scase: s

-- Factories

def ncons (n : Nat) (x : α) := iter n (List.cons x)
def nseq (n : Nat) (x : α) : Seq α := ncons n x []

@[simp] theorem nconsSn (n : Nat) (x : α) (s : Seq α) : ncons (n + 1) x s = x :: ncons n x s := by rfl

-- NOTE: it seems `simpl` (`/=`) in Coq somehow uses something akin to `nconsSn`
theorem size_ncons (n : Nat) (x : α) (s : Seq α) : size (ncons n x s) = n + size s := by
  elim: n=>//=

theorem size_nseq (n : Nat) (x : α) : size (nseq n x) = n := by
  -- NOTE: the equivalent of `dsimp` runs first in Coq, so `/=` is not needed there
  sby srw /= nseq size_ncons

-- n-ary, dependently typed constructor

def seqn_type (n : Nat) :=
  match n with
  | 0 => Seq α
  | n' + 1 => α -> seqn_type n'

-- Sequence catenation "cat"
-- set_option trace.Meta.synthInstance true

-- def cat (s1 s2 : Seq α) :=
--   match s1 with
--   | [] => s2
--   | x :: s1' => x :: cat s1' s2

theorem cat0s (s : Seq α) : [] ++ s = s := by sdone
theorem cat1s (x : α) (s : Seq α) : [x] ++ s = x :: s := by sdone
theorem cat_cons (x : α) (s1 s2 : Seq α) : (x :: s1) ++ s2 = x :: (s1 ++ s2) := by sdone

theorem cat_nseq (n : Nat) (x : α) (s : Seq α) : nseq n x ++ s = ncons n x s := by
  elim: n=>//
  srw nseq//


theorem nseqD (n1 n2 : Nat) (x : α) : nseq n1 x ++ nseq n2 x = nseq (n1 + n2) x := by
  srw cat_nseq /= ?nseq ?ncons iterD

theorem cats0 (s : Seq α) : s ++ [] = s := by sdone
theorem catA (s1 s2 s3 : Seq α) : (s1 ++ s2) ++ s3 = s1 ++ (s2 ++ s3) := by elim: s1=>//=

theorem size_cat (s1 s2 : Seq α) : size (s1 ++ s2) = size s1 + size s2 := by elim: s1=>//=

theorem cat_nilp (s1 s2 : Seq α) : nilp (s1 ++ s2) = (nilp s1 && nilp s2) := by elim: s1=>//=

-- last, belast, rcons, and last induction

@[simp] def rcons (s : Seq α) (z : α) :=
  match s with
  | [] => [z]
  | x :: s' => x :: rcons s' z

theorem rcons_cons (x : α) (s : Seq α) (z : α) : rcons (x :: s) z = x :: rcons s z := by sdone

theorem cats1 (s : Seq α) (x : α) : s ++ [x] = rcons s x := by elim: s=>//=

@[simp] def last (x : α) (s : Seq α) : α :=
  match s with
  | [] => x
  | x' :: s' => last x' s'

@[simp] def belast (x : α) (s : Seq α) : Seq α :=
  match s with
  | [] => []
  | x' :: s' => x :: belast x' s'

theorem lastI (x : α) (s : Seq α) : x :: s = rcons (belast x s) (last x s) := by
  elim: s x => [|y s IHs] x //=

theorem last_cons (x y : α) (s : Seq α) : last x (y :: s) = last y s := by sdone

theorem size_rcons (s : Seq α) (x : α) : size (rcons s x) = size s + 1 := by elim: s=>//=

theorem size_belast (x : α) (s : Seq α) : size (belast x s) = size s := by
  elim: s x => [|y s IHs] x //=

theorem last_cat (x : α) (s1 s2 : Seq α) : last x (s1 ++ s2) = last (last x s1) s2 := by elim: s1 x=>//=
theorem last_rcons (x : α) (s : Seq α) (y : α) : last x (rcons s y) = y := by elim: s x=>//=
theorem belast_cat (x : α) (s1 s2 : Seq α) : belast x (s1 ++ s2) = belast x s1 ++ belast (last x s1) s2 :=
  by elim: s1 x=>//=

theorem belast_rcons (x : α) (s : Seq α) (y : α) : belast x (rcons s y) = x :: s := by elim: s x=>//=

theorem cat_rcons (x : α) (s1 s2 : Seq α) : rcons s1 x ++ s2 = s1 ++ x :: s2 := by elim: s1=>//=

theorem rcons_cat (x : α) (s1 s2 : Seq α) : rcons (s1 ++ s2) x = s1 ++ rcons s2 x := by elim: s1=>//=

inductive last_spec : Seq α → Prop where
  | last_nil                        : last_spec []
  | last_rcons (s : Seq α) (x : α)  : last_spec (rcons s x)

theorem lastP (s : Seq α) : last_spec s := by
  scase: s => [|x s]; { left }; srw lastI; right

theorem last_ind (P : Seq α → Prop) :
  P [] → (∀ s x, P s → P (rcons s x)) → ∀ s, P s := by
  move=> Hnil Hlast s <;> srw -(cat0s s)
  elim: s ([]) Hnil=> [|x s2 IHs] s1 Hs1
  { sby srw cats0 }
  { sby srw -cat_rcons; apply IHs; apply Hlast }

-- Sequence indexing

@[simp] def nth [Inhabited α] (s : Seq α) (n : Nat) : α :=
  match s with
  | [] => default
  | x :: s' => match n with
    | 0 => x
    | n' + 1 => nth s' n'

@[simp] def set_nth [Inhabited α] (s : Seq α) (n : Nat) (y : α) : Seq α :=
  match s with
  | [] => ncons n default [y]
  | x :: s' => match n with
    | 0 => y :: s'
    | n' + 1 => x :: set_nth s' n' y

theorem nth0 [Inhabited α] (s : Seq α) : nth s 0 = head s := by elim: s=>//=

-- example (n m : Nat) : (Nat.succ n) <= (Nat.succ m) := by
--   simp

-- example (m n : Nat) : (Nat.succ m + n) = Nat.succ (m + n) := by simp?

theorem nth_default [Inhabited α] (s : Seq α) (n : Nat) : size s <= n -> nth s n = default := by
  -- NOTE: this solves the goal in Coq; there's probably some lemmas we're missing
  elim: s n=>[|x s IHs] [] //=
  -- { intro n Hle; apply IHs; omega }

-- requires some facts/reasoning principles about `<=`
theorem if_nth [Inhabited α] (s : Seq α) (b : Bool) (n : Nat) :
  b || (size s <= n) → (if b then nth s n else default) = nth s n := by sorry

-- We might not want to talk about Booleans at all. Consider the following formulation
theorem if_nthProp [Inhabited α] [Decidable P] (s : Seq α) (n : Nat) :
  P ∨ (size s <= n) → (if P then nth s n else default) = nth s n := by
  sby scase_if=> //== ? /nth_default


theorem nth_nil [Inhabited α] (n : Nat) : nth ([] : Seq α) n = default := by sdone

theorem nth_seq1 [Inhabited α] (n : Nat) (x : α) :
  nth [x] n = if n == 0 then x else default := by elim: n=>//=

-- Again, screw Bools
theorem nth_seq1Prop [Inhabited α] (n : Nat) (x : α) :
  nth [x] n = if n = 0 then x else default := by elim: n=>//=


theorem last_nth [Inhabited α] (x : α) (s : Seq α) : last x s = nth (x :: s) (size s) := by
  elim: s x => [|y s IHs] x //=

end seq
