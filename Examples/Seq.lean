import Ssreflect.Lang
import Std.Data.List
import Std.Tactic.Omega
import Examples.Nat

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
  srw nseq


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


end seq
