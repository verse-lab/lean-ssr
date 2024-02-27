import Ssreflect.Lang
import Std.Data.List
import Std.Tactic.Omega


notation "Seq" => List

namespace seq

variable {α : Type} [DecidableEq α]

@[simp] def size : Seq α -> Nat
  | [] => 0
  | _ :: xs => Nat.succ $ size xs

-- (1)
def size0nil (s : Seq α) : size s = 0 -> s = [] := by
  sby scase: s

@[simp] def beq : Seq α -> Seq α -> Bool
  | [], [] => true
  | x :: xs, y :: ys => x = y /\ beq xs ys
  | _, _ => false

def nilp (s : Seq α) : Bool := size s = 0

-- instance nilP (s : Seq α) : Decidable (s = []) := by
--   apply (decidable_of_bool (nilp s))
--   sby scase:s

instance : DecidableEq (Seq α) := by
  move=> x y; apply (decidable_of_bool (beq x y))
  sby elim: x y => [[]|???[]]



def mask : Seq Bool -> Seq α -> Seq α
  | b :: m', x :: s' => if b then x :: mask m' s' else mask m' s'
  | _, _ => []

@[simp] theorem mask_eq1 :
  mask (b :: m') (x :: s') = if b then x :: mask m' s' else mask m' s' := by rfl

@[simp] theorem mask_eq2 :
  mask [] x = [] := by rfl

@[simp] theorem mask_eq3 :
  mask x ([] : List α) = [] := by sby scase: x


@[simp] def subseq (s1 : Seq α) (s2 : Seq α) : Bool :=
  match s2 with
  | y :: s2' =>
    match s1 with
    | x :: s1' => subseq (if x = y then s1' else s1) s2'
    | _ => true
  | _ => s1 = []

@[simp] def nseq (x : α) : Nat -> Seq α
  | 0 => []
  | .succ n => x :: nseq x n

@[simp] theorem size_nseq n (x : α) : size (nseq x n) = n := by
  /- proof 1 -/
  -- induction n with
  -- | zero => simp
  -- | succ n ihn => dsimp; simp; rw [ihn]
  /- proof 2 -/
  -- elim: n=> [ // | n ihn /== ]; srw ihn
  /- proof 3 -/
  -- induction n <;> simp_all
  /- proof 4 -/
  sby elim: n

-- syntax num "?" : ssrIntro
-- elab_rules : tactic
--   | `(ssrIntro| $n:num ?) =>
--     Lean.Elab.Tactic.liftMetaTactic fun goal => do
--       let (_, goal) <- goal.introNP n.getNat
--       return [goal]


@[simp] theorem mask_false (s : Seq α) (n : Nat) : mask (nseq false n) s = [] := by
  sby elim: s n=> [|???][]

@[simp] def find (p : α -> Prop) [DecidablePred p] : Seq α -> Nat
  | [] => 0
  | x :: xs => if p x then 0 else Nat.succ $ find p xs

def index (x : α) := find (· = x)

@[simp] def take (n : Nat) (s : Seq α) :=
  match s, n with
  | x :: s', n' + 1 => x :: take n' s'
  | _, _ => []

-- all: https://github.com/math-comp/math-comp/blob/27b595cee274ade2fdc4a3a8e80213e3bb07a8bf/mathcomp/ssreflect/seq.v#L479
-- all_nthP: https://github.com/math-comp/math-comp/blob/27b595cee274ade2fdc4a3a8e80213e3bb07a8bf/mathcomp/ssreflect/seq.v#L1587C7-L1587C15
-- all_pred1P: https://github.com/math-comp/math-comp/blob/27b595cee274ade2fdc4a3a8e80213e3bb07a8bf/mathcomp/ssreflect/seq.v#L1250

@[simp] def all (p : α -> Prop) : Seq α -> Prop
  | [] => True
  | x :: xs => p x /\ all p xs

@[simp] def allb (p : α -> Prop) [DecidablePred p] : Seq α -> Bool
  | [] => true
  | x :: xs => p x /\ allb p xs

instance allP [DecidablePred p] (s : Seq α) : Decidable (all p s) := by
  apply (decidable_of_bool (allb p s))
  sby elim: s

@[simp] def nth (x0 : α) : Seq α -> Nat -> α
  | _ :: s, .succ n => nth x0 s n
  | x :: _, 0       => x
  | [], _           => x0

theorem all_nthP (x0 : α) (p : α -> Prop) [DecidablePred p] (s : Seq α) :
   all p s =
   ∀ i, i < size s -> p (nth x0 s i) := by sorry

@[simp↓] theorem all_pred1P (s : Seq α) (x : α) :
  (s = nseq x (size s)) =
  all (· = x) s := by
   sorry

theorem ltSS (a b : Nat) : ((a < b) <-> (Nat.succ a < Nat.succ b)) := by
  move=> /==; omega

-- (2)
@[simp] theorem size_take (s : Seq α) : size (take n s) = if n < size s then n else size s := by
  /- proof 1 -/
  induction s generalizing n with
  | nil => simp
  | cons x s IHs => {
    cases n with
    | zero => simp
    | succ n => {
      simp; rw [IHs]; simp [<-ltSS]
      by_cases h: n < size s <;> simp [h]
    }
  }
  /- proof 2 -/
  -- elim: s n=> [//|x s IHs [//|n/=]]; srw IHs -ltSS; scase_if


  -- elim: s n0=> [//|s IHs x [//|n/=]]; srw IHs
  -- sby elim: s n0=> [//|s IHs x [//|n/=]]; srw IHs -ltSS; scase_if


@[simp] theorem nth_take {n0 i : Nat} {s : Seq α} :
  i < n0 → nth x0 (take n0 s) i = nth x0 s i := by
  sorry

theorem before_find a [DecidablePred a] : i < find a s → ¬ a (nth x0 s i) :=
  sorry

theorem take_oversize (s : Seq α) : size s ≤ n → take n s = s := by
  sorry

@[simp] def drop : Nat -> Seq α -> Seq α
  | n' + 1, _ :: s' => drop n' s'
  | _, s => s

@[simp] theorem size_cat : size (s1 ++ s2) = size s1 + size s2 := by sorry
@[simp] theorem size_drop : size (drop n0 s) = size s - n0 := by sorry
def behead : Seq α -> Seq α
  | _ :: xs => xs
  | _ => []

@[simp] theorem behead_cons : behead (x :: xs) = xs := by rfl
@[simp] theorem cat_take_drop n0 (s : Seq α) : take n0 s ++ drop n0 s = s := by sorry
theorem cat_cons : x :: s1 ++ s2 = x :: (s1 ++ s2) := by sorry

@[simp] def rcons : Seq α -> α -> Seq α
  | x :: s', z => x :: rcons s' z
  | [], z => [z]

@[simp] def belast (x : α) : Seq α -> Seq α
  | x' :: xs => x :: belast x' xs
  | [] => []

@[simp] def last (x0 : α) : Seq α -> α
  | x' :: xs => last x' xs
  | [] => x0


theorem lastI : x :: s = rcons (belast x s) (last x s) := by sorry
theorem cat_rcons : rcons s1 x ++ s2 = s1 ++ x :: s2 := by sorry
theorem mask_cat : size m1 = size s1 → mask (m1 ++ m2) (s1 ++ s2) = mask m1 s1 ++ mask m2 s2 := by sorry
theorem drop_nth (x0 : α) : n < size s → drop n s = nth x0 s n :: drop (n+1) s := by sorry
theorem nth_index (s : Seq α) : x ∈ s → nth x0 s (index x s) = x := by sorry
theorem index_mem (s : Seq α) : (index x s < size s) = (x ∈ s) := by sorry
@[simp] theorem size_belast : size (belast x s) = size s := by sorry

-- count_uniq_mem: clear at intro
-- catCA_perm_ind: clear at revert
-- subseqP: clear at rewrite

-- macro_rules
--   | `(ssrTriv| //) => `(tactic| omega)

theorem subseqP (s1 s2 : Seq α) :
  (subseq s1 s2) <-> (exists m, size m = size s2 /\ s1 = mask m s2) := by
  elim: s2 s1=> [| y s2 IHs2] [|x s1]
  { simp; exists [] }
  { sby simp }
  { sby simp; exists (nseq false (Nat.succ (size s2))) }
  simp [IHs2]; constructor=> [] m [] sz_m def_s1
  { sby exists ((x = y) :: m); simp [<-def_s1]; scase_if }
  scase_if=> ne_xy; rotate_right
  { scase: m def_s1 sz_m=> [|[]] //== }
  generalize h : (index true m) = i at *
  shave def_m_i : take i m = nseq false (size (take i m))
  { simp [all_nthP true]=> j le; srw nth_take
    { shave//: ¬nth true m j; apply before_find (· = _)
      scase_if: le <;> srw index at h <;> omega }
    scase_if: le=> //== ? le
    sby apply (Nat.lt_of_lt_of_le le) }
  shave lt_i_m : i < size m
  { false_or_by_contra; srw take_oversize // at def_m_i
    sby srw def_m_i mask_false at def_s1 }
  simp [-all_pred1P, lt_i_m] at def_m_i
  exists (take i m ++ drop (i+1) m); constructor
  { simp_all; omega }
  move: {def_s1} (congrArg behead def_s1)=> /== -> {s1}
  srw -[1](cat_take_drop i m) -(cat_take_drop i s2) def_m_i -cat_cons
  shave sz_i_s2: size (take i s2) = i; simp; omega
  srw lastI cat_rcons ?mask_cat ?size_belast ?sz_i_s2 //==
  sby srw (drop_nth true) // -[1]h nth_index // -index_mem

end seq
