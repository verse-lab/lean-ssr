import Ssreflect.Lang
import Std.Data.List
-- import Std.Tactic.Omega
import Examples.Nat
import Loogle.Find
-- import Lean.Elab.Tactic
-- import Lean

notation "Seq" => List
-- set_option trace.reflect true

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

@[simp↓] theorem size_nseq (n : Nat) (x : α) : size (nseq n x) = n := by
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

theorem nth_default [Inhabited α] (s : Seq α) (n : Nat) : size s <= n -> nth s n = default := by
  -- NOTE: this solves the goal in Coq; there's probably some lemmas we're missing
  elim: s n=>[|x s IHs] [] //=
  -- { intro n Hle; apply IHs; omega }

-- We might not want to talk about Booleans at all. Consider the following formulation
theorem if_nthProp [Inhabited α] [Decidable P] (s : Seq α) (n : Nat) :
  P ∨ (size s <= n) → (if P then nth s n else default) = nth s n := by
  sby scase_if=> //== ? /nth_default

theorem if_nth [Inhabited α] (s : Seq α) (b : Bool) (n : Nat) :
  b || (size s <= n) → (if b then nth s n else default) = nth s n := by
  move=> H; srw if_nthProp
  scase: b H=>//=

theorem nth_nil [Inhabited α] (n : Nat) : nth ([] : Seq α) n = default := by sdone

theorem nth_seq1 [Inhabited α] (n : Nat) (x : α) :
  nth [x] n = if n = 0 then x else default := by elim: n=>//=

-- Again, screw Bools
theorem nth_seq1Prop [Inhabited α] (n : Nat) (x : α) :
  nth [x] n = if n = 0 then x else default := by elim: n=>//=

theorem last_nth [Inhabited α] (x : α) (s : Seq α) : last x s = nth (x :: s) (size s) := by
  elim: s x => [|y s IHs] x //=

theorem nth_last [Inhabited α] (s : Seq α) : nth s (size s - 1) = last default s := by
  sby scase: s => //= x s; srw last_nth

theorem nth_behead [Inhabited α] (s : Seq α) (n : Nat) : nth (behead s) n = nth s (n + 1) := by
  elim: s n=>[|x s _] [] //=

theorem nth_cat [Inhabited α] (s1 s2 : Seq α) (n : Nat) :
  nth (s1 ++ s2) n = if n < size s1 then nth s1 n else nth s2 (n - size s1) := by
  elim: s1 n=>[|x s1 IHs] [] //==

theorem nth_rcons [Inhabited α] (s : Seq α) (x) (n : Nat) :
  nth (rcons s x) n =
    if n < size s then nth s n else if n = size s then x else default := by
  elim: s n=>[|y s IHs] [] //==

-- needs comparison predicates
theorem nth_rcons_default [Inhabited α] (s : Seq α) (i : Nat) :
  nth (rcons s default) i = nth s i := by
  srw nth_rcons; repeat' scase_if <;> try omega
  { sby move=> _ _; srw nth_default }
  { move=> ? ?; srw nth_default; omega }

section seq_find
variable (a : α → Prop) [DecidablePred a]

@[simp] def find (s : Seq α) :=
  match s with
  | [] => 0
  | x :: s' => if a x then 0 else (find s') + 1

@[simp] def filter (s : Seq α) :=
  match s with
  | [] => []
  | x :: s' => if a x then x :: filter s' else filter s'

@[simp] def count (s : Seq α) :=
  match s with
  | [] => 0
  | x :: s' => nat_of_bool (a x) + count s'

def has (s : Seq α) : Prop := ∃ (x : α), x ∈ s ∧ a x

@[simp] def hasb (s : Seq α) :=
  match s with
  | [] => false
  | x :: s' => a x || hasb s'

@[reflect]
instance hasP (s : Seq α) : Reflect (has a s) (hasb a s) := by
  apply reflect_of_equiv
  elim: s=>//== => [[]//= | x s' ->] ⟨|⟩[]// ![]e;
  { sby move=> *; exists e }
  { move=> /== [-> //= | * /[tac (right; exists e)]] }
#reflect has hasb

def all (s : Seq α) : Prop := ∀ (x : α), x ∈ s → a x

@[simp] def allb (s : Seq α) :=
  match s with
  | [] => true
  | x :: s' => a x && allb s'

@[reflect]
instance allP (s : Seq α) : Reflect (all a s) (allb a s) := by
  apply reflect_of_equiv
  elim: s=>//== => [x //= | x s' ->]; constructor
  { move=>[]hx ha y [//= | /ha //=] }
  {
    move=>/[dup] h /(_ x) //== hx; constructor
    { sdone }
    { move=> y; move: h => /(_ y) //= }
  }
#reflect all allb


-- TODO: add lemmas in SeqFind

theorem size_filter (s : Seq α) : size (filter a s) = count a s := by
  elim: s => //== x s <-;
  -- NOTE: [a x] is a case on (a x) as a boolean
  scase: [a x]=>//==;

theorem count_size (s : Seq α) : count a s <= size s := by
   elim: s =>//== x s; scase_if=>//=

theorem all_count (s : Seq α) : all a s = (count a s = size s) := by
  elim: s=>//== x s ->
  scase_if=>//==??;
  move: (count_size a s)
  omega

theorem all_filter (s : Seq α) : all a (filter a s) := by
  elim: s=> // x s /=
  scase_if=> //

theorem all_filterP (s : Seq α) : (filter a s = s) = (all a s) := by
  elim: s=> //== x s
  scase_if=> /== ? _
  move: (all_filter a s)=> /[swap] ->/== //

theorem count_cat : count a (s1 ++ s2) = count a s1 + count a s2 := by
  sby elim: s1 s2=> //== *; scase_if


-- theorem all_nthP [Inhabited α] [DecidablePred p] (s : Seq α) :
--   all p s =
--   ∀ i, i < size s -> p (nth s i) := by
--   elim: s=> [/==|/== s ss ->]
--   { omega }
--   constructor=> [[px allP] [] //= i ?|allP]
--   { sby apply allP; omega }
--   constructor=> [|i ?]
--   { sby apply (allP 0) }
--   sby apply (allP (.succ i)); omega

end seq_find

section perm_seq

@[simp] abbrev count_mem (x : α) := count (fun y => x = y)

def eqfun {A B : Type} (f g : B → A) := ∀ (x : B), f x = g x

def perm_eq (s1 s2 : Seq α) : Prop :=
  all (fun x => count_mem x s1 = count_mem x s2) (s1 ++ s2)

theorem has_count  [DecidablePred a] : (count a s > 0) = has a s := by
  elim: s=> // > /==
  sby scase_if

theorem permP1 (s1 s2 : Seq α) [DecidablePred a]:
  perm_eq s1 s2 -> count a s1 = count a s2 := by
  move=> eq_cnt1
  scase: [count a (s1 ++ s2) = 0]=> [countN0|]; rotate_left
  { simp [count_cat]; omega }
  shave ![x s12x a_x]: has a (s1 ++ s2)
  { elim: (s1 ++ _) countN0=> // x s /== /- simplify has -/
    sby scase_if }
  let a' := fun y => ¬(x = y) ∧ a y
  shave eq_cnt' : ∀s, count a s = count_mem x s + count a' s
  { elim=> //== >; srw a'; repeat' scase_if=> // }
  sby srw !eq_cnt' eq_cnt1 // permP1 //
termination_by (count a (s1 ++ s2))
decreasing_by
  { simp_wf; srw H a'
    shave: count_mem w (s1 ++ s2) > 0
    { srw has_count; exists w }
    move: (count (fun y ↦ ¬w = y ∧ a y) (s1 ++ s2))
    omega }

-- NOTE: I have unfolded `eqfun` in this definition
theorem permP (s1 s2 : Seq α) :
  (perm_eq s1 s2) = (∀ x [DecidablePred x], count x s1 = count x s2) := by
  sby move=> /== ⟨/permP1|??⟩


theorem perm_refl (s : Seq α) : perm_eq s s := by sby srw permP

def mask : Seq Bool -> Seq α -> Seq α
  | b :: m', x :: s' => if b then x :: mask m' s' else mask m' s'
  | _, _ => []

@[simp] theorem mask_eq1 :
  mask (b :: m') (x :: s') = if b then x :: mask m' s' else mask m' s' := by rfl

@[simp] theorem mask_eq2 :
  mask [] x = [] := by rfl

@[simp] theorem mask_eq3 :
  mask x ([] : List α) = [] := by sby scase: x

@[simp] def subseqb : Seq α -> Seq α -> Bool
  | s1@(x :: s1'), y :: s2' => subseqb (if x = y then s1' else s1) s2'
  | [], _ :: _ => true
  | s1, [] => s1 = []

@[simp] theorem mask_false (s : Seq α) (n : Nat) : mask (nseq n false) s = [] := by
  elim: s n=> [|??/[swap]][]// ?
  srw ?nseq//

def index (x : α) := find (x = ·)

@[simp] def index_cons (s : Seq α) (y x : α) :
  index x (y :: s) = if x = y then 0 else  Nat.succ $ index x s := by rfl

@[simp] def take (n : Nat) (s : Seq α) :=
  match s, n with
  | x :: s', n' + 1 => x :: take n' s'
  | _, _ => []

theorem index_mem (s : Seq α) : (index x s < size s) = (x ∈ s) := by
  sby elim: s=> //== >; scase_if=> //==

variable [Inhabited α]

theorem nth_mem (s : Seq α) : i < size s -> nth s i ∈ s := by
  elim: s i=> // > /[swap][]//

theorem nth_index (s : Seq α) : x ∈ s → nth s (index x s) = x := by
  sby elim: s=> //== >; scase_if

theorem all_nthP (p : α -> Prop) [DecidablePred p] (s : Seq α) :
  all p s =
  ∀ i, i < size s -> p (nth s i) := by
  simp=> ⟨all *|all ? /[dup] /index_mem ? /nth_index<-⟩
  { apply all; apply nth_mem; omega }
  apply all; omega

theorem ltSS (a b : Nat) : (a < b) = (Nat.succ a < Nat.succ b) := by
  move=> /==

@[simp] theorem size_take (s : Seq α) : size (take n s) = if n < size s then n else size s := by
  elim: s n=> [//|x s IHs [//|n/=]]; srw IHs -ltSS; scase_if


@[simp] theorem nth_take {i : Nat} {s : Seq α}  :
  i < n → nth (take n s) i = nth s i := by
  sby elim: s n i=> // > IHs []//= ? []

theorem before_find a [DecidablePred a] (s : Seq α) : i < find a s → ¬ a (nth s i) := by
  elim: s i=> //= > IHs []//== <;> scase_if=> //

@[simp] def drop : Nat -> Seq α -> Seq α
  | n' + 1, _ :: s' => drop n' s'
  | _, s => s

@[simp] theorem size_drop : size (drop n s) = size s - n := by
  sby elim: s n=> //== > /[swap][]

@[simp] theorem cat_take_drop n0 (s : Seq α) : take n0 s ++ drop n0 s = s := by
  sby elim: s n0=> // > /[swap][]

theorem mask_cat : size m1 = size s1 → mask (m1 ++ m2) (s1 ++ s2) = mask m1 s1 ++ mask m2 s2 := by
  sby elim: m1 s1=> [/== ? /size0nil->|/== [] ?? []]

theorem drop_nth (s : Seq α) : n < size s → drop n s = nth s n :: drop (n+1) s := by
  sby elim: s n=> // x s /[swap][]//=

@[simp] theorem nseqSn : nseq (.succ n) x = x :: nseq n x := by rfl

@[simp↓] theorem all_pred1P (s : Seq α) (x : α) :
  (s = nseq (size s) x) =
  all (x = ·) s := by
    elim: s x=> //== >/[swap]?<- //==

theorem take_oversize (s : Seq α) : size s ≤ n → take n s = s := by
  sby elim: s n=> // > /[swap][] //==

@[simp] theorem behead_cons : behead (x :: xs) = xs := by rfl

def subseq (s1 s2 : Seq α) := exists m, size m = size s2 /\ s1 = mask m s2

@[reflect]
instance subseqP (s1 s2 : Seq α) :
  Reflect (subseq s1 s2) (subseqb s1 s2)  := by
  apply reflect_of_equiv; srw subseq
  elim: s2 s1=> [| y s2 IHs2] [|x s1] //
  { simp; exists [] }
  { sby simp; exists (nseq (Nat.succ (size s2)) false) }
  simp [IHs2]; constructor=> [] m [] sz_m def_s1
  { sby exists ((x = y) :: m); simp [<-def_s1]; scase_if }
  scase_if=> ne_xy; rotate_right
  { scase: m def_s1 sz_m=> [|[]] //== }
  generalize h : (index true m) = i at *
  shave def_m_i : take i m = nseq (size (take i m)) false
  { simp [all_nthP]=> j le; srw nth_take
    { shave: ¬(true = nth m j);
      { apply before_find (_ = ·)
        scase_if: le <;> srw index at h <;> omega }
      generalize (nth m j) = b; sby scase:b }
    scase_if: le=> //== ? le
    sby apply (Nat.lt_of_lt_of_le le) }
  shave lt_i_m : i < size m
  { apply Nat.lt_of_not_le=> ?
    srw take_oversize // at def_m_i
    sby srw def_m_i mask_false at def_s1 }
  simp [-all_pred1P, lt_i_m] at def_m_i
  exists (take i m ++ drop (i+1) m); constructor
  { simp_all [size_cat, size_drop] }
  move: {def_s1} (congrArg behead def_s1)=> /== -> {s1}
  srw -[1](cat_take_drop i m) -(cat_take_drop i s2) def_m_i -cat_cons
  shave sz_i_s2: size (take i s2) = i; simp; omega
  srw lastI cat_rcons ?mask_cat ?size_belast ?sz_i_s2 //== <;> try omega
  sby srw (drop_nth _ lt_i_m) // -[1]h nth_index // -index_mem


-- set_option trace.reflect true
#reflect subseq subseqb

-- theorem subseq_trans' (s1 s2 s3 : Seq α) : subseq s1 s2 -> subseq s2 s3 -> subseq s1 s3 := by
--   scase! => m2 _ -> ![m1 _ ->]
--   elim: s3 m1 m2=> [|x s IHs1] // /- use boolean to resolve base case -/
--   move=> [] // [] m1 /=; rotate_left /- use boolean to resolve m1=[] case -/
--   { scase=> // [] //= m2; /- use boolean to resolve m2=[] and m2 = true::_ , m1 = true::_ cases -/
--     sby scase!: (IHs1 m1 m2)=> m ??; exists (false :: m) }
--   move=> m2; scase!: (IHs1 m1 m2)=> m ??
--   sby exists (false :: m)

def travsitive {T : Type} (R : T -> T -> Prop) :=
  forall x y z, R x y -> R y z -> R x z

theorem subseq_trans : travsitive (@subseq α) := by
  move=> ? ? s ![m2 _ ->] ![m1 _ ->]
  elim: s m1 m2=> [//|x s IHs1]
  scase=> [//|[] m1 /=]; rotate_left
  { scase=> [/=|[] m2] //;
    scase!: (IHs1 m1 m2)=> m sz_m ?
    sby exists (false :: m) }
  move=> m2; scase!: (IHs1 m1 m2)=> m sz_m ?
  sby exists (false :: m)

/-
Lemma subseq_trans T : transitive (@subseq T).
Proof.
move=> _ _ s /subseqP[m2 _ ->] /subseqP[m1 _ ->].
elim: s m1 m2 => [*|x s IHs]; first by rewrite !mask0.
case=> [*|[] m1] //; first by rewrite mask0.
  case=> [/=|[] m2] //; first by rewrite /= eqxx IHs.
  case/subseqP: (IHs m1 m2) => m sz_m ?; apply/subseqP.
  by exists (false :: m); rewrite //= sz_m.
move=> m2; case/subseqP: (IHs m1 m2) => m sz_m ?; apply/subseqP.
by exists (false :: m); rewrite //= sz_m.
Qed.
-/

end perm_seq

end seq
