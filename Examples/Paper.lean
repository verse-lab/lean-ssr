import Ssreflect.Lang
import Std.Data.List
import Examples.Nat

-- Figure 2 (a)
example: α → α := by
  sapply

-- Figure 2 (b)
example: α → β → α := by
  move=> hA ?
  move: hA; sapply

-- Figure 2 (c)
example: α → (α → β) → β := by
  move=> /[swap] hAiB
  sapply: hAiB

-- Figure 3
example (m n : Nat) : n ≤ m →
  m - n + n = m := by
  elim: n m=>[| n IHn [| m']] //==
  move=> ?; srw -[2](IHn m') //

-- Figure 5/6, LeanSSR version
example (A B C : Prop) :
  (A → B) → (B → C) → (A → C) := by
  sby move=> AiB BiC /AiB /BiC

-- Figure 7
inductive even : Nat → Prop where
  | ev0 : even 0
  | ev2: ∀ n, even n → even (n + 2)

def evenb : Nat → Bool
  | 0 => true
  | 1 => false
  | n + 2 => evenb n

@[reflect] instance evenP n : Reflect (even n) (evenb n) :=
  match n with
  | 0 => by sdone
  | 1 => by simp [evenb]; apply Reflect.F; intro r; cases r; trivial
  | n + 2 => by
    simp [evenb]; cases (evenP n)
    { apply Reflect.T <;> try assumption
      constructor; assumption }
    apply Reflect.F <;> try assumption
    intro n; cases n; contradiction
#reflect even evenb

example n m : even n → even (m + n) = even m := by
  elim=> // n' _ <-
  srw -Nat.add_assoc /==

-- Figure 8
section Subseq
variable {α : Type} [DecidableEq α]

@[simp] def mask: List Bool → List α → List α
  | b :: m, x :: s =>
    if b then x :: mask m s else mask m s
  | _, _ => []

def subseq (s1 s2 : List α) : Prop :=
  ∃ m, List.length m = List.length s2 ∧
    s1 = mask m s2

def subseqb: List α → List α → Bool
  | [], _ :: _          => true
  | s, []               => s = []
  | s@(x :: s'), y :: r =>
    subseqb (if x = y then s' else s) r

-- A proof of this fact can be found in `Seq.lean`
@[reflect]
instance subseqP (s1 s2 : List α) :
  Reflect (subseq s1 s2) (subseqb s1 s2) := by sorry
#reflect subseq subseqb

def transitive (R : α → α → Prop) :=
  ∀ x y z, R x y → R y z → R x z

example : transitive (@subseq α):= by
  move=> ?? s ![m2 _ ->] ![m1 _ ->]
  elim: s m1 m2=> [// |x s IHs1]
  scase=> [// |[] m1 /= m2]
  { scase!: (IHs1 m1 m2)=> m ?->
    sby exists (false :: m) }
  scase: m2=> [|[] m2] //=;
  scase!: (IHs1 m1 m2)=> m ?->;
  sby exists (false :: m)



end Subseq
