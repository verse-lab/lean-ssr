import Ssreflect.Lang
import Talk.DemoLib

/- BigStep -/



/- Subseq via mask  -/

section subseq_via_mask

def subseq (s1 s2 : List α) : Prop :=
  ∃ m : List Bool, size m = size s2 ∧
       s1 = mask m s2

theorem subseq_uniq (s1 s2 : List α) : subseq s1 s2 -> uniq s2 -> uniq s1 := by
  scase! => m _ ->
  elim: s2 m=> // > ? [] // [] //== * ⟨/mask_mem|⟩//

theorem subseq_all (p : α -> Prop) [DecidablePred p] (s1 s2 : List α) :
  subseq s1 s2 -> all p s2 -> all p s1 := by
  scase! => m _ ->
  elim: s2 m=> // > ? [] // [] //

theorem size_subseq (s1 s2 : List α): subseq s1 s2 -> size s1 <= size s2 := by
  scase! => m _ ->
  elim: s2 m=> // > ? [] // [] //

end subseq_via_mask

/- Cons -/

section cons

-- example : subseq [2, 3, 6] [1, 2, 3, 4, 5, 6] := by simp
-- example : ¬ subseq [2, 7, 6] [1, 2, 3, 4, 5, 6] := by simp

-- example (x : List α) : subseq [] x = (x = []) := by simp
-- example (x : α) (s : List α) : subseq (x :: s) [] = False := by simp
-- example (x : α) (s r : List α) : subseq (x :: s) (x :: r) = subseq s r := by simp


end cons

/- Subseq via recursion -/

section subseq_via_recursion

variable {α : Type} [DecidableEq α]

@[simp] def subseqb : List α -> List α -> Bool
  | [], _ :: _ => true
  | s1, [] => s1 == []
  | x :: s1, y :: s2 =>
    if x = y then
      subseqb s1 s2
    else subseqb (x :: s1) s2


example : subseqb [2, 3, 6] [1, 2, 3, 4, 5, 6] = true := by simp
example : subseqb [2, 7, 6] [1, 2, 3, 4, 5, 6] = false := by simp

example (x : List α) : subseqb x [] = (x = []) := by simp
example (x : α) (s : List α) : subseqb (x :: s) [] = false := by simp
example (x : α) (s r : List α) : subseqb (x :: s) (x :: r) = subseqb s r := by simp

end subseq_via_recursion

/- Can we have them both? -/

section leanssr

variable {α : Type} [DecidableEq α]

@[reflect]
instance subseqP (s1 s2 : List α) :
  Reflect (subseq s1 s2) (subseqb s1 s2) := by
    apply reflect_of_equiv
    sorry


set_option trace.reflect true
#reflect subseq subseqb

#check fun s1 s2 => if subseq s1 s2 then true else false


def transitive {T : Type} (R : T -> T -> Prop) :=
  forall x y z, R x y -> R y z -> R x z

example : transitive (@subseq α) := by
  move=> ?? s ![m2 _ ->] ![m1 _ ->]
  elim: s m1 m2=> [|x s IHs1]
  { simp
    -- srw -(equiv_of_reflect (subseqP ..))
    -- simp
  }
  scase=> [|[] m1 /= m2]
  { simp }
  { scase!: (IHs1 m1 m2)=> m ?->
    sby exists (false :: m) }
  scase: m2=> [|[] m2] /=
  { simp }
  { scase!: (IHs1 m1 m2)=> m ?->
    exists (false :: m)=> // }
  { specialize IHs1 m1 m2
    simp [IHs1] }

example : transitive (@subseq α) := by
  move=> ?? s ![m2 _ ->] ![m1 _ ->]
  elim: s m1 m2=> [//|x s IHs1]
  scase=> [|[] m1 /= m2] //
  { scase!: (IHs1 m1 m2)=> m ?->
    sby exists (false :: m) }
  scase: m2=> [|[] m2] //=
  { scase!: (IHs1 m1 m2)=> m ?->
    sby exists (false :: m) }

end leanssr
--
