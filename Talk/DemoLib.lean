import Ssreflect.Lang

@[simp] def uniq : List α -> Prop
  | [] => true
  | x :: s => ¬ (x ∈ s) ∧ uniq s

@[simp] def mask : List Bool -> List α -> List α
  | true  :: m, x :: s => x :: mask m s
  | false :: m, _ :: s => mask m s
  | _         , _      => []

@[simp] def mask_mem (s : List α) m x : x ∈ mask m s -> x ∈ s := by
  elim: s m=> // > IHm [] // []/== > => [/IHm | []// /IHm] //

variable (a : α -> Prop) [DecidablePred a]

def all (a : α -> Prop) (s : List α) : Prop := ∀ (x : α), x ∈ s → a x

@[simp] def allb (s : List α) :=
  match s with
  | [] => true
  | x :: s' => a x && allb s'

@[reflect]
instance allP (s : List α) : Reflect (all a s) (allb a s) := by
  apply reflect_of_equiv
  elim: s=>//== => [x //= | x s' ->]; constructor
  { move=>[]hx ha y [//= | /ha //=] }
  {
    move=>/[dup] h /(_ x) //== hx; constructor
    { sdone }
    { move=> y; move: h => /(_ y) //= }
  }
#reflect all allb

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

@[simp] def size : List α -> Nat
  | [] => 0
  | _ :: xs => Nat.succ $ size xs
