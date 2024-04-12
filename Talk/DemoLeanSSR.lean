import Ssreflect.Lang

def State : Type := String → Nat

def State.update (name : String) (val : Nat) (s : State) : State :=
  fun name' ↦ if name' = name then val else s name'

macro s:term "[" name:term "|->" val:term "]" : term =>
  `(State.update $name $val $s)

/--
S  ::= skip                 -- no-op\
    |  x := a               -- assignment\
    |  S; S                 -- sequential composition\
    |  if B then S else S   -- conditional statement\
    |  while B do S         -- while loop
-/
inductive Stmt : Type where
  | skip       : Stmt
  | assign     : String → (State → Nat) → Stmt
  | seq        : Stmt → Stmt → Stmt
  | ifThenElse : (State → Prop) → Stmt → Stmt → Stmt
  | whileDo    : (State → Prop) → Stmt → Stmt

infixr:90 "; " => Stmt.seq
notation:90 "if " b "  then " t " else " e => Stmt.ifThenElse b t e
notation:90 "while " b "  do " t => Stmt.whileDo b t
notation:80 a " ::= " b => Stmt.assign a b
-- notation:80 "skip" => Stmt.skip

/-
if x = 0 then
  x := y + 1
else skip
-/
-- #check
--   if (fun s => s "x" = 0) then
--     "x" ::= (fun s => s "y" + 1)
--   else skip

@[inline] abbrev app_sem (f : A -> B) (g : A) : B := f g

notation:100 "〚" f "〛" g => app_sem f g

inductive BigStep : Stmt × State → State → Prop where
  | skip (s) :
    BigStep (Stmt.skip, s) s
  | assign (x a s) :
    BigStep (Stmt.assign x a, s) (s[x |-> 〚a〛s])
  | seq (S T s t u) (hS : BigStep (S, s) t)
      (hT : BigStep (T, t) u) :
    BigStep (S; T, s) u
  | if_true (B S T s t) (hcond : 〚B〛s)
      (hbody : BigStep (S, s) t) :
    BigStep (Stmt.ifThenElse B S T, s) t
  | if_false (B S T s t) (hcond : ¬ 〚B〛s)
      (hbody : BigStep (T, s) t) :
    BigStep (Stmt.ifThenElse B S T, s) t
  | while_true (B S s t u) (hcond : 〚B〛s)
      (hbody : BigStep (S, s) t)
      (hrest : BigStep (Stmt.whileDo B S, t) u) :
    BigStep (Stmt.whileDo B S, s) u
  | while_false (B S s) (hcond : ¬ 〚B〛s) :
    BigStep (Stmt.whileDo B S, s) s

infix:110 " ~~> " => BigStep


example : (Stmt.skip; Stmt.skip, s) ~~> s := by
  apply BigStep.seq (t := s)
  { apply BigStep.skip }
  { apply BigStep.skip }

/-
---------------------skip     ---------------------skip
(Stmt.skip, s) ~~> s          (Stmt.skip, s) ~~> s
--------------------------------------------------seq
       (Stmt.skip; Stmt.skip, s) ~~> s
  -/

/- (S, s) ~~> t -/

/-  ∀ Ss l, Ss ~~> l -> ∀ r, Ss ~~> r -> l = r -/
theorem BigStep_deterministic {Ss l r} (hl : Ss ~~> l) (hr : Ss ~~> r) :
  l = r :=
  by
    induction hl generalizing r with
    | skip s => /- hl : (Stmt.skip, s) ~~> s -/
      cases hr with
      | skip s => rfl
    | assign x a s =>
      cases hr with
      | assign x a => rfl
    | seq S T s l₀ l hS hT ihS ihT =>
     /-        ...                  ...     -/
     /-   _____________       _____________ -/
     /-   (S, s) ~~> l₀       (T, l₀) ~~> l -/
     /-  ---------------------------------- -/
      /-      hl : (S; T, s) ~~> l        -/
      cases hr with
      | seq _ _ _ r₀ _ hS' hT' =>
        specialize ihS hS'
        rw [<-ihS] at hT'
        specialize ihT hT'
        rw [ihT]
    | if_true B S T s l hB hS ih =>
      cases hr with
      | if_true _ _ _ _ _ hB' hS'  => apply ih hS'
      | if_false _ _ _ _ _ hB' hS' => contradiction
    | if_false B S T s l hB hT ih =>
      cases hr with
      | if_true _ _ _ _ _ hB' hS'  => contradiction
      | if_false _ _ _ _ _ hB' hS' => apply ih hS'
    | while_true B S s l₀ l hB hS hw ihS ihw =>
      cases hr with
      | while_true _ _ _ r₀ hB' hB' hS' hw' =>
        rw [<-ihS hS'] at hw'
        rw [ihw hw']
      | while_false _ _ _ hB' => contradiction
    | while_false B S s hB =>
      cases hr with
      | while_true _ _ _ s' _ hB' hS hw => contradiction
      | while_false _ _ _ hB'           => rfl


/- ⊢ ∀ x y z, A -> B -> C -> Goal -/

theorem BigStep_deterministicSSR :
  ∀ Ss l r,
      Ss ~~> l ->
      Ss ~~> r ->
        l = r :=
  by move=> Ss l r hl
     move: hl r;
     elim=>
     [ > []
     | > []
     | > ?? ihS ihT r [] r₀ /ihS <- /ihT
     | > ?? ih ? [] // ? /ih
     | > ?? ih ? [] // ? /ih
     | > ?? ? ihS ihw ? [?? /ihS <- /ihw|]
     | > ?? [] ] //

theorem BigStep_deterministicSSR' :
  ∀ Ss l r,
      Ss ~~> l -> Ss ~~> r -> l = r := by
    move=> > hl
    elim: hl r=> > =>
      [ []
      | []
      | ?? ihS ihT ? [] ? /ihS <- /ihT
      | ?? ih ? [] // ? /ih
      | ?? ih ? [] // ? /ih
      | ?? ? ihS ihw ? [?? /ihS <- /ihw|]
      | ?? [] ] //
