# LeanSSR: an SSReflect-Like Tactic Language for Lean

This repository provides a SSReflect tactic language for Lean4, as well as some extra handy tactics you might miss from Coq

## Building 

With `elan` installed, `lake build` should suffice.

## Adding SSReflect to your project

To use Ssreflect in a Lean 4 project, first add this package as a dependency. In your lakefile.lean, add

```lean
require ssreflect from git "https://github.com/verse-lab/lean-ssr" @ "master"
```

Then run 

```
lake update ssreflect
```

You also need to make sure that your lean-toolchain file contains the same version of Lean 4 as SSReflect's, and that your versions of SSReflect's dependencies (currently only std4) match. We unfortunately can't support version ranges at the moment.

Now the following test file should compile:

```lean
import Ssreflect.Lang

example {α : Type} : α → α := by
  -- The following is euqivalen to 
  -- intro x; trivial
  move=> x//
```


## Supported features

Here we list all features we support at the moment.

### Tactics

1. `scase`: equivalent to SSReflect's `case`
6. `scase_if`: does case analysis on the first `if` statement
2. `elim`: equivalent to SSReflect's `elim`
3. `move`:  Reduces goal to the weak head normal form
4. `moveR`: like `move` but only reduces `[@ reducable]` definitions
5. `apply t in H`: applies term `t` in hypothesis `H`, and moves the result on top the proof stack. `H` should not necessarily be the first argument of `t`, tactic will figure out which argument to instantiate automatically. It will also instantiate all other arguments of `t` which can be deduced from `H`
6. `shave`: SSReflect version of `have` (see below)
6. `srw`: SSReflect version of `rw` (see below)

### Intro patterns

SSReflect intro patterns come after `=>` tactical. The general syntax here would be `tac=> intro_pats`. This first executes `tac`, and then `intro_pats`. All intro patterns listed below are equivalent to their SSReflect counterparts.

1. `name`, `?`, `_`, `*`, `>`, `->`, `<-`
2. `/t`: applies `t` to the top hypothesis on the stack 
3. `/(_ t)`: applies top hypothesis on the stack to `t` 
4. `/[swap]`,`/[dup]`, `/[apply]`: swaps first two top hypothesis on the stack, duplicates top hypothesis on the stack, applies the first top hypothesis to the the second top hypothesis
5. `[]`: equivalent to `scase`
6. `![x y]`: iterative version of `[]`. Destructs the top element on the goal stack and all its nested structures. Equivalent to `[x .. [.. [y]]]`, e.g. to destruct `∃ (x y : Nat)`
7. `[ branch_1 | branch_2 | .. | branch_n  ]`: equivalent to `scase`, but runs `branch_i` on the `i`-th subgoal which appears after case analysis
8. `{ name_1 name_2 .. name_n }`: clears all `name_i`s
9. `{}name`: equivalent to `clear name; intro name`
10. `/=`, `/==`: equivalent to `dsimp` and `simp` correspondently
11. `//`: calls `ssr_triv` tactic (combination of `simp_all` and `trivial`). If you want to agument it with an extra tactic `tac`, you can write
```lean
macro_rules : tactic
  | `(tactic| ssr_triv) => `(tactic| tac)
```
Note that `//` will never fail. If it cannot solve the goal it will leave it unchanged. 

12. `//=`, `//==`: equivalent to `// /=` and `// /==`
13. `/[tac t]`: calls tactic `t`

Moreover intro patterns are extensible. If you want to add you own intro pattern `pat`, just write 

```lean
syntax <pat> : ssrIntro.
elab_rules : tactic
  | `(ssrIntro| pat) => <implementation>
```

### Revert patterns

We implement `:` tactical, which behaves in the same way as is does in SSReflect. `tac: r_1 r_2 .. r_n` will revert all `r_i`s back to the goal and then executes tactic `tac`. Note that if you put `r_i` in parentheses `(r_i)`, `:` will revert `r_i` keeping a copy of it in the context. 

[TODO] explain `tac: [p]`

### SSReflect version of `have` tactic

We support `shave intro_pats : ty` tactic. Same as in SSReflect, it asserts a term of type `ty` (introducing a new goal for it), puts it on the proof stack, and runs `intro_pats`.

### SSReflect version of `rewrite` tactic

We support SSReflect version of `rewrite`. The general syntax for it is 
```lean
srw ([-] [? <|> !] [ [[-] pos*] ] trm)* [at loc]
```
where
1.  `[-]` is responsible for the rewrite direction: empty for direct and `-` for reversed
2. `[? <|> !]` is responsible for the number of times we rewrite: `?` for 0 and more and `!` for 1 and more
3. `[ [[-] [pos*] ] ]` is responsible for positions of terms matching `thm` at which we rewrite: `[n_1 n_2 n_3 ...]` for rewriting at all `n_i` positions, `[- n_1 n_2 n_3 ...]` for rewriting at all positions except `n_i` and empty for rewriting at all positions
4. `thm` for the equality which we want to rewrite 
5. `[at loc]` for the location at which we rewrite (empty for rewriting in the goal)

You can also use `//`, `/=`, `//=`, `/==` and `//==` inside `srw`. 

example : 
```lean
srw -![1 3](cat_take_drop i m) //= -?[- 5 6](cat_take_drop i s2) def_m_i -cat_cons at h |-
```

### Examples

You can find SSL use case examples at `Examples` folder
