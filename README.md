# SSL: SSReflect Tactic language for Lean4

This repository provides a SSReflect tactic language for Lean4, as well as some extra handy tactics you might miss from Coq

## Building 

With `elan` installed, lake build should suffice.

## Adding SSReflect to your project

To use Ssreflect in a Lean 4 project, first add this package as a dependency. In your lakefile.lean, add

```lean
require aesop from git "https://github.com/verse-lab/ssr-lean"
```

Then run 

```
lake update Ssreflect
```

You also need to make sure that your lean-toolchain file contains the same version of Lean 4 as SSReflect's, and that your versions of SSReflect's dependencies (currently only std4) match. We unfortunately can't support version ranges at the moment.

Now the following test file should compile:

```lean
import Ssreflect.Lang

example : α → α :=
  move=> ? //=
```


## Supported features

Here we list all features we support at the moment.

### Tactics

1. `scase`: equivalent to SSReflect's `case`
2. `elim`: equivalent to SSReflect's `elim`
3. `move`:  Reduces goal to the weak head normal form
4. `moveR`: like `move` but only reduces `[@ reducable]` definitions
5. `apply t in H`: applies term `t` in hypothesis `H`, and moves the result on top the proof stack. `H` should not necessarily be the first argument of `t`, it will figure out what argument to instantiate automatically. It will also instantiate all arguments of `t` which can be deduced from `H`.

### Intro patterns

SSReflect intro patterns come after `=>` tactical. The general syntax here would be `tac=> intro_pats`, this will first execute `tac`, and then `intro_pats`. All intro patterns below listed are equivalent to their SSReflect counterparts.

1. `name`, `?`, `_`, `*`, `>`, `->`, `<-`
2. `/t`: applies `t` to the top hypothesis on the stack.  
3. `/(_ t)`: applies top hypothesis on the stack to `t` 
4. `/[swap]`,`/[dup]`, `/[apply]`: swaps first two top hypothesis on the stack, duplicates top hypothesis on the stack, applies the top hypothesis to the the second top hypothesis. 
5. `[]`: equivalent to `scase`
6. `[ branch_1 | branch_2 | .. | branch_n  ]`: equivalent to `scase`, but runs `branch_i` on the `i`-th subgoal, appears after case analysis.
7. `{ name_1 name_2 .. name_n }`: clears all `name_i`s
8. `{}name`: equivalent to `clear name; intro name`
9. `/=`, `/==`: equivalent to `dsimp` and `simp` correspondently 
10. `//`: calls `ssr_triv` tactic. By default it boils down to `trivial`, but you can customize it. For example if you want it to call tactic `tac` you have to write 
```lean
macro_rules
  | `(tactic| ssr_triv) => `(tactic| tac)
```
Note that it will **no** effect if `tac` didn't manage to solve the goal.

11. `//=`, `//==`: equivalent to `// /=` and `// /==`
12. `/[tac t]`: calls tactic `t`

Moreover intro patterns are extensible. If you want to add you own intro pattern `pat` that implemented with tactic `t`, just write 

```lean
macro "pat" : ssr_intro => `(ssr_intro| /[tac t])
```

### Revert patterns

We also implement `:` tactical, which behaves in the same way as is does in SSReflect. `tac: r_1 r_2 .. r_n` will revert all `r_i` back to the goal and then execute tactic `tac`. Note that if `r_i` is a term in parentheses `(t)`, then it will revert `t` keeping a copy of it in the context. 


### Examples

You can find SSL use case examples at [TODO]
