# LeanSSR: an SSReflect-Like Tactic Language for Lean

This repository provides LeanSSR: a SSReflect tactic DSL for Lean4. LeanSSR extends Coq/SSReflect's tactic DSL with various new DSL constructions and enhanced mechanism for computational reflection.

## Building 

With `elan` installed, `lake build` should suffice.

## Adding SSReflect to your project

To use SSReflect in a Lean 4 project, first add this package as a dependency. In your `lakefile.lean`, add

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

## Documentation

Main LeanSSR features are documented [here](https://arxiv.org/abs/2403.12733). More detailed documentation of LeanSSR DSL can be found at [LeanSSR Wiki](https://github.com/verse-lab/lean-ssr/wiki)

## Examples

You can find LeanSSR use case examples at `Examples` folder
