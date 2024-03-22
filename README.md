# LeanSSR: an SSReflect-Like Tactic Language for Lean

This repository provides LeanSSR: a SSReflect tactic DSL for Lean4. LeanSSR extends Coq/SSReflect's tactic DSL with various new DSL constructions and enhanced mechanism for computational reflection.

## Building 

With `elan` installed, `lake build` should suffice.

## Adding LeanSSR to your project

To use the latest version of LeanSSR in a Lean 4 project, first add this package as a dependency. In your `lakefile.lean`, add

```lean
require ssreflect from git "https://github.com/verse-lab/lean-ssr" @ "master"
```

Then run 

```
lake update ssreflect
```

You also need to make sure that your `lean-toolchain` file contains the same version of Lean 4 as LeanSSR's, and that your versions of LeanSSR's dependencies (currently only `std4`) match. THe project does not support version ranges at the moment.

You may also consider using a stable release of the framework by adding the following to your `lakefile.lean` instead:

```lean
require ssreflect from git "https://github.com/verse-lab/lean-ssr" @ "v1.0"
```

Once LeanSSR is downloaded and compiler, the following test file should compile:

```lean
import Ssreflect.Lang

example {α : Type} : α → α := by
  -- The following is equivalent to 
  -- intro x; trivial
  move=> x//
```

## Documentation

* The paper [Small Scale Reflection for the Working Lean User](https://arxiv.org/abs/2403.12733) provides a brief tutorial on LeanSSR and documents its main features
* [LeanSSR Wiki](https://github.com/verse-lab/lean-ssr/wiki) containts detailed technical documentation on LeanSSR tactics

## Examples

You can find LeanSSR use case examples at `Examples` folder

## Contributors

* [Vladimir Gladshtein](https://volodeyka.github.io/)
* [George Pîrlea](https://pirlea.net/)
* [Ilya Sergey](https://ilyasergey.net/)
