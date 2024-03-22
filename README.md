# LeanSAT

LeanSAT is a collection of utilities for SAT work. This includes:
- Encoding utilities
- Solver APIs
- Printers and parsers for common file formats

This repository is an active research code base using the
[Research Codebase Manifesto](https://www.moderndescartes.com/essays/research_code/),
and the core library (in `LeanSAT/`) is not very stable yet.

We would love to hear from any projects using LeanSAT!
Contact @JamesGallicchio by email or mastodon.

## Getting it

Add the following to your project's `lakefile`:
```
require «lean-sat» from git
  "https://github.com/JamesGallicchio/LeanSAT" @ "main"
```
The main branch is currently on Lean `v4.6.0`,
and Lean still has breaking changes every minor revision,
so expect it to not compile on any other version of Lean.

As this project relies on `mathlib`,
we recommend running `lake exe cache get` after modifying your lakefile.
This downloads a precompiled version of `mathlib`.

## Usage

In your files, `import LeanSAT` will import everything in the library.

Everything in the library is under the `LeanSAT` namespace,
so we generally assume you also have `open LeanSAT` at the top of your files.

Important types:
- `PropFun`: **The mathematical model of a propositional formula**.
  Two `PropFun`s are equal iff they have the same interpretation under all assignments.
- `EncCNF`: **The encoding monad.**
  This monad allows you to build up a CNF via do-notation.
  See `Examples/Encoding` for example usage.
- `VEncCNF`: **Verified encoding.**
  Similar to `EncCNF`, constrained to provably encode some predicate over assignments.
  This connects `EncCNF` to the `PropFun` math model.
- `Solver`, `Solver.ModelCount`, `Solver.ModelSample`: **Solver interfaces.**
  These are each typeclasses.
  The idea is that you should have an `instance` of the `Solver` typeclass in scope
  when you go to solve a CNF formula.
  See `Examples/Cadical.lean` for how to declare a solver instance.

### Notation

TODO(JG): describe available notation for `PropFun`, `PropForm`

## Planned scope

- Support (verified?) encoding to non-CNF formulas (KNF, d-DNNF, XOR-CNF, ...)
- Add verified checkers for sat certificates
  - See e.g. [here](https://github.com/joehendrix/lean-sat-checker),
      [here](https://github.com/leanprover-community/mathlib4/blob/master/Mathlib/Tactic/Sat/FromLRAT.lean),
      [here](https://github.com/leanprover/leansat)
- Add verified model counting
  - See [Bryant et al 2023](https://github.com/rebryant/cpog)
- Add verified pre-processing

## License

This project is licensed under the Apache 2.0 license (see [LICENSE](LICENSE)).
If you want to use the library but need it to be released under different terms,
please contact us or open an issue.

## Contributing

PRs are welcome and appreciated.
That said, because the repository is quite unstable,
please open an issue or comment on an existing one
to let us know what you are working on!

### Contributors

@vtec234
@ccodel
@JamesGallicchio
