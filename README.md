# smt-tools

Various self-contained programs for working with [SMT-LIB] files.
Lousy research-grade code without documentation and lots of limitations and bugs.
Without modifications, they will likely not work for your use-case.

## The Tools

* `smt-analyze`: Analyzes the composition of `QF_BV` SMT-LIB files
* `smt-normalize`: Normalizes SMT-LIB expression (e.g. removing incremental solving)
* `smt-depth`: Calculates the maximum nesting depth as a complexity metric
* `smt-simplify`: Simplifies selected expressions (e.g. all `bvadd`) using [Z3]

## See also

Some other tools I found useful:

* [`smtfmt`]: Formats SMT-LIB expressions for human readability
* [`diff-sexp`]: A tool for diffing SMT-LIB expressions
* …

[SMT-LIB]: https://smt-lib.org
[`smtfmt`]: https://github.com/symflower/smtfmt
[`diff-sexp`]: https://github.com/yav/simple-smt/blob/1.0.1/exe/DiffSExp.hs
[Z3]: https://github.com/Z3Prover/z3
