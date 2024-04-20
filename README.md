[![Build badge](https://github.com/formalsec/ocaml-cvc5/actions/workflows/build.yml/badge.svg)](https://github.com/formalsec/ocaml-cvc5/actions) [![GPL-3.0](https://img.shields.io/github/license/formalsec/ocaml-cvc5)](LICENSE) ![Platform](https://img.shields.io/badge/platform-linux%20%7C%20macos-lightgrey)

ocaml-cvc5 
===============================================================================

OCaml bindings for the [cvc5] Satisfiability Modulo Theories (SMT) solver

## Installation

### Build from source

---
- Clone the complete source tree:

```sh
git clone --recurse-submodules https://github.com/formalsec/ocaml-cvc5
```

- Install the library dependencies:

```sh
cd ocaml-cvc5
opam install . --deps-only
```

- Build and test:

```sh
dune build
dune runtest
```

- Install cvc5's OCaml bindings on your path by running:

```sh
dune install
```

## Examples

Run examples with:

```sh
dune exec -- examples/toy.exe  #replace toy with any other example
```

[cvc5]: https://github.com/cvc5/cvc5
