[![Build badge](https://github.com/formalsec/ocaml-cvc5/actions/workflows/build.yml/badge.svg)](https://github.com/formalsec/ocaml-cvc5/actions) [![MIT](https://img.shields.io/github/license/formalsec/ocaml-cvc5)](LICENSE) ![Platform](https://img.shields.io/badge/platform-linux%20%7C%20macos-lightgrey)

ocaml-cvc5 
===============================================================================

OCaml bindings for the [cvc5] Satisfiability Modulo Theories (SMT) solver

## Installation

### Opam

---
- Install [opam](https://opam.ocaml.org/doc/Install.html).
- Bootstrap the OCaml compiler:

```sh
opam init
opam switch create 5.2.0 5.2.0
```

- Install cvc5's OCaml bindings:

```sh
opam install cvc5
```
:warning:   Installation via Opam is only available for Linux systems.

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
