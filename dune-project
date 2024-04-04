(lang dune 3.10)

(name cvc5)

(generate_opam_files true)

(source
 (github formalsec/ocaml-cvc5))

(authors "João Pereira <joaomhmpereira@tecnico.ulisboa.pt>")

(maintainers "João Pereira <joaomhmpereira@tecnico.ulisboa.pt>")

(package
  (name cvc5)
  (synopsis "OCaml bindings for the CVC5 SMT solver")
  (description "OCaml bindings for the CVC5 SMT solver")
  (depends
   dune
   (ocaml (>= 4.12))
   (conf-gcc :build)
   (conf-g++ :build)
   (conf-gmp :build)
   (conf-python-3 :build)))
