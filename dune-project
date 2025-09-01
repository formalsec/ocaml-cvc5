(lang dune 3.19)

(name cvc5)

(generate_opam_files true)

(source
 (github formalsec/ocaml-cvc5))

(authors "João Pereira <joaomhmpereira@tecnico.ulisboa.pt>")

(maintainers "João Pereira <joaomhmpereira@tecnico.ulisboa.pt>")

(maintenance_intent "(latest)" "(latest).(latest-1).(any)")

(license "MIT")

(package
  (name cvc5)
  (synopsis "OCaml bindings for the cvc5 SMT solver")
  (description "OCaml bindings for the cvc5 SMT solver")
  (depends
   dune
   (ocaml (>= 4.12))
   (conf-gcc :build)
   (conf-g++ :build)
   (conf-gmp :build)
   (conf-cmake :build)
   (conf-python-3 :build)
   (conf-python-3-dev :build)
   (conf-python3-pyparsing :build)
   (conf-python3-tomli :build)))
