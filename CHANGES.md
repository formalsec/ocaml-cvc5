## 1.3.0

### Added

- Stub to create RegExp sort

### Changed

- Updated cvc5's version to v1.3.0
- Updated CaDiCaL's version to v2.1.3
- Updated LibPoly's version to v0.2.0
- Changed LICENSE to MIT

### Fixed

## 1.2.0

### Added

- Stub-side reference counting to deal with GC collection order
- Refactor stubs to include `CAMLparam`, `CAMLlocal`, and `CAMLreturn` directives to safeguard GC interactions
- Documentation for module interfaces

### Changed

- Updated the version of cvc5 supported to v1.2.0

### Fixed

- Changed number of Opam jobs used during compilation to avoid excessive memory use 

## 1.1.3

Initial release.

Vendor submodules:
- [cvc5](https://github.com/cvc5/cvc5/tree/27e8c50df1d91cbfc8801977b45df7fc57f58775) commit:27e8c50 (v1.1.3-unreleased)
- [CaDiCaL](https://github.com/arminbiere/cadical/tree/2df7b7fed0f9c522fd4cdf6e88cecad4cac8a2df) commit:2df7b7f
- [LibPoly](https://github.com/SRI-CSL/libpoly/tree/7a4dedcdc3446ac8fba5673faeb2e95bed9bb73a) commit:7a4dedc
- [SymFPU](https://github.com/cvc5/symfpu/tree/c3acaf62b137c36aae5eb380f1d883bfa9095f60) commit:c3acaf6

### Added

Stubs with support for the following cvc5 API classes:
- Solver
- TermManager
- Term
- Op
- Result
- Sort

### Changed

### Fixed
