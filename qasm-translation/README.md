# OpenQASM to SQIR Translation

Work in progress

## Requirements
Current version of OCaml and dune and the following dependencies:
```
$ opam install utop ppx_deriving
```

## Steps
- Follow [compilation instructions](../README.md#compilation-instructions) in the parent (`..`) directory.
- Run `make` in the `../benchmarks` directory.
- Copy `extracted_code.ml` to `src` directory: `cp ../benchmarks/extracted_code.ml src/`
- `dune utop .`
- In the `utop` REPL, play with `Main.parse "<file>.qasm";;` etc.
