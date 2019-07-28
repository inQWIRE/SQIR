# OpenQASM to SQIR Translation

Work in progress

## Requirements
Current version of OCaml and dune and the following dependencies:
```
$ opam install utop ppx_deriving
```

## Steps
- Follow [compilation instructions](../../README.md#compilation-instructions) in the top (`../..`) directory.
- Run `./extract.sh` in the parent (`..`) directory.
- `dune utop .`
- In the `utop` REPL, play with `Main.parse "<file>.qasm";;` etc.
