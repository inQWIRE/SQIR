# OpenQASM to SQIR Translation

Work in progress

## Requirements
Current version of OCaml and the following dependencies:
```
$ opam install menhir utop
```

## Steps
- Follow [compilation instructions](../README.md#compilation-instructions) in the top directory.
- Run `./extractSQIRGates.sh`
- `dune utop .`
- In the `utop` REPL, play with `Qasm_to_sqir.parse "<file>.qasm";;` etc.
