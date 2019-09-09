# OpenQASM to SQIR Translation

Work in progress

## Requirements
Current version of OCaml and the following dependencies:
```
$ opam install menhir utop
```

## Steps
- Follow [compilation instructions](../../README.md#compilation-instructions) in the top (`../..`) directory.
- Run `./extractSqireGates.sh`
- Run `./extract.sh` in the parent (`..`) directory (TODO: remove this dependency).
- `dune utop .`
- In the `utop` REPL, play with `Main.parse "<file>.qasm";;` etc.
