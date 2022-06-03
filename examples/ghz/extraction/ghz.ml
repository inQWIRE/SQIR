open Printf

open Qasm
open ExtrGHZ

let n = int_of_string Sys.argv.(1);;
printf "Generating GHZ circuit for N = %d\n" n;;
write_qasm_file "ghz.qasm" (ghz n) n;;
