open Printf
open ShorExtr

(* light argument parsing *)
let n = ref 0
let a = ref 0
let o = ref 0
let usage = "usage: " ^ Sys.argv.(0) ^ " [-N int] [-a int] [-o int]"
let speclist = [
    ("-N", Arg.Set_int n, ": number to factor");
    ("-a", Arg.Set_int a, ": coprime value");
    ("-o", Arg.Set_int o, ": measurement outcome")
  ]
let () =
  Arg.parse
    speclist
    (fun x -> raise (Arg.Bad ("Bad argument : " ^ x)))
    usage;
if (!a <= 0 || !n <= !a) then printf "ERROR: Requires 0 < a < N\n%!" else 
if (Z.gcd (Z.of_int !a) (Z.of_int !n) > Z.one) then printf "ERROR: Requires a, N comprime\n%!" else 
(* perform post-processing *)
(printf "Performing post-processing for N = %d, a = %d, and o = %d...\n%!" !n !a !o;
 let res = post_process !a !n !o in
 printf "Result is: %d\n%!" res)