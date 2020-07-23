open Ctypes
open UnitaryListRepresentation
open RzQGateSet.RzQGateSet
open GateCancellation
open HadamardReduction
open NotPropagation
open RotationMerging
open Optimize
open Qasm2sqir


(**Enums for RzQGateSet for Gates**)
type t =  |X | H| CNOT| Rz [@@deriving enum]
           
(**val get : int -> t**)
let get w = 
match w with 
1 -> X
|2 -> H
|3 -> CNOT
|4 -> Rz
|_ -> X

(**val set : t -> int**)
let set w = 
match w with 
X -> 1
|H -> 2
|CNOT -> 3
|Rz -> 4
let to_int64 d = Int64.of_int (to_enum d)
let coq_RzQ_Unitary1 = view ~read: get~write:set int

(**val rational : [ `rational ] Ctypes.structure Ctypes.typ
val num : (int, [ `rational ] Ctypes.structure) Ctypes.field
   val den : (int, [ `rational ] Ctypes.structure) Ctypes.field**)
let rational : [`rational] structure typ = structure "rational"
let num = field rational "num" (int)
let den = field rational "den" (int)
let () = seal rational

(**val get_rational : ([ `rational ], [ `Struct ]) Ctypes.structured -> Q.t**)
let get_rational d =
  let n = getf d num in
  let q = getf d den in
  Q.make (Z.of_int n) (Z.of_int q)
  
(**val set_rational : Q.t -> ([ `rational ], [ `Struct ]) Ctypes.structured**)
let set_rational x =
  let d = make rational in
  (setf d num (Z.to_int(Q.num x));setf d den (Z.to_int(Q.den x));d)
  
(**val rat : Q.t Ctypes.typ**)
let rat = view~read:get_rational~write:set_rational (rational)


    
(**val final_gates : [ `final_gates ] Ctypes.structure Ctypes.typ
val gates : (int, [ `final_gates ] Ctypes.structure) Ctypes.field
   val type1 : (Q.t, [ `final_gates ] Ctypes.structure) Ctypes.field**)
let final_gates : [`final_gates] structure typ = structure "final_gates"
let gates = field final_gates "gates" (int)
let type1 = field final_gates "type1" (rat)
let () = seal final_gates

(**val get_gates :
  ([ `final_gates ], [ `Struct ]) Ctypes.structured ->
   RzQGateSet.RzQGateSet.coq_RzQ_Unitary**)
let get_gates d : coq_RzQ_Unitary = 
  let w =getf d gates in
match w with 
1 -> URzQ_X
|2 -> URzQ_H
|3 -> URzQ_CNOT
|4 -> (URzQ_Rz (getf d type1))
|_-> URzQ_X

let set_gates x =
  let d = make final_gates in 
match x with 
URzQ_X ->(setf d gates 1;d)
|URzQ_H ->(setf d gates 2;d)
|URzQ_CNOT -> (setf d gates 3;d)
|URzQ_Rz y -> (setf d gates 4;setf d type1 y;d)
let coq_RzQ_Unitary2 = view ~read:get_gates~write:set_gates final_gates



(**App1 Tuple**)
let tuples : [`tuples] structure typ = structure "tuples"
let gate = field tuples "gate" (coq_RzQ_Unitary2)
let x = field tuples "x" (int)
let () = seal tuples

(**Connect the App1 Tuple to the App1 Union **)
let get_tuples d = 
let z =getf d gate in
let y = getf d x in
App1 (z,y)
let set_tuples (App1(z,y)) =
let d = make tuples in (setf d gate z; setf d x y;d)
let final_App1 = view ~read:get_tuples~write:set_tuples tuples


(**App2 Tuple**)
let triples : [`triples] structure typ = structure "triples"
let gate1 = field triples "gate1" (coq_RzQ_Unitary2)
let a= field triples "a" (int)
let b= field triples "b" (int)
let () = seal triples


(**App3 Tuple**)
let quad : [`quad] structure typ = structure "quad"
let gate2 = field quad "gate2" (coq_RzQ_Unitary2)
let c= field quad "c" (int)
let f= field quad "f" (int)
let e= field quad "e" (int)
let () = seal quad

(**Connect the App1 Tuple to the App1 Union **)
let get_triples d = 
let first =getf d gate1 in
let second = getf d a in
let third = getf d b in
 App2(first,second,third)


let set_triples (App2(first,second,third)) =
let d = make triples in (setf d gate1 first; setf d a second;setf d b third;d)

let final_App2 = view ~read:get_triples~write:set_triples triples


let get_quad d = 
let first_quad =getf d gate2 in
let second_quad = getf d c in
let third_quad = getf d f in
let fourth_quad = getf d e in

App3(first_quad,second_quad,third_quad,fourth_quad)

let set_quad (App3(first_quad,second_quad,third_quad,fourth_quad)) =

let d = make quad in (setf d gate2 first_quad; setf d c second_quad;setf d f third_quad;setf d e fourth_quad;d)
let final_App3 = view ~read:get_quad~write:set_quad quad

(**Gate Applications**)
let gate_app1 : [`gate_app1] structure typ = structure "gate_app1"
let app1 = field gate_app1 "App1" (final_App1)
let app2 = field gate_app1 "App2" (final_App2)
let app3 = field gate_app1 "App3" (final_App3)
let ans = field gate_app1 "ans" (int)
let () = seal gate_app1



let get1_app d = 
let p = getf d ans in 
match p with 
|1 -> (getf d app1)
|2 -> (getf d app2)
|3 -> (getf d app3)
let set1_app xy =
let d  = make gate_app1 in
match xy with 
|App1(_,_) ->  (setf d app1 xy;d)
|App2(_,_,_) ->  (setf d app2 xy;d)
|App3(_,_,_,_) ->  (setf d app3 xy;d)
let gate_app3 = view ~read:get1_app~write:set1_app gate_app1


type with_quibits
  let with_qubits : [`with_qubits] structure typ = structure "with_qubits"
  let length = field with_qubits "length" int
  let contents = field with_qubits "contents2" (array 1000 gate_app3)
  let qubits = field with_qubits "qubits" int 
  let () = seal with_qubits
  
  type gate_list = {
    length   : int;
    contents1 : RzQGateSet.RzQGateSet.coq_RzQ_Unitary UnitaryListRepresentation.gate_app list; 
    qubits : int
  }

  let of_gate_list_ptr p : gate_list =
   let y = !@p in
    let arr_len = getf y length in
    let num = getf y qubits in 
    let contents_list =
      let arr_start = getf y contents |> CArray.start in
      CArray.from_ptr arr_start arr_len |> CArray.to_list in
    { length = arr_len; contents1 = contents_list; qubits = num}
    
    let to_gate_list_ptr gate_list =
    let size = (sizeof with_qubits + gate_list.length * sizeof gate_app1) in
    let with_qubits =
      allocate_n (abstract ~name:"" ~size ~alignment:1) 1
      |> to_voidp |> from_voidp with_qubits |> (!@) in
    setf with_qubits length gate_list.length;
    setf with_qubits qubits gate_list.qubits;
    List.iteri (CArray.unsafe_set (getf with_qubits contents)) gate_list.contents1;
    addr with_qubits
    let final_with_q = view ~read:of_gate_list_ptr ~write:to_gate_list_ptr (ptr with_qubits)

let optimizer mem = 
let get  = optimize mem.contents1 in 
{length= List.length get;contents1 = get;qubits =mem.qubits}

let not_propagation1 a = 
let get1  = not_propagation a.contents1 in 
{length= List.length get1;contents1 = get1;qubits=a.qubits}


let merge mem = 
let get  = merge_rotations mem.contents1 in 
{length= List.length get;contents1 = get;qubits = mem.qubits}

let single mem=
let get  = cancel_single_qubit_gates mem.contents1 in 
{length= List.length get;contents1 = get;qubits =mem.qubits}
let two mem =
let get  = cancel_two_qubit_gates mem.contents1 in 
{length= List.length get;contents1 = get;qubits=mem.qubits}

 

let hadamard mem =
let get  = hadamard_reduction mem.contents1 in 
{length= List.length get;contents1 = get;qubits=mem.qubits}

let get_gate fname = 
let (sqir, num) = get_gate_list fname in 
{length = List.length sqir;contents1=sqir;qubits = num}

let write_qasm fname (sqir:gate_list) = 

write_qasm_file fname sqir.contents1 sqir.qubits

let voqc fname out =
  let (sqir, q) = get_gate_list fname in
  let af_optim = optimize sqir in
  write_qasm_file out af_optim q
let load fname =
  let (sqir, num) = get_gate_list fname in
  {length = List.length sqir;contents1 = sqir;qubits = num}


module Stubs(I: Cstubs_inverted.INTERNAL) = struct
 let () = I.structure rational
 let () = I.structure final_gates
 let () = I.structure tuples
 let () = I.structure triples
 let () = I.structure quad
 let () = I.structure gate_app1
 let () = I.structure with_qubits
 let () = I.internal "optimizer"(final_with_q @-> returning final_with_q) optimizer
 let () = I.internal "merge_rotations"(final_with_q @-> returning final_with_q) merge
 let () = I.internal "cancel_single_qubit_gates"(final_with_q @-> returning final_with_q)single
 let () = I.internal "cancel_two_qubit_gates"(final_with_q @-> returning final_with_q) two
 let () = I.internal "hadamard"(final_with_q @-> returning final_with_q) hadamard
 let () = I.internal "not_propagation"(final_with_q @-> returning final_with_q) not_propagation1
 let () = I.internal "get_gate_list"(string @-> returning final_with_q) get_gate
 let () = I.internal "write_qasm_file"(string @-> final_with_q @-> returning void) write_qasm
 let () = I.internal "voqc" (string @-> string @-> returning void) voqc
 let () = I.internal "load" (string @-> returning final_with_q) load
end
