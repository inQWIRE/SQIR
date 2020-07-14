module StringMap :   
  sig
    type key = String.t
    type 'a t = 'a Stdlib__map.Make(String).t
    val empty : 'a t
    val is_empty : 'a t -> bool
    val mem : key -> 'a t -> bool
    val add : key -> 'a -> 'a t -> 'a t
    val update : key -> ('a option -> 'a option) -> 'a t -> 'a t
    val singleton : key -> 'a -> 'a t
    val remove : key -> 'a t -> 'a t
    val merge :
      (key -> 'a option -> 'b option -> 'c option) -> 'a t -> 'b t -> 'c t
    val union : (key -> 'a -> 'a -> 'a option) -> 'a t -> 'a t -> 'a t
    val compare : ('a -> 'a -> int) -> 'a t -> 'a t -> int
    val equal : ('a -> 'a -> bool) -> 'a t -> 'a t -> bool
    val iter : (key -> 'a -> unit) -> 'a t -> unit
    val fold : (key -> 'a -> 'b -> 'b) -> 'a t -> 'b -> 'b
    val for_all : (key -> 'a -> bool) -> 'a t -> bool
    val exists : (key -> 'a -> bool) -> 'a t -> bool
    val filter : (key -> 'a -> bool) -> 'a t -> 'a t
    val partition : (key -> 'a -> bool) -> 'a t -> 'a t * 'a t
    val cardinal : 'a t -> int
    val bindings : 'a t -> (key * 'a) list
    val min_binding : 'a t -> key * 'a
    val min_binding_opt : 'a t -> (key * 'a) option
    val max_binding : 'a t -> key * 'a
    val max_binding_opt : 'a t -> (key * 'a) option
    val choose : 'a t -> key * 'a
    val choose_opt : 'a t -> (key * 'a) option
    val split : key -> 'a t -> 'a t * 'a option * 'a t
    val find : key -> 'a t -> 'a
    val find_opt : key -> 'a t -> 'a option
    val find_first : (key -> bool) -> 'a t -> key * 'a
    val find_first_opt : (key -> bool) -> 'a t -> (key * 'a) option
    val find_last : (key -> bool) -> 'a t -> key * 'a
    val find_last_opt : (key -> bool) -> 'a t -> (key * 'a) option
    val map : ('a -> 'b) -> 'a t -> 'b t
    val mapi : (key -> 'a -> 'b) -> 'a t -> 'b t
    val to_seq : 'a t -> (key * 'a) Seq.t
    val to_seq_from : key -> 'a t -> (key * 'a) Seq.t
    val add_seq : (key * 'a) Seq.t -> 'a t -> 'a t
    val of_seq : (key * 'a) Seq.t -> 'a t
  end
val qelib1 : (string * OpenQASM.AST.ty) list
val check_stmt :
  OpenQASM.AST.ty StringMap.t ->
  OpenQASM.AST.statement -> OpenQASM.AST.ty StringMap.t
val check : OpenQASM.AST.statement list -> OpenQASM.AST.ty StringMap.t
module QbitIdx :
  sig type t = string * int val compare : 'a * 'b -> 'a * 'b -> int end
module QbitMap :
  sig
    type key = QbitIdx.t
    type 'a t = 'a Stdlib__map.Make(QbitIdx).t
    val empty : 'a t
    val is_empty : 'a t -> bool
    val mem : key -> 'a t -> bool
    val add : key -> 'a -> 'a t -> 'a t
    val update : key -> ('a option -> 'a option) -> 'a t -> 'a t
    val singleton : key -> 'a -> 'a t
    val remove : key -> 'a t -> 'a t
    val merge :
      (key -> 'a option -> 'b option -> 'c option) -> 'a t -> 'b t -> 'c t
    val union : (key -> 'a -> 'a -> 'a option) -> 'a t -> 'a t -> 'a t
    val compare : ('a -> 'a -> int) -> 'a t -> 'a t -> int
    val equal : ('a -> 'a -> bool) -> 'a t -> 'a t -> bool
    val iter : (key -> 'a -> unit) -> 'a t -> unit
    val fold : (key -> 'a -> 'b -> 'b) -> 'a t -> 'b -> 'b
    val for_all : (key -> 'a -> bool) -> 'a t -> bool
    val exists : (key -> 'a -> bool) -> 'a t -> bool
    val filter : (key -> 'a -> bool) -> 'a t -> 'a t
    val partition : (key -> 'a -> bool) -> 'a t -> 'a t * 'a t
    val cardinal : 'a t -> int
    val bindings : 'a t -> (key * 'a) list
    val min_binding : 'a t -> key * 'a
    val min_binding_opt : 'a t -> (key * 'a) option
    val max_binding : 'a t -> key * 'a
    val max_binding_opt : 'a t -> (key * 'a) option
    val choose : 'a t -> key * 'a
    val choose_opt : 'a t -> (key * 'a) option
    val split : key -> 'a t -> 'a t * 'a option * 'a t
    val find : key -> 'a t -> 'a
    val find_opt : key -> 'a t -> 'a option
    val find_first : (key -> bool) -> 'a t -> key * 'a
    val find_first_opt : (key -> bool) -> 'a t -> (key * 'a) option
    val find_last : (key -> bool) -> 'a t -> key * 'a
    val find_last_opt : (key -> bool) -> 'a t -> (key * 'a) option
    val map : ('a -> 'b) -> 'a t -> 'b t
    val mapi : (key -> 'a -> 'b) -> 'a t -> 'b t
    val to_seq : 'a t -> (key * 'a) Seq.t
    val to_seq_from : key -> 'a t -> (key * 'a) Seq.t
    val add_seq : (key * 'a) Seq.t -> 'a t -> 'a t
    val of_seq : (key * 'a) Seq.t -> 'a t
  end
val apply_c_gate :
  ('a -> 'a -> 'b) ->
  StringMap.key * int option ->
  StringMap.key * int option ->
  'a QbitMap.t -> OpenQASM.AST.ty StringMap.t -> 'b list
val apply_double_c_gate :
  ('a -> 'a -> 'a -> 'b) ->
  string * int option ->
  string * int option -> string * int option -> 'a QbitMap.t -> 'c -> 'b
val apply_gate :
  ('a -> 'b) ->
  StringMap.key * int option ->
  'a QbitMap.t -> OpenQASM.AST.ty StringMap.t -> 'b list
val translate_statement :
  OpenQASM.AST.statement ->
  int QbitMap.t ->
  OpenQASM.AST.ty StringMap.t ->
  RzQGateSet.RzQGateSet.coq_RzQ_Unitary UnitaryListRepresentation.gate_app
  list
val parse_decl : OpenQASM.AST.statement -> (string * int) list
val parse_qreg_decls' :
  OpenQASM.AST.statement list -> (string * int) list -> (string * int) list
val parse_qreg_decls : OpenQASM.AST.statement list -> (string * int) list
val translate_program' :
  OpenQASM.AST.statement list ->
  int QbitMap.t ->
  OpenQASM.AST.ty StringMap.t ->
  RzQGateSet.RzQGateSet.coq_RzQ_Unitary UnitaryListRepresentation.gate_app
  list ->
  RzQGateSet.RzQGateSet.coq_RzQ_Unitary UnitaryListRepresentation.gate_app
  list
val translate_program :
  OpenQASM.AST.statement list ->
  int QbitMap.t ->
  OpenQASM.AST.ty StringMap.t ->
  RzQGateSet.RzQGateSet.coq_RzQ_Unitary UnitaryListRepresentation.gate_app
  list
val get_gate_list :
  string ->
  RzQGateSet.RzQGateSet.coq_RzQ_Unitary UnitaryListRepresentation.gate_app
  list * int
val sqir_to_qasm_gate :
  out_channel ->
  RzQGateSet.RzQGateSet.coq_RzQ_Unitary UnitaryListRepresentation.gate_app ->
  unit
val write_qasm_file :
  string ->
  RzQGateSet.RzQGateSet.coq_RzQ_Unitary UnitaryListRepresentation.gate_app
  list -> int -> unit
