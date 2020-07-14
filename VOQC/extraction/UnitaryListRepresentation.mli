module FSet :        
  sig
    type elt = OrderedTypeEx.Nat_as_OT.t
    type t = Stdlib__set.Make(OrderedTypeEx.Nat_as_OT).t
    val empty : t
    val is_empty : t -> bool
    val mem : elt -> t -> bool
    val add : elt -> t -> t
    val singleton : elt -> t
    val remove : elt -> t -> t
    val union : t -> t -> t
    val inter : t -> t -> t
    val disjoint : t -> t -> bool
    val diff : t -> t -> t
    val compare : t -> t -> int
    val equal : t -> t -> bool
    val subset : t -> t -> bool
    val iter : (elt -> unit) -> t -> unit
    val map : (elt -> elt) -> t -> t
    val fold : (elt -> 'a -> 'a) -> t -> 'a -> 'a
    val for_all : (elt -> bool) -> t -> bool
    val exists : (elt -> bool) -> t -> bool
    val filter : (elt -> bool) -> t -> t
    val partition : (elt -> bool) -> t -> t * t
    val cardinal : t -> int
    val elements : t -> elt list
    val min_elt : t -> elt
    val min_elt_opt : t -> elt option
    val max_elt : t -> elt
    val max_elt_opt : t -> elt option
    val choose : t -> elt
    val choose_opt : t -> elt option
    val split : elt -> t -> t * bool * t
    val find : elt -> t -> elt
    val find_opt : elt -> t -> elt option
    val find_first : (elt -> bool) -> t -> elt
    val find_first_opt : (elt -> bool) -> t -> elt option
    val find_last : (elt -> bool) -> t -> elt
    val find_last_opt : (elt -> bool) -> t -> elt option
    val of_list : elt list -> t
    val to_seq_from : elt -> t -> elt Seq.t
    val to_seq : t -> elt Seq.t
    val add_seq : elt Seq.t -> t -> t
    val of_seq : elt Seq.t -> t
  end
type 'u gate_app =
    App1 of 'u * int
  | App2 of 'u * int * int
  | App3 of 'u * int * int * int
type 'u gate_list = 'u gate_app list
val next_single_qubit_gate' :
  'a gate_app list ->
  int ->
  'a gate_app list -> (('a gate_app list * 'a) * 'a gate_app list) option
val next_single_qubit_gate :
  'a gate_app list ->
  int -> (('a gate_app list * 'a) * 'a gate_app list) option
val last_single_qubit_gate :
  'a gate_app list ->
  int -> (('a gate_app list * 'a) * 'a gate_app list) option
val next_two_qubit_gate' :
  'a gate_app list ->
  int ->
  'a gate_app list ->
  (((('a gate_app list * 'a) * int) * int) * 'a gate_app list) option
val next_two_qubit_gate :
  'a gate_app list ->
  int -> (((('a gate_app list * 'a) * int) * int) * 'a gate_app list) option
val next_gate' :
  'a gate_app list ->
  (int -> bool) ->
  'a gate_app list ->
  (('a gate_app list * 'a gate_app) * 'a gate_app list) option
val next_gate :
  'a gate_app list ->
  (int -> bool) ->
  (('a gate_app list * 'a gate_app) * 'a gate_app list) option
val does_not_reference_appl : int -> 'a gate_app -> bool
val does_not_reference : 'a gate_app list -> int -> bool
val try_rewrites : 'a -> ('a -> 'b option) list -> 'b option
val try_rewrites2 : 'a -> ('a -> 'b option) list -> 'b option
val propagate' :
  'a ->
  ('a -> ('b list * 'a) option) list ->
  ('a -> 'b list option) list -> int -> 'b list -> 'b list option
val propagate :
  'a ->
  ('a -> ('b list * 'a) option) list ->
  ('a -> 'b list option) list -> int -> 'b list option
val remove_prefix :
  'a gate_app list ->
  'b gate_app list -> (int -> 'b -> 'a -> bool) -> 'a gate_app list option
val remove_suffix :
  'a gate_app list ->
  'b gate_app list -> (int -> 'b -> 'a -> bool) -> 'a gate_app list option
val replace_pattern :
  'a gate_app list ->
  'b gate_app list ->
  'a gate_app list -> (int -> 'b -> 'a -> bool) -> 'a gate_app list option
val get_matching_prefix' :
  'a gate_app list ->
  'b gate_app list ->
  'a gate_app list ->
  'a gate_app list ->
  FSet.t ->
  int ->
  (int -> 'a -> 'b -> bool) ->
  ('a gate_app list * 'a gate_app list) * 'b gate_app list
val get_matching_prefix :
  'a gate_app list ->
  'b gate_app list ->
  (int -> 'a -> 'b -> bool) ->
  ('a gate_app list * 'a gate_app list) * 'b gate_app list
val coq_LCR :
  'a gate_app list ->
  ('a gate_app list -> 'a gate_app list) ->
  (int -> 'a -> 'a -> bool) ->
  (('a gate_app list * 'a gate_app list) * 'a gate_app list) option
