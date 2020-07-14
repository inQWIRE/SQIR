type __ = Obj.t      
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
module FMap :
  sig
    type key = OrderedTypeEx.Nat_as_OT.t
    type 'a t = 'a Stdlib__map.Make(OrderedTypeEx.Nat_as_OT).t
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
    val find : key -> 'a t -> 'a option
  end
val xor : FSet.t -> FSet.t -> FSet.t
val get_set : FSet.t FMap.t -> FMap.key -> FSet.t
val find_merge' :
  RzQGateSet.RzQGateSet.coq_RzQ_Unitary UnitaryListRepresentation.gate_app
  list ->
  FSet.t ->
  FSet.t ->
  FSet.elt ->
  FSet.t FMap.t ->
  int ->
  RzQGateSet.RzQGateSet.coq_RzQ_Unitary UnitaryListRepresentation.gate_app
  list ->
  (((RzQGateSet.RzQGateSet.coq_RzQ_Unitary UnitaryListRepresentation.gate_app
     list * Q.t) *
    int) *
   RzQGateSet.RzQGateSet.coq_RzQ_Unitary UnitaryListRepresentation.gate_app
   list)
  option
val find_merge :
  RzQGateSet.RzQGateSet.coq_RzQ_Unitary UnitaryListRepresentation.gate_app
  list ->
  FSet.elt ->
  (((RzQGateSet.RzQGateSet.coq_RzQ_Unitary UnitaryListRepresentation.gate_app
     list * Q.t) *
    int) *
   RzQGateSet.RzQGateSet.coq_RzQ_Unitary UnitaryListRepresentation.gate_app
   list)
  option
val merge_at_beginning :
  RzQGateSet.RzQGateSet.coq_RzQ_Unitary UnitaryListRepresentation.gate_app
  list ->
  Q.t ->
  FSet.elt ->
  RzQGateSet.RzQGateSet.coq_RzQ_Unitary UnitaryListRepresentation.gate_app
  list option
val merge_at_end :
  RzQGateSet.RzQGateSet.coq_RzQ_Unitary UnitaryListRepresentation.gate_app
  list ->
  Q.t ->
  FSet.elt ->
  RzQGateSet.RzQGateSet.coq_RzQ_Unitary UnitaryListRepresentation.gate_app
  list option
val merge_rotations_at_beginning :
  RzQGateSet.RzQGateSet.coq_RzQ_Unitary UnitaryListRepresentation.gate_app
  list ->
  int ->
  RzQGateSet.RzQGateSet.coq_RzQ_Unitary UnitaryListRepresentation.gate_app
  list ->
  RzQGateSet.RzQGateSet.coq_RzQ_Unitary UnitaryListRepresentation.gate_app
  list
val merge_rotations_at_end :
  RzQGateSet.RzQGateSet.coq_RzQ_Unitary UnitaryListRepresentation.gate_app
  list ->
  int ->
  RzQGateSet.RzQGateSet.coq_RzQ_Unitary UnitaryListRepresentation.gate_app
  list ->
  RzQGateSet.RzQGateSet.coq_RzQ_Unitary UnitaryListRepresentation.gate_app
  list
val invert_gate :
  RzQGateSet.RzQGateSet.coq_RzQ_Unitary UnitaryListRepresentation.gate_app ->
  RzQGateSet.RzQGateSet.coq_RzQ_Unitary UnitaryListRepresentation.gate_app
val rev_append_w_map : ('a -> 'b) -> 'a list -> 'b list -> 'b list
val invert :
  RzQGateSet.RzQGateSet.coq_RzQ_Unitary UnitaryListRepresentation.gate_app
  list ->
  RzQGateSet.RzQGateSet.coq_RzQ_Unitary UnitaryListRepresentation.gate_app
  list
val merge_rotations :
  RzQGateSet.RzQGateSet.coq_RzQ_Unitary UnitaryListRepresentation.gate_app
  list ->
  RzQGateSet.RzQGateSet.coq_RzQ_Unitary UnitaryListRepresentation.gate_app
  list
