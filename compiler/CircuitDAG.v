

(** General definitions **)
(* Idea: we want a graph with a node corresponding to each operation in
   a program. Incoming edges correspond to inputs to the operation, and
   outgoing edges correspond to outputs of the operation. Because we are
   dealing with quantum circuits, we require (at least?) the following:
   - The graph contains no cycles.
   - For every node, the set of incoming edges is the same as the set of 
     outgoing edges.
   - A node can never have two of the same incoming/outgoing edges (no cloning).
   - The number of incoming/outgoing edges must be consistent with the type
     of the node (e.g. 1-qubit vs. 2-qubit gate).
   
   We will want to define (at least) the following operations:
   - Traverse the circuit
   - Insert a node/sub-circuit
   - Remove a node/sub-circuit
   - Check whether a graph is a valid circuit
   - Check (sytactic) equality of two circuits -> graph isomorphism
   - Get the width of the circuit 
   - Get the depth of the circuit (longest path)
*)

(** Convert SQIRE program to circuit **)

(** Convert circuit to SQIRE program. **)
(* This will likely require checking validity of the circuit,
   and then printing out a lexicographic topological ordering
   of the nodes in the graph. *)


