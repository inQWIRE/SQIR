Require Coq.extraction.Extraction.
Require Export List.

(* A few common list functions *)
Extract Inlined Constant length => "List.length".
Extract Inlined Constant app => "List.append".
Extract Inlined Constant rev => "List.rev".
Extract Inlined Constant rev_append => "List.rev_append".
Extract Inlined Constant List.map => "List.map".
Extract Inlined Constant fold_right => "(fun f a l -> List.fold_right f l a)".
Extract Inlined Constant forallb => "List.for_all".
Extract Inlined Constant List.tl => "List.tl".
Extract Inlined Constant List.hd_error => "(fun l -> List.nth_opt l 0)".