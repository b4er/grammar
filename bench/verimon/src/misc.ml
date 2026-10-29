(* The part of MonPoly's Misc the vendored lexer and parser use: debugging is
   off. *)

type dbg = Dbg_all | Dbg_eval | Dbg_monitorable | Dbg_formula | Dbg_perf | Dbg_filter

let debugging (_ : dbg) = false

let union l1 l2 = List.fold_left (fun l x -> if List.mem x l then l else x :: l) l2 l1
