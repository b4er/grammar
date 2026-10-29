(* The exported parser's tables, evaluated and printed as an OCaml module:
   see the Makefile. *)

open Vp_open.VeriMon_Parser

let () =
  Printf.printf "let data = %S\n"
    (Marshal.to_string (verimon_parse_ptabs, verimon_parse_i0) [])
