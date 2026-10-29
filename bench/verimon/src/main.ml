(* verimon ast PARSER FILE...      each formula as an S-expression, or REJECT
   verimon tokens FILE             the number of tokens
   verimon parse PARSER FILE REPS  parse REPS times (0: lexing only)

   PARSER: ocamlyacc (MonPoly's own, vendor/formula_parser.mly) or isabelle
   (thys/VeriMon_Parser.thy).  Both read the tokens of MonPoly's lexer, lexed
   once. *)

let lex file =
  let ic = open_in_bin file in
  let lb = Lexing.from_channel ic in
  let rec go acc = match Formula_lexer.token lb with
    | Formula_parser.EOF -> Array.of_list (List.rev acc)
    | t -> go (t :: acc) in
  let ts = go [] in
  close_in ic;
  ts

(* the original reads the tokens from a lexer function, then EOF *)
let ocamlyacc ts =
  let i = ref 0 in
  let next _ =
    if !i < Array.length ts then (let t = ts.(!i) in incr i; t) else Formula_parser.EOF in
  fun () -> i := 0; Formula_parser.formula next (Lexing.from_string "")

let isabelle ts =
  let l = Isa.tokens ts in
  fun () -> Isa.parse l

let parser = function
  | "ocamlyacc" -> ocamlyacc
  | "isabelle" -> isabelle
  | p -> failwith ("unknown parser " ^ p)

let () =
  match Array.to_list Sys.argv |> List.tl with
  | ["tokens"; file] -> print_int (Array.length (lex file)); print_newline ()
  | "ast" :: p :: files ->
      List.iter (fun file ->
          let run = parser p (lex file) in
          print_endline (try Show.formula (run ()) with _ -> "REJECT")) files
  | ["parse"; p; file; reps] ->
      let run = parser p (lex file) in
      for _ = 1 to int_of_string reps do ignore (Sys.opaque_identity (run ())) done
  | _ ->
      prerr_endline "usage: verimon ast PARSER FILE... | tokens FILE | parse PARSER FILE REPS";
      exit 2
