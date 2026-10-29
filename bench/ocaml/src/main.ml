(* ocaml ast PARSER FILE...      each file's tree as S-expressions, or REJECT
   ocaml tokens FILE             the number of tokens
   ocaml parse PARSER FILE REPS  parse REPS times (0: lexing only)

   PARSER: menhir (src/ocaml_subset.mly), isabelle (thys/OCaml_Parser.thy),
   or, for ast only, ocaml (OCaml's own parser, converted).  The first two
   read the tokens of src/lex.mll, lexed once, EOF included. *)

let lex file =
  let ic = open_in_bin file in
  let lb = Lexing.from_channel ic in
  let rec go acc = match Lex.token lb with
    | Ocaml_subset.EOF -> Array.of_list (List.rev (Ocaml_subset.EOF :: acc))
    | t -> go (t :: acc) in
  Fun.protect ~finally:(fun () -> close_in ic) (fun () -> go [])

(* Menhir reads the tokens from a lexer function *)
let menhir ts =
  let lb = Lexing.from_string "" in
  fun () ->
    let i = ref 0 in
    Ocaml_subset.implementation (fun _ -> let t = ts.(!i) in incr i; t) lb

let isabelle ts =
  let l = Isa.tokens ts in
  fun () -> Isa.parse l

let parser = function
  | "menhir" -> menhir
  | "isabelle" -> isabelle
  | p -> failwith ("unknown parser " ^ p)

let tree p file =
  try
    Show.structure
      (if p = "ocaml" then Ref.parse_file file else parser p (lex file) ())
  with Ref.Outside what -> "REJECT (outside the subset: " ^ what ^ ")"
     | Lex.Error what -> "REJECT (" ^ what ^ ")"
     | _ -> "REJECT"

let () =
  match Array.to_list Sys.argv |> List.tl with
  | ["tokens"; file] -> print_int (Array.length (lex file)); print_newline ()
  | "ast" :: p :: files -> List.iter (fun file -> print_endline (tree p file)) files
  | ["parse"; p; file; reps] ->
      let run = parser p (lex file) in
      for _ = 1 to int_of_string reps do ignore (Sys.opaque_identity (run ())) done
  | _ ->
      prerr_endline "usage: ocaml ast PARSER FILE... | tokens FILE | parse PARSER FILE REPS";
      exit 2
