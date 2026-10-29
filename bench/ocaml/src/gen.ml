let items = ref 1000
let depth = ref 5
let seed = ref 42

let args =
  [ ("-n", Arg.Set_int items, "N top-level items (default 1000)");
    ("-d", Arg.Set_int depth, "D nesting depth (default 5)");
    ("-seed", Arg.Set_int seed, "S random seed (default 42)") ]

let b = Buffer.create (1 lsl 20)
let s x = Buffer.add_string b x
let pick a = a.(Random.int (Array.length a))
let chance n = Random.int n = 0
let times lo hi f = for i = 1 to lo + Random.int (hi - lo + 1) do f i done
let sep_list lo hi sep f = times lo hi (fun i -> if i > 1 then s sep; f ())

let lidents = [| "x"; "y"; "f"; "g"; "acc"; "loop"; "n"; "xs"; "k_1"; "fold'"; "go"; "aux"; "env"; "t" |]
let paths = [| "List.map"; "List.fold_left"; "String.length"; "Printf.sprintf"; "Hashtbl.find";
               "List.rev"; "Option.map"; "M.N.v" |]
let ctors = [| "None"; "Some"; "Leaf"; "Node"; "Ok"; "Error"; "A"; "B"; "Stdlib.Exit" |]
let constants = [| "None"; "Leaf"; "A"; "Stdlib.Exit"; "true"; "false"; "()"; "[]" |]
let labels = [| "name"; "next"; "size"; "data"; "left"; "right" |]
let tnames = [| "int"; "string"; "bool"; "t"; "tree"; "M.t" |]

let ident () = s (pick lidents)
let paren f = s "("; f (); s ")"

let constant () =
  match Random.int 6 with
  | 0 | 1 -> s (string_of_int (Random.int 1000))
  | 2 -> s (pick [| "1.5"; "0.25"; "1e3"; "2."; "0x1F"; "1_000" |])
  | 3 -> s (pick [| "\"str\""; "\"a\\nb\""; "\"q\\\"\""; "\"\"" |])
  | 4 -> s (pick [| "'a'"; "'\\n'"; "'\\''"; "'\\065'" |])
  | _ -> s "\"%d: %s\""

(* types *)

let rec core_type d =
  if d > 0 && chance 4 then (tuple_type (d - 1); s " -> "; core_type (d - 1)) else tuple_type d

and tuple_type d =
  if d > 0 && chance 4 then sep_list 2 3 " * " (fun () -> app_type (d - 1)) else app_type d

and app_type d =
  match if d <= 0 then 0 else Random.int 6 with
  | 0 | 1 | 2 -> atomic_type d
  | 3 -> app_type (d - 1); s " "; s (pick [| "list"; "option"; "M.t" |])
  | 4 -> s "("; sep_list 2 2 ", " (fun () -> core_type (d - 1)); s ") Hashtbl.t"
  | _ -> paren (fun () -> core_type (d - 1))

and atomic_type _ =
  if chance 3 then s (pick [| "'a"; "'b"; "'key" |]) else s (pick tnames)

(* patterns *)

let rec pattern d =
  match if d <= 0 then 9 else Random.int 12 with
  | 0 -> pattern_or (d - 1); s " as "; ident ()
  | _ -> pattern_or d

and pattern_or d =
  if d > 0 && chance 6 then (pattern_or (d - 1); s " | "; pattern_tuple (d - 1))
  else pattern_tuple d

and pattern_tuple d =
  if d > 0 && chance 5 then sep_list 2 3 ", " (fun () -> pattern_cons (d - 1))
  else pattern_cons d

and pattern_cons d =
  if d > 0 && chance 5 then (pattern_app (d - 1); s " :: "; pattern_cons (d - 1))
  else pattern_app d

and pattern_app d =
  if d > 0 && chance 4 then (s (pick [| "Some"; "Node"; "Ok"; "B" |]); s " "; simple_pattern (d - 1))
  else simple_pattern d

and simple_pattern d =
  match if d <= 0 then Random.int 6 else Random.int 13 with
  | 0 | 1 | 2 -> ident ()
  | 3 -> s "_"
  | 4 -> s (pick [| "None"; "Leaf"; "A"; "true"; "false"; "()"; "[]" |])
  | 5 -> s (string_of_int (Random.int 100))
  | 6 -> s (pick [| "'a'"; "\"s\"" |])
  | 7 | 8 -> paren (fun () -> pattern (d - 1))
  | 9 -> paren (fun () -> pattern (d - 1); s " : "; core_type (d - 1))
  | 10 -> s "["; sep_list 1 3 "; " (fun () -> pattern (d - 1)); s "]"
  | _ ->
      s "{ "; sep_list 1 3 "; " (fun () ->
          s (pick labels); if Random.bool () then (s " = "; pattern (d - 1)));
      if Random.bool () then s "; _"; s " }"

let simple_pattern_not_ident d =
  match Random.int 4 with
  | 0 -> s "()"
  | 1 -> s "_"
  | 2 -> paren (fun () -> sep_list 2 3 ", " (fun () -> pattern_cons d))
  | _ -> s "{ "; sep_list 1 2 "; " (fun () -> s (pick labels)); s " }"

(* expressions: closed: the sequence may not end in a match, function or
   try; matched: every if has an else *)

let rec seq_expr ~closed d =
  if d <= 0 then expr ~matched:false d
  else
    match Random.int (if closed then 9 else 13) with
    | 0 | 1 -> expr ~matched:false (d - 1); s ";\n  "; seq_expr ~closed (d - 1)
    | 2 | 3 -> let_bindings (d - 1); s " in\n  "; seq_expr ~closed (d - 1)
    | 4 -> s "fun "; params 1 3 (d - 1); s " -> "; seq_expr ~closed (d - 1)
    | 9 | 10 -> s "match "; seq_expr ~closed:false (d - 1); s " with"; cases (d - 1)
    | 11 -> s "function"; cases (d - 1)
    | 12 -> s "try "; seq_expr ~closed:false (d - 1); s " with"; cases (d - 1)
    | _ -> expr ~matched:false d

and cases d =
  let n = 1 + Random.int 4 in
  for i = 1 to n do
    s "\n  | "; pattern (d - 1);
    if chance 6 then (s " when "; expr ~matched:false (d - 1));
    s " -> "; seq_expr ~closed:(i < n) (d - 1)
  done

and let_bindings d =
  s "let "; if chance 4 then s "rec ";
  sep_list 1 2 "\nand " (fun () -> let_binding d)

and let_binding d =
  (match Random.int 8 with
   | 0 -> simple_pattern_not_ident (d - 1)
   | 1 -> ident (); params 0 2 (d - 1); s " : "; core_type (d - 1)
   | _ -> ident (); params 0 3 (d - 1));
  s " = "; seq_expr ~closed:false d

and params lo hi d = times lo hi (fun _ -> s " "; simple_pattern (d - 1))

and expr ~matched d =
  if d > 0 && chance 7 then begin
    s "if "; seq_expr ~closed:false (d - 1); s " then ";
    if matched || Random.bool () then begin
      expr ~matched:true (d - 1); s " else "; expr ~matched (d - 1)
    end else expr ~matched:false (d - 1)
  end
  else assign_expr d

and assign_expr d =
  match if d <= 0 then 2 else Random.int 16 with
  | 0 -> simple_expr_nc ~dot:true (d - 1); s "."; s (pick labels); s " <- "; assign_expr (d - 1)
  | 1 -> tuple_expr (d - 1); s " := "; assign_expr (d - 1)
  | _ -> tuple_expr d

and tuple_expr d =
  if d > 0 && chance 6 then sep_list 2 3 ", " (fun () -> or_expr (d - 1)) else or_expr d

(* a binary level: an operand of the next level (sub), or a chain *)
and binop ~left sub same ops d =
  if d > 0 && chance 4 then begin
    if left then (same (d - 1); s " "; s (pick ops); s " "; sub (d - 1))
    else (sub (d - 1); s " "; s (pick ops); s " "; same (d - 1))
  end
  else sub d

and or_expr d = binop ~left:false and_expr or_expr [| "||" |] d
and and_expr d = binop ~left:false cmp_expr and_expr [| "&&" |] d
and cmp_expr d = binop ~left:true concat_expr cmp_expr [| "="; "<"; ">"; "<>"; "=="; "<="; "|>"; "!=" |] d
and concat_expr d = binop ~left:false cons_expr concat_expr [| "@"; "^"; "@@" |] d
and cons_expr d = binop ~left:false add_expr cons_expr [| "::" |] d
and add_expr d = binop ~left:true mul_expr add_expr [| "+"; "-"; "+."; "-."; "++" |] d
and mul_expr d = binop ~left:true unary_expr mul_expr [| "*"; "/"; "mod"; "*."; "land"; "%" |] d

(* OCaml's parser folds a minus into a constant: - - 1 is the constant 1, and
   the reference cannot tell that from 1, so only names are negated *)
and unary_expr d =
  if d > 0 && chance 12 then begin
    s "- "; ident (); if Random.bool () then (s " "; simple_expr (d - 1))
  end
  else app_expr d

and app_expr d =
  match if d <= 0 then 0 else Random.int 6 with
  | 0 | 1 | 2 -> simple_expr d
  | 3 | 4 -> simple_expr_nc d; times 1 3 (fun _ -> s " "; simple_expr (d - 1))
  | _ -> s (pick ctors); s " "; simple_expr (d - 1)

and simple_expr d =
  if chance 6 then s (pick constants) else simple_expr_nc d

(* dot: followed by a field's dot, so not a number (747.data is not OCaml) *)
and simple_expr_nc ?(dot = false) d =
  if d > 0 && chance 8 then (simple_expr_nc ~dot:true (d - 1); s "."; s (pick labels))
  else atom ~dot d

and atom ?(dot = false) d =
  match if d <= 0 then Random.int 5 else Random.int 17 with
  | 0 | 1 -> ident ()
  | 2 -> s (pick paths)
  | 3 -> if dot then ident () else constant ()
  | 4 -> paren (fun () -> s (pick constants))
  | 5 | 6 | 7 -> paren (fun () -> seq_expr ~closed:false (d - 1))
  | 8 -> paren (fun () -> seq_expr ~closed:false (d - 1); s " : "; core_type (d - 1))
  | 9 -> s "begin "; seq_expr ~closed:false (d - 1); s " end"
  | 10 | 11 -> s "["; sep_list 1 3 "; " (fun () -> expr ~matched:false (d - 1));
                if chance 4 then s ";"; s "]"
  | 12 -> s "{ "; record_fields (d - 1); s " }"
  | 13 -> s "{ "; simple_expr (d - 1); s " with "; record_fields (d - 1); s " }"
  | 14 -> s "! "; atom ~dot (d - 1)
  | _ -> ident ()

and record_fields d =
  sep_list 1 3 "; " (fun () ->
      s (pick labels); if not (chance 4) then (s " = "; expr ~matched:false d));
  if chance 4 then s ";"

(* structure items *)

let type_decl d =
  (match Random.int 4 with
   | 0 -> ()
   | 1 -> s "'a "
   | 2 -> s "('a, 'b) "
   | _ -> s "'key ");
  s (pick [| "t"; "tree"; "state"; "token"; "env" |]);
  match Random.int 6 with
  | 0 -> ()
  | 1 -> s " = "; core_type d
  | 2 | 3 ->
      s " ="; if Random.bool () then s "\n  |";
      sep_list 1 5 "\n  |" (fun () ->
          s " "; s (pick [| "A"; "B"; "Leaf"; "Node"; "Int"; "Var"; "App" |]);
          if Random.bool () then (s " of "; sep_list 1 3 " * " (fun () -> app_type (d - 1))))
  | _ ->
      s " = {\n  "; sep_list 1 4 ";\n  " (fun () ->
          if chance 3 then s "mutable "; s (pick labels); s " : "; core_type (d - 1));
      if Random.bool () then s ";"; s "\n}"

let item () =
  match Random.int 12 with
  | 0 -> s "type "; sep_list 1 2 "\nand " (fun () -> type_decl 3)
  | 1 when chance 4 -> s "open "; s (pick [| "List"; "Printf"; "M.N" |])
  | _ -> let_bindings !depth

let () =
  Arg.parse (Arg.align args) (fun _ -> ()) "gen [-n ITEMS] [-d DEPTH] [-seed S]";
  Random.init !seed;
  for _ = 1 to !items do item (); s "\n\n" done;
  print_string (Buffer.contents b)
