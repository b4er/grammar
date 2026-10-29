(* JSON values: construction, queries, and printing (compact and indented)
   with string escaping. *)

type json =
  | Null
  | Bool of bool
  | Number of float
  | String of string
  | Array of json list
  | Object of (string * json) list

type printer = { buf : Buffer.t; mutable indent : int; pretty : bool }

let hex = "0123456789abcdef"

let escape_char b c =
  match c with
  | '"' -> Buffer.add_string b "\\\""
  | '\\' -> Buffer.add_string b "\\\\"
  | '\n' -> Buffer.add_string b "\\n"
  | '\t' -> Buffer.add_string b "\\t"
  | '\r' -> Buffer.add_string b "\\r"
  | c when Char.code c < 32 ->
      let n = Char.code c in
      Buffer.add_string b "\\u00";
      Buffer.add_char b (String.get hex (n / 16));
      Buffer.add_char b (String.get hex (n mod 16))
  | c -> Buffer.add_char b c

let add_string b s =
  Buffer.add_char b '"';
  String.iter (escape_char b) s;
  Buffer.add_char b '"'

let number x =
  if Float.is_integer x && Float.abs x < 1e15 then string_of_int (int_of_float x)
  else Printf.sprintf "%.17g" x

let newline p =
  if p.pretty then begin
    Buffer.add_char p.buf '\n';
    Buffer.add_string p.buf (String.make (2 * p.indent) ' ')
  end

let rec print p v =
  match v with
  | Null -> Buffer.add_string p.buf "null"
  | Bool true -> Buffer.add_string p.buf "true"
  | Bool false -> Buffer.add_string p.buf "false"
  | Number x -> Buffer.add_string p.buf (number x)
  | String s -> add_string p.buf s
  | Array [] -> Buffer.add_string p.buf "[]"
  | Object [] -> Buffer.add_string p.buf "{}"
  | Array vs -> seq p '[' ']' (fun v -> print p v) vs
  | Object fs ->
      seq p '{' '}' (fun (k, v) ->
          add_string p.buf k;
          Buffer.add_string p.buf (if p.pretty then ": " else ":");
          print p v) fs

and seq p op cl f xs =
  Buffer.add_char p.buf op;
  p.indent <- p.indent + 1;
  List.iteri (fun i x ->
      if i > 0 then Buffer.add_char p.buf ',';
      newline p;
      f x) xs;
  p.indent <- p.indent - 1;
  newline p;
  Buffer.add_char p.buf cl

let render pretty v =
  let p = { buf = Buffer.create 256; indent = 0; pretty = pretty } in
  print p v;
  Buffer.contents p.buf

let member k = function
  | Object fs -> (try Some (List.assoc k fs) with Not_found -> None)
  | _ -> None

let rec path ks v =
  match ks with
  | [] -> Some v
  | k :: ks ->
      match member k v with
      | Some v -> path ks v
      | None -> None

let to_list = function Array vs -> vs | Null -> [] | v -> [v]

let rec map_numbers f = function
  | Number x -> Number (f x)
  | Array vs -> Array (List.map (map_numbers f) vs)
  | Object fs -> Object (List.map (fun (k, v) -> k, map_numbers f v) fs)
  | v -> v

let rec size = function
  | Null | Bool _ | Number _ | String _ -> 1
  | Array vs -> List.fold_left (fun n v -> n + size v) 1 vs
  | Object fs -> List.fold_left (fun n (_, v) -> n + size v) 1 fs

let person name age langs =
  Object [
    "name", String name;
    "age", Number (float_of_int age);
    "languages", Array (List.map (fun l -> String l) langs);
    "admin", Bool (age > 40);
  ]

let doc =
  Object [
    "version", Number 2.;
    "people", Array [
      person "Ada" 36 ["Analytical Engine"];
      person "Grace" 45 ["COBOL"; "FLOW-MATIC"];
      person "Robin" 52 ["ML"; "LCF"];
    ];
    "notes", String "tab:\there, quote: \", newline:\n";
    "missing", Null;
  ]

let () =
  print_endline (render false doc);
  print_endline (render true (map_numbers (fun x -> x *. 2.) doc));
  Printf.printf "%d nodes\n" (size doc);
  match path ["people"] doc with
  | Some people ->
      List.iter (fun p ->
          match member "name" p, member "age" p with
          | Some (String n), Some (Number a) -> Printf.printf "%s is %g\n" n a
          | _ -> ()) (to_list people)
  | None -> print_endline "no people"
