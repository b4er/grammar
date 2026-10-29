(* A small language: a lexer and a recursive-descent parser over strings,
   an environment-passing evaluator with closures, and a printer. *)

type token =
  | TInt of int
  | TIdent of string
  | TSym of string
  | TLet | TIn | TFun | TIf | TThen | TElse | TEnd

type expr =
  | Int of int
  | Var of string
  | Bin of string * expr * expr
  | Let of string * expr * expr
  | Fun of string * expr
  | App of expr * expr
  | If of expr * expr * expr

type value =
  | VInt of int
  | VClosure of string * expr * env

and env = (string * value) list

let is_digit c = c >= '0' && c <= '9'
let is_alpha c = (c >= 'a' && c <= 'z') || (c >= 'A' && c <= 'Z') || c = '_'
let is_space c = c = ' ' || c = '\n' || c = '\t'

let keyword = function
  | "let" -> TLet
  | "in" -> TIn
  | "fun" -> TFun
  | "if" -> TIf
  | "then" -> TThen
  | "else" -> TElse
  | "end" -> TEnd
  | s -> TIdent s

let tokenize s =
  let n = String.length s in
  let rec scan i acc =
    if i >= n then List.rev acc
    else
      let c = String.get s i in
      if is_space c then scan (i + 1) acc
      else if is_digit c then begin
        let j = ref i in
        let v = ref 0 in
        let rec digits () =
          if !j < n && is_digit (String.get s !j) then begin
            v := !v * 10 + (Char.code (String.get s !j) - Char.code '0');
            j := !j + 1;
            digits ()
          end
        in
        digits ();
        scan !j (TInt !v :: acc)
      end
      else if is_alpha c then begin
        let rec stop j = if j < n && (is_alpha (String.get s j) || is_digit (String.get s j)) then stop (j + 1) else j in
        let j = stop i in
        scan j (keyword (String.sub s i (j - i)) :: acc)
      end
      else
        match c, (if i + 1 < n then String.get s (i + 1) else ' ') with
        | '-', '>' -> scan (i + 2) (TSym "->" :: acc)
        | '<', '=' -> scan (i + 2) (TSym "<=" :: acc)
        | _ -> scan (i + 1) (TSym (String.make 1 c) :: acc)
  in
  scan 0 []

let expect sym = function
  | TSym s :: rest when s = sym -> rest
  | _ -> failwith ("expected " ^ sym)

let rec parse_expr toks =
  match toks with
  | TLet :: TIdent x :: TSym "=" :: rest ->
      let e1, rest = parse_expr rest in
      (match rest with
       | TIn :: rest -> let e2, rest = parse_expr rest in Let (x, e1, e2), rest
       | _ -> failwith "expected in")
  | TFun :: TIdent x :: TSym "->" :: rest ->
      let body, rest = parse_expr rest in
      Fun (x, body), rest
  | TIf :: rest ->
      let c, rest = parse_expr rest in
      let rest = match rest with TThen :: r -> r | _ -> failwith "expected then" in
      let a, rest = parse_expr rest in
      let rest = match rest with TElse :: r -> r | _ -> failwith "expected else" in
      let b, rest = parse_expr rest in
      If (c, a, b), rest
  | _ -> parse_cmp toks

and parse_cmp toks =
  let a, rest = parse_sum toks in
  match rest with
  | TSym ("<" | "<=" | "=" as op) :: rest -> let b, rest = parse_sum rest in Bin (op, a, b), rest
  | _ -> a, rest

and parse_sum toks =
  let rec loop a = function
    | TSym ("+" | "-" as op) :: rest -> let b, rest = parse_prod rest in loop (Bin (op, a, b)) rest
    | rest -> a, rest
  in
  let a, rest = parse_prod toks in
  loop a rest

and parse_prod toks =
  let rec loop a = function
    | TSym ("*" | "/" as op) :: rest -> let b, rest = parse_app rest in loop (Bin (op, a, b)) rest
    | rest -> a, rest
  in
  let a, rest = parse_app toks in
  loop a rest

and parse_app toks =
  let rec loop f toks =
    match parse_atom toks with
    | Some (a, rest) -> loop (App (f, a)) rest
    | None -> f, toks
  in
  match parse_atom toks with
  | Some (f, rest) -> loop f rest
  | None -> failwith "expected an expression"

and parse_atom = function
  | TInt n :: rest -> Some (Int n, rest)
  | TIdent x :: rest -> Some (Var x, rest)
  | TSym "(" :: rest ->
      let e, rest = parse_expr rest in
      Some (e, expect ")" rest)
  | _ -> None

let parse s =
  match parse_expr (tokenize s) with
  | e, [] -> e
  | _, _ :: _ -> failwith "trailing input"

let arith op a b =
  match op with
  | "+" -> VInt (a + b)
  | "-" -> VInt (a - b)
  | "*" -> VInt (a * b)
  | "/" -> if b = 0 then failwith "division by zero" else VInt (a / b)
  | "<" -> VInt (if a < b then 1 else 0)
  | "<=" -> VInt (if a <= b then 1 else 0)
  | "=" -> VInt (if a = b then 1 else 0)
  | _ -> failwith ("unknown operator " ^ op)

let rec eval (env : env) = function
  | Int n -> VInt n
  | Var x ->
      (try List.assoc x env with Not_found -> failwith ("unbound " ^ x))
  | Bin (op, a, b) ->
      begin match eval env a, eval env b with
      | VInt a, VInt b -> arith op a b
      | _ -> failwith "arithmetic on a function"
      end
  | Let (x, e1, e2) -> eval ((x, eval env e1) :: env) e2
  | Fun (x, body) -> VClosure (x, body, env)
  | App (f, a) ->
      let v = eval env a in
      (match eval env f with
       | VClosure (x, body, cenv) -> eval ((x, v) :: cenv) body
       | VInt _ -> failwith "application of a number")
  | If (c, a, b) ->
      (match eval env c with
       | VInt 0 -> eval env b
       | _ -> eval env a)

let rec show = function
  | Int n -> string_of_int n
  | Var x -> x
  | Bin (op, a, b) -> "(" ^ show a ^ " " ^ op ^ " " ^ show b ^ ")"
  | Let (x, a, b) -> Printf.sprintf "let %s = %s in %s" x (show a) (show b)
  | Fun (x, b) -> "fun " ^ x ^ " -> " ^ show b
  | App (f, a) -> show f ^ " " ^ (match a with Int _ | Var _ -> show a | _ -> "(" ^ show a ^ ")")
  | If (c, a, b) -> "if " ^ show c ^ " then " ^ show a ^ " else " ^ show b

let show_value = function
  | VInt n -> string_of_int n
  | VClosure (x, _, _) -> "<fun " ^ x ^ ">"

let programs = [
  "1 + 2 * 3";
  "let double = fun x -> x + x in double (double 5)";
  "let fact = fun f -> fun n -> if n <= 1 then 1 else n * f f (n - 1) in fact fact 10";
  "let compose = fun f -> fun g -> fun x -> f (g x) in compose (fun x -> x * 3) (fun x -> x - 1) 7";
  "if 2 < 1 then 10 else 20";
]

let () =
  List.iter (fun p ->
      let e = parse p in
      let v = try show_value (eval [] e) with Failure msg -> "error: " ^ msg in
      Printf.printf "%s\n  => %s\n" (show e) v)
    programs
