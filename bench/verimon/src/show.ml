(* MonPoly formulas as S-expressions: the format the two parsers' results are
   compared in.  The parser names `_` variables _1, _2, ... from a counter that
   is never reset; [formula] renumbers them from 1 in order, so a formula
   prints the same whatever was parsed before it. *)

open Predicate
open MFOTL

let num x = Printf.sprintf "%.17g" x

let cst = function
  | Int i -> Printf.sprintf "(int %d)" i
  | Str s -> Printf.sprintf "(str %S)" s
  | Float x -> Printf.sprintf "(float %s)" (num x)

let rec term v = function
  | Var x -> Printf.sprintf "(var %S)" (v x)
  | Cst c -> cst c
  | F2i t -> Printf.sprintf "(f2i %s)" (term v t)
  | I2f t -> Printf.sprintf "(i2f %s)" (term v t)
  | UMinus t -> Printf.sprintf "(neg %s)" (term v t)
  | Plus (a, b) -> Printf.sprintf "(+ %s %s)" (term v a) (term v b)
  | Minus (a, b) -> Printf.sprintf "(- %s %s)" (term v a) (term v b)
  | Mult (a, b) -> Printf.sprintf "(* %s %s)" (term v a) (term v b)
  | Div (a, b) -> Printf.sprintf "(/ %s %s)" (term v a) (term v b)
  | Mod (a, b) -> Printf.sprintf "(mod %s %s)" (term v a) (term v b)

let bound = function
  | OBnd x -> "(open " ^ num x ^ ")"
  | CBnd x -> "(closed " ^ num x ^ ")"
  | Inf -> "inf"

let intv (a, b) = Printf.sprintf "(%s %s)" (bound a) (bound b)

let agg = function
  | Cnt -> "cnt" | Min -> "min" | Max -> "max" | Sum -> "sum" | Avg -> "avg" | Med -> "med"

let vars v xs = "(" ^ String.concat " " (List.map (fun x -> Printf.sprintf "%S" (v x)) xs) ^ ")"

let pred v ((n, a, ts) : predicate) =
  Printf.sprintf "(pred %S %d%s)" n a (String.concat "" (List.map (fun t -> " " ^ term v t) ts))

let rec fml v = function
  | Equal (a, b) -> Printf.sprintf "(= %s %s)" (term v a) (term v b)
  | Less (a, b) -> Printf.sprintf "(< %s %s)" (term v a) (term v b)
  | LessEq (a, b) -> Printf.sprintf "(<= %s %s)" (term v a) (term v b)
  | Pred p -> pred v p
  | Let (p, a, b) -> Printf.sprintf "(let %s %s %s)" (pred v p) (fml v a) (fml v b)
  | Neg f -> Printf.sprintf "(not %s)" (fml v f)
  | And (a, b) -> Printf.sprintf "(and %s %s)" (fml v a) (fml v b)
  | Or (a, b) -> Printf.sprintf "(or %s %s)" (fml v a) (fml v b)
  | Implies (a, b) -> Printf.sprintf "(implies %s %s)" (fml v a) (fml v b)
  | Equiv (a, b) -> Printf.sprintf "(equiv %s %s)" (fml v a) (fml v b)
  | Exists (xs, f) -> Printf.sprintf "(exists %s %s)" (vars v xs) (fml v f)
  | ForAll (xs, f) -> Printf.sprintf "(forall %s %s)" (vars v xs) (fml v f)
  | Aggreg (_, y, op, x, g, f) ->
      Printf.sprintf "(aggreg %S %s %S %s %s)" (v y) (agg op) (v x) (vars v g) (fml v f)
  | Prev (i, f) -> Printf.sprintf "(prev %s %s)" (intv i) (fml v f)
  | Next (i, f) -> Printf.sprintf "(next %s %s)" (intv i) (fml v f)
  | Eventually (i, f) -> Printf.sprintf "(eventually %s %s)" (intv i) (fml v f)
  | Once (i, f) -> Printf.sprintf "(once %s %s)" (intv i) (fml v f)
  | Always (i, f) -> Printf.sprintf "(always %s %s)" (intv i) (fml v f)
  | PastAlways (i, f) -> Printf.sprintf "(historically %s %s)" (intv i) (fml v f)
  | Since (i, a, b) -> Printf.sprintf "(since %s %s %s)" (intv i) (fml v a) (fml v b)
  | Until (i, a, b) -> Printf.sprintf "(until %s %s %s)" (intv i) (fml v a) (fml v b)
  | Frex (i, r) -> Printf.sprintf "(frex %s %s)" (intv i) (re v r)
  | Prex (i, r) -> Printf.sprintf "(prex %s %s)" (intv i) (re v r)
and re v = function
  | Wild -> "wild"
  | Test f -> Printf.sprintf "(test %s)" (fml v f)
  | Concat (a, b) -> Printf.sprintf "(concat %s %s)" (re v a) (re v b)
  | Plus (a, b) -> Printf.sprintf "(alt %s %s)" (re v a) (re v b)
  | Star r -> Printf.sprintf "(star %s)" (re v r)

(* `_` variables: _ and digits only, numbered by the parser's counter *)
let anon x =
  String.length x > 1 && x.[0] = '_'
  && String.for_all (fun c -> c >= '0' && c <= '9') (String.sub x 1 (String.length x - 1))

let formula f =
  let seen = Hashtbl.create 8 in
  let ns = ref [] in
  ignore (fml (fun x -> if anon x && not (Hashtbl.mem seen x) then begin
      Hashtbl.add seen x (); ns := int_of_string (String.sub x 1 (String.length x - 1)) :: !ns end; x) f);
  let sorted = List.sort compare !ns in
  let renum x =
    if anon x then
      let n = int_of_string (String.sub x 1 (String.length x - 1)) in
      let rec idx i = function [] -> n | m :: r -> if m = n then i else idx (i + 1) r in
      "_" ^ string_of_int (idx 1 sorted)
    else x
  in
  fml renum f
