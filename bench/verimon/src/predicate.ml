(* The part of MonPoly's Predicate (9bce98f^, 2020) the vendored parser uses:
   the term types (without the zarith constants the parser never builds) and
   predicates. *)

type var = string

type cst =
  | Int of int
  | Str of string
  | Float of float

type tcl = TNum | TAny
type tcst = TInt | TStr | TFloat
type tsymb = TSymb of (tcl * int) | TCst of tcst

type 'a eterm =
  | Var of 'a
  | Cst of cst
  | F2i of 'a eterm
  | I2f of 'a eterm
  | Plus of 'a eterm * 'a eterm
  | Minus of 'a eterm * 'a eterm
  | UMinus of 'a eterm
  | Mult of 'a eterm * 'a eterm
  | Div of 'a eterm * 'a eterm
  | Mod of 'a eterm * 'a eterm

type term = var eterm

type predicate = var * int * term list

let make_predicate (name, args) = (name, List.length args, args)

let get_args ((_, _, args) : predicate) = args

let rec tvars = function
  | Var v -> [v]
  | Cst _ -> []
  | F2i t | I2f t | UMinus t -> tvars t
  | Plus (t1, t2) | Minus (t1, t2) | Mult (t1, t2) | Div (t1, t2) | Mod (t1, t2) ->
      tvars t1 @ tvars t2

let pvars (p : predicate) = List.concat_map tvars (get_args p)
