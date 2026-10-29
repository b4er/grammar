(* Hindley-Milner type inference with levels (as in OCaml's own
   typechecker): mutable type variables, unification with an occurs check,
   generalisation, and a printer for the inferred schemes. *)

type ty =
  | TCon of string * ty list
  | TVar of tvar ref
  | TArrow of ty * ty

and tvar =
  | Unbound of int * int
  | Link of ty
  | Generic of int

type term =
  | Var of string
  | Lam of string * term
  | App of term * term
  | Let of string * term * term
  | Lit of int
  | Pair of term * term

let counter = ref 0
let current_level = ref 1

let fresh_id () = counter := !counter + 1; !counter
let enter_level () = current_level := !current_level + 1
let leave_level () = current_level := !current_level - 1

let new_var () = TVar (ref (Unbound (fresh_id (), !current_level)))
let int_t = TCon ("int", [])
let pair_t a b = TCon ("*", [a; b])

let rec repr t =
  match t with
  | TVar ({ contents = Link t' } as r) ->
      let t'' = repr t' in
      r := Link t'';
      t''
  | _ -> t

let rec occurs id level t =
  match repr t with
  | TVar ({ contents = Unbound (id', level') } as r) ->
      if id = id' then failwith "recursive type"
      else if level' > level then r := Unbound (id', level)
  | TVar _ -> ()
  | TCon (_, ts) -> List.iter (occurs id level) ts
  | TArrow (a, b) -> occurs id level a; occurs id level b

let rec unify a b =
  let a = repr a in
  let b = repr b in
  if a == b then ()
  else
    match a, b with
    | TVar ({ contents = Unbound (id, level) } as r), t
    | t, TVar ({ contents = Unbound (id, level) } as r) ->
        occurs id level t;
        r := Link t
    | TArrow (a1, b1), TArrow (a2, b2) -> unify a1 a2; unify b1 b2
    | TCon (c1, ts1), TCon (c2, ts2) when c1 = c2 && List.length ts1 = List.length ts2 ->
        List.iter2 unify ts1 ts2
    | _ -> failwith "type mismatch"

let rec generalize t =
  match repr t with
  | TVar ({ contents = Unbound (id, level) } as r) when level > !current_level ->
      r := Generic id; t
  | TArrow (a, b) -> TArrow (generalize a, generalize b)
  | TCon (c, ts) -> TCon (c, List.map generalize ts)
  | t -> t

let instantiate t =
  let table = Hashtbl.create 8 in
  let rec go t =
    match repr t with
    | TVar { contents = Generic id } ->
        begin try Hashtbl.find table id with Not_found ->
          let v = new_var () in
          Hashtbl.add table id v;
          v
        end
    | TArrow (a, b) -> TArrow (go a, go b)
    | TCon (c, ts) -> TCon (c, List.map go ts)
    | t -> t
  in
  go t

let rec infer env = function
  | Var x ->
      (match List.assoc_opt x env with
       | Some t -> instantiate t
       | None -> failwith ("unbound variable " ^ x))
  | Lit _ -> int_t
  | Lam (x, body) ->
      let a = new_var () in
      let b = infer ((x, a) :: env) body in
      TArrow (a, b)
  | App (f, arg) ->
      let tf = infer env f in
      let ta = infer env arg in
      let r = new_var () in
      unify tf (TArrow (ta, r));
      r
  | Pair (a, b) -> pair_t (infer env a) (infer env b)
  | Let (x, e, body) ->
      enter_level ();
      let t = infer env e in
      leave_level ();
      infer ((x, generalize t) :: env) body

let show t =
  let names = Hashtbl.create 8 in
  let name id =
    match Hashtbl.find_opt names id with
    | Some n -> n
    | None ->
        let n = Printf.sprintf "'%c" (Char.chr (Char.code 'a' + Hashtbl.length names)) in
        Hashtbl.add names id n;
        n
  in
  let rec go prec t =
    match repr t with
    | TVar { contents = Generic id } | TVar { contents = Unbound (id, _) } -> name id
    | TVar { contents = Link _ } -> assert_false ()
    | TCon (c, []) -> c
    | TCon ("*", [a; b]) ->
        let s = go 2 a ^ " * " ^ go 2 b in
        if prec > 1 then "(" ^ s ^ ")" else s
    | TCon (c, ts) -> "(" ^ String.concat ", " (List.map (go 0) ts) ^ ") " ^ c
    | TArrow (a, b) ->
        let s = go 1 a ^ " -> " ^ go 0 b in
        if prec > 0 then "(" ^ s ^ ")" else s
  and assert_false () = failwith "a link survived repr"
  in
  go 0 t

let examples = [
  "id", Lam ("x", Var "x");
  "const", Lam ("x", Lam ("y", Var "x"));
  "compose", Lam ("f", Lam ("g", Lam ("x", App (Var "f", App (Var "g", Var "x")))));
  "let-poly", Let ("id", Lam ("x", Var "x"), Pair (App (Var "id", Lit 1), App (Var "id", Var "id")));
  "swap", Lam ("p", Var "p");
  "apply", Lam ("f", Lam ("x", App (Var "f", Var "x")));
]

let () =
  List.iter (fun (name, e) ->
      counter := 0;
      current_level := 1;
      let t =
        try show (generalize (infer [] e)) with Failure msg -> "error: " ^ msg
      in
      Printf.printf "%-10s : %s\n" name t) examples
