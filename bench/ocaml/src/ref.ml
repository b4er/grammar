(* OCaml's own parser (compiler-libs), its Parsetree converted to the
   exported types: the reference `make check` compares both parsers with.
   It is not measured.  Where OCaml's tree differs from the subset's by
   construction, the conversion undoes OCaml's rewriting:
   - a negative constant is the negation of a positive one;
   - a function's parameters, its result constraint and its cases are one
     Pexp_function node in OCaml, nested Pexp_fun / Pexp_constraint /
     Pexp_function here;
   - a let-binding's type constraint is on the bound expression. *)

open Parsetree
module P = Names.P

exception Outside of string

let outside what = raise (Outside what)
let x = P.explode

let rec lid : Longident.t -> P.longident = function
  | Lident s -> Lident (x s)
  | Ldot (m, s) -> Ldot (lid m.txt, x s.txt)
  | Lapply _ -> outside "functor application"

let label : Longident.t -> P.char list = function
  | Lident s -> x s
  | _ -> outside "qualified label"

let const (c : constant) : P.expression =
  let neg s = String.length s > 0 && s.[0] = '-' in
  let num mk s =
    if neg s then
      P.Pexp_apply (Pexp_ident (Lident Names.neg),
                    [Pexp_constant (mk (x (String.sub s 1 (String.length s - 1))))])
    else Pexp_constant (mk (x s)) in
  match c.pconst_desc with
  | Pconst_integer (s, None) -> num (fun s -> P.Pconst_integer s) s
  | Pconst_float (s, None) -> num (fun s -> P.Pconst_float s) s
  | Pconst_char c -> Pexp_constant (Pconst_char (x (String.make 1 c)))
  | Pconst_string (s, _, None) -> Pexp_constant (Pconst_string (x s))
  | _ -> outside "constant"

let pconst (c : constant) : P.pconstant =
  match const c with Pexp_constant c -> c | _ -> outside "negative constant pattern"

let nolabel : Asttypes.arg_label -> unit = function
  | Nolabel -> ()
  | _ -> outside "label"

let unlabeled xs = List.map (fun (l, e) -> if l <> None then outside "labeled tuple" else e) xs

let rec typ (t : core_type) : P.core_type =
  match t.ptyp_desc with
  | Ptyp_var v -> Ptyp_var (x v)
  | Ptyp_arrow (l, a, b) -> nolabel l; Ptyp_arrow (typ a, typ b)
  | Ptyp_tuple ts -> Ptyp_tuple (List.map typ (unlabeled ts))
  | Ptyp_constr (c, ts) -> Ptyp_constr (lid c.txt, List.map typ ts)
  | _ -> outside "type"

let rec pat (p : pattern) : P.pattern =
  match p.ppat_desc with
  | Ppat_any -> Ppat_any
  | Ppat_var v -> Ppat_var (x v.txt)
  | Ppat_alias (p, v) -> Ppat_alias (pat p, x v.txt)
  | Ppat_constant c -> Ppat_constant (pconst c)
  | Ppat_tuple (ps, Closed) -> Ppat_tuple (List.map pat (unlabeled ps))
  | Ppat_construct (c, None) -> Ppat_construct (lid c.txt, None)
  | Ppat_construct (c, Some ([], p)) -> Ppat_construct (lid c.txt, Some (pat p))
  | Ppat_record (fs, f) ->
      Ppat_record (List.map (fun ((l : Longident.t Asttypes.loc), p) -> (label l.txt, pat p)) fs,
                   match f with Closed -> Closed | Open -> Open)
  | Ppat_or (a, b) -> Ppat_or (pat a, pat b)
  | Ppat_constraint (p, t) -> Ppat_constraint (pat p, typ t)
  | _ -> outside "pattern"

let rec_flag : Asttypes.rec_flag -> P.rec_flag = function
  | Nonrecursive -> Nonrecursive
  | Recursive -> Recursive

let rec exp (e : expression) : P.expression =
  match e.pexp_desc with
  | Pexp_ident i -> Pexp_ident (lid i.txt)
  | Pexp_constant c -> const c
  | Pexp_let (r, bs, e) -> Pexp_let (rec_flag r, List.map vb bs, exp e)
  | Pexp_function (ps, c, body) ->
      let param (p : function_param) = match p.pparam_desc with
        | Pparam_val (l, None, p) -> nolabel l; pat p
        | _ -> outside "parameter" in
      let body = match body with
        | Pfunction_body e -> exp e
        | Pfunction_cases (cs, _, _) -> Pexp_function (List.map case cs) in
      let body = match c with
        | None -> body
        | Some (Pconstraint t) -> Pexp_constraint (body, typ t)
        | Some (Pcoerce _) -> outside "coercion" in
      P.mk_fun (List.map param ps) body
  | Pexp_apply (f, xs) -> Pexp_apply (exp f, List.map (fun (l, e) -> nolabel l; exp e) xs)
  | Pexp_match (e, cs) -> Pexp_match (exp e, List.map case cs)
  | Pexp_try (e, cs) -> Pexp_try (exp e, List.map case cs)
  | Pexp_tuple es -> Pexp_tuple (List.map exp (unlabeled es))
  | Pexp_construct (c, e) -> Pexp_construct (lid c.txt, Option.map exp e)
  | Pexp_record (fs, e) ->
      Pexp_record (List.map (fun ((l : Longident.t Asttypes.loc), e) -> (label l.txt, exp e)) fs, Option.map exp e)
  | Pexp_field (e, l) -> Pexp_field (exp e, label l.txt)
  | Pexp_setfield (e, l, v) -> Pexp_setfield (exp e, label l.txt, exp v)
  | Pexp_ifthenelse (c, a, b) -> Pexp_ifthenelse (exp c, exp a, Option.map exp b)
  | Pexp_sequence (a, b) -> Pexp_sequence (exp a, exp b)
  | Pexp_constraint (e, t) -> Pexp_constraint (exp e, typ t)
  | _ -> outside "expression"

and case (c : case) : P.match_case = Pcase (pat c.pc_lhs, Option.map exp c.pc_guard, exp c.pc_rhs)

and vb (b : value_binding) : P.value_binding =
  let e = exp b.pvb_expr in
  match b.pvb_constraint with
  | None -> Pvb (pat b.pvb_pat, e)
  | Some (Pvc_constraint { locally_abstract_univars = []; typ = t }) ->
      Pvb (pat b.pvb_pat, Pexp_constraint (e, typ t))
  | Some _ -> outside "binding constraint"

let decl (d : type_declaration) : P.type_declaration =
  let param (t, _) = match t.ptyp_desc with Ptyp_var v -> x v | _ -> outside "type parameter" in
  let kind : P.type_kind = match d.ptype_kind with
    | Ptype_abstract -> Ptype_abstract
    | Ptype_variant cs ->
        Ptype_variant (List.map (fun c -> match c.pcd_args, c.pcd_res with
          | Pcstr_tuple ts, None -> (x c.pcd_name.txt, List.map typ ts)
          | _ -> outside "constructor") cs)
    | Ptype_record ls ->
        Ptype_record (List.map (fun l ->
          ((match l.pld_mutable with Mutable -> P.Mutable | Immutable -> P.Immutable),
           (x l.pld_name.txt, typ l.pld_type))) ls)
    | Ptype_open -> outside "extensible type" in
  Ptype (List.map param d.ptype_params, x d.ptype_name.txt, kind, Option.map typ d.ptype_manifest)

let item (i : structure_item) : P.structure_item =
  match i.pstr_desc with
  | Pstr_value (r, bs) -> Pstr_value (rec_flag r, List.map vb bs)
  | Pstr_type (_, ds) -> Pstr_type (List.map decl ds)
  | Pstr_open { popen_expr = { pmod_desc = Pmod_ident m; _ }; _ } -> Pstr_open (lid m.txt)
  | _ -> outside "structure item"

let parse_file file =
  let ic = open_in_bin file in
  let lb = Lexing.from_channel ic in
  Location.init lb file;
  let s = Fun.protect ~finally:(fun () -> close_in ic) (fun () -> Parse.implementation lb) in
  List.map item s
