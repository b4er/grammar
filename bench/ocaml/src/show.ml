open Names.P

let pf = Format.fprintf
let str ppf s = pf ppf "%S" (implode s)
let list f ppf xs = pf ppf "(%a)" (Format.pp_print_list ~pp_sep:Format.pp_print_space f) xs
let opt f ppf = function None -> pf ppf "-" | Some x -> f ppf x
let pair f g ppf (a, b) = pf ppf "(%a %a)" f a g b

let rec lid ppf = function
  | Lident x -> str ppf x
  | Ldot (m, x) -> pf ppf "%a.%a" lid m str x

let const ppf = function
  | Pconst_integer s -> pf ppf "(int %a)" str s
  | Pconst_char s -> pf ppf "(char %a)" str s
  | Pconst_string s -> pf ppf "(string %a)" str s
  | Pconst_float s -> pf ppf "(float %a)" str s

let rec typ ppf = function
  | Ptyp_var v -> pf ppf "'%a" str v
  | Ptyp_arrow (a, b) -> pf ppf "(-> %a %a)" typ a typ b
  | Ptyp_tuple ts -> pf ppf "(* %a)" (list typ) ts
  | Ptyp_constr (c, ts) -> pf ppf "(%a %a)" lid c (list typ) ts

let rec pat ppf = function
  | Ppat_any -> pf ppf "_"
  | Ppat_var x -> str ppf x
  | Ppat_alias (p, x) -> pf ppf "(as %a %a)" pat p str x
  | Ppat_constant c -> const ppf c
  | Ppat_tuple ps -> pf ppf "(tuple %a)" (list pat) ps
  | Ppat_construct (c, p) -> pf ppf "(%a %a)" lid c (opt pat) p
  | Ppat_record (fs, f) ->
      pf ppf "(record%s %a)" (match f with Closed -> "" | Open -> "_") (list (pair str pat)) fs
  | Ppat_or (a, b) -> pf ppf "(| %a %a)" pat a pat b
  | Ppat_constraint (p, t) -> pf ppf "(: %a %a)" pat p typ t

let rec_flag ppf = function Nonrecursive -> () | Recursive -> pf ppf " rec"

let rec exp ppf = function
  | Pexp_ident x -> lid ppf x
  | Pexp_constant c -> const ppf c
  | Pexp_let (r, bs, e) -> pf ppf "(let%a %a %a)" rec_flag r (list vb) bs exp e
  | Pexp_function cs -> pf ppf "(function %a)" (list case) cs
  | Pexp_fun (ps, e) -> pf ppf "(fun %a %a)" (list pat) ps exp e
  | Pexp_apply (f, xs) -> pf ppf "(%a %a)" exp f (list exp) xs
  | Pexp_match (e, cs) -> pf ppf "(match %a %a)" exp e (list case) cs
  | Pexp_try (e, cs) -> pf ppf "(try %a %a)" exp e (list case) cs
  | Pexp_tuple es -> pf ppf "(tuple %a)" (list exp) es
  | Pexp_construct (c, e) -> pf ppf "(%a %a)" lid c (opt exp) e
  | Pexp_record (fs, e) -> pf ppf "(record %a %a)" (list (pair str exp)) fs (opt exp) e
  | Pexp_field (e, l) -> pf ppf "(. %a %a)" exp e str l
  | Pexp_setfield (e, l, v) -> pf ppf "(<- %a %a %a)" exp e str l exp v
  | Pexp_ifthenelse (c, a, b) -> pf ppf "(if %a %a %a)" exp c exp a (opt exp) b
  | Pexp_sequence (a, b) -> pf ppf "(; %a %a)" exp a exp b
  | Pexp_constraint (e, t) -> pf ppf "(: %a %a)" exp e typ t

and case ppf (Pcase (p, g, e)) = pf ppf "(%a %a %a)" pat p (opt exp) g exp e
and vb ppf (Pvb (p, e)) = pf ppf "(%a %a)" pat p exp e

let kind ppf = function
  | Ptype_abstract -> pf ppf "abstract"
  | Ptype_variant cs -> pf ppf "(variant %a)" (list (pair str (list typ))) cs
  | Ptype_record ls ->
      let mut ppf = function Immutable -> pf ppf "" | Mutable -> pf ppf "mutable " in
      pf ppf "(record %a)" (list (fun ppf (m, (l, t)) -> pf ppf "(%a%a %a)" mut m str l typ t)) ls

let decl ppf (Ptype (ps, n, k, m)) = pf ppf "(%a %a %a %a)" (list str) ps str n kind k (opt typ) m

let item ppf = function
  | Pstr_value (r, bs) -> pf ppf "(let%a %a)" rec_flag r (list vb) bs
  | Pstr_type ds -> pf ppf "(type %a)" (list decl) ds
  | Pstr_open m -> pf ppf "(open %a)" lid m

(* one item per line *)
let structure items = String.concat "\n" (List.map (Format.asprintf "@[<h>%a@]" item) items)
