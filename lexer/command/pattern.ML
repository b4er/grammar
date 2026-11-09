(* the pattern sublanguage of the lexer commands: a lexer over the symbols of a
   cartouche, a parser, and elaboration to nat cls and nat cls rexp terms *)

signature PATTERN_SYMBOL =
sig
  val read_hex: Symbol.symbol list -> int
  val codepoint: Symbol.symbol -> int option
end;

structure Pattern_Symbol: PATTERN_SYMBOL =
struct

fun hex_value s =
  if Symbol.is_ascii_digit s then ord s - ord "0"
  else ord (Symbol.to_ascii_lower s) - ord "a" + 10;

fun read_hex ss = fold (fn s => fn n => 16 * n + hex_value s) ss 0;

(* the code: column of ~~/etc/symbols *)
fun code_entry line =
  (case String.tokens Char.isSpace line of
    sym :: fields =>
      (case drop_prefix (fn f => f <> "code:") fields of
        _ :: code :: _ =>
          if String.isPrefix "0x" code
          then SOME (sym, read_hex (Symbol.explode (unprefix "0x" code))) else NONE
      | _ => NONE)
  | [] => NONE);

val code_table =
  Lazy.lazy (fn () =>
    Symtab.make (map_filter code_entry (File.read_lines (Path.explode "~~/etc/symbols"))));

fun codepoint s =
  (case Symbol.decode s of
    Symbol.Char c => SOME (ord c)
  | Symbol.UTF8 u => (case UTF8.decode_permissive u of [c] => SOME c | _ => NONE)
  | Symbol.Sym _ => Symtab.lookup (Lazy.force code_table) s
  | _ => NONE);

end;

signature PATTERN =
sig
  datatype kind = Class | Regex
  val print_kind: kind -> string
  type entry = {kind: kind, params: kind list, term: term}
  type env = string * Position.T -> entry
  type ast
  val parse: Proof.context -> Input.source -> ast
  val elaborate: env -> ast -> kind * term
  val template: env -> (string * Position.T) list -> ast -> entry
  val read: Proof.context -> env -> Input.source -> kind * term
  val regex_of: kind * term -> term
  val literal: int list -> term
  val class_term: (int * int) list -> term
  val codepoint: Symbol_Pos.T -> int
  val empty_env: env
  val const_env: Proof.context -> env
  val pattern_tr: Proof.context -> term list -> term
end;

structure Pattern: PATTERN =
struct

val max_cp = 0x10FFFF;

fun err pos msg = error ("Lexer pattern: " ^ msg ^ Position.here pos);


(** lexer **)

datatype tok_kind =
    Lit of int list
  | Cls of bool * (int * int) list
  | Any
  | Name of string
  | App of string  (*a name directly followed by a parenthesis*)
  | Op of string;

type tok = tok_kind * Position.range;

fun pos_of_tok ((_, (pos, _)): tok) = pos;

fun cp_of (s, pos) =
  (case Pattern_Symbol.codepoint s of
    SOME c => c
  | NONE => err pos ("unknown symbol " ^ quote s));

(* the digits of \u{h...} *)
fun scan_hex pos ss =
  (case chop_prefix (Symbol.is_ascii_hex o fst) ss of
    (ds as _ :: _, ("}", _) :: rest) =>
      let val c = Pattern_Symbol.read_hex (map fst ds) in
        if length ds > 6 orelse c > max_cp then err pos "codepoint above U+10FFFF"
        else (c, rest)
      end
  | _ => err pos "malformed escape \\u{...}");

(* after a backslash: in a class, any other symbol stands for itself *)
fun scan_escape in_class pos ss =
  (case ss of
    ("n", _) :: rest => (10, rest)
  | ("t", _) :: rest => (9, rest)
  | ("r", _) :: rest => (13, rest)
  | ("u", _) :: ("{", _) :: rest => scan_hex pos rest
  | (s, p) :: rest =>
      if in_class orelse s = "\\" orelse s = "\"" then (cp_of (s, p), rest)
      else err pos ("unknown escape \\" ^ s)
  | [] => err pos "backslash at the end");

fun scan_string pos acc ss =
  (case ss of
    ("\"", _) :: rest => (rev acc, rest)
  | ("\\", p) :: rest =>
      let val (c, rest') = scan_escape false p rest in scan_string pos (c :: acc) rest' end
  | s :: rest => scan_string pos (cp_of s :: acc) rest
  | [] => err pos "unterminated string");

datatype item = Char of int * Position.T | Dash of Position.T;

fun scan_items pos acc ss =
  (case ss of
    ("]", _) :: rest => (rev acc, rest)
  | ("\\", p) :: rest =>
      let val (c, rest') = scan_escape true p rest in scan_items pos (Char (c, p) :: acc) rest' end
  | ("-", p) :: rest => scan_items pos (Dash p :: acc) rest
  | (s, p) :: rest =>
      if Symbol.is_blank s then scan_items pos acc rest
      else scan_items pos (Char (cp_of (s, p), p) :: acc) rest
  | [] => err pos "unterminated class");

(* a dash at either end stands for itself *)
fun ranges (Char (a, p) :: Dash _ :: Char (b, _) :: items) =
      if b < a then err p "empty range" else (a, b) :: ranges items
  | ranges (Char (a, _) :: items) = (a, a) :: ranges items
  | ranges [Dash _] = [(ord "-", ord "-")]
  | ranges (Dash p :: _) = err p "misplaced -"
  | ranges [] = [];

(* the sorted normal form: disjoint, nonadjacent intervals *)
fun normalize rs =
  let
    fun merge ((l, h) :: (l', h') :: rs) =
          if l' <= h + 1 then merge ((l, Int.max (h, h')) :: rs)
          else (l, h) :: merge ((l', h') :: rs)
      | merge rs = rs;
  in merge (sort (prod_ord int_ord int_ord) rs) end;

fun scan_class pos ss =
  let
    val (neg, ss') = (case ss of ("^", _) :: rest => (true, rest) | _ => (false, ss));
    val (items, rest) = scan_items pos [] ss';
    val rs =
      (case items of
        Dash _ :: items' => (ord "-", ord "-") :: ranges items'
      | _ => ranges items);
  in (Cls (neg, normalize rs), rest) end;

fun is_name_symbol s = Symbol.is_ascii_letdig s orelse member (op =) ["_", "'", "."] s;

val operators = ["|", "*", "+", "?", "#", "(", ")", ","];

fun scan_token ss =
  (case ss of
    ("\"", pos) :: rest => scan_string pos [] rest |>> Lit
  | ("[", pos) :: rest => scan_class pos rest
  | ("_", _) :: rest => (Any, rest)
  | (s, pos) :: rest =>
      if member (op =) operators s then (Op s, rest)
      else if Symbol.is_ascii_letter s then
        let
          val (name, rest') =
            chop_prefix (is_name_symbol o fst) rest |>> (fn ns => s :: map fst ns);
          val app = (case rest' of ("(", _) :: _ => true | _ => false);
        in (if app then App (implode name) else Name (implode name), rest') end
      else err pos ("unexpected " ^ quote s)
  | [] => raise Fail "scan_token");

fun tokenize ss =
  (case ss of
    [] => []
  | (s, _) :: rest =>
      if Symbol.is_blank s then tokenize rest
      else
        let val (k, rest') = scan_token ss
        in (k, Symbol_Pos.range (take (length ss - length rest') ss)) :: tokenize rest' end);

fun reports_of_tok ((Lit _, range): tok) = [(Position.range_position range, Markup.inner_string)]
  | reports_of_tok (Op s, range) =
      if member (op =) ["|", "*", "+", "?", "#"] s
      then [(Position.range_position range, Markup.keyword3)] else []
  | reports_of_tok _ = [];


(** parser **)

(*precedence as in flex: postfix, concatenation, #, |*)
datatype ast =
    Lit_A of int list
  | Cls_A of bool * (int * int) list
  | Any_A
  | Ref of string * Position.T
  | App_A of (string * Position.T) * (ast * Position.T) list
  | Seq of ast list
  | Alt of ast * ast
  | Diff of ast * ast * Position.T
  | Rep of string * ast;

fun starts_atom ((k, _) :: _ : tok list) =
      (case k of Op "(" => true | Op _ => false | _ => true)
  | starts_atom [] = false;

fun parse_ast eof (toks: tok list) =
  let
    fun pos_at [] = eof
      | pos_at (t :: _) = pos_of_tok t;
    fun expect s ((Op s', p) :: rest) =
          if s = s' then rest else err (#1 p) ("expected " ^ quote s)
      | expect s toks = err (pos_at toks) ("expected " ^ quote s);

    fun alt toks =
      let val (a, rest) = diff toks in
        (case rest of
          (Op "|", _) :: rest' => alt rest' |>> (fn b => Alt (a, b))
        | _ => (a, rest))
      end
    and diff toks = seq toks |-> diff_tail
    and diff_tail a ((Op "#", (pos, _)) :: rest) =
          seq rest |-> (fn b => diff_tail (Diff (a, b, pos)))
      | diff_tail a rest = (a, rest)
    and seq toks =
      let
        fun items acc toks =
          if starts_atom toks then postfix toks |-> (fn a => items (a :: acc)) else (rev acc, toks);
      in
        (case items [] toks of
          ([], _) => err (pos_at toks) "expected a pattern"
        | ([a], rest) => (a, rest)
        | (asts, rest) => (Seq asts, rest))
      end
    and postfix toks = atom toks |-> repeat
    and repeat a ((Op s, r) :: rest) =
          if member (op =) ["*", "+", "?"] s then repeat (Rep (s, a)) rest
          else (a, (Op s, r) :: rest)
      | repeat a rest = (a, rest)
    and atom ((Lit cs, _) :: rest) = (Lit_A cs, rest)
      | atom ((Cls c, _) :: rest) = (Cls_A c, rest)
      | atom ((Any, _) :: rest) = (Any_A, rest)
      | atom ((Name n, (pos, _)) :: rest) = (Ref (n, pos), rest)
      | atom ((App n, (pos, _)) :: (Op "(", _) :: rest) =
          args [] rest |>> (fn xs => App_A ((n, pos), xs))
      | atom ((Op "(", _) :: rest) = alt rest ||> expect ")"
      | atom toks = err (pos_at toks) "expected a pattern"
    and args acc toks =
      let val (a, rest) = alt toks in
        (case rest of
          (Op ",", _) :: rest' => args ((a, pos_at toks) :: acc) rest'
        | _ => (rev ((a, pos_at toks) :: acc), expect ")" rest))
      end;
  in
    (case toks of
      [] => err eof "empty pattern"
    | _ =>
        (case alt toks of
          (a, []) => a
        | (_, t :: _) => err (pos_of_tok t) "unexpected token"))
  end;

fun report ctxt reports =
  if Context_Position.reports_enabled ctxt then Context_Position.reports ctxt reports else ();

fun parse ctxt source =
  let
    val _ =
      report ctxt [(Input.pos_of source,
        Markup.language {name = "lexer_pattern", symbols = true, antiquotes = false,
          delimited = Input.is_delimited source})];
    val toks = tokenize (Input.source_explode source);
    val _ = report ctxt (maps reports_of_tok toks);
  in parse_ast (#2 (Input.range_of source)) toks end;


(** elaboration **)

datatype kind = Class | Regex;

fun print_kind Class = "class"
  | print_kind Regex = "regex";

type entry = {kind: kind, params: kind list, term: term};
type env = string * Position.T -> entry;

val clsT = \<^typ>\<open>nat cls\<close>;
val rexpT = \<^typ>\<open>nat cls rexp\<close>;

fun typ_of Class = clsT
  | typ_of Regex = rexpT;

fun mk_nat n = HOLogic.mk_number HOLogic.natT n;

fun mk_cls rs =
  HOLogic.mk_list (HOLogic.mk_prodT (HOLogic.natT, HOLogic.natT))
    (map (fn (l, h) => HOLogic.mk_prod (mk_nat l, mk_nat h)) rs);

val top = mk_cls [(0, max_cp)];

fun disj s t = \<^Const>\<open>cp_disj for s t\<close>;
fun neg t = \<^Const>\<open>cp_neg for t\<close>;
fun diff s t = if s aconv top then neg t else \<^Const>\<open>cp_conj for s \<open>neg t\<close>\<close>;

fun pred t = \<^Const>\<open>Atom clsT for t\<close>;
val one = \<^Const>\<open>One clsT\<close>;
fun plus r s = \<^Const>\<open>Plus clsT for r s\<close>;
fun times r s = \<^Const>\<open>Times clsT for r s\<close>;
fun star r = \<^Const>\<open>Star clsT for r\<close>;

fun lift (Class, t) = pred t
  | lift (Regex, r) = r;

fun literal [] = one
  | literal cs = foldr1 (uncurry times) (map (fn c => pred (mk_cls [(c, c)])) cs);

fun plural 1 x = x
  | plural _ x = x ^ "s";

fun elaborate (env: env) ast =
  (case ast of
    Lit_A cs => (Regex, literal cs)
  | Cls_A (false, rs) => (Class, mk_cls rs)
  | Cls_A (true, rs) => (Class, neg (mk_cls rs))
  | Any_A => (Class, top)
  | Ref (n, pos) =>
      (case env (n, pos) of
        {kind, params = [], term} => (kind, term)
      | {params, ...} =>
          err pos (quote n ^ " takes " ^ string_of_int (length params) ^ " " ^
            plural (length params) "argument"))
  | App_A ((n, pos), args) =>
      let
        val {kind, params, term} = env (n, pos);
        val _ =
          if length params = length args then ()
          else err pos (quote n ^ " takes " ^ string_of_int (length params) ^ " " ^
            plural (length params) "argument");
        fun arg Regex (a, _) = lift (elaborate env a)
          | arg Class (a, apos) =
              (case elaborate env a of
                (Class, t) => t
              | (Regex, _) => err apos "this argument must be a class");
      in (kind, Envir.beta_norm (Term.betapplys (term, map2 arg params args))) end
  | Seq asts => (Regex, foldr1 (uncurry times) (map (lift o elaborate env) asts))
  | Alt (a, b) =>
      (case (elaborate env a, elaborate env b) of
        ((Class, s), (Class, t)) => (Class, disj s t)
      | (x, y) => (Regex, plus (lift x) (lift y)))
  | Diff (a, b, pos) =>
      (case (elaborate env a, elaborate env b) of
        ((Class, s), (Class, t)) => (Class, diff s t)
      | ((Regex, _), _) => err pos "the left side of # is not a class"
      | _ => err pos "the right side of # is not a class")
  | Rep ("*", a) => (Regex, star (lift (elaborate env a)))
  | Rep ("+", a) => let val r = lift (elaborate env a) in (Regex, times r (star r)) end
  | Rep (_, a) => (Regex, plus one (lift (elaborate env a))));

(* the names in class position: the sides of # and the alternatives below them *)
fun class_names in_class ast =
  (case ast of
    Ref (n, _) => if in_class then [n] else []
  | Alt (a, b) => class_names in_class a @ class_names in_class b
  | Diff (a, b, _) => class_names true a @ class_names true b
  | Seq asts => maps (class_names false) asts
  | Rep (_, a) => class_names false a
  | App_A (_, args) => maps (class_names false o #1) args
  | _ => []);

(* a parameter is a class if the body uses it as one, else a regex *)
fun template env params ast =
  let
    val _ =
      (case duplicates (op =) (map #1 params) of
        [] => ()
      | x :: _ => err (the (AList.lookup (op =) params x)) ("duplicate parameter " ^ quote x));
    val classes = class_names false ast;
    val kinds = map (fn (x, _) => if member (op =) classes x then Class else Regex) params;
    val frees = map2 (fn (x, _) => fn k => Free (x, typ_of k)) params kinds;
    val locals = map #1 params ~~ (kinds ~~ frees);
    fun env' (n, pos) =
      (case AList.lookup (op =) locals n of
        SOME (k, t) => {kind = k, params = [], term = t}
      | NONE => env (n, pos));
    val (kind, body) = elaborate env' ast;
  in {kind = kind, params = kinds, term = fold_rev Term.lambda frees body} end;

fun read ctxt env source = elaborate env (parse ctxt source);

val regex_of = lift;
val class_term = mk_cls;
val codepoint = cp_of;

fun empty_env (n, pos) = err pos ("undefined name " ^ quote n);

(* HOL constants whose type is an instance of nat cls, nat cls rexp, or a function
   between them *)
fun const_env ctxt (n, pos) =
  let
    val (t, reports) = Proof_Context.check_const {proper = true, strict = false} ctxt (n, [pos]);
    val _ = report ctxt reports;
    val thy = Proof_Context.theory_of ctxt;
    fun match T (kinds, tyenv) =
      (case get_first (fn k => try (Sign.typ_match thy (T, typ_of k)) tyenv |> Option.map (pair k))
          [Class, Regex] of
        SOME (k, tyenv') => (k :: kinds, tyenv')
      | NONE => err pos (quote n ^ " is neither a class nor a regex"));
    val (Ts, U) = strip_type (fastype_of t);
    val (kinds, tyenv) = fold match (U :: Ts) ([], Vartab.empty);
  in
    (case (t, rev kinds) of
      (Const (c, T), kind :: params) =>
        {kind = kind, params = params, term = Const (c, Envir.subst_type tyenv T)}
    | _ => empty_env (n, pos))
  end;


(** PAT\<open>...\<close> in terms **)

fun pattern_tr ctxt args =
  (case args of
    [(Const (\<^syntax_const>\<open>_constrain\<close>, _)) $ Free (s, _) $ p] =>
      (case Term_Position.decode_position1 p of
        SOME {pos, ...} =>
          let val source = Input.cartouche_content (Symbol_Pos.explode (s, pos))
          in #2 (read ctxt (const_env ctxt) source) end
      | NONE => raise TERM ("pattern_tr", args))
  | _ => raise TERM ("pattern_tr", args));


(** the diagnostic command **)

fun pattern_cmd ctxt source defs =
  let
    fun define (((n, pos), params), body) entries =
      let
        fun env (m, mpos) =
          (case AList.lookup (op =) entries m of
            SOME e => e
          | NONE => empty_env (m, mpos));
        val _ =
          if AList.defined (op =) entries n then err pos ("duplicate name " ^ quote n) else ();
      in (n, template env params (parse ctxt body)) :: entries end;
    val entries = fold define defs [];
    fun env (n, pos) =
      (case AList.lookup (op =) entries n of SOME e => e | NONE => empty_env (n, pos));
    val (kind, t) = read ctxt env source;
  in
    Pretty.writeln
      (Pretty.block [Pretty.str (print_kind kind ^ ":"), Pretty.brk 1, Syntax.pretty_term ctxt t])
  end;

val definition =
  Parse.position Parse.name --
    Scan.optional (Parse.$$$ "(" |-- Parse.enum1 "," (Parse.position Parse.name) --| Parse.$$$ ")")
      [] --|
    Parse.$$$ "=" -- Parse.input Parse.cartouche;

val _ =
  Outer_Syntax.command \<^command_keyword>\<open>pattern\<close>
    "elaborate a lexer pattern and print its term and kind"
    (Parse.input Parse.cartouche -- Scan.optional (Parse.where_ |-- Parse.enum1 "|" definition) []
      >> (fn (source, defs) =>
        Toplevel.keep (fn st => pattern_cmd (Toplevel.context_of st) source defs)));

end;
