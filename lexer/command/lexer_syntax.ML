(* outer syntax of the lexer command: the options, the clauses, the where entries and the
   rules, handed to Lexer_Command.lexer_cmd and, unless sketch, Lexer_Tables.tables_cmd *)

structure Lexer_Syntax:
sig
  val options: (string * Position.T) list parser
  val spec: Lexer_Command.spec parser
  val lexer: (string * Position.T) list -> Lexer_Command.spec -> local_theory -> local_theory
end =
struct

open Lexer_Command;

fun err pos msg = error ("Lexer: " ^ msg ^ Position.here pos);

(* the clause and action words are minor keywords (Lexer_Command.thy); an entry of
   where may still be named like one of them *)
val words =
  ["modes", "start", "exclusive", "final", "after", "newline", "rules", "skip", "error", "push",
   "pop"];

val entry_name = Parse.position (Parse.name || Scan.first (map Parse.$$$ words));

datatype clause =
    Modes of modes
  | Start of Input.source
  | Exclusive of Input.source list
  | Final of Input.source list
  | After of Input.source
  | Newline of string * Position.T;

val term = Parse.input Parse.term;

val clause =
  Parse.$$$ "modes" |--
    (Parse.input Parse.cartouche >> Mode_Type || Scan.repeat1 Parse.binding >> Mode_Names)
    >> Modes ||
  Parse.$$$ "start" |-- term >> Start ||
  Parse.$$$ "exclusive" |-- Scan.repeat1 term >> Exclusive ||
  Parse.$$$ "final" |-- Scan.repeat1 term >> Final ||
  Parse.$$$ "after" |-- term >> After ||
  Parse.$$$ "newline" |-- entry_name >> Newline;

fun clause_name (Modes _) = "modes"
  | clause_name (Start _) = "start"
  | clause_name (Exclusive _) = "exclusive"
  | clause_name (Final _) = "final"
  | clause_name (After _) = "after"
  | clause_name (Newline _) = "newline";

val definition =
  entry_name --
    Scan.optional (Parse.$$$ "(" |-- Parse.enum1 "," (Parse.position Parse.name) --| Parse.$$$ ")")
      [] --|
    Parse.$$$ "=" -- Parse.input Parse.cartouche;


(* a tag <p, q>: the outer lexer reads _> and <_> as single symbolic names, so the tag
   is split at the level of symbols *)

fun has_gt tok =
  not (Token.is_kind Token.Cartouche tok) andalso
    exists (fn s => s = ">") (Symbol.explode (Token.content_of tok));

fun starts_lt tok = String.isPrefix "<" (Token.content_of tok);

val tag_tokens =
  Scan.one (fn t => Token.not_eof t andalso starts_lt t) :|-- (fn t =>
    if has_gt t then Scan.succeed [t]
    else
      Scan.repeat (Scan.one (fn t => Token.not_eof t andalso not (has_gt t))) --
        Scan.one (fn t => Token.not_eof t andalso has_gt t)
      >> (fn (ts, t') => t :: ts @ [t']));

(* the symbols of the tokens, with blanks for the gaps so that offsets stay right *)
fun join_tokens toks =
  let
    fun gap a b =
      (case (Position.offset_of (#2 (List.last a)), Position.offset_of (#2 (hd b))) of
        (SOME i, SOME j) => Int.max (j - i - 1, 1)
      | _ => 1);
    fun join (a :: (rest as b :: _)) =
          if null a then join rest else a @ replicate (gap a b) (" ", Position.none) @ join rest
      | join [a] = a
      | join [] = [];
  in join (filter_out null (map (Input.source_explode o Token.input_of) toks)) end;

fun split_commas depth acc cur syms =
  (case syms of
    [] => rev (rev cur :: acc)
  | (s as ("(", _)) :: rest => split_commas (depth + 1) acc (s :: cur) rest
  | (s as (")", _)) :: rest => split_commas (depth - 1) acc (s :: cur) rest
  | (",", _) :: rest =>
      if depth = 0 then split_commas depth (rev cur :: acc) [] rest
      else split_commas depth acc (("," , Position.none) :: cur) rest
  | s :: rest => split_commas depth acc (s :: cur) rest);

val trim_blanks =
  drop_prefix (Symbol.is_blank o fst) #> rev #> drop_prefix (Symbol.is_blank o fst) #> rev;

fun tag_sources toks =
  let
    val pos = Token.pos_of (hd toks);
    val syms = trim_blanks (join_tokens toks);
    val inner =
      (case (syms, rev syms) of
        (("<", _) :: _, (">", _) :: _) => tl (take (length syms - 1) syms)
      | _ => err pos "malformed mode tag");
    fun source piece =
      (case trim_blanks piece of
        [] => err pos "empty mode pattern in a tag"
      | ps => Input.source false (Symbol_Pos.content ps) (Symbol_Pos.range ps));
  in map source (split_commas 0 [] [] inner) end;

val tag = tag_tokens >> tag_sources;


(* rules *)

val pattern =
  Parse.input Parse.cartouche >> Cartouche || Parse.input Parse.string >> Literal;

val arrow = Parse.position (Parse.$$$ "\<Rightarrow>" || Parse.$$$ "=>") >> #2;

val action =
  Parse.$$$ "skip" >> K Skip || Parse.$$$ "error" >> K Fail || term >> Act;

val mode_op =
  Scan.optional
    (Parse.$$$ "," |--
      (Parse.$$$ "begin" |-- term >> Begin ||
       Parse.$$$ "push" |-- term >> Push ||
       Parse.$$$ "pop" >> K Pop ||
       Parse.input Parse.cartouche >> Stack))
    Keep;

val rule =
  pattern -- arrow -- action -- Scan.option (Parse.$$$ "when" |-- term) -- mode_op
    >> (fn ((((p, a), act), g), m) =>
      {pattern = p, arrow = a, action = act, guard = g, mode_op = m});

datatype body = Scope_Body of item list | Rule_Body of rule;

fun item toks =
  (Scan.optional tag [] --
    (Parse.$$$ "(" |-- Parse.enum1 "|" item --| Parse.$$$ ")" >> Scope_Body ||
     rule >> Rule_Body)
  >> (fn (tags, Scope_Body items) => Scope (tags, items)
       | (tags, Rule_Body r) => Rule (tags, r))) toks;


(* the command *)

fun make_spec ((((name, tok), clauses), defs), items) : spec =
  let
    val _ =
      (case duplicates (op =) (map clause_name clauses) of
        [] => ()
      | c :: _ => err (Binding.pos_of name) ("duplicate clause " ^ quote c));
    fun get f = get_first f clauses;
  in
    {name = name, tok = tok,
     modes = the_default No_Modes (get (fn Modes m => SOME m | _ => NONE)),
     start = get (fn Start s => SOME s | _ => NONE),
     exclusive = the_default [] (get (fn Exclusive e => SOME e | _ => NONE)),
     final = get (fn Final f => SOME f | _ => NONE),
     after = get (fn After a => SOME a | _ => NONE),
     newline = get (fn Newline n => SOME n | _ => NONE),
     defs = defs, items = items}
  end;

val spec =
  Parse.binding --| Parse.$$$ "::" -- Parse.input Parse.typ --
  Scan.repeat clause --
  Scan.optional (Parse.where_ |-- Parse.enum1 "|" definition) [] --
  (Parse.$$$ "rules" |-- Parse.enum1 "|" item) >> make_spec;

val options =
  Scan.optional (Parse.$$$ "(" |-- Parse.list1 (Parse.position Parse.name) --| Parse.$$$ ")")
    [];

(* the spec and, unless sketch, the tables and the lexer L_lex on them (in a context where
   the constants of the spec are no longer local) *)
fun lexer opts (spec: spec) =
  let
    val name = #name spec;
    val (sketch, opts') = List.partition (fn (n, _) => n = "sketch") opts;
  in
    Local_Theory.begin_nested #> snd #> lexer_cmd spec #> Local_Theory.end_nested #>
    (if null sketch then
      Lexer_Tables.tables_cmd opts' (Binding.suffix_name "_lex" name)
        (Binding.name_of name, Binding.pos_of name)
    else I)
  end;

val _ =
  Outer_Syntax.local_theory \<^command_keyword>\<open>lexer\<close>
    "define the classes, regexes, modes and rules of a lexer spec and its lexer"
    (options -- spec >> (fn (opts, spec) => lexer opts spec));

end;
