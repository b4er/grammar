(* Author: Basil Fürer *)

(* outer syntax of the grammar command: the specification as written (terminals,
   precedence declarations, productions with semantic actions), handed to
   Grammar_Command.grammar_cmd *)

structure Grammar_Syntax: sig end =
struct

open Grammar_Common Grammar_Command;

val annotation =
  (Parse.control -- (Parse.not_eof >> Token.content_of) :|--
    (fn (ctl, s) =>
      if #1 (#name ctl) = "sup" andalso null (#body ctl) then
        (case s of
          "=" => Scan.succeed Eq
        | "\<ge>" => Scan.succeed Ge
        | ">" => Scan.succeed Gt
        | _ => Scan.fail)
      else Scan.fail)) ||
  Parse.$$$ "^=" >> K Eq ||
  Parse.$$$ "^>=" >> K Ge ||
  Parse.$$$ "^>" >> K Gt;

val arrow_action =
  (Parse.$$$ "\<Rightarrow>" || Parse.$$$ "=>") |-- Parse.input Parse.term;

val prec_mark =
  Parse.$$$ "(" |-- Parse.reserved "prec" |-- Parse.position Parse.name --| Parse.$$$ ")";

(* \<open>P(\<close> is an instance only when the parenthesis follows the name directly:
   \<open>A (B C)*\<close> is \<open>A\<close> and a group *)
fun adjacent (n, pos) ppos =
  (case (Position.offset_of pos, Position.offset_of ppos) of
    (SOME i, SOME j) => i + length (Symbol.explode n) = j
  | _ => true);

fun operators it =
  Scan.repeat (Parse.position (Parse.$$$ "*" || Parse.$$$ "+" || Parse.$$$ "?"))
    >> (fn ops => fold (fn (opr, pos) => fn it => Rep (opr, it, pos)) ops it);

fun atom toks =
  (Parse.position (Args.$$$ "@") --| Parse.reserved "span" >> (Sym o Span o #2) ||
   Parse.position Parse.string >> (Sym o Lit) ||
   Parse.input Parse.cartouche >> (Sym o Tok) ||
   Parse.position (Parse.$$$ "(") -- Scan.unless (Parse.reserved "prec") (Scan.repeat1 annotated)
     --| Parse.$$$ ")" >> (fn ((_, pos), its) => Group (its, pos)) ||
   Parse.position Parse.name :|-- (fn np =>
     Scan.optional
       (Parse.position (Parse.$$$ "(") :|-- (fn (_, ppos) =>
          if adjacent np ppos then Parse.enum1 "," item --| Parse.$$$ ")" >> SOME
          else Scan.fail))
       NONE
     >> (fn NONE => Sym (Ref np) | SOME args => App (np, args)))) toks
and item toks = (atom :|-- operators) toks
and annotated toks = (item -- Scan.option annotation) toks;

(* an alternative with its \<open>(prec NAME)\<close> *)
val alternative : salternative parser =
  Scan.repeat1 annotated -- Scan.option prec_mark -- Scan.option arrow_action
    >> (fn ((syms, mark), action) => ((syms, action), mark)) ||
  Scan.option prec_mark -- arrow_action >> (fn (mark, a) => (([], SOME a), mark));

val terminal_decl : terminal_decl parser =
  Parse.string --| Parse.$$$ "=" -- Parse.input Parse.term >> Fixed ||
  Parse.binding >> Class;

val production_group : sgroup parser =
  Parse.binding --
    Scan.optional (Parse.$$$ "(" |-- Parse.enum1 "," (Parse.position Parse.name) --| Parse.$$$ ")") [] --
    Scan.option (Parse.$$$ "::" |-- Parse.input Parse.typ) --|
    Parse.$$$ "=" -- Parse.enum1 "|" alternative;

val option_name : gram_opt parser =
  Parse.position Parse.name >> (fn (s, pos) =>
    if s = "relation" then Opt_Relation
    else error ("Unknown grammar option: " ^ quote s ^ Position.here pos));

val options_parser =
  Parse.$$$ "(" |-- Parse.enum1 "," option_name --| Parse.$$$ ")";

(* not keywords, so that no grammar loses a name: every word here is read in place;
   Args.$$$ since `open` is a keyword of Pure *)
val assoc_names = ["left", "right", "nonassoc", "open", "list"];

val prec_name =
  Scan.unless (Parse.reserved "precedence" || Parse.reserved "forbid" || Args.$$$ ">")
    (Parse.position Parse.name);

val prec_item : Grammar_Common.prec_item parser =
  prec_name -- Scan.optional (Args.$$$ "!" >> K true) false;

val prec_level : Grammar_Common.prec_level parser =
  (Scan.first (map (Parse.position o Args.$$$) assoc_names) ||
   Parse.position Parse.name :|-- (fn (a, pos) =>
     error ("precedence: " ^ quote a ^ " is not one of " ^ commas assoc_names ^ Position.here pos)))
  -- Scan.repeat1 prec_item;

val prec_chain = prec_level -- Scan.repeat (Args.$$$ ">" |-- prec_level) >> op ::;

val forbid_decl : Grammar_Common.forbid_decl parser =
  prec_name --| Args.$$$ "@" -- Parse.nat -- Parse.position Parse.name -- Scan.repeat1 prec_name
    >> (fn (((p, k), kind), cs) => (p, k, kind, cs));

datatype prec_line =
    Prec_Line of Grammar_Common.prec_level list
  | Forbid_Line of Grammar_Common.forbid_decl;

val prec_lines =
  Scan.repeat
    (Parse.reserved "precedence" |-- prec_chain >> Prec_Line ||
     Parse.reserved "forbid" |-- forbid_decl >> Forbid_Line);

val grammar_parser =
  Scan.optional options_parser [] --
  Parse.binding --| Parse.$$$ "=" --
  Scan.optional (Args.$$$ "open" |-- Scan.repeat1 (Scan.unless
    (Parse.reserved "precedence" || Parse.reserved "forbid") (Parse.position Parse.name))) [] --
  Scan.option (Parse.$$$ "tokens" |-- Parse.input Parse.typ) --
  Scan.optional (Parse.$$$ "terminals" |-- Parse.and_list1 terminal_decl) [] --
  prec_lines --
  (Parse.$$$ "productions" |-- Parse.and_list1 production_group);

val _ =
  Outer_Syntax.local_theory \<^command_keyword>\<open>grammar\<close>
    "validate a grammar spec: parse, type-check semantic actions and register the \
    \resolved grammar. Always defines the grammar constant and the per-nonterminal \
    \decoders. Option (relation) also defines the inductive relation family \
    \(slower)."
    (grammar_parser >> (fn ((((((opts, name), opens), ttyp), ts), lines), gs) =>
      grammar_surface_cmd opts
        {name = name, opens = opens, tok_typ = ttyp, terminals = ts, groups = gs,
         chains = map_filter (fn Prec_Line c => SOME c | _ => NONE) lines,
         forbids = map_filter (fn Forbid_Line f => SOME f | _ => NONE) lines}));

end;
