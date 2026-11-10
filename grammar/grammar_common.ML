(* shared by the grammar and parser commands: the surface syntax types,
   the grammar record and its morphism, name checks and registration,
   term builders, code-declaration helpers and per-step timing *)

signature GRAMMAR_COMMON =
sig
  datatype ann = Eq | Ge | Gt | Any

  datatype gsym =
      Lit of string * Position.T
    | Ref of string * Position.T
    | Tok of Input.source
    | Span of Position.T   (* \<open>@span\<close>: the span of the alternative's yield, a value *)

  datatype terminal_decl = Class of binding | Fixed of string * Input.source

  type alternative = (gsym * ann option) list * Input.source option
  type production_group = (binding * Input.source option) * alternative list

  (* \<open>precedence right "^" > left "*" "/"\<close>: tightest first; an item is a terminal's
     spelling or a \<open>(prec NAME)\<close>, \<open>!\<close> marks it strict; \<open>forbid p @ k right c\<close> *)
  type prec_item = (string * Position.T) * bool
  type prec_level = (string * Position.T) * prec_item list
  type forbid_decl =
    (string * Position.T) * int * (string * Position.T) * (string * Position.T) list
  type prec_decl =
    {chains: prec_level list list,
     forbids: forbid_decl list,
     alts: (string * Position.T) option list}   (*the \<open>(prec NAME)\<close> of each alternative*)

  type spec =
    {name: binding,
     tok_typ: Input.source option,
     terminals: terminal_decl list,
     productions: production_group list,
     prec: prec_decl option}

  val check_spec: spec -> unit

  (* the surface of a production before expansion (Grammar_Expand): a template
     instance \<open>P(a, \<dots>)\<close>, a parenthesised group, a postfix operator \<open>* + ?\<close> *)
  datatype item =
      Sym of gsym
    | App of (string * Position.T) * item list
    | Group of (item * ann option) list * Position.T
    | Rep of string * item * Position.T

  type salternative =
    ((item * ann option) list * Input.source option) * (string * Position.T) option
  (* \<open>((name, parameters), ascription), alternatives\<close>; parameters only for a template *)
  type sgroup =
    ((binding * (string * Position.T) list) * Input.source option) * salternative list
  (* \<open>open a b\<close>: a bare name that no local nonterminal, parameter or terminal class
     claims, and that exactly one opened grammar defines, is that grammar's \<open>a.X\<close> *)
  type surface =
    {name: binding,
     opens: (xstring * Position.T) list,
     tok_typ: Input.source option,
     terminals: terminal_decl list,
     groups: sgroup list,
     chains: prec_level list list,
     forbids: forbid_decl list}

  (* what expansion generated: the nonterminals with their identifiers, those that bind
     no value (an operator over symbols without values), the instances whose
     ascription has type variables, and the grammars whose templates were used *)
  type expansion =
    {generated: (string * string) list,
     silent: string list,
     patterns: string list,
     owners: string list}
  val no_expansion: expansion

  (** elaborated grammar **)
  datatype rsym =
      RN of string  (* non-terminal by name *)
    | RC of int     (* class terminal, binds a payload; indexes \<open>terminals\<close> *)
    | RT of int     (* fixed terminal, binds nothing; indexes \<open>terminals\<close> *)

  type prod =
    {no: int,
     lhs: string,
     rhs: (rsym * ann) list,
     action: term,
     span: bool,    (* \<open>@span\<close>: the action takes the yield's span first *)
     pos: Position.T}

  type nonterm =
    {no: int,
     binding: binding,
     carrier: typ,
     prods: int list}

  type rel_info =
    {preds: (string * term) list,
     intros: thm list,
     inducts: thm list,
     sound_thms: thm list}

  (* only on the record a backend is handed for a grammar with declarations:
     orig, the name of a nonterminal of gram_t in the grammar the user wrote; fresh, for
     the parser's start name; prods, the productions of gram_t for reports; counts, its
     numbers of productions and nonterminals *)
  type restricted =
    {orig: term,
     fresh: thm,
     prods: prod list lazy,
     counts: (int * int) lazy}

  type artifacts =
    {gram_t: term,
     gram_def: thm,
     decs: (string * term) list,
     rel: rel_info option,
     restricted: restricted option}

  (* the declarations over production numbers: chains of levels, loosest first, each
     level an associativity with its productions, and (p, k, kind, c) *)
  type prec_info =
    {chains: (string * (int * bool) list) list list,
     forbids: (int * int * string * int) list}

  type grammar =
    {name: binding,
     tokT: typ,
     tokenT: typ,
     start: string,
     nat_labels: bool,   (* the nonterminals are numbered (\<open>#no\<close>) in HOL, not named *)
     terminals: term Vector.vector,
     lit_names: (term * string) list,
     nonterms: nonterm Symtab.table,
     prods: prod list,
     prec: prec_info option,
     artifacts: artifacts option}

  type grammar_desc =
    {astT: typ,
     chT: typ,
     moreT: typ,
     isgT: typ,
     nameT: typ,
     tokenT: typ,
     wordT: typ,
     symT: typ,
     ptreeT: typ}

  val nonterms_list: grammar -> (string * nonterm) list   (*ordered by #no*)
  val morph_rel_info: morphism -> rel_info -> rel_info
  val put_artifacts: artifacts -> grammar -> grammar
  val put_prec: prec_info option -> grammar -> grammar
  val report_grammar: grammar -> grammar
  val orig_string: string -> string
  val artifacts_of: grammar -> artifacts

  val get_desc: grammar -> grammar_desc;
  (* a nonterminal in HOL terms: its name, or under \<open>nat_labels\<close> its number \<open>#no\<close> *)
  val name_typ: grammar -> typ
  val name_term: grammar -> string -> term
  val name_of_term: grammar -> term -> string
  (* the start of the augmented grammar, from the fresh name chosen on strings *)
  val fresh_term: grammar -> string -> term
  val nat_labels: bool Config.T

  (** helpers **)
  val mk_optionT: typ -> typ
  val mk_Some: typ -> term
  val mk_None: typ -> term
  val irel_term: ann -> term
  val string_of_ann: ann -> string
  val qualify_bind: binding -> string -> binding
  (* the name of a nonterminal in identifiers: a copy \<open>a.X\<close> of another grammar's
     nonterminal (composition by reference) binds as \<open>a_X\<close> *)
  val ident_of: string -> string
  (* a copy \<open>a.X\<close>: a qualifier before any template argument list *)
  val is_copy_name: string -> bool
  (* the names of the nonterminals in messages: a grammar's qualifier \<open>a.\<close> dropped
     (\<open>a.Atom\<close> as \<open>Atom\<close>, \<open>a.Block(b.Ty)\<close> as \<open>Block(Ty)\<close>) wherever no two
     nonterminals then show alike; the changed names only *)
  val display_names: Proof.context -> string list -> (string * string) list
  (* the identifier of a nonterminal of the grammar, from its binding *)
  val ident_in: grammar -> string -> string
  val carrier_of: grammar -> string -> typ
  val close_binders: Proof.context -> string list -> thm -> thm
  val timing: bool Config.T
  val timing_components: bool Config.T
  val timed: Proof.context -> string -> string -> ('a -> 'b) -> 'a -> 'b
  val when_timing: Proof.context -> (unit -> unit) -> unit
  (* PARALLEL_CASES tacs i: the goals i, ..., i + n - 1 by the n tactics, each solving
     its goal in a state of its own, in parallel *)
  val PARALLEL_CASES: (int -> tactic) list -> int -> tactic
  val profiled: Proof.context -> ('a -> 'b) -> 'a -> 'b

  (** code equations that reach the background theory (also inside a target) **)
  val def_axiom: local_theory -> binding * binding -> thm option
  val declare_code_global: {default: bool} -> thm list -> local_theory -> local_theory
  val declare_def_code_global: {default: bool} -> binding * binding -> thm ->
    local_theory -> local_theory

  (** name space **)
  val get_grammar_global: theory -> string -> grammar option
  val check_grammar: Proof.context -> xstring * Position.T -> string * grammar
  val register: binding -> grammar -> local_theory -> local_theory

end;

structure Grammar_Common: GRAMMAR_COMMON =
struct

datatype ann = Eq | Ge | Gt | Any;

datatype gsym =
    Lit of string * Position.T   (*quoted spelling, declared in the terminals block*)
  | Ref of string * Position.T   (*terminal class or nonterminal*)
  | Tok of Input.source          (*inline token value \<open>t\<close>*)
  | Span of Position.T;          (*\<open>@span\<close>*)

datatype terminal_decl = Class of binding | Fixed of string * Input.source;

type alternative = (gsym * ann option) list * Input.source option;
type production_group = (binding * Input.source option) * alternative list;

type prec_item = (string * Position.T) * bool;
type prec_level = (string * Position.T) * prec_item list;
type forbid_decl =
  (string * Position.T) * int * (string * Position.T) * (string * Position.T) list;
type prec_decl =
  {chains: prec_level list list,
   forbids: forbid_decl list,
   alts: (string * Position.T) option list};

type spec =
  {name: binding,
   tok_typ: Input.source option,
   terminals: terminal_decl list,
   productions: production_group list,
   prec: prec_decl option};

datatype item =
    Sym of gsym
  | App of (string * Position.T) * item list
  | Group of (item * ann option) list * Position.T
  | Rep of string * item * Position.T;

type salternative =
  ((item * ann option) list * Input.source option) * (string * Position.T) option;
type sgroup =
  ((binding * (string * Position.T) list) * Input.source option) * salternative list;
type surface =
  {name: binding,
   opens: (xstring * Position.T) list,
   tok_typ: Input.source option,
   terminals: terminal_decl list,
   groups: sgroup list,
   chains: prec_level list list,
   forbids: forbid_decl list};

type expansion =
  {generated: (string * string) list,
   silent: string list,
   patterns: string list,
   owners: string list};
val no_expansion: expansion = {generated = [], silent = [], patterns = [], owners = []};

fun check_spec ({terminals, productions, ...}: spec) =
  let
    fun class_name (Class b) = SOME (Binding.name_of b)
      | class_name (Fixed _) = NONE;
    val tnames = map_filter class_name terminals;
    val nnames = map (Binding.name_of o #1 o #1) productions;
    fun dup_error msg ds =
      error (msg ^ ": " ^ commas_quote ds);
    val _ =
      (case duplicates (op =) (tnames @ nnames) of
        [] => () | ds => dup_error "Duplicate terminal/nonterminal declaration(s)" ds);
    val _ =
      (case duplicates (op =)
          (map_filter (fn Fixed (s, _) => SOME s | _ => NONE) terminals) of
        [] => () | ds => dup_error "Duplicate fixed terminal(s)" ds);
    val _ =
      productions |> List.app (fn ((b, _), _) =>
        if Long_Name.is_qualified (Binding.name_of b) then
          error ("Nonterminal " ^ quote (Binding.name_of b) ^ ": a defined nonterminal has \
            \a plain name; a.X refers to the nonterminal X of an earlier grammar a" ^
            Position.here (Binding.pos_of b))
        else ());
    fun check_alt b ([], NONE) =
          error ("Empty alternative for " ^ quote (Binding.name_of b) ^
            ": give symbols or an action" ^ Position.here (Binding.pos_of b))
      | check_alt _ _ = ();
  in
    List.app (fn ((b, _), alts) => List.app (check_alt b) alts) productions
  end;


(** elaborated grammar **)

datatype rsym =
    RN of string
  | RC of int
  | RT of int;

type prod =
  {no: int, lhs: string, rhs: (rsym * ann) list, action: term, span: bool, pos: Position.T};

type nonterm =
  {no: int, binding: binding, carrier: typ, prods: int list};

(* the relation family of a grammar, as defined by \<open>grammar (relation)\<close> or
   Grammar_Defs.define_relation_of *)
type rel_info =
  {preds: (string * term) list,
   intros: thm list,
   inducts: thm list,
   sound_thms: thm list};

type restricted =
  {orig: term,
   fresh: thm,
   prods: prod list lazy,
   counts: (int * int) lazy};

(* constants and facts produced by the defining command, carried in the
   record so that nothing is ever looked up by name again *)
type artifacts =
  {gram_t: term,
   gram_def: thm,
   decs: (string * term) list,
   rel: rel_info option,
   restricted: restricted option};

(* \<open>(assoc, [(production, strict)])\<close> *)
type prec_info =
  {chains: (string * (int * bool) list) list list,
   forbids: (int * int * string * int) list};

type grammar =
  {name: binding,
   tokT: typ,
   tokenT: typ,   (* ground \<open>(tokT, 'ch, 'more) token_scheme\<close>, see \<open>get_desc\<close> *)
   start: string,
   nat_labels: bool,
   terminals: term Vector.vector,
   lit_names: (term * string) list,   (* token value of a Fixed terminal, its spelling *)
   nonterms: nonterm Symtab.table,
   prods: prod list,
   prec: prec_info option,
   artifacts: artifacts option};   (* NONE only during elaboration *)

type grammar_desc =
  {astT: typ,
   chT: typ,
   moreT: typ,
   isgT: typ,
   nameT: typ,
   tokenT: typ,
   wordT: typ,
   symT: typ,
   ptreeT: typ}

(* declaration order (\<^ML>\<open>Symtab.dest\<close> alone is alphabetical) *)
fun nonterms_list ({nonterms, ...}: grammar) =
  sort (int_ord o apply2 (#no o #2)) (Symtab.dest nonterms);

fun morph_rel_info phi ({preds, intros, inducts, sound_thms}: rel_info) =
  let
    val term = Morphism.term phi;
    val thm = Morphism.thm phi;
  in
    {preds = map (apsnd term) preds,
     intros = map thm intros,
     inducts = map thm inducts,
     sound_thms = map thm sound_thms}
  end;

fun morph_artifacts phi ({gram_t, gram_def, decs, rel, restricted}: artifacts) =
  {gram_t = Morphism.term phi gram_t,
   gram_def = Morphism.thm phi gram_def,
   decs = map (apsnd (Morphism.term phi)) decs,
   rel = Option.map (morph_rel_info phi) rel,
   restricted = restricted};

fun morph_grammar phi
    ({name, tokT, tokenT, start, nat_labels, terminals, lit_names, nonterms, prods, prec,
      artifacts}: grammar) =
  let
    val typ = Morphism.typ phi;
    val term = Morphism.term phi;
    fun morph_nt ({no, binding, carrier, prods}: nonterm) =
      {no = no, binding = Morphism.binding phi binding,
       carrier = typ carrier, prods = prods};
    fun morph_prod ({no, lhs, rhs, action, span, pos}: prod) =
      {no = no, lhs = lhs, rhs = rhs, action = term action, span = span, pos = pos};
  in
    {name = Morphism.binding phi name,
     tokT = typ tokT, tokenT = typ tokenT, start = start, nat_labels = nat_labels,
     terminals = Vector.map term terminals,
     lit_names = map (apfst term) lit_names,
     nonterms = Symtab.map (K morph_nt) nonterms,
     prods = map morph_prod prods,
     prec = prec,
     artifacts = Option.map (morph_artifacts phi) artifacts}
  end;

fun put_artifacts arts
    ({name, tokT, tokenT, start, nat_labels, terminals, lit_names, nonterms, prods, prec,
      artifacts = _}: grammar) : grammar =
  {name = name, tokT = tokT, tokenT = tokenT, start = start, nat_labels = nat_labels,
   terminals = terminals, lit_names = lit_names, nonterms = nonterms,
   prods = prods, prec = prec, artifacts = SOME arts};

fun put_prec prec
    ({name, tokT, tokenT, start, nat_labels, terminals, lit_names, nonterms, prods, prec = _,
      artifacts}: grammar) : grammar =
  {name = name, tokT = tokT, tokenT = tokenT, start = start, nat_labels = nat_labels,
   terminals = terminals, lit_names = lit_names, nonterms = nonterms,
   prods = prods, prec = prec, artifacts = artifacts};

(* the name a nonterminal of a restricted grammar comes from: \<open>orig_name\<close> on strings *)
fun orig_string s =
  let val cs = rev (raw_explode s) in
    if member (op =) cs "#" then implode (rev (drop 1 (drop_prefix (fn c => c <> "#") cs)))
    else s
  end;

(* for reports: the productions of the grammar the tables are built from *)
fun report_grammar (gr as {name, tokT, tokenT, start, nat_labels, terminals, lit_names,
    nonterms, prec, artifacts, ...}: grammar) : grammar =
  (case artifacts of
    SOME {restricted = SOME {prods, ...}, ...} =>
      {name = name, tokT = tokT, tokenT = tokenT, start = start, nat_labels = nat_labels,
       terminals = terminals, lit_names = lit_names, nonterms = nonterms,
       prods = Lazy.force prods, prec = prec, artifacts = artifacts}
  | _ => gr);

fun artifacts_of ({name, artifacts, ...}: grammar) =
  (case artifacts of
    SOME arts => arts
  | NONE =>
      raise Fail ("grammar " ^ quote (Binding.name_of name) ^
        ": no artifacts (record not registered by the defining command)"));

(* the token type is a ground \<open>('tok, 'ch, 'more) token_scheme\<close> fixed by the
   \<open>tokens\<close> clause *)
fun get_desc (gr: grammar) =
  let
    val {tokT, tokenT, nat_labels, ...} = gr;
    val nameT = if nat_labels then HOLogic.natT else HOLogic.stringT;

    val isgT = Type (\<^type_name>\<open>is_cfg_ext\<close>, [nameT, tokT, \<^typ>\<open>unit\<close>]);
    val (chT, moreT) =
      (case tokenT of
        Type (\<^type_name>\<open>Token.token_ext\<close>, [_, ch, more]) => (ch, more)
      | _ => raise Fail "get_desc: token type is not a token scheme");
    val wordT = HOLogic.listT tokenT;
    val astT = Type (\<^type_name>\<open>ast\<close>, [moreT, chT, nameT, tokT]);
    val symT = Type (\<^type_name>\<open>sym\<close>, [nameT, tokT]);
    val ptreeT = Type (\<^type_name>\<open>ptree\<close>, [moreT, chT, nameT, tokT]);
  in {nameT = nameT, isgT = isgT, chT = chT, moreT = moreT, tokenT = tokenT,
      wordT = wordT, astT = astT, symT = symT, ptreeT = ptreeT} end;


(** the nonterminals in HOL: their names, or their numbers under \<open>nat_labels\<close> **)

(* nonterminal no k is labelled 0 for k = 0 and k + 1 otherwise: 1 is never a label,
   since the default simpset rewrites \<open>1 :: nat\<close> to \<open>Suc 0\<close> (One_nat_def), and
   an equation over \<open>Nt 1\<close> would no longer match its goal; 0 and the numerals from 2
   on are simp normal forms *)
fun label_of_no k = if k = 0 then 0 else k + 1;
fun no_of_label n = if n = 0 then SOME 0 else if n >= 2 then SOME (n - 1) else NONE;

fun name_typ ({nat_labels, ...}: grammar) = if nat_labels then HOLogic.natT else HOLogic.stringT;

fun name_term ({nat_labels, nonterms, name, ...}: grammar) A =
  if not nat_labels then HOLogic.mk_string A
  else
    (case Symtab.lookup nonterms A of
      SOME {no, ...} => HOLogic.mk_number HOLogic.natT (label_of_no no)
    | NONE =>
        raise Fail ("grammar " ^ quote (Binding.name_of name) ^ ": no nonterminal " ^ quote A));

fun name_of_term ({nat_labels, nonterms, ...}: grammar) t =
  if not nat_labels then HOLogic.dest_string t
  else
    let val n = snd (HOLogic.dest_number t) in
      (case Option.mapPartial (fn k =>
          Symtab.get_first (fn (A, {no, ...}) => if no = k then SOME A else NONE) nonterms)
          (no_of_label n) of
        SOME A => A
      | NONE => raise TERM ("name_of_term: no nonterminal labelled " ^ string_of_int n, [t]))
    end;

(* the start of the augmented grammar: a name no nonterminal has *)
fun fresh_term ({nat_labels, nonterms, ...}: grammar) shn =
  if nat_labels then
    HOLogic.mk_number HOLogic.natT (label_of_no (Symtab.fold (fn _ => fn k => k + 1) nonterms 0))
  else HOLogic.mk_string shn;

val nat_labels = Attrib.setup_config_bool \<^binding>\<open>grammar_nat_labels\<close> (K false);


(** helpers **)

fun mk_optionT T = Type (\<^type_name>\<open>option\<close>, [T]);
fun mk_Some T = Const (\<^const_name>\<open>Some\<close>, T --> mk_optionT T);
fun mk_None T = Const (\<^const_name>\<open>None\<close>, mk_optionT T);

fun irel_term Eq = \<^term>\<open>Eq :: irel\<close>
  | irel_term Ge = \<^term>\<open>Ge :: irel\<close>
  | irel_term Gt = \<^term>\<open>Gt :: irel\<close>
  | irel_term Any = \<^term>\<open>Any :: irel\<close>;

fun string_of_ann Eq = "\<^sup>="
  | string_of_ann Ge = "\<^sup>\<ge>"
  | string_of_ann Gt = "\<^sup>>"
  | string_of_ann Any = "";

fun qualify_bind gram_b nm =
  Binding.qualify true (Binding.name_of gram_b) (Binding.name nm);

val ident_of = String.map (fn #"." => #"_" | c => c);

fun is_copy_name m =
  Long_Name.is_qualified
    (Substring.string (#1 (Substring.splitl (fn c => c <> #"(") (Substring.full m))));

fun ident_in (gram: grammar) A =
  (case Symtab.lookup (#nonterms gram) A of
    SOME {binding, ...} => Binding.name_of binding
  | NONE => ident_of A);

fun carrier_of (gram: grammar) A = #carrier (the (Symtab.lookup (#nonterms gram) A));

(* rebuild the outer \<And>-binders of a Goal.prove_sorry result, in the given order *)
fun close_binders ctxt names th =
  let
    val vars = Term.add_vars (Thm.prop_of th) [];
    val present =
      map_filter (fn nm => find_first (fn ((n, _), _) => n = nm) vars) names;
    val (fresh, _) = Variable.variant_fixes (map (#1 o #1) present) ctxt;
    val insts =
      map2 (fn (ixn, T) => fn f => ((ixn, T), Thm.cterm_of ctxt (Free (f, T))))
        present fresh;
    val th' = Thm.instantiate (TVars.empty, Vars.make insts) th;
  in fold_rev (fn (_, ct) => Thm.forall_intr ct) insts th' end;

(* per-step timings of the grammar and parser commands, \<open>[[grammar_timing = true]]\<close> shows them;
   \<open>[[grammar_profile = time]]\<close> (or \<open>allocations\<close>) additionally runs the parser's table
   evaluation under Poly/ML profiling and prints the report; \<open>grammar_timing_components\<close>
   (default off) lets the timed run of the parser re-evaluate the tables prefix by
   prefix, which costs several evaluations *)
val timing = Attrib.setup_config_bool \<^binding>\<open>grammar_timing\<close> (K false);
val profile = Attrib.setup_config_string \<^binding>\<open>grammar_profile\<close> (K "");
val timing_components =
  Attrib.setup_config_bool \<^binding>\<open>grammar_timing_components\<close> (K false);

fun timed ctxt prefix label f x =
  if Config.get ctxt timing then
    let val (t, y) = Timing.timing (fn () => f x) ()
    in writeln ("[" ^ prefix ^ "] " ^ label ^ ": " ^ Timing.message t); y end
  else f x;

(* goals i to i + n - 1, one tactic each: in a goal state of their own, in parallel.
   In the one state, each step of a case rebuilds the state with all the other
   cases. Each tactic has to solve its goal. If the goals have schematic variables,
   the tactics run in order in the one state *)
fun PARALLEL_CASES [] _ st = all_tac st
  | PARALLEL_CASES tacs i st =
      let val n = length tacs in
        if i < 1 orelse i + n - 1 > Thm.nprems_of st then Seq.empty
        else
          let val st' = Goal.restrict i n st in
            (case Par_Tactical.strip_goals st' of
              SOME goals =>
                let
                  fun solve (g, tac) =
                    (case SINGLE (tac 1) (Goal.init g) of
                      SOME r => if Thm.nprems_of r = 0 then SOME r else NONE
                    | NONE => NONE);
                  val results = Par_List.map solve (goals ~~ tacs);
                in
                  if forall is_some results then
                    Seq.map (Goal.unrestrict i)
                      (Par_Tactical.retrofit_tac {close = false} (rev (map the results)) st')
                  else Seq.empty
                end
            | NONE => EVERY (map (fn tac => SOLVED' tac i) tacs) st)
          end
      end;

(* a measurement that runs only under \<open>[[grammar_timing = true]]\<close> *)
fun when_timing ctxt f = if Config.get ctxt timing then f () else ();

(* \<open>PolyML.Profiling\<close> is not visible from Isabelle/ML, so the report is ML_Profiling's,
   with every entry *)
fun profiled ctxt f x =
  let val mode = Config.get ctxt profile
  in (ML_Profiling.check_mode mode; ML_Profiling.profile mode f x) end;

(* code equations of constants defined inside a target are declared on the
   background theory as well (a theory target's declaration reaches it
   already); inside a locale with assumptions the noted facts carry the
   locale predicate, so use the foundation axiom (def_axiom) or export by
   expanding local definitions only (export_unconditional) *)

fun def_axiom lthy (b, def_b) =
  let
    val thy = Proof_Context.theory_of lthy;
    val def_b' = if Binding.is_empty def_b then Thm.def_binding b else def_b;
    val name = Name_Space.full_name (Local_Theory.background_naming_of lthy) def_b';
    fun defines ax =
      (case try (Term.head_of o #1 o Logic.dest_equals o Thm.prop_of) ax of
        SOME (Const (c, _)) => Long_Name.base_name c = Binding.name_of b
      | _ => false);
  in
    (case try (Thm.axiom thy) name of
      SOME ax => if defines ax then SOME ax else NONE
    | NONE => NONE)
  end;

fun export_unconditional inner outer th =
  let
    (* Local_Defs.head_of_def, which is not exported *)
    val head_of_def =
      Term.dest_Free o Term.head_of o #1 o Logic.dest_equals o Term.strip_all_body;
    fun is_def ct =
      (case try (head_of_def o Thm.term_of) ct of
        NONE => false
      | SOME x =>
          (case try (Assumption.export_term inner outer) (Free x) of
            NONE => false
          | SOME u => not (Free x aconv u)));
    val defs = filter is_def (Assumption.local_assms_of inner outer);
    val th' =
      th |> Local_Defs.expand defs
      |> singleton (Variable.export inner outer)
      |> Drule.zero_var_indexes;
  in
    if null (Thm.hyps_of th') then th'
    else raise THM ("export_unconditional: assumption used", 0, [th])
  end;

fun declare_code_global {default} ths lthy =
  if Named_Target.is_theory lthy then lthy
  else Local_Theory.background_theory (fn thy =>
    let
      val ctxt0 = Proof_Context.init_global thy;
      fun export th =
        (case try (export_unconditional lthy ctxt0) th of
          SOME th' => th'
        | NONE => singleton (Proof_Context.export lthy ctxt0) th);
      val declare =
        if default then Code.declare_default_eqns_global else Code.declare_eqns_global;
    in
      declare (map (rpair true o export) ths) thy
      handle ERROR msg =>
        (if default then ()
         else warning ("code equation not declared on the background theory:\n" ^ msg);
         thy)
    end) lthy;

fun declare_def_code_global {default} (b, def_b) th lthy =
  declare_code_global {default = default} [the_default th (def_axiom lthy (b, def_b))] lthy;


(** name space **)

structure Data = Generic_Data
(
  type T = grammar Name_Space.table;
  val empty: T = Name_Space.empty_table "grammar";
  fun merge data: T = Name_Space.merge_tables data;
);

fun get_grammar_global thy = Name_Space.lookup (Data.get (Context.Theory thy));

fun check_grammar ctxt =
  Name_Space.check (Context.Proof ctxt) (Data.get (Context.Proof ctxt));

fun register b gr =
  Local_Theory.declaration
    {syntax = false, pervasive = false, pos = Binding.pos_of b}
    (fn phi => fn context =>
      Data.map
        (#2 o Name_Space.define context true
          (Morphism.binding phi b, morph_grammar phi gr))
        context);

(* an identifier followed by a dot, starting a name or after a non-identifier
   character, that names a grammar *)
fun display_names ctxt names =
  let
    fun is_id c = Char.isAlphaNum c orelse c = #"_" orelse c = #"'";
    fun quals [] _ acc = acc
      | quals (c :: cs) prev acc =
          if is_id c andalso not (is_id prev) then
            let
              val (w, rest) = chop_prefix is_id (c :: cs);
              val acc' = (case rest of #"." :: _ => insert (op =) (String.implode w) acc | _ => acc);
            in quals rest (List.last w) acc' end
          else quals cs c acc;
    val grams =
      fold (fn n => quals (String.explode n) #" ") names []
      |> filter (fn q => is_some (try (check_grammar ctxt) (q, Position.none)));
    fun is_gram q = member (op =) grams q;
    fun strip s =
      let
        fun go [] _ = []
          | go (c :: cs) prev =
              if is_id c andalso not (is_id prev) then
                let val (w, rest) = chop_prefix is_id (c :: cs) in
                  (case rest of
                    #"." :: rest' =>
                      if is_gram (String.implode w) then go rest' #"."
                      else w @ [#"."] @ go rest' #"."
                  | _ => w @ go rest (List.last w))
                end
              else c :: go cs c;
      in String.implode (go (String.explode s) #" ") end;
    val stripped = map (fn n => (n, strip n)) names;
    fun unique d = length (filter (fn (_, d') => d' = d) stripped) = 1;
  in filter (fn (n, d) => n <> d andalso unique d) stripped end;

end;
