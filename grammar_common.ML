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

  datatype terminal_decl = Class of binding | Fixed of string * Input.source

  type alternative = (gsym * ann option) list * Input.source option
  type production_group = (binding * Input.source option) * alternative list

  type spec =
    {name: binding,
     tok_typ: Input.source option,
     terminals: terminal_decl list,
     productions: production_group list}

  val check_spec: spec -> unit

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

  type artifacts =
    {gram_t: term,
     gram_def: thm,
     decs: (string * term) list,
     rel: rel_info option}

  type grammar =
    {name: binding,
     tokT: typ,
     tokenT: typ,
     start: string,
     terminals: term Vector.vector,
     lit_names: (term * string) list,
     nonterms: nonterm Symtab.table,
     prods: prod list,
     artifacts: artifacts option}

  type grammar_desc =
    {astT: typ,
     chT: typ,
     moreT: typ,
     isgT: typ,
     nameT: typ,
     tokenT: typ,
     wordT: typ}

  val nonterms_list: grammar -> (string * nonterm) list   (*ordered by #no*)
  val morph_rel_info: morphism -> rel_info -> rel_info
  val morph_grammar: morphism -> grammar -> grammar
  val put_artifacts: artifacts -> grammar -> grammar
  val artifacts_of: grammar -> artifacts

  val get_desc: grammar -> grammar_desc;

  (** helpers **)
  val mk_optionT: typ -> typ
  val mk_Some: typ -> term
  val mk_None: typ -> term
  val irel_term: ann -> term
  val string_of_ann: ann -> string
  val qualify_bind: binding -> string -> binding
  val carrier_of: grammar -> string -> typ
  val close_binders: Proof.context -> string list -> thm -> thm
  val timing: bool Config.T
  val profile: string Config.T
  val timing_components: bool Config.T
  val timed: Proof.context -> string -> string -> ('a -> 'b) -> 'a -> 'b
  val when_timing: Proof.context -> (unit -> unit) -> unit
  val profiled: Proof.context -> ('a -> 'b) -> 'a -> 'b

  (** code equations that reach the background theory (also inside a target) **)
  val def_axiom: local_theory -> binding * binding -> thm option
  val export_unconditional: Proof.context -> Proof.context -> thm -> thm
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
  | Tok of Input.source;         (*inline token value \<open>t\<close>*)

datatype terminal_decl = Class of binding | Fixed of string * Input.source;

type alternative = (gsym * ann option) list * Input.source option;
type production_group = (binding * Input.source option) * alternative list;

type spec =
  {name: binding,
   tok_typ: Input.source option,
   terminals: terminal_decl list,
   productions: production_group list};

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
  {no: int, lhs: string, rhs: (rsym * ann) list, action: term, pos: Position.T};

type nonterm =
  {no: int, binding: binding, carrier: typ, prods: int list};

(* the relation family of a grammar, as defined by \<open>grammar (relation)\<close> or
   Grammar_Defs.define_relation_of *)
type rel_info =
  {preds: (string * term) list,
   intros: thm list,
   inducts: thm list,
   sound_thms: thm list};

(* constants and facts produced by the defining command, carried in the
   record so that nothing is ever looked up by name again *)
type artifacts =
  {gram_t: term,
   gram_def: thm,
   decs: (string * term) list,
   rel: rel_info option};

type grammar =
  {name: binding,
   tokT: typ,
   tokenT: typ,   (* ground \<open>(tokT, 'ch, 'more) token_scheme\<close>, see \<open>get_desc\<close> *)
   start: string,
   terminals: term Vector.vector,
   lit_names: (term * string) list,   (* token value of a Fixed terminal, its spelling *)
   nonterms: nonterm Symtab.table,
   prods: prod list,
   artifacts: artifacts option};   (* NONE only during elaboration *)

type grammar_desc =
  {astT: typ,
   chT: typ,
   moreT: typ,
   isgT: typ,
   nameT: typ,
   tokenT: typ,
   wordT: typ}

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

fun morph_artifacts phi ({gram_t, gram_def, decs, rel}: artifacts) =
  {gram_t = Morphism.term phi gram_t,
   gram_def = Morphism.thm phi gram_def,
   decs = map (apsnd (Morphism.term phi)) decs,
   rel = Option.map (morph_rel_info phi) rel};

fun morph_grammar phi
    ({name, tokT, tokenT, start, terminals, lit_names, nonterms, prods,
      artifacts}: grammar) =
  let
    val typ = Morphism.typ phi;
    val term = Morphism.term phi;
    fun morph_nt ({no, binding, carrier, prods}: nonterm) =
      {no = no, binding = Morphism.binding phi binding,
       carrier = typ carrier, prods = prods};
    fun morph_prod ({no, lhs, rhs, action, pos}: prod) =
      {no = no, lhs = lhs, rhs = rhs, action = term action, pos = pos};
  in
    {name = Morphism.binding phi name,
     tokT = typ tokT, tokenT = typ tokenT, start = start,
     terminals = Vector.map term terminals,
     lit_names = map (apfst term) lit_names,
     nonterms = Symtab.map (K morph_nt) nonterms,
     prods = map morph_prod prods,
     artifacts = Option.map (morph_artifacts phi) artifacts}
  end;

fun put_artifacts arts
    ({name, tokT, tokenT, start, terminals, lit_names, nonterms, prods,
      artifacts = _}: grammar) : grammar =
  {name = name, tokT = tokT, tokenT = tokenT, start = start,
   terminals = terminals, lit_names = lit_names, nonterms = nonterms,
   prods = prods, artifacts = SOME arts};

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
    val {tokT, tokenT, ...} = gr;
    val nameT = \<^typ>\<open>string\<close>;

    val isgT = Type (\<^type_name>\<open>is_cfg_ext\<close>, [nameT, tokT, \<^typ>\<open>unit\<close>]);
    val (chT, moreT) =
      (case tokenT of
        Type (\<^type_name>\<open>Token.token_ext\<close>, [_, ch, more]) => (ch, more)
      | _ => raise Fail "get_desc: token type is not a token scheme");
    val wordT = HOLogic.listT tokenT;
    val astT = Type (\<^type_name>\<open>ast\<close>, [moreT, chT, nameT, tokT]);
  in {nameT = nameT, isgT = isgT, chT = chT, moreT = moreT, tokenT = tokenT,
      wordT = wordT, astT = astT} end;


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

end;
