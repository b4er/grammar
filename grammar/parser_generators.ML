(* Author: Basil Fürer, Dmitriy Traytel *)

(* the generic `parser` command.  A backend contributes the body of the parse
   constant, its sound/complete theorems and tactics for its own premises;
   the decoder totality premise is discharged here (Parser_Dec_Total), the
   relational forms go through Parser_Rel_Bridge, unclaimed premises stay as
   assumptions.

   emitted: `<parse>.sound_lang` / `.complete_lang` (against \<open>ilang G\<close>) and
   `<parse>.sound` / `.complete` (against the start relation, when the
   grammar has one and the backend relational forms; else the same).

   `parser p for G (A)` with A not the start of G: an entry.  The backend
   builds from `G\<lparr>istart := ''A''\<rparr>` (the record it is handed says so, see
   entry_grammar); everything else is G's: the decoders, the relation family,
   and the decoder and bridge lemmas, shared by the entries of one command *)

signature PARSER_GENERATORS =
sig
  (* gram: the grammar the parser starts from; for an entry its start is the
     entry's and its gram_t \<open>G\<lparr>istart := ''A''\<rparr>\<close> (see entry_grammar);
     options: the names in \<open>parser (\<dots>)\<close> other than the generator's, e.g.
     "diagnostics";
     errors: the entry's \<open>errors\<close> block;
     recover: the error token named by the entry's \<open>recover\<close>;
     repair: the entry's \<open>repair\<close>: its token function and the terminals to avoid;
     on_error_reduce: the nonterminals named by the entry's \<open>on_error_reduce\<close>;
     token_info: the term of the entry's \<open>token_info\<close> *)
  datatype sentence =
    Symbols of (string * int option) list
  | Word of string
  datatype msg_key = By_State | By_Token | By_Shift
  type error_message = {sentence: sentence, key: msg_key, text: string}
  type repair = {token: string option, avoid: string list}

  type build_input =
   {gram: Grammar_Common.grammar,
    parse_bind: binding,
    shn: string,
    options: string list,
    errors: error_message list,
    recover: string option,
    repair: repair option,
    on_error_reduce: string list,
    token_info: string option}

  type post_input =
   {parse_const: term,
    parse_def_th: thm}

  (* checks: the equations `check G Shn = value` the backend evaluated while
     building, handed back to its discharge_tac;
     recover: the binding of the parser with recovery and its error token *)
  type build_output =
   {parse_body: term,
    post: post_input -> local_theory -> local_theory,
    checks: thm list,
    recover: (binding * term) option}

  (* gram: as in build_input, the entry's record *)
  type discharge_input =
   {gram: Grammar_Common.grammar,
    parse_bind: binding,
    shn: string,
    checks: thm list}

  (* the theorems of \<open>parser (ast)\<close>, whose decoder is \<open>Some\<close>: completeness against the
     language, soundness and exact completeness against the trees, and the tree of a
     word without the error token *)
  type ast_thms = {complete_lang: thm, sound: thm, complete: thm, no_error: thm}

  (* discharge_tac: SOME on a premise the backend claims (a failing tactic
     warns), NONE on premises left as assumptions; rel_sound_thm /
     rel_complete_thm: stated against a relation P of the start symbol;
     ast_thms: for \<open>parser (ast)\<close>, NONE if the backend has no such mode *)
  type parser_generator =
   {build_parse:   build_input -> local_theory -> build_output * local_theory,
    sound_thm:     thm,
    complete_thm:  thm,
    rel_sound_thm:    thm option,
    rel_complete_thm: thm option,
    no_error_thm:     thm option,
    ast_thms:         ast_thms option,
    discharge_tac: discharge_input -> Proof.context -> term -> (int -> tactic) option}

  (* precedence declarations, from LR_Prec_Parse: `prepare parse_b shn gr` defines the
     restricted grammar of the entry gr; gram replaces gr for the backend, inst fixes the
     grammar and the declarations in the theorems below, whose premises discharge
     claims first *)
  type prec_output =
   {gram: Grammar_Common.grammar,
    inst: Proof.context -> thm -> thm,
    discharge: Proof.context -> term -> (int -> tactic) option}

  type prec_hook =
   {prepare: binding -> string -> Grammar_Common.grammar -> local_theory ->
      prec_output * local_theory,
    sound_lang: thm,
    complete_lang: thm,
    sound: thm,
    complete: thm,
    no_error: thm,
    ast: ast_thms}

  type result =
   {parse_const: term,
    parse_def: thm,
    sound: thm,
    complete: thm,
    sound_lang: thm,
    complete_lang: thm}

  val register: string -> parser_generator -> theory -> theory
  val set_prec_hook: prec_hook -> theory -> theory
  val set_default: string -> theory -> theory
  val default: theory -> string option

  (* `NAME for G (A)`; NONE: the start of G *)
  type entry = binding * (xstring * Position.T) * (string * Position.T) option

  val define: string option -> binding -> xstring * Position.T -> local_theory
    -> result * local_theory
  val define_entries: string option -> entry list -> local_theory
    -> result list * local_theory
  val define_cmd: string option -> entry list -> local_theory -> local_theory

  (** helpers reusable by backends **)
  val eval_tac: Proof.context -> int -> tactic
end;

structure Parser_Generators: PARSER_GENERATORS =
struct

(** registry **)

(* a sentence of an \<open>errors\<close> block: its terminals, each with an optional column, or a
   word as a term *)
datatype sentence =
  Symbols of (string * int option) list
| Word of string;

datatype msg_key = By_State | By_Token | By_Shift;

type error_message = {sentence: sentence, key: msg_key, text: string};

type repair = {token: string option, avoid: string list};

type build_input =
 {gram: Grammar_Common.grammar,
  parse_bind: binding,
  shn: string,
  options: string list,
  errors: error_message list,
  recover: string option,
  repair: repair option,
  on_error_reduce: string list,
  token_info: string option};

type post_input =
 {parse_const: term,
  parse_def_th: thm};

type build_output =
 {parse_body: term,
  post: post_input -> local_theory -> local_theory,
  checks: thm list,
  recover: (binding * term) option};

type discharge_input =
 {gram: Grammar_Common.grammar,
  parse_bind: binding,
  shn: string,
  checks: thm list};

type ast_thms = {complete_lang: thm, sound: thm, complete: thm, no_error: thm};

type parser_generator =
 {build_parse:   build_input -> local_theory -> build_output * local_theory,
  sound_thm:     thm,
  complete_thm:  thm,
  rel_sound_thm:    thm option,
  rel_complete_thm: thm option,
  no_error_thm:     thm option,
  ast_thms:         ast_thms option,
  discharge_tac: discharge_input -> Proof.context -> term -> (int -> tactic) option};

type prec_output =
 {gram: Grammar_Common.grammar,
  inst: Proof.context -> thm -> thm,
  discharge: Proof.context -> term -> (int -> tactic) option};

type prec_hook =
 {prepare: binding -> string -> Grammar_Common.grammar -> local_theory ->
    prec_output * local_theory,
  sound_lang: thm,
  complete_lang: thm,
  sound: thm,
  complete: thm,
  no_error: thm,
  ast: ast_thms};

type result =
 {parse_const: term,
  parse_def: thm,
  sound: thm,
  complete: thm,
  sound_lang: thm,
  complete_lang: thm};

structure Data = Theory_Data
(
  type T =
    {gens: parser_generator Symtab.table, default: string option, prec: prec_hook option};
  val empty: T = {gens = Symtab.empty, default = NONE, prec = NONE};
  fun merge ({gens = g1, default = d1, prec = p1}, {gens = g2, default = d2, prec = p2}): T =
    {gens = Symtab.merge (K true) (g1, g2),
     default = (case d2 of NONE => d1 | _ => d2),
     prec = (case p2 of NONE => p1 | _ => p2)};
);

(* registering a backend does not change the default *)
fun register nm gen =
  Data.map (fn {gens, default, prec} =>
    {gens = Symtab.update (nm, gen) gens, default = default, prec = prec});

fun set_prec_hook hook =
  Data.map (fn {gens, default, ...} => {gens = gens, default = default, prec = SOME hook});

fun registered thy = Symtab.keys (#gens (Data.get thy));
fun default thy = #default (Data.get thy);

fun set_default nm thy =
  (if Symtab.defined (#gens (Data.get thy)) nm then ()
   else error ("Unknown parser generator " ^ quote nm ^
     "; registered: " ^ commas_quote (registered thy));
   Data.map (fn {gens, prec, ...} => {gens = gens, default = SOME nm, prec = prec}) thy);

fun get thy nm =
  (case Symtab.lookup (#gens (Data.get thy)) nm of
    SOME g => g
  | NONE =>
      error ("Unknown parser generator " ^ quote nm ^
        "; registered: " ^ commas_quote (registered thy)));

fun resolve_generator thy NONE =
      (case default thy of
        SOME nm => (nm, get thy nm)
      | NONE =>
          error "No parser generator specified and no default set; \
            \use \<open>parser (GEN) ...\<close> or Parser_Generators.set_default")
  | resolve_generator thy (SOME nm) = (nm, get thy nm);


(** shared helpers **)

fun pick_fresh_shn (gr: Grammar_Common.grammar) =
  let
    val nts = map fst (Grammar_Common.nonterms_list gr);
    fun pick n =
      let val cand = replicate_string (n + 1) "!"
      in if member (op =) nts cand then pick (n + 1) else cand end;
  in pick 0 end;

fun eval_tac ctxt =
  let val conv = Code_Runtime.dynamic_holds_conv
  in
    CONVERSION (Conv.params_conv ~1 (Conv.concl_conv ~1 o conv) ctxt) THEN'
    resolve_tac ctxt [@{thm TrueI}]
  end;


(** discharging obligations **)

(* discharge every premise `lemma` matches by implies_elim; OF/RS would lift
   the lemma's \<And>-binders over the premise's and leave an `?wa t` residue *)
fun discharge_by_lemma ctxt lemma th =
  let
    val pat = Thm.cprop_of lemma;
    fun matches prem = try Thm.first_order_match (pat, Thm.cterm_of ctxt prem);
    fun go th =
      (case get_index matches (Thm.prems_of th) of
        NONE => th
      | SOME (i, inst) =>
          th |> Drule.rotate_prems i
             |> (fn th' => Thm.implies_elim th' (Thm.instantiate inst lemma))
             |> Drule.rotate_prems (~ i)
             |> go);
  in go th end;

(* does a premise mention one of the decoders? *)
fun mentions_dec dec_names p =
  Term.exists_Const (fn (c, _) => member (op =) dec_names c) p;

(* the decoder-totality premise: any premise mentioning a decoder; the lemma
   is proved on first demand *)
fun discharge_dec_total ctxt gram_name dec_names dec_total th =
  if not (exists (mentions_dec dec_names) (Thm.prems_of th)) then th
  else
    (case Exn.result Lazy.force dec_total of
      Exn.Res tot =>
        let val th' = discharge_by_lemma ctxt tot th in
          if Thm.nprems_of th' = Thm.nprems_of th then
            (warning ("parser: decoder-totality lemma for \<open>" ^ gram_name ^
               "\<close> matches no premise; keeping the decoder premise as an \
               \assumption");
             th)
          else th'
        end
    | Exn.Exn exn =>
        if Exn.is_interrupt exn then Exn.reraise exn
        else
          (warning ("parser: could not prove decoder totality for \<open>" ^
             gram_name ^ "\<close>: " ^ Runtime.exn_message exn ^
             "; keeping the decoder premise as an assumption");
           th));

fun try_prove ctxt prop tac =
  SOME (Goal.prove_sorry ctxt [] [] prop (K (HEADGOAL tac)))
  handle ERROR _ => NONE | THM _ => NONE | TYPE _ => NONE | Fail _ => NONE;

(* proofs memoised per premise: the same \<open>mdet\<close> premise occurs in several
   of the emitted theorems *)
fun discharge_prover ctxt discharge =
  let
    val cache = Synchronized.var "parser_discharge" (Termtab.empty: thm Termtab.table);
    fun prove prop =
      (case discharge prop of
        NONE => @{thm asm_rl}
      | SOME tac =>
          (case try_prove ctxt prop tac of
            SOME p => p
          | NONE =>
              (warning ("parser: could not discharge \<open>" ^
                  Syntax.string_of_term ctxt prop ^ "\<close>\
                 \; keeping it as an assumption");
               @{thm asm_rl})));
    fun proof_for prop =
      (case Termtab.lookup (Synchronized.value cache) prop of
        SOME p => p
      | NONE =>
          let val p = prove prop
          in Synchronized.change cache (Termtab.update (prop, p)); p end);
  in proof_for end;

fun discharge_via_tac proof_for th = th OF map proof_for (Thm.prems_of th);

(* fix the schematic relation P to the grammar's start relation *)
fun instantiate_P ctxt P th =
  (case filter (fn ((n, _), _) => n = "P") (Term.add_vars (Thm.prop_of th) []) of
    [(ixn, T)] =>
      Drule.instantiate_normalize
        (TVars.empty, Vars.make [((ixn, T), Thm.cterm_of ctxt P)]) th
  | _ => raise Fail "parser: relational theorem without a unique schematic P");

(* both bridge premises must go *)
fun discharge_bridges ctxt dec_names ({dec_sound, rel_dec, ...}: Parser_Rel_Bridge.bridge) th =
  let
    val th' = th |> discharge_by_lemma ctxt dec_sound |> discharge_by_lemma ctxt rel_dec;
  in
    if exists (mentions_dec dec_names) (Thm.prems_of th') then
      raise Fail "relation bridge lemma matches no premise"
    else th'
  end;


(** the `parser` command **)

type entry = binding * (xstring * Position.T) * (string * Position.T) option;

(* the parser's own name is checked before anything is defined *)
fun check_parse_binding lthy parse_b =
  let
    val thy = Proof_Context.theory_of lthy;
    val full = Local_Theory.full_name lthy parse_b;
    val nm = Binding.name_of parse_b;
    val here = Position.here (Binding.pos_of parse_b);
  in
    if is_some (Grammar_Common.get_grammar_global thy full) then
      error ("parser " ^ quote nm ^ ": name already used by grammar " ^ quote nm ^ here)
    else if Sign.declared_const thy full then
      error ("parser " ^ quote nm ^ ": constant " ^ quote full ^ " already exists" ^ here)
    else ()
  end;

(* the entries of a command, before anything is defined: names, starts, and one
   grammar for all *)
fun check_entries lthy (entries: entry list) =
  let
    fun check (parse_b, gram_ref, start_opt) =
      let
        val _ = check_parse_binding lthy parse_b;
        val (_, gr) = Grammar_Common.check_grammar lthy gram_ref;
        val start =
          (case start_opt of
            NONE => #start gr
          | SOME (A, pos) =>
              if Symtab.defined (#nonterms gr) A then A
              else
                error ("parser " ^ quote (Binding.name_of parse_b) ^ ": " ^ quote A ^
                  " is not a nonterminal of grammar " ^ quote (Binding.name_of (#name gr)) ^
                  " (nonterminals: " ^
                  commas_quote (map fst (Grammar_Common.nonterms_list gr)) ^ ")" ^
                  Position.here pos));
      in (parse_b, gr, start) end;
    val checked = map check entries;
    val _ =
      fold (fn (b, _, _) => fn seen =>
          let val nm = Binding.name_of b in
            if member (op =) seen nm then
              error ("parser " ^ quote nm ^ ": declared twice in one command" ^
                Position.here (Binding.pos_of b))
            else nm :: seen
          end) checked [];
    (* one grammar per command: the entries share its lemmas *)
    val key = #gram_t o Grammar_Common.artifacts_of;
    val _ =
      (case checked of
        (_, gr0, _) :: _ =>
          ListPair.app (fn ((b, gr, _), (_, (g, pos), _)) =>
              if key gr aconv key gr0 then ()
              else
                error ("parser " ^ quote (Binding.name_of b) ^ ": grammar " ^ quote g ^
                  " is not the grammar " ^ quote (Binding.name_of (#name gr0)) ^
                  " of the first entry; the entries of one command are for one grammar" ^
                  " (use a second parser command)" ^ Position.here pos))
            (checked, entries)
      | [] => ());
  in checked end;

(* an entry from a nonterminal A that is not the start of G: the backend builds
   from G's record with start A and gram_t the term

     G\<lparr>istart := ''A''\<rparr>

   (not a constant: within the command a new constant is a fixed variable, which
   the evaluation of the tables cannot read), with gram_def
   `G\<lparr>istart := ''A''\<rparr> \<equiv> is_cfg.make ps ''A'' 0` over G's productions ps.
   `transport` rewrites the premises of a theorem about that term which only read
   its productions and its start (wf_ptree_iprods_cong, ast_of_iprods_cong) to
   premises about G, where G's decoder and bridge lemmas discharge them *)
fun entry_grammar (gr: Grammar_Common.grammar) A ctxt =
  let
    val {gram_t, gram_def, decs, rel, ...} = Grammar_Common.artifacts_of gr;
    val {isgT, ...} = Grammar_Common.get_desc gr;
    val upd_c =
      Const (\<^const_name>\<open>is_cfg.istart_update\<close>,
        (Grammar_Common.name_typ gr --> Grammar_Common.name_typ gr) --> isgT --> isgT);
    val eg_t =
      upd_c $ Term.absdummy (Grammar_Common.name_typ gr) (Grammar_Common.name_term gr A) $ gram_t;

    fun prove ctxt' prop =
      Goal.prove_sorry ctxt [] [] (HOLogic.mk_Trueprop prop)
        (fn {context, ...} => HEADGOAL (simp_tac (put_simpset (simpset_of ctxt') context)));
    val basic = put_simpset HOL_basic_ss ctxt;
    val (make_c, ps) =
      (case Term.strip_comb (snd (Logic.dest_equals (Thm.prop_of gram_def))) of
        (make, [ps, _, _]) => (make, ps)
      | _ => raise Fail "entry_grammar: grammar definition");
    val zero = \<^term>\<open>0 :: nat\<close>;
    val make_eq =
      prove (basic |> Simplifier.add_simps (gram_def :: @{thms is_cfg.make_def is_cfg.update_convs refl}))
        (HOLogic.mk_eq (eg_t, make_c $ ps $ Grammar_Common.name_term gr A $ zero));
    fun sel c T t = Const (c, isgT --> T) $ t;
    val sel_ctxt = basic |> Simplifier.add_simps (make_eq :: @{thms is_cfg.make_def is_cfg.select_convs});
    val iprodsT = fastype_of ps;
    val iprods_eq =
      prove ctxt
        (HOLogic.mk_eq
          (sel \<^const_name>\<open>iprods\<close> iprodsT eg_t, sel \<^const_name>\<open>iprods\<close> iprodsT gram_t));
    val istart_eq =
      prove sel_ctxt
        (HOLogic.mk_eq (sel \<^const_name>\<open>istart\<close> (Grammar_Common.name_typ gr) eg_t,
          Grammar_Common.name_term gr A));
    val istart_ind_eq =
      prove sel_ctxt (HOLogic.mk_eq (sel \<^const_name>\<open>istart_ind\<close> HOLogic.natT eg_t, zero));
    val transport_ss =
      simpset_of (basic |> Simplifier.add_simps
        [@{thm wf_ptree_iprods_cong} OF [iprods_eq], @{thm ast_of_iprods_cong} OF [iprods_eq],
         istart_eq, istart_ind_eq]);
    fun transport ctxt' =
      Conv.fconv_rule
        (Conv.prems_conv ~1 (Simplifier.full_rewrite (put_simpset transport_ss ctxt')));
    (* the conclusion of an (ast) soundness theorem: a tree of A in G *)
    fun transport_concl ctxt' =
      Conv.fconv_rule
        (Conv.concl_conv ~1 (Simplifier.full_rewrite (put_simpset transport_ss ctxt')));

    val {name, tokT, tokenT, nat_labels, terminals, lit_names, nonterms, prods, prec, ...} = gr;
    val egr: Grammar_Common.grammar =
      {name = name, tokT = tokT, tokenT = tokenT, start = A, nat_labels = nat_labels,
       terminals = terminals,
       lit_names = lit_names, nonterms = nonterms, prods = prods, prec = prec,
       artifacts =
        SOME {gram_t = eg_t, gram_def = mk_meta_eq make_eq, decs = decs, rel = rel,
              restricted = NONE}};
  in (egr, (transport, transport_concl)) end;

(* the decoder and bridge lemmas of the grammar, for any start, proved on first
   demand and shared by the entries of the command *)
type shared =
 {dec_total: (string -> thm) lazy,
  bridge: (Grammar_Common.rel_info * (string -> Parser_Rel_Bridge.bridge) lazy) option};

fun shared_lemmas lthy gr : shared =
  let val dec_nones = Lazy.lazy (fn () => Parser_Dec_Total.dec_nones lthy gr) in
    {dec_total = Lazy.lazy (fn () => Parser_Dec_Total.prover lthy gr (Lazy.force dec_nones)),
     bridge =
      Option.map (fn ri =>
          (ri, Lazy.lazy (fn () => Parser_Rel_Bridge.prover lthy gr ri (Lazy.force dec_nones))))
        (Grammar_Defs.lookup_rel lthy gr)}
  end;

(* \<open>parser (ast)\<close>: every decoder of the grammar is \<open>Some\<close> at its tree type, so the
   parser returns the tree of dparse; an entry and a restriction read the decoders from
   here, the latter composes them with plain_ast *)
fun ast_grammar (gr: Grammar_Common.grammar) =
  let
    val {gram_t, gram_def, decs, rel, restricted} = Grammar_Common.artifacts_of gr;
    val {astT, ...} = Grammar_Common.get_desc gr;
    val some = Const (\<^const_name>\<open>Some\<close>, astT --> Grammar_Common.mk_optionT astT);
  in
    Grammar_Common.put_artifacts
      {gram_t = gram_t, gram_def = gram_def, decs = map (fn (A, _) => (A, some)) decs,
       rel = rel, restricted = restricted} gr
  end;

(* one entry: as a command of its own, but for the shared lemmas *)
fun define_entry options all_errors (gen_name, gen) (shared: shared) (parse_b, gr, start) lthy =
  let
    val gram_name = Binding.name_of (#name gr);
    val ast = member (op =) options "ast";
    val gr = if ast then ast_grammar gr else gr;
    val ((recover, repair), (on_error_reduce, (token_info, errors))) =
      the_default ((NONE, NONE), ([], (NONE, [])))
        (AList.lookup (op =) all_errors (Binding.name_of parse_b));
    val _ =
      if not (null on_error_reduce) andalso not (member (op =) options "diagnostics") then
        warning ("parser: \<open>on_error_reduce\<close> of \<open>" ^ Binding.name_of parse_b ^
          "\<close> needs diagnostics, off by \<open>no_diagnostics\<close>; it is ignored")
      else ();
    val _ =
      if not (null errors) andalso not (member (op =) options "diagnostics") then
        warning ("parser: the \<open>errors\<close> block of \<open>" ^ Binding.name_of parse_b ^
          "\<close> needs diagnostics, off by \<open>no_diagnostics\<close>; it is ignored")
      else ();
    val _ =
      if (is_some recover orelse is_some repair) andalso not (member (op =) options "diagnostics") then
        warning ("parser: \<open>recover\<close> or \<open>repair\<close> of \<open>" ^ Binding.name_of parse_b ^
          "\<close> needs diagnostics, off by \<open>no_diagnostics\<close>; it is ignored")
      else ();
    (* (ast): no decoder, no totality premise *)
    val dec_names =
      if ast then [] else
      Grammar_Common.nonterms_list gr
      |> map_filter (fn (A, _) =>
          (case Term.head_of (Grammar_Defs.decoder_of lthy gr A) of
            Const (c, _) => SOME c
          | _ => NONE));
    fun timed label f x = Grammar_Common.timed lthy "parser" label f x;

    (* 0. the entry's grammar; the start of G is G itself *)
    val (egr, (transport, transport_concl)) =
      if start = #start gr then (gr, (K I, K I))
      else timed "0 entry grammar" (entry_grammar gr start) lthy;
    val shn_name = pick_fresh_shn gr;

    (* with declarations: the backend builds from the restricted grammar *)
    val prec_hook =
      (case #prec gr of
        NONE => NONE
      | SOME _ =>
          (case #prec (Data.get (Proof_Context.theory_of lthy)) of
            SOME hook => SOME hook
          | NONE =>
              error ("parser " ^ quote (Binding.name_of parse_b) ^ ": grammar " ^ quote gram_name ^
                " has precedence declarations; import TIGER_Grammar.LR_Prec_Parse")));
    val (prec_out, lthy) =
      (case prec_hook of
        NONE => (NONE, lthy)
      | SOME hook =>
          timed "0 restrict" (#prepare hook parse_b shn_name egr) lthy |>> SOME);
    val (egr, inst, gen) =
      (case (prec_hook, prec_out) of
        (SOME hook, SOME {gram, inst, discharge}) =>
          (gram, inst,
           {build_parse = #build_parse gen,
            sound_thm = #sound_lang hook,
            complete_thm = #complete_lang hook,
            rel_sound_thm = NONE,
            rel_complete_thm = NONE,
            no_error_thm = SOME (#no_error hook),
            ast_thms = SOME (#ast hook),
            discharge_tac = fn dinp => fn ctxt => fn prem =>
              (case discharge ctxt prem of
                SOME tac => SOME tac
              | NONE => #discharge_tac gen dinp ctxt prem)})
      | _ => (egr, K I, gen));
    (* (ast): the tree forms in place of the decoder's *)
    val ast_thms =
      if not ast then NONE
      else
        (case #ast_thms gen of
          SOME a => SOME a
        | NONE =>
            error ("parser " ^ quote (Binding.name_of parse_b) ^ ": backend " ^ quote gen_name ^
              " has no option ast"));
    val gen =
      (case ast_thms of
        NONE => gen
      | SOME a =>
          {build_parse = #build_parse gen,
           sound_thm = #sound_thm gen,
           complete_thm = #complete_lang a,
           rel_sound_thm = NONE,
           rel_complete_thm = NONE,
           no_error_thm = SOME (#no_error a),
           ast_thms = SOME a,
           discharge_tac = #discharge_tac gen});
    val binp = {gram = egr, parse_bind = parse_b, shn = shn_name, options = options,
                errors = errors, recover = recover, repair = repair,
                on_error_reduce = on_error_reduce,
                token_info = token_info};

    (* 1. the backend builds the parse body (may define auxiliary constants) *)
    val ({parse_body, post, checks, recover = recovered}, lthy) =
      timed "1 build_parse" (#build_parse gen binp) lthy;

    (* 2. the parse constant *)
    val ((parse_c, parse_def_th), lthy) =
      timed "2 define parse" (Grammar_Defs.define_const true (parse_b, Thm.def_binding parse_b, parse_body)) lthy;

    (* 3. backend post-processing (typically an inlined code equation) *)
    val lthy = timed "3 post" (post {parse_const = parse_c, parse_def_th = parse_def_th}) lthy;

    (* 4. sound/complete: the body equation from parse_def_th, then decoder
          totality, then the backend's tactics *)
    val hol_parse_eq = @{thm HOL.meta_eq_to_obj_eq} OF [parse_def_th];
    val dec_total = Lazy.lazy (fn () => Lazy.force (#dec_total shared) start);

    val dinp = {gram = egr, parse_bind = parse_b, shn = shn_name, checks = checks};
    val proof_for = discharge_prover lthy (#discharge_tac gen dinp lthy);

    fun discharge th =
      (hol_parse_eq RS inst lthy th)
      |> transport lthy
      |> discharge_dec_total lthy gram_name dec_names dec_total
      |> discharge_via_tac proof_for;

    val sound_lang = timed "4 sound_lang" discharge (#sound_thm gen);
    val complete_lang = timed "4 complete_lang (incl. dec_total)" discharge (#complete_thm gen);

    (* 5. relational forms: both theorems against the relation of the start
          symbol, the bridge premises by Parser_Rel_Bridge; when the bridges
          fail the language forms are kept under the plain names *)
    val rel_forms =
      if ast then NONE else
      (case (#bridge shared, #rel_sound_thm gen, #rel_complete_thm gen) of
        (SOME (_, bridges), SOME rel_sound, SOME rel_complete) =>
          (case Exn.result (fn () =>
              let
                val bridge =
                  timed "5 Parser_Rel_Bridge.prove" (fn () => Lazy.force bridges start) ();
                fun discharge_rel th =
                  (hol_parse_eq RS th)
                  |> instantiate_P lthy (#pred_P bridge)
                  |> transport lthy
                  |> discharge_bridges lthy dec_names bridge
                  |> discharge_via_tac proof_for;
              in (discharge_rel rel_sound, discharge_rel rel_complete) end) () of
            Exn.Res forms => SOME forms
          | Exn.Exn exn =>
              if Exn.is_interrupt exn then Exn.reraise exn
              else
                (warning ("parser: could not relate \<open>" ^ Binding.name_of parse_b ^
                   "\<close> to the relation family of \<open>" ^ gram_name ^ "\<close>: " ^
                   Runtime.exn_message exn ^
                   "; .sound/.complete are stated against the language");
                 NONE))
      | (SOME _, _, _) =>
          if is_some prec_hook then
            (warning ("parser: \<open>" ^ Binding.name_of parse_b ^ "\<close> is stated against \<open>" ^
               gram_name ^ "\<close> and its precedence declarations: the relation family \
               \does not read them");
             NONE)
          else
          (warning ("parser: backend \<open>" ^ gen_name ^ "\<close> has no relational \
             \theorems; .sound/.complete of \<open>" ^ Binding.name_of parse_b ^
             "\<close> are the language forms although grammar \<open>" ^ gram_name ^
             "\<close> has a relation family");
           NONE)
      | _ => NONE);

    (* declarations: the tree forms, against G and prec_ok *)
    val (sound_final, complete_final) =
      (case (ast_thms, prec_hook, rel_forms) of
        (SOME a, _, _) =>
          (discharge (#sound a) |> transport_concl lthy, discharge (#complete a))
      | (NONE, SOME hook, _) =>
          let
            (* no totality here: the decoder premise of a tree form is its statement *)
            fun discharge_tree th =
              (hol_parse_eq RS inst lthy th) |> transport lthy |> discharge_via_tac proof_for;
          in (discharge_tree (#sound hook), discharge_tree (#complete hook)) end
      | (NONE, _, SOME forms) => forms
      | _ => (sound_lang, complete_lang));

    (* the tree of a word without the error token has no error node; before the
       notes, since discharge belongs to this context *)
    val no_error =
      (case (recovered, #no_error_thm gen) of
        (SOME (b, e), SOME th) =>
          [((Grammar_Common.qualify_bind b "no_error", []),
            [([discharge (Drule.infer_instantiate lthy [(("e", 0), Thm.cterm_of lthy e)] th)], [])])]
      | _ => []);

    val (noted, lthy) =
      timed "6 notes" (Local_Theory.notes
        [((Grammar_Common.qualify_bind parse_b "sound",         []), [([sound_final],   [])]),
         ((Grammar_Common.qualify_bind parse_b "complete",      []), [([complete_final],[])]),
         ((Grammar_Common.qualify_bind parse_b "sound_lang",    []), [([sound_lang],    [])]),
         ((Grammar_Common.qualify_bind parse_b "complete_lang", []), [([complete_lang], [])])])
      lthy;
    val lthy = lthy |> Local_Theory.notes no_error |> #2;
    val result: result =
      (case map (the_single o #2) noted of
        [s, c, sl, cl] =>
          {parse_const = parse_c, parse_def = parse_def_th,
           sound = s, complete = c, sound_lang = sl, complete_lang = cl}
      | _ => raise Fail "parser: unexpected notes result");
  in (result, lthy) end;

(* phase 1: the entries one after the other, sharing the lemmas of the grammar *)
fun define_entries_options parser_name_opt options errors entries lthy =
  let
    val checked = check_entries lthy entries;
    val gen = resolve_generator (Proof_Context.theory_of lthy) parser_name_opt;
    val shared = shared_lemmas lthy (#2 (hd checked));
  in fold_map (define_entry options errors gen shared) checked lthy end;

fun define_entries parser_name_opt entries lthy =
  define_entries_options parser_name_opt [] [] entries lthy;

fun define parser_name_opt parse_b gram_ref lthy =
  define_entries parser_name_opt [(parse_b, gram_ref, NONE)] lthy
  |>> the_single;

fun define_cmd parser_name_opt entries lthy =
  #2 (define_entries parser_name_opt entries lthy);

val known_options = ["diagnostics", "no_diagnostics", "ast"];

fun define_names_cmd names errors entries lthy =
  let
    val (given, gens) = List.partition (member (op =) known_options) names;
    val off = member (op =) given "no_diagnostics";
    val _ =
      if off andalso member (op =) given "diagnostics" then
        error "parser: both diagnostics and no_diagnostics named"
      else ();
    (* diagnostics are on unless \<open>no_diagnostics\<close> is named *)
    val options =
      (if off then [] else ["diagnostics"]) @
      (if member (op =) given "ast" then ["ast"] else []);
    val gen_opt =
      (case gens of
        [] => NONE
      | [g] => SOME g
      | _ =>
          error ("parser: more than one generator named: " ^ commas_quote gens ^
            "; known options: " ^ commas_quote known_options));
  in #2 (define_entries_options gen_opt options errors entries lthy) end;


(** outer syntax **)

val parse_sentence =
  Parse.inner_syntax Parse.cartouche >> Word
  || Scan.repeat1 (Scan.unless (Args.$$$ "@") Parse.name -- Scan.option (Args.$$$ "@" |-- Parse.nat))
     >> Symbols;

val parse_msg_key =
  Scan.optional
    (\<^keyword>\<open>(\<close> |-- (Args.$$$ "token" >> K By_Token || Args.$$$ "shift" >> K By_Shift)
      --| \<^keyword>\<open>)\<close>)
    By_State;

val parse_error_message =
  parse_sentence -- parse_msg_key --| (\<^keyword>\<open>\<Rightarrow>\<close> || \<^keyword>\<open>=>\<close>) -- Parse.embedded
  >> (fn ((sentence, key), text) => {sentence = sentence, key = key, text = text});

val entry_name =
  Scan.unless (Parse.reserved "token_info" || Parse.reserved "errors") Parse.name;

val parse_repair =
  Parse.reserved "repair"
  |-- Scan.option (Parse.reserved "token" |-- Parse.term)
  -- Scan.optional
       (Parse.reserved "avoid"
        |-- Scan.repeat1 (Scan.unless (Parse.reserved "on_error_reduce") entry_name)) []
  >> (fn (token, avoid) => {token = token, avoid = avoid});

val _ =
  Outer_Syntax.local_theory \<^command_keyword>\<open>parser\<close>
    "emit an executable, verified parser from a grammar spec"
    (Scan.optional (\<^keyword>\<open>(\<close> |-- Parse.list1 Parse.name --| \<^keyword>\<open>)\<close>) []
     -- Parse.and_list1
          (Parse.binding
           -- (Scan.option \<^keyword>\<open>for\<close> |-- Parse.name_position)
           -- Scan.option (\<^keyword>\<open>(\<close> |-- Parse.name_position --| \<^keyword>\<open>)\<close>)
           -- Scan.option (Parse.reserved "recover" |-- Parse.name)
           -- Scan.option parse_repair
           -- Scan.optional (Parse.reserved "on_error_reduce" |-- Scan.repeat1 entry_name) []
           -- Scan.option (Parse.reserved "token_info" |-- Parse.inner_syntax Parse.cartouche)
           -- Scan.optional (Parse.reserved "errors" |-- Parse.enum1 "|" parse_error_message) []
           >> (fn (((((((b, g), a), recover), repair), reduce), info), errors) =>
                ((b, g, a), (Binding.name_of b, ((recover, repair), (reduce, (info, errors)))))))
     >> (fn (names, entries) =>
          define_names_cmd names (map #2 entries) (map #1 entries)));

end;
