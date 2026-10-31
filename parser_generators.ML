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
     errors: the entry's \<open>errors\<close> block *)
  datatype sentence =
    Symbols of (string * int option) list
  | Word of string
  datatype msg_key = By_State | By_Token | By_Shift
  type error_message = {sentence: sentence, key: msg_key, text: string}

  type build_input =
   {gram: Grammar_Common.grammar,
    parse_bind: binding,
    shn: string,
    options: string list,
    errors: error_message list}

  type post_input =
   {parse_const: term,
    parse_def_th: thm}

  (* checks: the equations `check G Shn = value` the backend evaluated while
     building, handed back to its discharge_tac *)
  type build_output =
   {parse_body: term,
    post: post_input -> local_theory -> local_theory,
    checks: thm list}

  (* gram: as in build_input, the entry's record *)
  type discharge_input =
   {gram: Grammar_Common.grammar,
    parse_bind: binding,
    shn: string,
    checks: thm list}

  (* discharge_tac: SOME on a premise the backend claims (a failing tactic
     warns), NONE on premises left as assumptions; rel_sound_thm /
     rel_complete_thm: stated against a relation P of the start symbol *)
  type parser_generator =
   {build_parse:   build_input -> local_theory -> build_output * local_theory,
    sound_thm:     thm,
    complete_thm:  thm,
    rel_sound_thm:    thm option,
    rel_complete_thm: thm option,
    discharge_tac: discharge_input -> Proof.context -> term -> (int -> tactic) option}

  type result =
   {parse_const: term,
    parse_def: thm,
    sound: thm,
    complete: thm,
    sound_lang: thm,
    complete_lang: thm}

  val register: string -> parser_generator -> theory -> theory
  val set_default: string -> theory -> theory
  val default: theory -> string option

  (* `NAME for G (A)`; NONE: the start of G *)
  type entry = binding * (xstring * Position.T) * (string * Position.T) option

  val define: string option -> binding -> xstring * Position.T -> local_theory
    -> result * local_theory
  val define_entries: string option -> entry list -> local_theory
    -> result list * local_theory
  (* the options known to the command; any other name in \<open>parser (\<dots>)\<close> is the
     generator *)
  val known_options: string list
  val define_entries_options: string option -> string list ->
    (string * error_message list) list -> entry list -> local_theory
    -> result list * local_theory
  val define_cmd: string option -> entry list -> local_theory -> local_theory
  (* `parser (N1, ..., Nk)`: the names split into the options and at most one generator *)
  val define_names_cmd: string list -> (string * error_message list) list -> entry list ->
    local_theory -> local_theory

  (** helpers reusable by backends **)
  val pick_fresh_shn: Grammar_Common.grammar -> string
  val eval_tac: Proof.context -> int -> tactic
  val discharge_by_lemma: Proof.context -> thm -> thm -> thm
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

type build_input =
 {gram: Grammar_Common.grammar,
  parse_bind: binding,
  shn: string,
  options: string list,
  errors: error_message list};

type post_input =
 {parse_const: term,
  parse_def_th: thm};

type build_output =
 {parse_body: term,
  post: post_input -> local_theory -> local_theory,
  checks: thm list};

type discharge_input =
 {gram: Grammar_Common.grammar,
  parse_bind: binding,
  shn: string,
  checks: thm list};

type parser_generator =
 {build_parse:   build_input -> local_theory -> build_output * local_theory,
  sound_thm:     thm,
  complete_thm:  thm,
  rel_sound_thm:    thm option,
  rel_complete_thm: thm option,
  discharge_tac: discharge_input -> Proof.context -> term -> (int -> tactic) option};

type result =
 {parse_const: term,
  parse_def: thm,
  sound: thm,
  complete: thm,
  sound_lang: thm,
  complete_lang: thm};

structure Data = Theory_Data
(
  type T = {gens: parser_generator Symtab.table, default: string option};
  val empty: T = {gens = Symtab.empty, default = NONE};
  fun merge ({gens = g1, default = d1}, {gens = g2, default = d2}): T =
    {gens = Symtab.merge (K true) (g1, g2),
     default = (case d2 of NONE => d1 | _ => d2)};
);

(* registering a backend does not change the default *)
fun register nm gen =
  Data.map (fn {gens, default} =>
    {gens = Symtab.update (nm, gen) gens, default = default});

fun registered thy = Symtab.keys (#gens (Data.get thy));
fun default thy = #default (Data.get thy);

fun set_default nm thy =
  (if Symtab.defined (#gens (Data.get thy)) nm then ()
   else error ("Unknown parser generator " ^ quote nm ^
     "; registered: " ^ commas_quote (registered thy));
   Data.map (fn {gens, ...} => {gens = gens, default = SOME nm}) thy);

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
    val {gram_t, gram_def, decs, rel} = Grammar_Common.artifacts_of gr;
    val {isgT, ...} = Grammar_Common.get_desc gr;
    val upd_c =
      Const (\<^const_name>\<open>is_cfg.istart_update\<close>,
        (HOLogic.stringT --> HOLogic.stringT) --> isgT --> isgT);
    val eg_t = upd_c $ Term.absdummy HOLogic.stringT (HOLogic.mk_string A) $ gram_t;

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
      prove (basic addsimps (gram_def :: @{thms is_cfg.make_def is_cfg.update_convs refl}))
        (HOLogic.mk_eq (eg_t, make_c $ ps $ HOLogic.mk_string A $ zero));
    fun sel c T t = Const (c, isgT --> T) $ t;
    val sel_ctxt = basic addsimps (make_eq :: @{thms is_cfg.make_def is_cfg.select_convs});
    val iprodsT = fastype_of ps;
    val iprods_eq =
      prove ctxt
        (HOLogic.mk_eq
          (sel \<^const_name>\<open>iprods\<close> iprodsT eg_t, sel \<^const_name>\<open>iprods\<close> iprodsT gram_t));
    val istart_eq =
      prove sel_ctxt
        (HOLogic.mk_eq (sel \<^const_name>\<open>istart\<close> HOLogic.stringT eg_t, HOLogic.mk_string A));
    val istart_ind_eq =
      prove sel_ctxt (HOLogic.mk_eq (sel \<^const_name>\<open>istart_ind\<close> HOLogic.natT eg_t, zero));
    val transport_ss =
      simpset_of (basic addsimps
        [@{thm wf_ptree_iprods_cong} OF [iprods_eq], @{thm ast_of_iprods_cong} OF [iprods_eq],
         istart_eq, istart_ind_eq]);
    fun transport ctxt' =
      Conv.fconv_rule
        (Conv.prems_conv ~1 (Simplifier.full_rewrite (put_simpset transport_ss ctxt')));

    val {name, tokT, tokenT, terminals, lit_names, nonterms, prods, ...} = gr;
    val egr: Grammar_Common.grammar =
      {name = name, tokT = tokT, tokenT = tokenT, start = A, terminals = terminals,
       lit_names = lit_names, nonterms = nonterms, prods = prods,
       artifacts =
        SOME {gram_t = eg_t, gram_def = mk_meta_eq make_eq, decs = decs, rel = rel}};
  in (egr, transport) end;

(* the decoder and bridge lemmas of the grammar, for any start, proved on first
   demand and shared by the entries of the command *)
type shared =
 {dec_total: (string -> thm) lazy,
  bridge: (Grammar_Common.rel_info * (string -> Parser_Rel_Bridge.bridge) lazy) option};

fun shared_lemmas lthy gr : shared =
  {dec_total = Lazy.lazy (fn () => Parser_Dec_Total.prover lthy gr),
   bridge =
    Option.map (fn ri => (ri, Lazy.lazy (fn () => Parser_Rel_Bridge.prover lthy gr ri)))
      (Grammar_Defs.lookup_rel lthy gr)};

(* one entry: as a command of its own, but for the shared lemmas *)
fun define_entry options all_errors (gen_name, gen) (shared: shared) (parse_b, gr, start) lthy =
  let
    val gram_name = Binding.name_of (#name gr);
    val errors = the_default [] (AList.lookup (op =) all_errors (Binding.name_of parse_b));
    val _ =
      if not (null errors) andalso not (member (op =) options "diagnostics") then
        warning ("parser: the \<open>errors\<close> block of \<open>" ^ Binding.name_of parse_b ^
          "\<close> needs \<open>parser (diagnostics)\<close>; it is ignored")
      else ();
    val dec_names =
      Grammar_Common.nonterms_list gr
      |> map_filter (fn (A, _) =>
          (case Term.head_of (Grammar_Defs.decoder_of lthy gr A) of
            Const (c, _) => SOME c
          | _ => NONE));
    fun timed label f x = Grammar_Common.timed lthy "parser" label f x;

    (* 0. the entry's grammar; the start of G is G itself *)
    val (egr, transport) =
      if start = #start gr then (gr, K I)
      else timed "0 entry grammar" (entry_grammar gr start) lthy;
    val shn_name = pick_fresh_shn gr;
    val binp = {gram = egr, parse_bind = parse_b, shn = shn_name, options = options,
                errors = errors};

    (* 1. the backend builds the parse body (may define auxiliary constants) *)
    val ({parse_body, post, checks}, lthy) = timed "1 build_parse" (#build_parse gen binp) lthy;

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
      (hol_parse_eq RS th)
      |> transport lthy
      |> discharge_dec_total lthy gram_name dec_names dec_total
      |> discharge_via_tac proof_for;

    val sound_lang = timed "4 sound_lang" discharge (#sound_thm gen);
    val complete_lang = timed "4 complete_lang (incl. dec_total)" discharge (#complete_thm gen);

    (* 5. relational forms: both theorems against the relation of the start
          symbol, the bridge premises by Parser_Rel_Bridge; when the bridges
          fail the language forms are kept under the plain names *)
    val rel_forms =
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
          (warning ("parser: backend \<open>" ^ gen_name ^ "\<close> has no relational \
             \theorems; .sound/.complete of \<open>" ^ Binding.name_of parse_b ^
             "\<close> are the language forms although grammar \<open>" ^ gram_name ^
             "\<close> has a relation family");
           NONE)
      | _ => NONE);

    val (sound_final, complete_final) =
      (case rel_forms of SOME forms => forms | NONE => (sound_lang, complete_lang));

    val (noted, lthy) =
      timed "6 notes" (Local_Theory.notes
        [((Grammar_Common.qualify_bind parse_b "sound",         []), [([sound_final],   [])]),
         ((Grammar_Common.qualify_bind parse_b "complete",      []), [([complete_final],[])]),
         ((Grammar_Common.qualify_bind parse_b "sound_lang",    []), [([sound_lang],    [])]),
         ((Grammar_Common.qualify_bind parse_b "complete_lang", []), [([complete_lang], [])])])
      lthy;
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

val known_options = ["diagnostics"];

fun define_names_cmd names errors entries lthy =
  let
    val (options, gens) = List.partition (member (op =) known_options) names;
    val gen_opt =
      (case gens of
        [] => NONE
      | [g] => SOME g
      | _ =>
          error ("parser: more than one generator named: " ^ commas_quote gens ^
            "; known options: " ^ commas_quote known_options));
  in #2 (define_entries_options gen_opt (distinct (op =) options) errors entries lthy) end;


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

val _ =
  Outer_Syntax.local_theory \<^command_keyword>\<open>parser\<close>
    "emit an executable, verified parser from a grammar spec"
    (Scan.optional (\<^keyword>\<open>(\<close> |-- Parse.list1 Parse.name --| \<^keyword>\<open>)\<close>) []
     -- Parse.and_list1
          (Parse.binding
           -- (Scan.option \<^keyword>\<open>for\<close> |-- Parse.name_position)
           -- Scan.option (\<^keyword>\<open>(\<close> |-- Parse.name_position --| \<^keyword>\<open>)\<close>)
           -- Scan.optional (Parse.reserved "errors" |-- Parse.enum1 "|" parse_error_message) []
           >> (fn (((b, g), a), errors) => ((b, g, a), (Binding.name_of b, errors))))
     >> (fn (names, entries) =>
          define_names_cmd names (map #2 entries) (map #1 entries)));

end;
