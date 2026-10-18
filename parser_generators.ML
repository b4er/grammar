(* the generic `parser` command.  A backend contributes the body of the parse
   constant, its sound/complete theorems and tactics for its own premises;
   the decoder totality premise is discharged here (Parser_Dec_Total), the
   relational forms go through Parser_Rel_Bridge, unclaimed premises stay as
   assumptions.

   emitted: `<parse>.sound_lang` / `.complete_lang` (against \<open>ilang G\<close>) and
   `<parse>.sound` / `.complete` (against the start relation, when the
   grammar has one and the backend relational forms; else the same) *)

signature PARSER_GENERATORS =
sig
  type build_input =
   {gram: Grammar_Common.grammar,
    parse_bind: binding,
    shn: string}

  type post_input =
   {parse_const: term,
    parse_def_th: thm}

  (* checks: the equations `check G Shn = value` the backend evaluated while
     building, handed back to its discharge_tac *)
  type build_output =
   {parse_body: term,
    post: post_input -> local_theory -> local_theory,
    checks: thm list}

  type discharge_input =
   {gram: Grammar_Common.grammar,
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

  val define: string option -> binding -> xstring * Position.T -> local_theory
    -> result * local_theory
  val define_cmd: string option -> binding -> xstring * Position.T -> local_theory
    -> local_theory

  (** helpers reusable by backends **)
  val pick_fresh_shn: Grammar_Common.grammar -> string
  val eval_tac: Proof.context -> int -> tactic
  val discharge_by_lemma: Proof.context -> thm -> thm -> thm
end;

structure Parser_Generators: PARSER_GENERATORS =
struct

(** registry **)

type build_input =
 {gram: Grammar_Common.grammar,
  parse_bind: binding,
  shn: string};

type post_input =
 {parse_const: term,
  parse_def_th: thm};

type build_output =
 {parse_body: term,
  post: post_input -> local_theory -> local_theory,
  checks: thm list};

type discharge_input =
 {gram: Grammar_Common.grammar,
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

fun define parser_name_opt parse_b gram_ref lthy =
  let
    val _ = check_parse_binding lthy parse_b;
    val (_, gr) = Grammar_Common.check_grammar lthy gram_ref;
    val (gen_name, gen) =
      resolve_generator (Proof_Context.theory_of lthy) parser_name_opt;
    val shn_name = pick_fresh_shn gr;
    val binp = {gram = gr, parse_bind = parse_b, shn = shn_name};
    val gram_name = Binding.name_of (#name gr);
    val dec_names =
      Grammar_Common.nonterms_list gr
      |> map_filter (fn (A, _) =>
          (case Term.head_of (Grammar_Defs.decoder_of lthy gr A) of
            Const (c, _) => SOME c
          | _ => NONE));
    fun timed label f x = Grammar_Common.timed lthy "parser" label f x;

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
    val dec_total = Lazy.lazy (fn () => Parser_Dec_Total.prove lthy gr);

    val dinp = {gram = gr, shn = shn_name, checks = checks};
    val proof_for = discharge_prover lthy (#discharge_tac gen dinp lthy);

    fun discharge th =
      (hol_parse_eq RS th)
      |> discharge_dec_total lthy gram_name dec_names dec_total
      |> discharge_via_tac proof_for;

    val sound_lang = timed "4 sound_lang" discharge (#sound_thm gen);
    val complete_lang = timed "4 complete_lang (incl. dec_total)" discharge (#complete_thm gen);

    (* 5. relational forms: both theorems against the relation of the start
          symbol, the bridge premises by Parser_Rel_Bridge; when the bridges
          fail the language forms are kept under the plain names *)
    val rel_forms =
      (case (Grammar_Defs.lookup_rel lthy gr, #rel_sound_thm gen, #rel_complete_thm gen) of
        (SOME ri, SOME rel_sound, SOME rel_complete) =>
          (case Exn.result (fn () =>
              let
                val bridge = timed "5 Parser_Rel_Bridge.prove" (Parser_Rel_Bridge.prove lthy gr) ri;
                fun discharge_rel th =
                  (hol_parse_eq RS th)
                  |> instantiate_P lthy (#pred_P bridge)
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

fun define_cmd parser_name_opt parse_b gram_ref lthy =
  #2 (define parser_name_opt parse_b gram_ref lthy);


(** outer syntax **)

val _ =
  Outer_Syntax.local_theory \<^command_keyword>\<open>parser\<close>
    "emit an executable, verified parser from a grammar spec"
    (Scan.option (\<^keyword>\<open>(\<close> |-- Parse.name --| \<^keyword>\<open>)\<close>)
     -- Parse.binding
     -- (Scan.option \<^keyword>\<open>for\<close> |-- Parse.name_position)
     >> (fn ((gen_opt, parse_b), gram_ref) => define_cmd gen_opt parse_b gram_ref));

end;
