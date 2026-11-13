(* Author: Basil Fürer, Dmitriy Traytel, Claude *)

(* the LR backend of the parser command (precise tables), with the build step in
   lr_build.ML, the diagnostics in lr_diag.ML and the helpers in lr_util.ML: the
   determinism and accept/reduce premises discharged by evaluating the static checks,
   the printers that explain a non-empty check, and parser_error_states *)

signature LR_BACKEND =
sig
  val lr_gen: Parser_Generators.parser_generator
  val string_of_tm: Proof.context -> Grammar_Common.grammar -> term -> string
  (* coverage of the error states, for the tests *)
  type coverage =
   {coverage: term, spelled: string list, hide: int option, columns: bool, vec: bool,
    replay: bool, keys: (int * int option) list, shifts: int}
  val get_coverage: Proof.context -> string -> coverage option
  val evaluate_coverage: Proof.context -> term -> term list ->
    (int list list * (int list -> int list)) * int list list
  val dest_view: int list list -> LR_Reach.view * (int * int) list * int list
  val error_hits: Proof.context -> coverage ->
    int list list * (int list -> int list) -> LR_Reach.hit list
end;

structure LR_Backend: LR_BACKEND =
struct

open LR_Util LR_Diagnostics LR_Build;

(** explaining a non-empty check (LR_Parser: explain_rp / explain_acc) **)

(* decoding evaluated literals *)

fun dest_ctor t =
  (case Term.strip_comb t of
    (Const (c, _), args) => (c, args)
  | _ => raise TERM ("dest_ctor", [t]));

datatype tsym = SNt of string | STm of term;

fun dest_sym gram t =
  (case dest_ctor t of
    (c, [n]) =>
      if c = \<^const_name>\<open>Nt\<close> then SNt (Grammar_Common.name_of_term gram n)
      else if c = \<^const_name>\<open>Tm\<close> then STm n
      else raise TERM ("dest_sym", [t])
  | _ => raise TERM ("dest_sym", [t]));

val wrel_names =
  [(\<^const_name>\<open>WEq\<close>, "column = item indentation"),
   (\<^const_name>\<open>WGe\<close>, "column \<ge> item indentation"),
   (\<^const_name>\<open>WGt\<close>, "column > item indentation"),
   (\<^const_name>\<open>WLe\<close>, "column \<le> item indentation"),
   (\<^const_name>\<open>WLt\<close>, "column < item indentation"),
   (\<^const_name>\<open>WAny\<close>, "any column")];

fun dest_wrel t =
  (case dest_ctor t of
    (c, []) =>
      (case AList.lookup (op =) wrel_names c of
        SOME s => s
      | NONE => raise TERM ("dest_wrel", [t]))
  | _ => raise TERM ("dest_wrel", [t]));

datatype xact = XShift of term * string | XReduce of int * string;

fun dest_xact t =
  (case dest_ctor t of
    (c, [a, r]) =>
      if c = \<^const_name>\<open>XShift\<close> then XShift (a, dest_wrel r)
      else if c = \<^const_name>\<open>XReduce\<close> then XReduce (dest_nat a, dest_wrel r)
      else raise TERM ("dest_xact", [t])
  | _ => raise TERM ("dest_xact", [t]));

fun dest_triple t =
  let val (a, bc) = HOLogic.dest_prod t; val (b, c) = HOLogic.dest_prod bc in (a, b, c) end;

(* printing against the grammar record: a token value is printed by its
   declared spelling when it is one of the fixed terminals (evaluated values
   are in the normal form the declaration was read into); a value that only
   agrees on the head constant with a single declaration is that terminal
   spelled differently (\<open>Suc 0\<close> for \<open>1\<close>) *)

fun string_of_tm ctxt (gram: Grammar_Common.grammar) t =
  let
    val lits = #lit_names gram;
    fun head u = (case Term.head_of u of Const (c, _) => SOME c | _ => NONE);
  in
    (case AList.lookup (op aconv) lits t of
      SOME s => quote s
    | NONE =>
        (case filter (fn (u, _) => is_some (head u) andalso head u = head t) lits of
          [(_, s)] => quote s
        | _ => Syntax.string_of_term ctxt t))
  end;

(* \<open>#\<close> occurs in the names of restricted grammars only; the reports speak of the grammar *)
fun string_of_sym _ _ (SNt n) = Grammar_Common.orig_string n
  | string_of_sym ctxt gram (STm a) = string_of_tm ctxt gram a;

(* production `i` of `iprods`, i.e. of the grammar record, dotted at `dot`;
   the synthesized start production has no record entry *)
fun pretty_prod ctxt (gram: Grammar_Common.grammar) i dot =
  if i < length (#prods gram) then
    let
      val p = nth (#prods gram) i;
      fun sym (Grammar_Common.RN n) = n
        | sym (Grammar_Common.RC k) = string_of_tm ctxt gram (Vector.sub (#terminals gram, k))
        | sym (Grammar_Common.RT k) = string_of_tm ctxt gram (Vector.sub (#terminals gram, k));
      (* a unit chain of a restricted grammar: its relation is not the user's *)
      val chain = is_some (#restricted (Grammar_Common.artifacts_of gram)) andalso
        (case #rhs p of [(Grammar_Common.RN m, _)] => m = #lhs p | _ => false);
      val syms = map (fn (s, a) =>
        sym s ^ (if chain then "" else Grammar_Common.string_of_ann a)) (#rhs p);
      val body =
        (case dot of
          NONE => syms
        | SOME m => take m syms @ ["\<cdot>"] @ drop m syms);
      val text = #lhs p ^ " = " ^ space_implode " " body;
    in Pretty.mark_str (Position.markup (#pos p), text) end
  else
    Pretty.str ("\<langle>start\<rangle> = " ^ #start gram ^
      (case dot of NONE => "" | SOME 0 => " \<cdot> " ^ #start gram | SOME _ => " \<cdot>"));

fun indent n prt = Pretty.block [Pretty.str (replicate_string n " "), prt];

fun quoted_prod ctxt gram i dot =
  Pretty.block [Pretty.str "\<open>", pretty_prod ctxt gram i dot, Pretty.str "\<close>"];

fun toks_text ctxt gram toks = space_implode " " (map (string_of_tm ctxt gram) toks);

fun state_text ctxt gram path =
  (case path of
    NONE => "unreachable state:"
  | SOME [] => "start state:"
  | SOME syms =>
      "state after \<open>" ^ space_implode " " (map (string_of_sym ctxt gram) syms) ^ "\<close>:");

fun dest_path gram t = Option.map (map (dest_sym gram) o HOLogic.dest_list) (dest_option t);
fun dest_sample t = Option.map (HOLogic.dest_list) (dest_option t);

(* the item of the state that shifts `a`: some `(pr, m)` with `a` after the dot *)
fun shift_item (gram: Grammar_Common.grammar) items a =
  let
    val n_prods = length (#prods gram);
    fun tm_of (Grammar_Common.RC k) = SOME (Vector.sub (#terminals gram, k))
      | tm_of (Grammar_Common.RT k) = SOME (Vector.sub (#terminals gram, k))
      | tm_of _ = NONE;
    fun dotted (i, m) =
      i < n_prods andalso
      (case try (nth (#rhs (nth (#prods gram) i))) m of
        SOME (s, _) => (case tm_of s of SOME t => t aconv a | NONE => false)
      | NONE => false);
  in find_first dotted items end;

fun pretty_act ctxt gram items (XShift (a, _)) =
      (case shift_item gram items a of
        SOME (i, m) => Pretty.block [Pretty.str "shift into ", quoted_prod ctxt gram i (SOME m)]
      | NONE => Pretty.str ("shift " ^ string_of_tm ctxt gram a))
  | pretty_act ctxt gram _ (XReduce (i, _)) =
      Pretty.block [Pretty.str "reduce ", quoted_prod ctxt gram i NONE];

fun rel_of (XShift (_, r)) = r
  | rel_of (XReduce (_, r)) = r;
fun kind_of (XShift _) = "shift"
  | kind_of (XReduce _) = "reduce";
(* by the text: copies of a production in a restricted grammar are one line *)
fun act_key ctxt _ (XShift (a, _)) = "s" ^ Syntax.string_of_term ctxt a
  | act_key ctxt gram (XReduce (i, _)) = "r" ^ Pretty.string_of (pretty_prod ctxt gram i NONE);

(* the unit chains of a restricted grammar read `E = E` and its copies of a production
   read alike: a pair with a chain, or of two copies, says nothing a pair without them
   does not.  So of a state's pairs only the most telling kind stays, in one order *)
fun drop_chains ctxt (gram: Grammar_Common.grammar) prs =
  let
    fun chain (XReduce (i, _)) =
          i < length (#prods gram) andalso
          (case nth (#prods gram) i of
            {lhs, rhs = [(Grammar_Common.RN m, _)], ...} => m = lhs
          | _ => false)
      | chain _ = false;
    val key = act_key ctxt gram;
    fun kind (_, a, b) =
      if chain a orelse chain b then 2 else if key a = key b then 1 else 0 : int;
    fun order (la, a as XReduce _, b as XReduce _) =
          if key a <= key b then (la, a, b) else (la, b, a)
      | order pr = pr;
    val best = fold (Integer.min o kind) prs 2;
  in
    if is_some (#restricted (Grammar_Common.artifacts_of gram))
    then map order (filter (fn pr => kind pr = best) prs)
    else prs
  end;

(* one line per action pair of a state, shift first as in every other generator's
   report, with the set of lookaheads the pair fires on; a lookahead all of whose cell
   variants constrain both sides is layout-dependent, which the line says as a suffix
   of the set, with the relations of the first such variant *)
fun pretty_pairs ctxt gram items prs =
  let
    fun norm (la, a1, a2) =
      (case (a1, a2) of (XReduce _, XShift _) => (la, a2, a1) | _ => (la, a1, a2));
    val prs = map norm (drop_chains ctxt gram prs);
    fun pair_key (_, a1, a2) = act_key ctxt gram a1 ^ "|" ^ act_key ctxt gram a2;
    fun la_key NONE = "$"
      | la_key (SOME a) = Syntax.string_of_term ctxt a;
    fun constrained rels =
      forall (fn (r1, r2) => r1 <> "any column" andalso r2 <> "any column") rels;
    fun line k =
      let
        val entries = filter (fn e => pair_key e = k) prs;
        val (_, a1, a2) = hd entries;
        (* the lookaheads in order of first occurrence, each with its variants' relations *)
        val las =
          map (fn lk =>
            let val vs = filter (fn (la, _, _) => la_key la = lk) entries
            in (#1 (hd vs), map (fn (_, b1, b2) => (rel_of b1, rel_of b2)) vs) end)
            (distinct (op =) (map (la_key o #1) entries));
        val toks = map_filter (Option.map (string_of_tm ctxt gram) o fst) las;
        val at_end = exists (is_none o fst) las;
        val dep = map_filter (fn (la, rels) =>
          if is_some la andalso constrained rels
          then SOME (string_of_tm ctxt gram (the la), hd rels) else NONE) las;
        val on =
          (if null toks then "" else " on " ^ space_implode " " toks) ^
          (if not at_end then "" else if null toks then " at end of input"
           else " and at end of input");
        val layout =
          (case dep of
            [] => ""
          | (_, (r1, r2)) :: _ =>
              " [layout-dependent" ^
              (if length dep = length toks then "" else " on " ^ space_implode " " (map fst dep)) ^
              ": " ^ kind_of a1 ^ " needs " ^ r1 ^ ", " ^ kind_of a2 ^ " needs " ^ r2 ^ "]");
      in
        indent 2 (Pretty.block
          [Pretty.str (kind_of a1 ^ "/" ^ kind_of a2 ^ on ^ layout ^ ":  "),
           pretty_act ctxt gram items a1, Pretty.str "  vs  ", pretty_act ctxt gram items a2])
      end;
  in map line (distinct (op =) (map pair_key prs)) end;

(* the example of a state: the witness word with the driver's position and the columns,
   else the sample input the search started from *)
fun pretty_example ctxt gram sample wit =
  (case wit of
    NONE =>
      (case sample of
        NONE => []
      | SOME toks =>
          [indent 2 (Pretty.str ("example input \<open>" ^ toks_text ctxt gram toks ^ "\<close>"))])
  | SOME w =>
      let
        val (word_t, remaining_t, _) = dest_triple w;
        val word = map (apsnd dest_nat o HOLogic.dest_prod) (HOLogic.dest_list word_t);
        val consumed = length word - dest_nat remaining_t;
        val cols = map snd word;
        val same = forall (fn c => c = hd cols) cols;
        fun tok (a, c) = string_of_tm ctxt gram a ^ (if same then "" else "@" ^ string_of_int c);
        val toks = map tok word;
        val marked = take consumed toks @ ["\<cdot>"] @ drop consumed toks;
      in
        [indent 2 (Pretty.str
          ((if null word then "example: the empty input"
            else "example \<open>" ^ space_implode " " marked ^ "\<close>") ^ ": two actions live" ^
           (if null cols then "" else if same then " (all tokens at column " ^ string_of_int (hd cols) ^ ")"
            else " (token@column)")))]
      end);

(* the entries of the three explanations, each a state's report: the path line, then
   the action pairs and the example; \<open>pretty_rp\<close> also says whether the search found
   a witness *)
fun dest_items t = map (apply2 dest_nat o HOLogic.dest_prod) (HOLogic.dest_list t);

fun dest_prs t =
  map (fn u =>
    let val (la, a1, a2) = dest_triple u
    in (dest_option la, dest_xact a1, dest_xact a2) end) (HOLogic.dest_list t);

fun pretty_state ctxt gram path_t lines =
  let val state = state_text ctxt gram (dest_path gram path_t)
  in (state, Pretty.chunks (Pretty.str state :: lines)) end;

(* the path alone, so without the colon that introduces a state's lines *)
fun pretty_path ctxt gram entry =
  Pretty.str (perhaps (try (unsuffix ":"))
    (state_text ctxt gram (dest_path gram (snd (HOLogic.dest_prod entry)))));

fun pretty_brief ctxt gram entry =
  (case dest_tuple 4 entry of
    [_, items_t, path_t, prs_t] =>
      snd (pretty_state ctxt gram path_t
        (pretty_pairs ctxt gram (dest_items items_t) (dest_prs prs_t)))
  | _ => raise TERM ("pretty_brief", [entry]));

(* with the state's text, for the timing line *)
fun pretty_rp ctxt gram entry =
  (case dest_tuple 6 entry of
    [_, items_t, path_t, sample_t, prs_t, wit_t] =>
      let
        val wit = dest_option wit_t;
        val (state, prt) =
          pretty_state ctxt gram path_t
            (pretty_pairs ctxt gram (dest_items items_t) (dest_prs prs_t) @
             pretty_example ctxt gram (dest_sample sample_t) wit);
      in (is_some wit, state, prt) end
  | _ => raise TERM ("pretty_rp", [entry]));

(* one entry of explain_acc *)
fun pretty_acc ctxt gram entry =
  let
    val (_, rest) = HOLogic.dest_prod entry;
    val (prs_t, rest) = HOLogic.dest_prod rest;
    val (path_t, sample_t) = HOLogic.dest_prod rest;
    val prs = map dest_nat (HOLogic.dest_list prs_t);
  in
    Pretty.chunks
      ([Pretty.str (state_text ctxt gram (dest_path gram path_t)),
        indent 2 (Pretty.block (Pretty.str "accept/reduce at end of input:  accept  vs  " ::
          Pretty.separate "  vs " (map (fn i => Pretty.block
            [Pretty.str "reduce ", quoted_prod ctxt gram i NONE]) prs) @
          [Pretty.str "  \<comment> a cycle through the start symbol: the driver returns the \
            \first parse, the relation admits more"]))] @
       (case dest_sample sample_t of
          SOME [] => [indent 2 (Pretty.str "example: the empty input")]
        | SOME toks => [indent 2 (Pretty.str ("example \<open>" ^ toks_text ctxt gram toks ^ " \<cdot>\<close>"))]
        | NONE => []))
  end;

(* the summary line, then the groups of entries, each under its heading when it has one;
   an empty group is left out with its heading *)
fun pretty_report header groups =
  Pretty.string_of (Pretty.chunks (Pretty.str header ::
    maps (fn (heading, entries) =>
      if null entries then []
      else (case heading of NONE => entries | SOME h => Pretty.str h :: entries)) groups));

fun lr_discharge
  ({gram, parse_bind, shn, checks}: Parser_Generators.discharge_input) ctxt prem =
  let
    fun get_check t = find_first (fn th => lhs_of_eq th aconv t) checks;
    val gram_short = Binding.name_of (#name gram);
    (* the reports name the entry: two entries of one grammar have their own tables *)
    val entry =
      "\<open>" ^ Binding.name_of parse_bind ^ "\<close> (grammar \<open>" ^ gram_short ^
      "\<close>, start \<open>" ^ #start gram ^ "\<close>)";
    val arts = Grammar_Common.artifacts_of gram;
    val gram_t = #gram_t arts;
    val gram_def_th = #gram_def arts;
    fun conflicts_term c =
      Syntax.check_term ctxt (Term.list_comb (Const (c, dummyT), [gram_t, Grammar_Common.fresh_term gram shn]));
    (* the symbol paths of the reported states: a value of the checks bundle *)
    fun paths_term () =
      Syntax.check_term ctxt (Term.list_comb (Const (\<^const_name>\<open>explain_paths\<close>, dummyT),
        [gram_t, Grammar_Common.fresh_term gram shn, conflicts_term \<^const_name>\<open>rlalr_conflicts\<close>]));
    val fresh_tac =
      (case #restricted arts of
        SOME {fresh, ...} => resolve_tac ctxt [fresh]
      | NONE => fresh_name_tac ctxt gram_def_th);
    (* the reports walk the tables, so they read the productions the tables have *)
    val report_gram = Lazy.lazy (fn () => Grammar_Common.report_grammar gram);

    (* the check's value: the equation cached by build_parse, else evaluated here;
       an evaluation failure is reported and leaves the premise in place *)
    fun check_value t =
      (case get_check t of
        SOME eq => SOME (snd (HOLogic.dest_eq (HOLogic.dest_Trueprop (Thm.prop_of eq))))
      | NONE =>
          (case Exn.result (Value_Command.value ctxt) t of
            Exn.Res v => SOME v
          | Exn.Exn exn =>
              if Exn.is_interrupt exn then Exn.reraise exn
              else
                (warning ("parser: could not evaluate \<open>" ^ Syntax.string_of_term ctxt t ^
                   "\<close> for \<open>" ^ gram_short ^ "\<close>: " ^ Runtime.exn_message exn);
                 NONE)));
    fun check_tac t =
      (case get_check t of
        SOME eq => resolve_tac ctxt [eq]
      | NONE => Parser_Generators.eval_tac ctxt);

    (* mdet: `rlalr_sufficient` leaves the executable check and freshness. *)
    val mdet_tac =
      SOLVED' (resolve_tac ctxt @{thms rlalr_sufficient}
        THEN' check_tac (conflicts_term \<^const_name>\<open>rlalr_conflicts\<close>)
        THEN' fresh_tac);

    (* \<open>head G Shn v\<close> evaluated, as the list of its entries; \<open>explained\<close> under its own
       timing *)
    fun evaluated head v =
      HOLogic.dest_list (Value_Command.value ctxt
        (Syntax.check_term ctxt
          (Term.list_comb (Const (head, dummyT), [gram_t, Grammar_Common.fresh_term gram shn, v]))));
    fun explained label head v = timed ctxt label (evaluated head) v;

    (* a report whose explanation failed: the one group that says so, over the reported
       states themselves *)
    fun failed v exn =
      if Exn.is_interrupt exn then Exn.reraise exn
      else
        (NONE, [Pretty.str ("  (no explanation: " ^ Runtime.exn_message exn ^ ")"),
                Pretty.str ("  " ^ Syntax.string_of_term ctxt v)]);

    val stateT = HOLogic.natT;

    (* the groups of the conflict report with the counts for its summary: the witnessed
       states, the states where the search found nothing, the states it did not run
       on; with \<open>[[grammar_explain]]\<close> off, every state by its symbol path.  Under
       \<open>[[grammar_timing]]\<close> the searched states are evaluated one by one, after the
       tables alone, so that every search has its own time. *)
    fun rp_groups pairs () =
      let
        val explain_on = Config.get ctxt explain;
        val (searched, rest) =
          chop (if explain_on then Int.max (0, Config.get ctxt explain_states) else 0) pairs;
        val rp = \<^const_name>\<open>explain_rp\<close>;
        fun rp_entries ps = evaluated rp (HOLogic.mk_list stateT ps);
        fun rp_value label ps = timed ctxt label rp_entries ps;
        val full =
          if null searched then []
          else if Config.get ctxt Grammar_Common.timing then
            (rp_value "explain_rp (tables)" [];
             maps (fn (k, p) =>
               let
                 val (t, entries) = Timing.timing (map (pretty_rp ctxt (Lazy.force report_gram)) o rp_entries) [p];
                 val state = (case entries of (_, s, _) :: _ => s | [] => "no entry:");
               in
                 writeln ("[parser] explain_rp state " ^ string_of_int (k + 1) ^ ", " ^ state ^
                   " " ^ Timing.message t);
                 entries
               end) (map_index I searched))
          else map (pretty_rp ctxt (Lazy.force report_gram)) (rp_value "explain_rp" searched);
        val (witnessed, unwitnessed) = List.partition #1 full;
        val brief =
          if null rest orelse not explain_on then []
          else
            map (pretty_brief ctxt (Lazy.force report_gram))
              (explained "explain_rp_brief" \<^const_name>\<open>explain_rp_brief\<close>
                (HOLogic.mk_list stateT rest));
        val paths =
          if explain_on then []
          else
            (case check_value (paths_term ()) of
              SOME v => map (pretty_path ctxt (Lazy.force report_gram)) (HOLogic.dest_list v)
            | NONE => []);
        val summary =
          if explain_on then
            map_filter (fn (k, s) => if k = 0 then NONE else SOME (string_of_int k ^ " " ^ s))
              [(length witnessed, "with a layout witness"),
               (length unwitnessed, "without one within the search budget"),
               (length brief, "not searched")]
          else ["symbol paths only, \<open>grammar_explain\<close> is off"];
      in
        (summary,
         [(NONE, map #3 witnessed),
          (SOME "no layout with two live actions found within the search budget (the check \
            \may over-approximate in these states):", map #3 unwitnessed),
          (SOME ("not searched for a witness (\<open>grammar_explain_states\<close> = " ^
            string_of_int (length searched) ^ "):"), brief),
          (NONE, paths)])
      end;

    fun count n what = string_of_int n ^ " " ^ what ^ (if n = 1 then "" else "s");

    fun report_check () =
      let val t = conflicts_term \<^const_name>\<open>rlalr_conflicts\<close> in
        case check_value t of
          SOME (Const (\<^const_name>\<open>List.list.Nil\<close>, _)) =>
            (writeln ("parser: static determinism check empty for " ^
              entry ^ "; \<open>mdet\<close> discharged - \<open>" ^
              ".complete\<close> is unconditional"); true)
        | SOME v =>
            let
              val pairs = HOLogic.dest_list v;
              val (summary, groups) =
                (case Exn.result (rp_groups pairs) () of
                  Exn.Res x => x
                | Exn.Exn exn => ([], [failed v exn]));
            in
              (warning (pretty_report
                ("parser: " ^ entry ^ " has LR conflicts in " ^
                  count (length pairs) "state" ^
                  (if null summary then "" else " (" ^ commas summary ^ ")") ^
                  "; \<open>mdet\<close> kept as an assumption on .complete") groups); false)
            end
        | NONE => false
      end;

    (* accept/reduce: the relational .complete needs this check as well *)
    val acc_tac = SOLVED' (check_tac (conflicts_term \<^const_name>\<open>acc_conflicts\<close>));

    fun report_acc () =
      let val t = conflicts_term \<^const_name>\<open>acc_conflicts\<close> in
        case check_value t of
          SOME (Const (\<^const_name>\<open>List.list.Nil\<close>, _)) =>
            (writeln ("parser: accept/reduce check empty for " ^
              entry ^ "; the relational \<open>.complete\<close> is unconditional"); true)
        | SOME v =>
            let
              val groups =
                (case Exn.result (fn () =>
                    map (pretty_acc ctxt (Lazy.force report_gram))
                      (explained "explain_acc" \<^const_name>\<open>explain_acc\<close> v)) () of
                  Exn.Res entries => [(NONE, entries)]
                | Exn.Exn exn => [failed v exn]);
            in
              (warning (pretty_report
                ("parser: " ^ entry ^ " has accept/reduce conflicts in " ^
                  count (length (HOLogic.dest_list v)) "state" ^
                  "; \<open>acc_conflicts\<close> kept as an assumption on the relational .complete")
                groups); false)
            end
        | NONE => false
      end;

    val (head_name, arg_head) =
      (case HOLogic.dest_Trueprop prem of
        Const (c, _) $ (Const (d, _) $ _ $ _) $ _ => (c, d)
      | Const (c, _) $ _ $ _ => (c, "")
      | Const (c, _) $ _ => (c, "")
      | _ => ("", ""))
      handle TERM _ => ("", "");
  in
    if head_name = \<^const_name>\<open>fresh_name\<close> then
      (case get_check (HOLogic.dest_Trueprop prem) of
        SOME eq => SOME (resolve_tac ctxt [eq RS @{thm eqTrueE}])
      | NONE => SOME fresh_tac)
    else if head_name = \<^const_name>\<open>mdet\<close> then
      (if report_check () then SOME mdet_tac else NONE)
    else if head_name = \<^const_name>\<open>HOL.eq\<close> andalso
            arg_head = \<^const_name>\<open>acc_conflicts\<close> then
      (if report_acc () then SOME acc_tac else NONE)
    else NONE
  end;

val lr_gen : Parser_Generators.parser_generator =
  {build_parse      = lr_build_parse,
   sound_thm        = @{thm dparse_sound_generic},
   complete_thm     = @{thm dparse_complete_generic},
   rel_sound_thm    = SOME @{thm dparse_rel_sound_generic},
   rel_complete_thm = SOME @{thm dparse_rel_complete_generic},
   no_error_thm     = SOME @{thm recover_no_error_generic},
   ast_thms         =
     SOME {complete_lang = @{thm dparse_ast_complete_lang_generic},
           sound = @{thm dparse_ast_sound_generic},
           complete = @{thm dparse_ast_complete_generic},
           no_error = @{thm recover_no_error_ast_generic}},
   discharge_tac    = lr_discharge};

(** parser_error_states **)

fun error_states_cmd by_token raw ctxt =
  let
    val name =
      (case Proof_Context.read_const {proper = true, strict = false} ctxt raw of
        Const (n, _) => n
      | _ => error "parser_error_states: not a parser");
    val cov as {coverage, spelled, keys, ...} =
      (case get_coverage ctxt name of
        SOME c => c
      | NONE => error ("parser_error_states: " ^ quote raw ^ " is not a parser (diagnostics)"));
    val ((view, driver), _) = evaluate_coverage ctxt coverage [];
    val {hits, open_hits, ...} = report_coverage ctxt raw false cov (view, driver);
    val nt = length spelled;
    val lines =
      map (fn h as {state, look, word} =>
        "state " ^ string_of_int state ^ ", " ^ look_text spelled nt look ^
        (if covered keys h then "" else " (no message)") ^ ": " ^ sentence_text spelled word) hits;
  in
    writeln (cat_lines lines ^
      (if null open_hits then "" else "\n\n" ^ sendback (skeleton spelled by_token open_hits)))
  end;

val _ =
  Outer_Syntax.command \<^command_keyword>\<open>parser_error_states\<close>
    "list the error states of a parser with a shortest sentence"
    (Scan.optional (\<^keyword>\<open>(\<close> |-- Args.$$$ "token" --| \<^keyword>\<open>)\<close> >> K true) false -- Parse.const
      >> (fn (by_token, raw) =>
           Toplevel.keep (error_states_cmd by_token raw o Toplevel.context_of)));

end;

val _ = Theory.setup
  (Parser_Generators.register "LR" LR_Backend.lr_gen #> Parser_Generators.set_default "LR");
