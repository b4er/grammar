(* Author: Basil Fürer, Claude *)

(* the LR backend, diagnostics: the error driver of a parser, the errors block
   (sentences to messages), and the coverage of the error states *)

structure LR_Diagnostics =
struct

open LR_Util;

(** diagnostics: \<open>parser (diagnostics) p for G\<close> (LR_Diag) **)

(* the driver of p's code equation and its arguments, as lr_build_parse chose them:
   `p = (\<lambda>w. Option.bind (drv \<dots>) dec)` with drv
   - `brun (pctl P) (pfinal P) fst d ([i0], map (tenc f) w, [])`,
   - `case vrun_k K [v_av0 V] (vtnum f w) w [] of Some r \<Rightarrow> r | None \<Rightarrow> sdrun T \<dots>`,
     with sdrun started on kin, kcl and i0, and the theorem `vnum V = f`,
   - `drun_nh_c G Shn gt sts rt dt (([xin], tcols w), [xclos], [i0], w, [])`, or
   - `drun\<^sub>w\<^sub>f G Shn gt sts rt (\<dots>)`, which keeps a history *)
datatype diag_driver =
  Plain of term * term * term
| Vec of term * term * term * term * term * term * term * thm
| Dense of term * term * term * term * term * term * term * term * term
| Hist of term * term * term * term * term * term * term * term;

(* the terminals of the grammar in the order of their first occurrence in the
   productions, each with its spelling: the declared one for a fixed terminal,
   otherwise the name of the token value *)
fun spellings ctxt (gram: Grammar_Common.grammar) =
  let
    fun spelling t =
      (case AList.lookup (op aconv) (#lit_names gram) t of
        SOME s => s
      | NONE =>
          (case t of
            Const (c, _) => Long_Name.base_name c
          | _ => XML.content_of (YXML.parse_body (Syntax.string_of_term ctxt t))));
  in map (fn t => (t, spelling t)) (Vector.foldr (op ::) [] (#terminals gram)) end;

(* a generated list or option in messages: its element, so that \<open>Decl+\<close>, \<open>Decl*\<close>,
   \<open>Decl?\<close>, \<open>Sep1(Decl, ;)\<close> show as \<open>Decl\<close>, a group as its first symbol (a terminal
   quoted, \<open>(; Decl)*\<close> as \<open>';'\<close>), through nested lists. Generated: a display name ending
   in an operator (and fresh primes), or an instance of a list template of the prelude.
   The element: the first symbol of the first nonempty alternative, after the
   nonterminal itself if that alternative starts with it. Other templates, as
   \<open>Block(Decl)\<close>, keep their names. *)
fun element_names ctxt (gram: Grammar_Common.grammar) shown =
  let
    val spelled = Vector.fromList (map snd (spellings ctxt gram));
    val prods = fold (fn p => Inttab.update (#no p, p)) (#prods gram) Inttab.empty;
    fun disp n = the_default n (AList.lookup (op =) shown n);
    val list_templates = ["List", "List1", "Opt", "Sep", "Sep1"];
    fun generated n =
      let
        val cs = rev (String.explode (disp n)) |> drop_prefix (fn c => c = #"'");
        val head = Substring.string (#1 (Substring.splitl (fn c => c <> #"(") (Substring.full n)));
      in
        (case cs of
          c :: _ => member (op =) [#"*", #"+", #"?"] c
        | [] => false) orelse
        (head <> n andalso member (op =) list_templates (Long_Name.base_name head))
      end;
    fun first_sym n =
      (case Symtab.lookup (#nonterms gram) n of
        NONE => NONE
      | SOME {prods = ps, ...} =>
          (case find_first (not o null) (map (map #1 o #rhs o the o Inttab.lookup prods) ps) of
            SOME (Grammar_Common.RN m :: rest) => if m = n then try hd rest else SOME (Grammar_Common.RN m)
          | SOME (x :: _) => SOME x
          | _ => NONE));
    fun elem seen n =
      if member (op =) seen n orelse not (generated n) then NONE
      else
        (case first_sym n of
          SOME (Grammar_Common.RN m) =>
            SOME (the_default (disp m) (elem (n :: seen) m))
        | SOME (Grammar_Common.RC i) => SOME ("'" ^ Vector.sub (spelled, i) ^ "'")
        | SOME (Grammar_Common.RT i) => SOME ("'" ^ Vector.sub (spelled, i) ^ "'")
        | NONE => NONE);
  in map_filter (fn n => Option.map (pair n) (elem [] n)) (Symtab.keys (#nonterms gram)) end;

fun terminals_term ctxt (gram: Grammar_Common.grammar) =
  HOLogic.mk_list (HOLogic.mk_prodT (#tokT gram, HOLogic.stringT))
    (map (fn (t, s) => HOLogic.mk_prod (t, HOLogic.mk_string s)) (spellings ctxt gram));

(* a token on line 0 from its terminal, spelling, width and column, with its spelling as
   its text if the text is over char; a record with further fields needs \<open>token_info\<close> *)
fun token_maker ctxt (gram: Grammar_Common.grammar) token_info =
  let
    val {chT, moreT, ...} = Grammar_Common.get_desc gram;
    fun c n = Const (n, dummyT);
    val zero = HOLogic.mk_number \<^typ>\<open>nat\<close> 0;
    fun make more t s width col =
      let
        val txt = if chT = \<^typ>\<open>char\<close> then s else HOLogic.mk_list chT [];
        val sp = c \<^const_name>\<open>span.make\<close> $ zero $ col $ col $ width $ txt;
      in c \<^const_name>\<open>token_ext\<close> $ t $ sp $ more t end;
  in
    (case (token_info, moreT = HOLogic.unitT) of
      (_, true) => SOME (make (K HOLogic.unit))
    | (SOME f, false) =>
        let
          val fT = #tokT gram --> moreT;
          val ft = Syntax.check_term ctxt (Type.constraint fT (Syntax.parse_term ctxt f));
        in SOME (make (fn t => ft $ t)) end
    | (NONE, false) => NONE)
  end;

(* the word of a sentence, NONE with a warning if it cannot be built: its tokens are at
   the given column or one past the token before; a token record with further fields
   needs token_info or a word given as a term *)
fun sentence_word ctxt (gram: Grammar_Common.grammar) mk_token label sentence =
  let
    val {wordT, ...} = Grammar_Common.get_desc gram;
    val spelled = map swap (spellings ctxt gram);
    fun num n = HOLogic.mk_number \<^typ>\<open>nat\<close> n;
    fun token (t, s) col =
      the mk_token t (HOLogic.mk_string s) (num (size s)) (num col);
    fun tokens _ [] = []
      | tokens next ((ts, col) :: rest) =
          let val at = the_default next col
          in token ts at :: tokens (at + size (snd ts) + 1) rest end;
    fun skip msg = (warning ("parser: errors, " ^ label ^ ": " ^ msg ^ "; it is ignored"); NONE);
  in
    (case sentence of
      Parser_Generators.Word s =>
        (case Exn.result (Syntax.check_term ctxt o Type.constraint wordT o Syntax.parse_term ctxt) s of
          Exn.Res w =>
            (case Term.add_frees w [] of
              [] => SOME (w, NONE)
            | (x, _) :: _ => skip ("the variable " ^ quote x ^ " is free"))
        | Exn.Exn exn =>
            if Exn.is_interrupt exn then Exn.reraise exn else skip (Runtime.exn_message exn))
    | Parser_Generators.Symbols syms =>
        (case filter_out (AList.defined (op =) spelled o fst) syms of
          (s, _) :: _ => skip (quote s ^ " is not a terminal of the grammar")
        | [] =>
            if is_none mk_token then
              skip "tokens with further fields need a word as a term, or token_info"
            else
              let
                val toks =
                  map (fn (s, col) => ((the (AList.lookup (op =) spelled s), s), col)) syms;
              in
                SOME
                  (Syntax.check_term ctxt
                    (Type.constraint wordT (HOLogic.mk_list dummyT (tokens 0 toks))),
                   SOME (length syms))
              end))
  end;

(* the hole digits of a template: $i stands for the source text of stack entry i, as in
   the message templates of \<^cite>\<open>\<open>Sect.~5\<close> in "pottier2016-lr1-reachability"\<close> *)
fun template_holes text =
  let
    fun go ("$" :: d :: rest) =
          if Symbol.is_ascii_digit d then (ord d - ord "0") :: go rest else go (d :: rest)
      | go (_ :: rest) = go rest
      | go [] = [];
  in go (map String.str (String.explode text)) end;

(** coverage of the error states \<^cite>\<open>\<open>Sect.~3.5\<close> in "pottier2016-lr1-reachability"\<close>, LR_Reach **)

val parser_errors_budget =
  Attrib.setup_config_int \<^binding>\<open>parser_errors_budget\<close> (K 0);

(* what \<open>parser_error_states\<close> needs: the constant p_coverage, the terminals with their
   spellings, the error token, whether columns matter, the keys of the block as (state,
   SOME terminal for (token)), and the number of (shift) keys *)
type coverage =
 {coverage: term, spelled: string list, hide: int option, columns: bool, vec: bool,
  replay: bool, keys: (int * int option) list, shifts: int};

structure Coverage_Data = Generic_Data
(
  type T = coverage Symtab.table;
  val empty = Symtab.empty;
  fun merge data = Symtab.merge (K true) data;
);

fun get_coverage ctxt name = Symtab.lookup (Coverage_Data.get (Context.Proof ctxt)) name;

fun evaluate_coverage ctxt cov_c ws =
  Code_Runtime.dynamic_value_strict
    (LR_Reach_Cookie.get, LR_Reach_Cookie.put, \<^unchecked_name>\<open>LR_Reach_Cookie.put\<close>)
    ctxt NONE (K I)
    (Syntax.check_term ctxt
      (HOLogic.mk_prod (cov_c, HOLogic.mk_list (HOLogic.listT \<^typ>\<open>integer\<close>) ws))) [];

fun triples (a :: b :: c :: r) = (a, b, c) :: triples r
  | triples _ = [];

fun pairs (a :: b :: r) = (a, b) :: pairs r
  | pairs _ = [];

fun prods (a :: n :: r) = (a, take n r) :: prods (drop n r)
  | prods _ = [];

fun dest_view ([ns, nt, nn, i0] :: tr :: pr :: rd :: fin :: dep :: ambig :: _) =
      ({nstates = ns, nterms = nt, nnts = nn, start = i0, finals = fin,
        trans = triples tr, prods = prods pr, reds = triples rd}: LR_Reach.view,
       pairs dep, ambig)
  | dest_view _ = raise Fail "dest_view";

(* the anchors of the vector driver, from the rows after the view (lr_view) *)
fun dest_anchors (_ :: _ :: _ :: _ :: _ :: _ :: _ :: rl :: kn :: cl :: _) =
      let
        fun rels (n :: r) = take n r :: rels (drop n r)
          | rels _ = [];
        fun kernels (_ :: n :: r) = pairs (take (2 * n) r) :: kernels (drop (2 * n) r)
          | kernels _ = [];
        fun fives (a :: b :: c :: d :: e :: r) = (a, b, c, d, e) :: fives r
          | fives _ = [];
      in SOME {rels = rels rl, kernels = kernels kn, cells = fives cl}: LR_Reach.anchors option end
  | dest_anchors _ = NONE;

(* the error pairs of a view: found by the driver; without columns the engine's, with
   them the column-blind automaton gives an upper bound, each pair of it a candidate
   unless the anchors of the vector driver rule it out *)
fun error_pairs ctxt ({spelled, hide, columns, vec, replay, ...}: coverage) (view, driver) =
  let
    val seconds = Real.fromInt (Config.get ctxt parser_errors_budget);
    val timer = Timer.startRealTimer ();
    val (v, dep, _) = dest_view view;
    val nt = #nterms v;
    val r = LR_Reach.run {hide = hide, seconds = seconds} v;
    val dep_tab = Inttab.make_set (map (fn (s, z) => s * (nt + 1) + z) dep);
    val on_columns =
      if columns then
        filter (fn {state, look, ...} => Inttab.defined dep_tab (state * (nt + 1) + look))
          (#reached r)
      else [];
    val (on_columns, pruned) =
      (case (if columns andalso vec then dest_anchors view else NONE) of
        NONE => (on_columns, 0)
      | SOME a =>
          (case LR_Reach.column_errors
              {seconds = Real.max (0.0, seconds - Time.toReal (Timer.checkRealTimer timer))} v a of
            NONE => (on_columns, 0)
          | SOME may =>
              let val (keep, out) = List.partition (fn {state, look, ...} => may (state, look)) on_columns
              in (keep, length out) end));
    fun target ({state, look, word, ...}: LR_Reach.vertex) = (state, look, word);
    val targets =
      sort (int_ord o apply2 (fn (_, _, w) => length w))
        (map target (#errors r @ on_columns));
    val left = Real.max (0.0, seconds - Time.toReal (Timer.checkRealTimer timer));
    val widths = Vector.fromList (map size spelled);
    val hits =
      if replay then
        LR_Reach.confirm {driver = driver o maps (fn (t, c) => [t, c]), nterms = nt,
          widths = widths, columns = columns, seconds = left} targets
      else
        map (fn {state, look, word, ...} =>
          {state = state, look = look, word = map (rpair NONE) word}) (#errors r);
    val hit = member (op =) (map (fn {state, look, ...} => (state, look)) hits);
    val missed = filter_out (fn (s, z, _) => hit (s, z)) targets;
  in
    {complete = #complete r, facts = #facts r, nodes = #nodes r, edges = #edges r,
     errors = length (#errors r), hits = hits, missed = missed, pruned = pruned,
     time = Time.toReal (Timer.checkRealTimer timer)}
  end;

fun error_hits ctxt cov result = #hits (error_pairs ctxt cov result);

fun sentence_text spelled word =
  if null word then "\<open>[]\<close>"
  else
    space_implode " " (map (fn (t, col) =>
      quote (nth spelled t) ^ (case col of NONE => "" | SOME c => " @ " ^ string_of_int c)) word);

fun look_text spelled nt z = if z >= nt then "the end of the input" else quote (nth spelled z);

fun covered keys ({state, look, ...}: LR_Reach.hit) =
  member (op =) keys (state, NONE) orelse member (op =) keys (state, SOME look);

(* one entry for each state, on the shortest sentence, or for each pair under \<open>(token)\<close> *)
fun skeleton spelled by_token (hits: LR_Reach.hit list) =
  let
    fun entry ({state, look, word}: LR_Reach.hit) =
      sentence_text spelled word ^ (if by_token then " (token)" else "") ^
      " \<Rightarrow> \<open>TODO state " ^ string_of_int state ^
      (if by_token then ", before " ^ look_text spelled (length spelled) look else "") ^ "\<close>";
    fun shortest (h: LR_Reach.hit) tab =
      Inttab.map_default (#state h, h)
        (fn h' => if length (#word h) < length (#word h') then h else h') tab;
    val chosen = if by_token then hits else map #2 (Inttab.dest (fold shortest hits Inttab.empty));
  in
    "errors\n    " ^ space_implode "\n  | " (map entry chosen)
  end;

fun sendback text =
  Active.sendback_markup_properties [Markup.padding_command] text;

fun report_coverage ctxt name warn_open
    (cov as {spelled, columns, keys, shifts, replay, ...}: coverage) result =
  let
    val {complete, facts, errors, hits, missed, pruned, time, ...} = error_pairs ctxt cov result;
    val nt = length spelled;
    val states = distinct (op =) (map #state hits);
    val open_hits = filter_out (covered keys) hits;
    val open_states = distinct (op =) (map #state open_hits);
    val _ =
      writeln ("parser: " ^ name ^ ": " ^ string_of_int (length states) ^ " error states (" ^
        string_of_int (length hits) ^ " pairs of a state and a terminal), " ^
        string_of_int (length states - length open_states) ^ " of them covered, by " ^
        string_of_int (length keys) ^ " keys; " ^ string_of_int facts ^ " facts, " ^
        Real.fmt (StringCvt.FIX (SOME 2)) time ^ " s" ^
        (if pruned > 0 then "; " ^ string_of_int pruned ^
           " pairs that need columns ruled out by the anchors" else "") ^
        (if shifts > 0 then "; " ^ string_of_int shifts ^
           " (shift) keys do not count, as they cover no error state" else ""));
    val _ =
      if complete then ()
      else
        warning ("parser: " ^ name ^ ": [[parser_errors_budget]] ran out: the list is not complete");
    val _ =
      if null missed then ()
      else if not replay then
        warning ("parser: " ^ name ^ ": tokens with further fields need token_info to run a \
          \sentence, so the pairs that depend on columns are left out")
      else
        warning ("parser: " ^ name ^ ": " ^ string_of_int (length missed) ^
          (if columns then
             " candidates were not reached in any layout tried: the list is not known to be complete"
           else " sentences did not stop where expected: the list may be wrong") ^
          "\n" ^ cat_lines (map (fn (s, z, w) =>
            "  state " ^ string_of_int s ^ ", " ^ look_text spelled nt z ^ ": " ^
            sentence_text spelled (map (rpair NONE) w)) (take 20 missed)));
    val _ =
      if not warn_open orelse null open_hits then ()
      else
        warning ("parser: " ^ name ^ ": " ^ string_of_int (length open_states) ^
          " error states have no message:\n" ^ sendback (skeleton spelled false open_hits));
  in {errors = errors, hits = hits, open_hits = open_hits} end;

(* `p_messages`, from the sentences of an \<open>errors\<close> block: one evaluation of p_coverage
   with the error of each word gives each its error state, with no theorem, and the
   tables and the driver for coverage on the way.  The key is the state where the error
   is detected, with the terminal for \<open>(token)\<close>, or the state after the last shift for
   \<open>(shift)\<close>.  Everything wrong with a sentence is a warning and the sentence is dropped,
   so that a block can never fail the parser: a word that cannot be evaluated, is accepted
   (not correct), or has a key taken by an earlier sentence (not irredundant).  Should
   the evaluation fail, the sentences are evaluated one by one, so that the others stay.
   With \<open>given\<close>, the errors from the evaluation of the checks (lr_checks_keys), there
   is no evaluation here and no tables for coverage.
   A word rejected before its last token, or a hole below the stack, only warns. *)
fun sentence_label i = "sentence " ^ string_of_int (i + 1);

(* the words of the sentences that can be built, with their index and message *)
fun error_words lthy gram mk_token errors =
  map_filter I (map_index (fn (i, m as {sentence, ...}: Parser_Generators.error_message) =>
    Option.map (fn (w, n) => (i, m, w, n))
      (sentence_word lthy gram mk_token (sentence_label i) sentence)) errors);

fun error_messages lthy (gram: Grammar_Common.grammar) (probe_b, cov_b) (words, given) =
  let
    fun c n = Const (n, dummyT);
    val label = sentence_label;
    fun global b =
      (case Grammar_Common.def_axiom lthy (b, Thm.def_binding b) of
        SOME ax => fst (Logic.dest_equals (Thm.prop_of (Local_Defs.meta_rewrite_rule lthy ax)))
      | NONE => raise Fail "error_messages: no foundation for a constant");
    val probe_c = global probe_b;
    val cov_c = global cov_b;
    val ts = Vector.foldr (op ::) [] (#terminals gram);
    val ts_t = HOLogic.mk_list (#tokT gram) ts;
    fun dest_probe [] = NONE
      | dest_probe [st, tk, sh, idx, depth] = SOME (st, tk, sh, idx, depth)
      | dest_probe _ = raise Fail "error_messages: probe";
    fun enc_of (_, _, w, _) =
      c \<^const_name>\<open>reach_enc\<close> $ ts_t $ (c \<^const_name>\<open>diag_probe\<close> $ (probe_c $ w));
    fun probes ws = evaluate_coverage lthy cov_c (map enc_of ws) ||> map dest_probe;
    fun guarded ws =
      (case Exn.result probes ws of
        Exn.Res rs => Exn.Res rs
      | Exn.Exn exn => if Exn.is_interrupt exn then Exn.reraise exn else Exn.Exn exn);
    fun one (word as (i, _, _, _)) =
      (case guarded [word] of
        Exn.Res (_, rs) => map (pair word) rs
      | Exn.Exn exn =>
          (warning ("parser: errors, " ^ label i ^ ": it cannot be evaluated: " ^
             Runtime.exn_message exn ^ "; it is ignored"); []));
    val keyT = Type (\<^type_name>\<open>pkey\<close>, [#tokT gram]);
    val num = HOLogic.mk_number \<^typ>\<open>nat\<close>;
    val nt = length ts;
    val optT = Type (\<^type_name>\<open>option\<close>, [#tokT gram]);
    fun tk_term tk =
      if tk = nt then SOME (Const (\<^const_name>\<open>None\<close>, optT))
      else if tk < nt then SOME (Const (\<^const_name>\<open>Some\<close>, #tokT gram --> optT) $ nth ts tk)
      else NONE;
    fun key ({key, ...}: Parser_Generators.error_message) (st, tk, sh) =
      (case key of
        Parser_Generators.By_State => SOME (Const (\<^const_name>\<open>PState\<close>, \<^typ>\<open>nat\<close> --> keyT) $ num st, (st, NONE))
      | Parser_Generators.By_Token =>
          Option.map (fn t =>
            (Const (\<^const_name>\<open>PToken\<close>, \<^typ>\<open>nat\<close> --> fastype_of t --> keyT) $ num st $ t, (st, SOME tk)))
            (tk_term tk)
      | Parser_Generators.By_Shift => SOME (Const (\<^const_name>\<open>PShift\<close>, \<^typ>\<open>nat\<close> --> keyT) $ num sh, (~1, NONE)));
    fun step ((i, m as {text, ...}: Parser_Generators.error_message, _, len), r) kept =
      (case r of
        NONE =>
          (warning ("parser: errors, " ^ label i ^ ": the word is accepted, so the message \
             \cannot be reached (not correct); it is ignored"); kept)
      | SOME (st, tk, sh, idx, depth) =>
          let
            val _ =
              (case len of
                SOME n =>
                  if idx + 1 < n then
                    warning ("parser: errors, " ^ label i ^ ": the word is rejected at its token " ^
                      string_of_int idx ^ ", before its last one")
                  else ()
              | NONE => ());
            val _ =
              (case filter (fn h => h >= depth) (template_holes text) of
                h :: _ =>
                  warning ("parser: errors, " ^ label i ^ ": $" ^ string_of_int h ^
                    " is below the stack, which has " ^ string_of_int depth ^ " entries here")
              | [] => ());
          in
            (case key m (st, tk, sh) of
              NONE =>
                (warning ("parser: errors, " ^ label i ^
                   ": it is rejected at a terminal of no production; it is ignored"); kept)
            | SOME (k, code) =>
                (case find_first (fn (k', _, _, _) => k' aconv k) kept of
                  SOME (_, j, _, _) =>
                    (warning ("parser: errors, " ^ label i ^ ": same key as " ^ label j ^
                       " (not irredundant), state " ^ string_of_int st ^ "; it is ignored"); kept)
                | NONE => (k, i, text, code) :: kept))
          end);
    fun messages kept =
      HOLogic.mk_list (HOLogic.mk_prodT (keyT, HOLogic.stringT))
        (map (fn (k, _, s, _) => HOLogic.mk_prod (k, HOLogic.mk_string s)) (rev kept));
    val (tables, results) =
      (case given of
        SOME rs => (NONE, words ~~ map dest_probe rs)
      | NONE =>
          (case guarded words of
            Exn.Res (tabs, rs) => (SOME tabs, words ~~ rs)
          | Exn.Exn _ => (NONE, maps one words)));
    val kept = fold step results [];
  in
    (Syntax.check_term lthy (messages kept), map #4 (rev kept), tables)
  end;

(* `p_terminals`, the candidates of the expected set with their spellings, and
   `p_diag`, which runs the word once over the tables of p's code equation `p = (\<lambda>w.
   Option.bind (drv \<dots>) dec)`: `p_diag w = pdiag P i0 f ts dec w` for the simple
   driver, `ldiag_c G Shn gt sts rt dt xin xclos i0 ts dec w` for drun_nh_c,
   `vkdiag V K T kin kcl i0 f ts dec w` for the vector one, with `ts = map fst p_terminals`; for
   a driver with a history (drun\<^sub>w\<^sub>f) it runs p and on a rejection the
   diagnosis, `p_diag w = (case p w of Some x \<Rightarrow> Inr x | None \<Rightarrow> Inl (ldiagnose G Shn gt
   sts rt xin xclos i0 ts w))`.  `p_diag.Inr_iff` from LR_Diag's `*_Inr_iff`.  For the
   messages `p_info`, over the grammar, the states `states_c` and `p_terminals`, and for
   tokens over char `p_render = perr_render p_info (\<lambda>c. [c])` (over unit, whose tokens
   have no text, `\<lambda>_. []`; over any other type the client supplies its own).  Only definitions,
   nothing is evaluated, but for an \<open>errors\<close> block, which also defines `p_messages` *)
fun define_diagnostics gram states_c (block, errors, given) recover repair on_error_reduce token_info tabs columns
    parse_bind parse_c parse_alt_th dec driver lthy =
  let
    fun c n = Const (n, dummyT);
    (* on the vector driver the code equations of p_diag (or p_diag_base) and p_repair
       number the tokens by p's numbering f, by `vnum V = f`, not by a search in V *)
    val recode_rews =
      (case driver of
        SOME (Vec (_, _, _, _, _, _, _, tnum_th)) =>
          map (fn r => (r OF [tnum_th]) RS @{thm eq_reflection})
            @{thms vkdiag_f_eq vrstop_f_eq}
      | _ => []);
    fun recode b def lthy =
      let val th = Local_Defs.unfold lthy recode_rews def in
        if null recode_rews orelse Thm.eq_thm_prop (th, def) then lthy
        else
          let
            val glob =
              (case Grammar_Common.def_axiom lthy (b, Thm.def_binding b) of
                SOME ax => Local_Defs.unfold lthy recode_rews ax
              | NONE => th);
          in
            lthy
            |> Code.declare_eqns [(th, true)]
            |> Grammar_Common.declare_code_global {default = false} [glob]
          end
      end;
    fun rerun e w =
      c \<^const_name>\<open>case_option\<close> $ (c \<^const_name>\<open>Inl\<close> $ e) $ c \<^const_name>\<open>Inr\<close> $ (parse_c $ w);
    (* the one pass with the fact that rewrites its Inr case to p's code equation,
       or the rerun *)
    fun diag_with drv d ts w =
      (case drv of
        Plain (P, i0, f) =>
          (SOME @{thm pdiag_Inr_iff}, c \<^const_name>\<open>pdiag\<close> $ P $ i0 $ f $ ts $ d $ w)
      | Vec (V, K, T, kin, kcl, i0, f, _) =>
          (SOME @{thm vkdiag_Inr_iff},
            c \<^const_name>\<open>vkdiag\<close> $ V $ K $ T $ kin $ kcl $ i0 $ f $ ts $ d $ w)
      | Dense (G, Shn, gt, sts, rt, dt, xin, xclos, i0) =>
          (SOME @{thm ldiag_c_Inr_iff},
            c \<^const_name>\<open>ldiag_c\<close> $ G $ Shn $ gt $ sts $ rt $ dt $ xin $ xclos $ i0 $ ts $ d $ w)
      | Hist (G, Shn, gt, sts, rt, xin, xclos, i0) =>
          (NONE, rerun
            (c \<^const_name>\<open>ldiagnose\<close> $ G $ Shn $ gt $ sts $ rt $ xin $ xclos $ i0 $ ts $ w) w));
    val keep_ast = Abs ("t", dummyT, c \<^const_name>\<open>Some\<close> $ HOLogic.unit);
    (* the error of a sentence, with no decoder and no trial, as only its state and
       stack are read; on the vector driver by `vdiag`, whose error is the one a message
       is looked up for at run time *)
    fun probe_body drv w =
      let
        val keep = keep_ast;
        val none = c \<^const_name>\<open>Nil\<close>;
      in
        (case drv of
          Vec (V, _, T, kin, kcl, i0, _, _) =>
            c \<^const_name>\<open>vdiag\<close> $ V $ T $ kin $ kcl $ i0 $ none $ keep $ w
        | _ => snd (diag_with drv keep none w))
      end;
  in
    (case driver of
      NONE =>
        (warning ("parser (diagnostics): not supported for the driver of \<open>" ^
           Binding.name_of parse_bind ^ "\<close>; \<open>" ^
           Binding.name_of parse_bind ^ "_diag\<close> is not defined");
         lthy)
    | SOME drv =>
        let
          val wordT = domain_type (fastype_of parse_c);
          val w = Free ("w", wordT);
          val (terminals_eq, lthy) =
            define_term parse_bind "terminals" (terminals_term lthy gram) lthy;
          val all_ts = c \<^const_name>\<open>map\<close> $ c \<^const_name>\<open>fst\<close> $ rhs_of_eq terminals_eq;
          (* the error token is never offered as expected *)
          val ts =
            (case recover of
              SOME (_, e) =>
                c \<^const_name>\<open>filter\<close> $
                  Abs ("t", #tokT gram, HOLogic.mk_not (c \<^const_name>\<open>HOL.eq\<close> $ Bound 0 $ e)) $ all_ts
            | NONE => all_ts);
          val {gram_t, shn_t, gt_t, rt_t, i0_t} = tabs;
          val pf_t = c \<^const_name>\<open>pfins\<close> $ shn_t $ states_c;
          (* on_error_reduce: the forced tables and the second run on them, none on the
             simple driver *)
          val forced_names =
            (case (drv, on_error_reduce) of
              (_, []) => []
            | (Plain _, _) =>
                (warning ("parser: on_error_reduce is not supported on the simple driver of \<open>" ^
                   Binding.name_of parse_bind ^ "\<close>; it is ignored"); [])
            | _ =>
                let
                  val known = map fst (Grammar_Common.nonterms_list gram);
                  val (good, bad) = List.partition (member (op =) known) on_error_reduce;
                  val _ =
                    if null bad then ()
                    else warning ("parser: on_error_reduce: not a nonterminal of the grammar: " ^
                      commas_quote bad ^ "; ignored");
                in good end);
          val names_t =
            HOLogic.mk_list (#nameT (Grammar_Common.get_desc gram))
              (map (Grammar_Common.name_term gram) forced_names);
          val (rt_view, forced, lthy) =
            if null forced_names then (rt_t, NONE, lthy)
            else
              let
                val (rt_eq, lthy) =
                  define_term parse_bind "oer_redtab"
                    (Syntax.check_term lthy
                      (c \<^const_name>\<open>oer_cells\<close> $ names_t $ gram_t $ ts $ pf_t $ gt_t $ rt_t))
                    lthy;
                val rt' = rhs_of_eq rt_eq;
              in
                (case drv of
                  Vec (_, _, _, _, _, i0, _, _) =>
                    let
                      val (T_eq, lthy) =
                        define_term parse_bind "oer_stab"
                          (Syntax.check_term lthy
                            (c \<^const_name>\<open>mk_stab\<close> $ gram_t $ shn_t $ gt_t $ states_c $ rt')) lthy;
                      val T = rhs_of_eq T_eq;
                      val (kin_eq, lthy) =
                        define_term parse_bind "oer_sinit"
                          (Syntax.check_term lthy (c \<^const_name>\<open>sinit\<close> $ T)) lthy;
                      val kin = rhs_of_eq kin_eq;
                      val (kcl_eq, lthy) =
                        define_term parse_bind "oer_sclos"
                          (Syntax.check_term lthy (c \<^const_name>\<open>sclosure\<close> $ T $ kin)) lthy;
                      fun run d w = c \<^const_name>\<open>sdiag\<close> $ T $ kin $ rhs_of_eq kcl_eq $ i0 $ ts $ d $ w;
                    in (rt', SOME run, lthy) end
                | Dense (G, Shn, gt, sts, _, dt, xin, xclos, i0) =>
                    (rt', SOME (fn d => fn w =>
                       c \<^const_name>\<open>ldiag_c\<close> $ G $ Shn $ gt $ sts $ rt' $ dt $ xin $ xclos $ i0 $ ts $ d $ w),
                     lthy)
                | Hist (G, Shn, gt, sts, _, xin, xclos, i0) =>
                    (rt', SOME (fn _ => fn w =>
                       c \<^const_name>\<open>Inl\<close> $
                         (c \<^const_name>\<open>ldiagnose\<close> $ G $ Shn $ gt $ sts $ rt' $ xin $ xclos $ i0 $ ts $ w)),
                     lthy)
                | Plain _ => raise Fail "define_diagnostics: Plain")
              end;
          fun with_forced d base =
            (case forced of
              NONE => base
            | SOME run =>
                c \<^const_name>\<open>oer_diag\<close> $ base $
                  (let val v = Free ("v", wordT) in lambda v (run d v) end));
          val (iff_rule, body) = diag_with drv dec ts w;
          (* with forced tables, p_diag is oer_diag over the one pass, p_diag_base *)
          val (base_def, body, lthy) =
            (case forced of
              NONE => (NONE, body, lthy)
            | SOME _ =>
                let
                  val base_b = Binding.map_name (fn n => n ^ "_diag_base") parse_bind;
                  val ((base_c, def), lthy) =
                    Grammar_Defs.define_const true (base_b, Thm.def_binding base_b,
                      Syntax.check_term lthy (lambda w body)) lthy;
                  val lthy = recode base_b def lthy;
                in (SOME (base_c, def), with_forced dec base_c $ w, lthy) end);
          (* the raw errors speak of the grammar the user wrote *)
          val orig_opt = Option.map #orig (#restricted (Grammar_Common.artifacts_of gram));
          val body =
            (case orig_opt of
              SOME orig => c \<^const_name>\<open>pe_diag_names\<close> $ orig $ body
            | NONE => body);
          val diag_b = Binding.map_name (fn n => n ^ "_diag") parse_bind;
          val ((diag_c, diag_def), lthy) =
            Grammar_Defs.define_const true (diag_b, Thm.def_binding diag_b,
              Syntax.check_term lthy (lambda w body)) lthy;
          val lthy = recode diag_b diag_def lthy;
          val x = Free ("x", (case range_type (fastype_of parse_c) of Type (_, [T]) => T | T => T));
          val iff_t =
            Syntax.check_prop lthy
              (HOLogic.mk_Trueprop (HOLogic.mk_eq
                (HOLogic.mk_eq (diag_c $ w, c \<^const_name>\<open>Inr\<close> $ x),
                 HOLogic.mk_eq (parse_c $ w, c \<^const_name>\<open>Some\<close> $ x))));
          fun tac ctxt =
            (case (iff_rule, base_def) of
              (SOME r, SOME (_, def)) =>
                Local_Defs.unfold_tac ctxt
                  [diag_def, @{thm pe_diag_names_Inr_iff}, @{thm oer_diag_Inr_iff}, def, r, parse_alt_th]
                THEN resolve_tac ctxt @{thms refl} 1
            | (SOME r, NONE) =>
                Local_Defs.unfold_tac ctxt [diag_def, @{thm pe_diag_names_Inr_iff}, r, parse_alt_th]
                THEN resolve_tac ctxt @{thms refl} 1
            | (NONE, SOME (_, def)) =>
                HEADGOAL (asm_full_simp_tac
                  (ctxt |> Simplifier.add_simps [diag_def, def, @{thm pe_diag_names_Inr_iff}, @{thm oer_diag_Inr_iff}]
                    |> Splitter.add_split @{thm option.split}))
            | (NONE, NONE) =>
                HEADGOAL (asm_full_simp_tac
                  (ctxt |> Simplifier.add_simps [diag_def, @{thm pe_diag_names_Inr_iff}] |> Splitter.add_split @{thm option.split})));
          val iff_th = Goal.prove lthy ["w", "x"] [] iff_t (fn {context, ...} => tac context);
          val lthy =
            lthy
            |> Local_Theory.notes [((Grammar_Common.qualify_bind diag_b "Inr_iff", []), [([iff_th], [])])]
            |> #2;
          (* the messages: p_info (grammar, states, spellings, nonterminal names, up to
             5 terminals listed before the summary, hand-written messages) and, for tokens
             over char, p_render = perr_render p_info (\<lambda>c. [c]) *)
          val mk_token = token_maker lthy gram token_info;
          val spelled = map snd (spellings lthy gram);
          (* p_probe, and p_coverage, which only \<open>errors\<close> and parser_error_states
             evaluate: the view of the tables and the driver as a function on numbers *)
          val probe_b = Binding.map_name (fn n => n ^ "_probe") parse_bind;
          val ((probe_c, _), lthy) =
            Grammar_Defs.define_const true (probe_b, Thm.def_binding probe_b,
              Syntax.check_term lthy
                (lambda w
                  (if is_some forced then with_forced keep_ast (lambda w (probe_body drv w)) $ w
                   else probe_body drv w))) lthy;
          val cov_b = Binding.map_name (fn n => n ^ "_coverage") parse_bind;
          val view_t =
            c \<^const_name>\<open>lr_view\<close> $ names_t $ gram_t $ pf_t $ i0_t $ all_ts $ states_c $
              gt_t $ rt_view;
          val fn_t =
            (case mk_token of
              NONE =>
                Abs ("is", HOLogic.listT \<^typ>\<open>integer\<close>,
                  HOLogic.mk_list \<^typ>\<open>integer\<close> [])
            | SOME mk =>
                c \<^const_name>\<open>reach_fn\<close> $ probe_c $
                  Abs ("t", #tokT gram, Abs ("s", HOLogic.stringT, Abs ("c", \<^typ>\<open>nat\<close>,
                    mk (Bound 2) (Bound 1) (HOLogic.size_const HOLogic.stringT $ Bound 1) (Bound 0)))) $
                  rhs_of_eq terminals_eq);
          val (_, lthy) =
            Grammar_Defs.define_const true (cov_b, Thm.def_binding cov_b,
              Syntax.check_term lthy (c \<^const_name>\<open>Pair\<close> $ view_t $ fn_t)) lthy;
          val (msgs, keys, tables, lthy) =
            if not block then (c \<^const_name>\<open>Nil\<close>, [], NONE, lthy)
            else
              let
                val (t, keys, tables) =
                  timed lthy "post: errors"
                    (error_messages lthy gram (probe_b, cov_b))
                    (errors, (case (drv, forced) of (Vec _, NONE) => given | _ => NONE));
                val (eq, lthy) = define_term parse_bind "messages" t lthy;
              in (rhs_of_eq eq, keys, tables, lthy) end;
          val cov_axiom = Grammar_Common.def_axiom lthy (cov_b, Thm.def_binding cov_b);
          val cov_term =
            (case cov_axiom of
              SOME ax => SOME (fst (Logic.dest_equals (Thm.prop_of (Local_Defs.meta_rewrite_rule lthy ax))))
            | NONE => NONE);
          val hide =
            Option.map (fn (_, e) =>
              find_index (fn t => t aconv e) (Vector.foldr (op ::) [] (#terminals gram))) recover;
          val record: coverage =
            {coverage = the_default (c \<^const_name>\<open>Nil\<close>) cov_term, spelled = spelled, hide = hide,
             columns = columns, vec = (case (drv, forced) of (Vec _, NONE) => true | _ => false),
             replay = is_some mk_token,
             keys = filter (fn (s, _) => s >= 0) keys,
             shifts = length (filter (fn (s, _) => s < 0) keys)};
          val _ =
            (case tables of
              SOME tabs =>
                if Config.get lthy parser_errors_budget > 0 then
                  let
                    val (_, _, ambig) = dest_view (fst tabs);
                    val _ =
                      if null ambig then ()
                      else warning ("parser: on_error_reduce: states with two reductions, the \
                        \lowest production is taken: " ^ commas (map string_of_int ambig));
                  in
                    ignore (timed lthy "post: coverage"
                      (report_coverage lthy (Binding.name_of parse_bind) true record)
                      (fst tabs, fn x => snd tabs x))
                  end
                else ()
            | NONE => ());
          val lthy =
            lthy |> Local_Theory.declaration {syntax = false, pervasive = true, pos = Position.none}
              (fn phi => fn ctxt =>
                (case Morphism.term phi parse_c of
                  Const (n, _) =>
                    Coverage_Data.map (Symtab.update (n,
                      {coverage = Morphism.term phi (#coverage record), spelled = spelled, hide = hide,
                       columns = columns, vec = #vec record, replay = #replay record, keys = #keys record,
                       shifts = #shifts record})) ctxt
                | _ => ctxt));
          val {nameT, chT, moreT, ...} = Grammar_Common.get_desc gram;
          (* a nonterminal in messages: its name in the grammar as written (under a
             precedence restriction), shown with the grammars' qualifiers dropped, a
             generated list or option as its element *)
          val shown = Grammar_Common.display_names lthy (Symtab.keys (#nonterms gram));
          (* a generated list or option: its element *)
          val shown =
            let val elems = element_names lthy gram shown
            in elems @ filter_out (AList.defined (op =) elems o #1) shown end;
          (* under nat_labels every nonterminal is in the table, shown by its name *)
          val table =
            if #nat_labels gram then
              map (fn (n, _) => (n, the_default n (AList.lookup (op =) shown n)))
                (Grammar_Common.nonterms_list gram)
            else shown;
          val show_t =
            if null table then NONE
            else
              let
                val pairT = HOLogic.mk_prodT (nameT, HOLogic.stringT);
                val tbl =
                  HOLogic.mk_list pairT
                    (map (fn (n, d) =>
                      HOLogic.mk_prod (Grammar_Common.name_term gram n, HOLogic.mk_string d)) table);
                val dflt = Abs ("d", HOLogic.stringT, Bound 0);
              in
                SOME (fn t =>
                  Const (\<^const_name>\<open>case_option\<close>,
                      HOLogic.stringT --> (HOLogic.stringT --> HOLogic.stringT) -->
                        Grammar_Common.mk_optionT HOLogic.stringT --> HOLogic.stringT) $
                    (if #nat_labels gram then HOLogic.mk_string "?" else t) $ dflt $
                    (Const (\<^const_name>\<open>map_of\<close>,
                      HOLogic.listT pairT --> nameT --> Grammar_Common.mk_optionT HOLogic.stringT) $
                      tbl $ t))
              end;
          val orig_t =
            (case (#restricted (Grammar_Common.artifacts_of gram), show_t) of
              (SOME {orig, ...}, NONE) => orig
            | (SOME {orig, ...}, SOME f) => Abs ("n", nameT, Envir.beta_norm (f (orig $ Bound 0)))
            | (NONE, NONE) => Abs ("n", nameT, Bound 0)
            | (NONE, SOME f) => Abs ("n", nameT, f (Bound 0)));
          val info_gram =
            (case recover of
              SOME (_, e) => c \<^const_name>\<open>no_err\<close> $ e $ gram_t
            | NONE => gram_t);
          val (info_eq, lthy) =
            define_term parse_bind "info"
              (Syntax.check_term lthy
                (c \<^const_name>\<open>pinfo.make\<close> $ info_gram $ states_c $ rhs_of_eq terminals_eq $
                   orig_t $ HOLogic.mk_number \<^typ>\<open>nat\<close> 5 $ msgs))
              lthy;
          val errT = Type (\<^type_name>\<open>perr_ext\<close>, [nameT, #tokT gram, chT, moreT, HOLogic.unitT]);
          val chs =
            if chT = \<^typ>\<open>char\<close> then SOME (Abs ("c", chT, HOLogic.mk_list chT [Bound 0]))
            else if chT = HOLogic.unitT then SOME (Abs ("c", chT, HOLogic.mk_string ""))
            else NONE;
          val lthy =
            (case chs of
              SOME f =>
                define_term parse_bind "render"
                  (Syntax.check_term lthy
                    (Abs ("e", errT, c \<^const_name>\<open>perr_render\<close> $ rhs_of_eq info_eq $ f $ Bound 0)))
                  lthy |> #2
            | NONE => lthy);
          (* the recovery: `p_repair w = repair stop w`, with `stop` the error and the
             new word at a stop of the driver of p's code equation, `p_recover = precover
             p p_repair`, and `p_recover.clean`; `p_recover.no_error` is noted with the
             theorems of p *)
          fun define_recover lthy =
            let
              val b = Binding.map_name (fn n => n ^ "_recover") parse_bind;
              val mode =
                c \<^const_name>\<open>rmode.make\<close>
                $ (case recover of
                    SOME (_, e) => c \<^const_name>\<open>Some\<close> $ e
                  | NONE => c \<^const_name>\<open>None\<close>)
                $ (case repair of
                    SOME (av, mk) => c \<^const_name>\<open>Some\<close> $ (c \<^const_name>\<open>Pair\<close> $ av $ mk)
                  | NONE => c \<^const_name>\<open>None\<close>);
              val stop0 =
                (case drv of
                  Plain (P, i0, f) => c \<^const_name>\<open>prstop\<close> $ P $ i0 $ f $ ts $ mode
                | Vec (V, _, T, kin, kcl, i0, _, _) =>
                    c \<^const_name>\<open>vrstop\<close> $ V $ T $ kin $ kcl $ i0 $ ts $ mode
                | Dense (G, Shn, gt, sts, rt, _, xin, xclos, i0) =>
                    c \<^const_name>\<open>drstop\<close> $ G $ Shn $ gt $ sts $ rt $ xin $ xclos $ i0 $ ts $ mode
                | Hist (G, Shn, gt, sts, rt, xin, xclos, i0) =>
                    c \<^const_name>\<open>drstop\<close> $ G $ Shn $ gt $ sts $ rt $ xin $ xclos $ i0 $ ts $ mode);
              (* the plan on p's tables, the report of p_diag *)
              val stop =
                (case forced of
                  NONE => stop0
                | SOME run =>
                    c \<^const_name>\<open>oer_stop\<close> $ stop0 $
                      (let val v = Free ("v", wordT) in lambda v (run dec v) end));
              val stop =
                (case orig_opt of
                  SOME orig => c \<^const_name>\<open>pe_stop_names\<close> $ orig $ stop
                | NONE => stop);
              val repair_b = Binding.map_name (fn n => n ^ "_repair") parse_bind;
              val ((repair_c, repair_def), lthy) =
                Grammar_Defs.define_const true (repair_b, Thm.def_binding repair_b,
                  Syntax.check_term lthy (lambda w (c \<^const_name>\<open>repair\<close> $ stop $ w))) lthy;
              val lthy = recode repair_b repair_def lthy;
              val ((_, recover_def), lthy) =
                Grammar_Defs.define_const true (b, Thm.def_binding b,
                  Syntax.check_term lthy (c \<^const_name>\<open>precover\<close> $ parse_c $ repair_c)) lthy;
            in
              lthy
              |> Local_Theory.notes
                   [((Grammar_Common.qualify_bind b "clean", []),
                     [([recover_def RS @{thm precover_clean}], [])])]
              |> #2
            end;
        in lthy |> (if is_some recover orelse is_some repair then define_recover else I) end)
  end;

end;
