(* the LR backend of the parser command (precise tables): the parse body over table constants
   defined by their terms, the determinism and accept/reduce premises discharged
   by evaluating the static checks, and the printers that explain a non-empty
   check *)

signature LR_BACKEND =
sig
  val lr_gen: Parser_Generators.parser_generator
  val string_of_tm: Proof.context -> Grammar_Common.grammar -> term -> string
end;

structure LR_Backend: LR_BACKEND =
struct

fun timed lthy label = Grammar_Common.timed lthy "parser" label;

fun dest_tuple 1 t = [t]
  | dest_tuple n t =
      let val (a, b) = HOLogic.dest_prod t in a :: dest_tuple (n - 1) b end;

(* `(a, bs) = (c, ds)`  ~>  `a = c` + the rest *)
fun split_tuple_eq 1 th = [th]
  | split_tuple_eq n th =
      let val conj = th RS @{thm prod.inject [THEN iffD1]} in
        (conj RS @{thm conjunct1}) :: split_tuple_eq (n - 1) (conj RS @{thm conjunct2})
      end;

(* evaluate `t` to a literal and prove `t = literal` by the code generator; `prof` runs
   the evaluation under the profiler of \<open>[[grammar_profile]]\<close> *)
fun eval_lit lthy prof label t =
  let
    val run =
      if prof then Grammar_Common.profiled lthy (Value_Command.value lthy)
      else Value_Command.value lthy;
    val lit = timed lthy ("value " ^ label) run t;
    val th =
      timed lthy ("eval " ^ label) (fn () =>
        Goal.prove_sorry lthy [] [] (HOLogic.mk_Trueprop (HOLogic.mk_eq (t, lit)))
          (fn {context, ...} => HEADGOAL (Parser_Generators.eval_tac context))) ();
  in (lit, th) end;

fun lhs_of_eq th = fst (HOLogic.dest_eq (HOLogic.dest_Trueprop (Thm.prop_of th)));
fun rhs_of_eq th = snd (HOLogic.dest_eq (HOLogic.dest_Trueprop (Thm.prop_of th)));

(* a parser constant `c \<equiv> rhs`, with `rhs` over the constants defined before it, and
   its equation `rhs = c`; the code generator prints a nullary constant as a `val`, so
   the generated code computes `c` once when it loads *)
fun define_term parse_b nm rhs lthy =
  timed lthy ("define " ^ nm) (fn () =>
    let
      val b = Binding.map_name (fn n => n ^ "_" ^ nm) parse_b;
      val ((_, def_th), lthy') =
        Grammar_Defs.define_const true (b, Thm.def_binding b, rhs) lthy;
    in (Thm.symmetric def_th RS @{thm meta_eq_to_obj_eq}, lthy') end) ();

(* under \<open>[[parser_literal_tables]]\<close>: the constant is the evaluated literal, and
   `expr = literal` becomes `expr = c` with the earlier tables' equations folded into
   `expr`; as in define_term, `c` is the local definition's variable *)
fun define_literal parse_b nm (expr_eq, literal) prior_eqs lthy =
  timed lthy ("define " ^ nm) (fn () =>
  let
    val b = Binding.map_name (fn n => n ^ "_" ^ nm) parse_b;
    val ((_, def_th), lthy') =
      Grammar_Defs.define_const true (b, Thm.def_binding b, literal) lthy;
    val eq_folded = Local_Defs.fold lthy' [def_th] expr_eq;
    val eq_th =
      if null prior_eqs then eq_folded
      else Local_Defs.unfold lthy' prior_eqs eq_folded;
  in (eq_th, lthy') end) ();

(* the numbering of the tokens by a case distinction over the constructors of
   the token type: `p_tnum = case_tok n1 ... nk` with `ni` the number of the
   i-th constructor, computed with the tables (`map (pnum P) ctrs = ns`), and
   `pnum p_ptabs = p_tnum` proved constructor by constructor *)
fun tnum_case lthy parse_b (sugar: Ctr_Sugar.ctr_sugar) (ptabs_eq, nums_e, nums_l) prior_eqs =
  let
    val nums_eq = Local_Defs.unfold lthy prior_eqs nums_e;
    val nums = HOLogic.dest_list nums_l;
    val case_c = Const (fst (dest_Const (#casex sugar)), dummyT);
    val body = Syntax.check_term lthy (Term.list_comb (case_c, nums));
    val b = Binding.map_name (fn n => n ^ "_tnum") parse_b;
    val ((_, def_th), lthy') = Grammar_Defs.define_const true (b, Thm.def_binding b, body) lthy;
    val def_ax = the_default def_th (Grammar_Common.def_axiom lthy' (b, Thm.def_binding b));
    val def_eq = Local_Defs.meta_rewrite_rule lthy' def_ax;
    (* the constant as the other tables' equations name it *)
    val tnum_c = fst (Logic.dest_equals (Thm.prop_of def_eq));
    val ptabs_c = snd (HOLogic.dest_eq (HOLogic.dest_Trueprop (Thm.prop_of ptabs_eq)));
    val conjs =
      HOLogic.conj_elims
        (Simplifier.full_simplify
          (put_simpset HOL_basic_ss lthy' addsimps @{thms list.map list.inject simp_thms}) nums_eq);
    val pnum_t = Syntax.check_term lthy' (Const (\<^const_name>\<open>pnum\<close>, dummyT) $ ptabs_c);
    val tokT = domain_type (fastype_of tnum_c);
    val y = Free ("y", tokT);
    val exhaust = #exhaust sugar;
    (* the variable of `(?y = C1 ==> ?P) ==> ... ==> ?P` *)
    val yv =
      (case Logic.strip_imp_prems (Thm.prop_of exhaust) of
        prem :: _ =>
          (case Logic.strip_imp_prems prem of
            eq :: _ =>
              (case fst (HOLogic.dest_eq (HOLogic.dest_Trueprop eq)) of
                Var (v, _) => v
              | _ => raise Fail "tnum_case: exhaust")
          | _ => raise Fail "tnum_case: exhaust")
      | _ => raise Fail "tnum_case: exhaust");
    val goal = HOLogic.mk_Trueprop (HOLogic.mk_eq (pnum_t $ y, tnum_c $ y));
    val th =
      Goal.prove_sorry lthy' ["y"] [] goal (fn {context = ctxt, ...} =>
        HEADGOAL (resolve_tac ctxt
          [infer_instantiate ctxt [(yv, Thm.cterm_of ctxt y)] exhaust])
        THEN ALLGOALS (fn i =>
          hyp_subst_tac ctxt i
          THEN simp_tac (put_simpset HOL_basic_ss ctxt
            addsimps (def_eq :: conjs @ #case_thms sugar @ @{thms simp_thms})) i));
  in (@{thm ext} OF [th], lthy') end;

val parser_int_tables = Attrib.setup_config_bool \<^binding>\<open>parser_int_tables\<close> (K false);

(* the six tables as evaluated literals, as before they were definitions by their terms *)
val parser_literal_tables =
  Attrib.setup_config_bool \<^binding>\<open>parser_literal_tables\<close> (K false);

(* the report of a non-empty check: \<open>[[grammar_explain = false]]\<close> lists the states by
   their symbol paths only; otherwise the first \<open>[[grammar_explain_states]]\<close> states get
   the witness search and the rest their action pairs *)
val explain = Attrib.setup_config_bool \<^binding>\<open>grammar_explain\<close> (K true);
val explain_states = Attrib.setup_config_int \<^binding>\<open>grammar_explain_states\<close> (K 8);

(* \<open>[[grammar_timing]]\<close> only: the sizes the cost of a parser grows with *)
(* \<open>[[grammar_timing]]\<close> only: the sizes, by one evaluation of \<open>sizes_t\<close>, which shares
   the state list between the rows of the three tables *)
fun report_sizes lthy (gram: Grammar_Common.grammar) sizes_t (rlalr_l, acc_l) =
  let
    fun nat_of (Const (\<^const_name>\<open>Suc\<close>, _) $ t) = nat_of t + 1
      | nat_of t = snd (HOLogic.dest_number t);
    fun nats t = map nat_of (HOLogic.dest_list t);
    val (items, gotos, cells, xclos) =
      (case dest_tuple 4 (timed lthy "value (sizes)" (Value_Command.value lthy) sizes_t) of
        [a, b, c, d] => (nats a, nats b, nats c, nat_of d)
      | _ => raise Fail "report_sizes: tuple literal");
    fun sum xs = fold (curry (op +)) xs 0;
    val sizes =
      [("productions", length (#prods gram)),
       ("nonterminals", Symtab.size (#nonterms gram)),
       ("terminals", Vector.length (#terminals gram)),
       ("states", length items),
       ("items", sum items),
       ("items per state (max)", fold (curry Int.max) items 0),
       ("goto entries", sum gotos),
       ("reduce cells", sum cells),
       ("xclosure items", xclos),
       ("conflict states", length (HOLogic.dest_list rlalr_l)),
       ("accept/reduce states", length (HOLogic.dest_list acc_l))];
  in
    writeln ("[parser] sizes: " ^
      commas (map (fn (k, v) => k ^ " = " ^ string_of_int v) sizes))
  end;

(* \<open>[[grammar_timing_components]]\<close> only: the let-chain of \<^const>\<open>lr_tables\<close> evaluated
   prefix by prefix (the first k binders, then the first j tuple components), each
   prefix with the sharing of the original, so that the increments are the costs of
   the components, including the conversion of their results to terms; nothing
   downstream uses it. Substituting the literals of earlier components instead
   makes the code generator compile them, which is GC-bound and slower than the
   evaluation itself. *)
fun profile_bundle lthy gram_t shn_t ii_t =
  let
    fun head_name binds t =
      (case Term.head_of t of
        Const (c, _) => Long_Name.base_name c
      | Bound i => #1 (nth (rev binds) i)
      | Abs _ => "\<lambda>"
      | _ => "?");
    val body =
      Drule.infer_instantiate lthy
        [(("G", 0), Thm.cterm_of lthy gram_t), (("Shn", 0), Thm.cterm_of lthy shn_t)]
        @{thm lr_tables_def}
      |> Thm.prop_of |> HOLogic.dest_Trueprop |> HOLogic.dest_eq |> snd;
    fun strip (Const (\<^const_name>\<open>Let\<close>, _) $ e $ Abs (x, T, b)) =
          apfst (cons (x, T, e)) (strip b)
      | strip t = ([], t);
    val (binds, tuple) = strip body;
    val Ts = map #2 binds;
    val comps = HOLogic.strip_tuple tuple;
    fun tupT [T] = T
      | tupT (T :: Ts) = HOLogic.mk_prodT (T, tupT Ts)
      | tupT [] = HOLogic.unitT;
    fun tup [(t, _)] = t
      | tup ((t, T) :: rest) = HOLogic.pair_const T (tupT (map snd rest)) $ t $ tup rest
      | tup [] = HOLogic.unit;
    fun wrap [] b _ = b
      | wrap ((x, T, e) :: bs) b bT =
          Const (\<^const_name>\<open>Let\<close>, fastype_of1 (rev Ts, e) --> (T --> bT) --> bT) $ e
            $ Abs (x, T, wrap bs b bT);
    (* the term after the first k binders, observing each bound value under all of
       them: a list by its length (so the evaluator does not rebuild it as a term,
       which costs more than computing it), anything else by itself *)
    fun observe (t, T as Type (\<^type_name>\<open>list\<close>, _)) =
          (Const (\<^const_name>\<open>size\<close>, T --> HOLogic.natT) $ t, HOLogic.natT)
      | observe tT = tT;
    fun prefix_binds k =
      let val obs = map_index (fn (i, T) => observe (Bound (k - 1 - i), T)) (take k Ts)
      in wrap (take k binds) (tup obs) (tupT (map snd obs)) end;
    fun prefix_comps j =
      let val cs = map (fn c => (c, fastype_of1 (rev Ts, c))) (take j comps)
      in wrap binds (tup cs) (tupT (map snd cs)) end;
    val steps =
      map_index (fn (i, (x, _, e)) => (x ^ " = " ^ head_name binds e, prefix_binds (i + 1)))
        binds @
      map_index (fn (j, c) => ("component " ^ string_of_int (j + 1) ^ " " ^ head_name binds c,
        prefix_comps (j + 1))) comps;
    fun step (label, t) prev =
      let
        val ({elapsed, ...}, _) = Timing.timing (Value_Command.value lthy) t;
        val now = Time.toReal elapsed;
      in
        writeln ("[parser] profile " ^ label ^ ": " ^ Time.toString elapsed ^
          "s cumulative, +" ^ Real.fmt (StringCvt.FIX (SOME 3)) (now - prev) ^ "s");
        now
      end;
  in
    ignore (fold step steps 0.0);
    ignore (timed lthy "profile ii (mdet)" (Value_Command.value lthy) ii_t)
  end;

(* a derivation A \<Rightarrow>\<^sup>+ A that consumes nothing, as the cycle A, \<dots>, A of the graph
   with an edge A \<rightarrow> B for each production A = \<alpha> B \<beta> whose \<alpha> and \<beta> are nullable.
   Only such a derivation lets the set-anchored driver revisit a configuration
   without shifting (LR_Driver, drun_nh).  Relations are ignored, so a cycle may
   be spurious but is never missed; the answer picks a proved code equation and
   is trusted only for the termination of the generated code. *)
fun nullable_cycle (gram: Grammar_Common.grammar) =
  let
    val prods = map (fn p => (#lhs p, map fst (#rhs p))) (#prods gram);
    fun nt (Grammar_Common.RN n) = SOME n
      | nt _ = NONE;
    fun nullable nul s = (case nt s of SOME n => member (op =) nul n | NONE => false);
    fun grow nul =
      let
        val nul' =
          fold (fn (a, rhs) => fn acc =>
            if not (member (op =) acc a) andalso forall (nullable acc) rhs then a :: acc
            else acc) prods nul;
      in if length nul' = length nul then nul else grow nul' end;
    val nul = grow [];
    fun edges (a, rhs) =
      map_filter I (map_index (fn (i, s) =>
        (case nt s of
          SOME b => if forall (nullable nul) (nth_drop i rhs) then SOME (a, b) else NONE
        | NONE => NONE)) rhs);
    val graph = maps edges prods;
    fun succs a = map snd (filter (fn (x, _) => x = a) graph);
    (* depth-first, the path most recent first *)
    fun visit path a (done, found) =
      if is_some found then (done, found)
      else if member (op =) path a then
        (done, SOME (a :: rev (take_prefix (fn x => x <> a) path) @ [a]))
      else if member (op =) done a then (done, found)
      else
        let val (done', found') = fold (visit (a :: path)) (succs a) (done, found)
        in (a :: done', found') end;
  in snd (fold (visit []) (distinct (op =) (map fst prods)) ([], NONE)) end;

fun lr_build_parse
  ({gram, parse_bind, shn}: Parser_Generators.build_input) lthy =
  let
    val {isgT, wordT, astT, ...} = Grammar_Common.get_desc gram;
    val start_nt = #start gram;
    val start_cT = Grammar_Common.carrier_of gram start_nt;

    val gram_t = #gram_t (Grammar_Common.artifacts_of gram);
    val shn_t = HOLogic.mk_string shn;
    val decoder = Grammar_Defs.decoder_of lthy gram start_nt;

    val optT = Grammar_Common.mk_optionT;
    val dlr_c = Const (\<^const_name>\<open>dparse\<close>,
      isgT --> \<^typ>\<open>string\<close> --> wordT --> optT astT);
    val bind_c = Const (\<^const_name>\<open>Option.bind\<close>,
      optT astT --> (astT --> optT start_cT) --> optT start_cT);

    val parse_body =
      Abs ("w", wordT,
        bind_c $ (dlr_c $ gram_t $ shn_t $ Bound 0) $ decoder);

    (* over the current context: a table constant is a local fixed variable until
       the context that defined it *)
    fun app' lthy c args =
      Syntax.check_term lthy (Term.list_comb (Const (c, dummyT), args));
    val app = app' lthy;
    fun is_const c (Const (d, _)) = c = d
      | is_const _ _ = false;
    fun size_of t = HOLogic.size_const (fastype_of t) $ t;

    (* the tables as the theorems name them *)
    val states_t = app \<^const_name>\<open>pr0_states\<close> [gram_t, shn_t];
    val gtab_t   = app \<^const_name>\<open>pgtab\<close> [gram_t, states_t];
    val redtab_t = app \<^const_name>\<open>red_buckets\<close> [gram_t, shn_t, size_of states_t];
    val xinit_t  = app \<^const_name>\<open>xinit\<close> [gram_t, shn_t];
    val xclos_t  = app \<^const_name>\<open>xclosure_auto\<close> [gram_t, xinit_t];
    val lr0_start_t = app \<^const_name>\<open>lr0_start\<close> [gram_t, shn_t];
    val ii_t = app \<^const_name>\<open>ii\<close> [gram_t];

    (* the constructors of the token type, if it is a datatype whose constructors
       have no arguments: the tokens are then numbered by a case distinction
       instead of a search (tnum below) *)
    val tokT = #tokT gram;
    val tok_sugar =
      (case tokT of
        Type (tname, []) =>
          (case Ctr_Sugar.ctr_sugar_of lthy tname of
            SOME sugar =>
              if forall (fn c => fastype_of c = tokT) (#ctrs sugar) then SOME sugar
              else NONE
          | NONE => NONE)
      | _ => NONE);
    val ctrs_t = HOLogic.mk_list tokT (the_default [] (Option.map #ctrs tok_sugar));

    (* 1. The checks, in one evaluation before any definition: a definition empties
       the code generator's cache of the preprocessed program, so an evaluation after
       it starts cold. \<^const>\<open>lr_checks\<close> shares the automaton, its goto table, the
       cells and the precise automaton between its five values (the paths of the
       reported states are the report's cheapest level, free here), and
       \<^text>\<open>lr_checks_eq\<close> transports them to the terms the theorems name. *)
    val (checks_l, checks_th) =
      eval_lit lthy true "(checks)" (app \<^const_name>\<open>lr_checks\<close> [gram_t, shn_t]);
    val checks_eq = @{thm trans} OF [@{thm lr_checks_eq} RS @{thm sym}, checks_th];
    val (rlalr_l, acc_l, ii_l, wany_l) =
      (case dest_tuple 5 checks_l of
        [a, b, c, d, _] => (a, b, c, d)
      | _ => raise Fail "lr_build_parse: checks literal");
    val (rlalr_eq, acc_eq, ii_eq, wany_eq, paths_eq) =
      (case split_tuple_eq 5 checks_eq of
        [a, b, c, d, e] => (a, b, c, d, e)
      | _ => raise Fail "lr_build_parse: checks equations");

    (* the simple driver of LR_Simple applies when the grammar has no layout
       annotations, the determinism check is empty, and no reduce cell that
       names a token constrains its width; its further value is evaluated now
       as well *)
    val simple =
      is_const \<^const_name>\<open>True\<close> ii_l andalso
      is_const \<^const_name>\<open>List.list.Nil\<close> rlalr_l andalso
      is_const \<^const_name>\<open>True\<close> wany_l;
    val simple_checks =
      if simple then
        SOME (eval_lit lthy false "(simple checks)"
          (app \<^const_name>\<open>lr_simple_checks\<close> [gram_t, shn_t, ctrs_t]))
      else NONE;

    (* under parser_literal_tables the six tables are evaluated literals, from one
       evaluation of \<^const>\<open>lr_tables\<close> *)
    val literal_tabs =
      if Config.get lthy parser_literal_tables then
        let
          val (bundle_l, bundle_th) =
            eval_lit lthy false "(tables)" (app \<^const_name>\<open>lr_tables\<close> [gram_t, shn_t]);
          val tables_eq = @{thm trans} OF [@{thm lr_tables_eq} RS @{thm sym}, bundle_th];
        in
          SOME (["states", "gtab", "redtab", "xinit", "xclos", "i0"] ~~
            take 6 (split_tuple_eq 8 tables_eq ~~ dest_tuple 8 bundle_l))
        end
      else NONE;

    val _ = Grammar_Common.when_timing lthy (fn () =>
      let
        fun c n = Const (n, dummyT);
        fun elemT (Type (_, [T])) = T
          | elemT _ = raise Fail "lr_build_parse: sizes";
        fun pair a b = c \<^const_name>\<open>Pair\<close> $ a $ b;
        fun lens T t = c \<^const_name>\<open>map\<close> $ HOLogic.size_const (elemT T) $ t;
        val stsT = fastype_of states_t;
        val sm = Bound 0;
        val sizes_t =
          Syntax.check_term lthy
            (c \<^const_name>\<open>Let\<close> $ states_t $ Abs ("sm", stsT,
              pair (lens stsT sm)
                (pair (lens (fastype_of gtab_t) (c \<^const_name>\<open>pgtab\<close> $ gram_t $ sm))
                  (pair (lens (fastype_of redtab_t)
                      (c \<^const_name>\<open>red_buckets\<close> $ gram_t $ shn_t $
                        (HOLogic.size_const stsT $ sm)))
                    (size_of xclos_t)))));
      in
        report_sizes lthy gram sizes_t (rlalr_l, acc_l);
        if Config.get lthy Grammar_Common.timing_components
        then timed lthy "profile (total)" (profile_bundle lthy gram_t shn_t) ii_t else ()
      end);

    (* 2. The tables: each a constant defined by its term over the constants before
       it, `table nm rhs prior` returning `rhs = c`; under parser_literal_tables the
       literal of the bundle instead, folded into the same equation *)
    fun table nm rhs prior lthy =
      (case literal_tabs of
        NONE => define_term parse_bind nm rhs lthy
      | SOME tab =>
          define_literal parse_bind nm (the (AList.lookup (op =) tab nm)) prior lthy);
    val define = define_term parse_bind;

    val (states_eq, lthy) = table "states" states_t [] lthy;
    val sts = rhs_of_eq states_eq;
    val (gtab_eq, lthy) =
      table "gtab" (app' lthy \<^const_name>\<open>pgtab\<close> [gram_t, sts]) [states_eq] lthy;
    val (redtab_eq, lthy) =
      table "redtab" (app' lthy \<^const_name>\<open>red_buckets\<close> [gram_t, shn_t, size_of sts])
        [states_eq] lthy;
    val (i0_eq, lthy) =
      table "i0" (app' lthy \<^const_name>\<open>st_find\<close> [sts, lr0_start_t]) [states_eq] lthy;

    fun simple_tables (nums_l, nums_th) lthy =
      let
        val arts = Grammar_Common.artifacts_of gram;
        val fresh_simps = @{thms fresh_name_def is_cfg.make_def} @ [#gram_def arts];
        val fresh_th =
          Goal.prove_sorry lthy [] []
            (HOLogic.mk_Trueprop (app \<^const_name>\<open>fresh_name\<close> [gram_t, shn_t]))
            (fn {context, ...} => HEADGOAL (asm_full_simp_tac (context addsimps fresh_simps)));
        val static_th =
          @{thm sstaticI} OF
            [ii_eq RS @{thm eqTrueE}, rlalr_eq, fresh_th, wany_eq RS @{thm eqTrueE}];

        (* the driver's tables are the parser's own; only its components and
           finals are new *)
        val (pc_eq, lthy) = define "pcomps" (app' lthy \<^const_name>\<open>pcomps\<close> [gram_t, sts]) lthy;
        val (pf_eq, lthy) = define "pfins" (app' lthy \<^const_name>\<open>pfins\<close> [shn_t, sts]) lthy;
        (* the indexed tables: productions and nonterminals numbered, rows keyed by
           terminal or nonterminal number *)
        val (ltabs_eq, lthy) =
          define "ltabs"
            (app' lthy \<^const_name>\<open>mk_ltabs\<close>
              (map rhs_of_eq [gtab_eq, states_eq, redtab_eq, pc_eq, pf_eq]))
            lthy;
        val ltabs = rhs_of_eq ltabs_eq;
        (* the tables of the code: by default binary tries (jtabs_of), which are
           static data and need no arithmetic with binary naturals; with
           parser_int_tables, arrays with integer indices (ztabs_of) *)
        val (tabs_eqs, via, tabs_msg, lthy) =
          if Config.get lthy parser_int_tables then
            let val (ztabs_eq, lthy) = define "ztabs" (app' lthy \<^const_name>\<open>ztabs_of\<close> [ltabs]) lthy
            in
              ([ztabs_eq], @{thm dparse_via_int_tables}, "integer tables (LR_Simple, LR_Int)", lthy)
            end
          else
            let
              val (jtabs_eq, lthy) = define "jtabs" (app' lthy \<^const_name>\<open>jtabs_of\<close> [ltabs]) lthy;
              val (ktabs_eq, lthy) =
                define "ktabs" (app' lthy \<^const_name>\<open>ktabs_of\<close> [rhs_of_eq jtabs_eq]) lthy;
              val (ptabs_eq, lthy) =
                define "ptabs" (app' lthy \<^const_name>\<open>ptabs_of\<close> [rhs_of_eq ktabs_eq]) lthy;
              (* the evaluated \<^const>\<open>lr_simple_checks\<close> over the constants: its let
                 chain unfolded, then every table term rewritten to its constant *)
              val nums_e =
                nums_th
                |> Local_Defs.unfold lthy @{thms lr_simple_checks_def Let_def}
                |> Local_Defs.unfold lthy
                     [states_eq, gtab_eq, redtab_eq, pc_eq, pf_eq, ltabs_eq, jtabs_eq, ktabs_eq,
                      ptabs_eq];
              val (tnum_th, tnum_msg, lthy) =
                (case tok_sugar of
                  NONE => (@{thm refl}, "a search", lthy)
                | SOME sugar =>
                    let
                      val (th, lthy) =
                        timed lthy "tnum" (fn () =>
                          tnum_case lthy parse_bind sugar (ptabs_eq, nums_e, nums_l) []) ();
                    in (th, "a case distinction", lthy) end);
            in
              ([jtabs_eq, ktabs_eq, ptabs_eq, tnum_th], @{thm dparse_via_plain},
               "an action table over the states, numbering tokens by " ^ tnum_msg ^
               " (LR_Simple, LR_Trie, LR_Tok, LR_Prod, LR_Loop, LR_Plain)", lthy)
            end;
        val _ =
          writeln ("parser: the code equation of \<open>" ^ Binding.name_of parse_bind ^
            "\<close> runs the simple driver on " ^ tabs_msg);
      in
        (via OF
          ([static_th, states_eq, gtab_eq, redtab_eq, pc_eq, pf_eq, i0_eq, ltabs_eq] @ tabs_eqs),
         lthy)
      end;

    fun set_tables lthy =
      let
        fun xinit lthy = table "xinit" xinit_t [] lthy;
        (* fresh_name G Shn, decided on the grammar itself: Shn is neither the start
           nor a nonterminal of a production.  Its proof is forked: it unfolds the
           whole grammar, and lr_discharge reuses it through the checks *)
        fun fresh lthy =
          let
            fun nts (p: Grammar_Common.prod) =
              #lhs p :: map_filter (fn (Grammar_Common.RN n, _) => SOME n | _ => NONE) (#rhs p);
            val fresh_simps =
              @{thms fresh_name_def is_cfg.make_def} @ [#gram_def (Grammar_Common.artifacts_of gram)];
          in
            if shn = start_nt orelse member (op =) (maps nts (#prods gram)) shn
            then NONE
            else
              SOME (Goal.prove_sorry lthy [] []
                (HOLogic.mk_Trueprop (app \<^const_name>\<open>fresh_name\<close> [gram_t, shn_t]))
                (fn {context, ...} => HEADGOAL (asm_full_simp_tac (context addsimps fresh_simps))))
          end;
      in
        (* without a cycle the driver keeps no history: linear on reduce chains.  With
           a fresh start name it runs on sparse closures (sdrun, LR_Sparse) over the
           bundle stab, the initial kernel and its closure, each defined by its term;
           otherwise on the dense ones (drun_nh_c, LR_Fast).  With a cycle it stops on
           a repeated configuration (drun_hist) *)
        (case timed lthy "cycle check" nullable_cycle gram of
          NONE =>
            (case timed lthy "fresh_name" fresh lthy of
              SOME fresh_th =>
                let
                  val (stab_eq, lthy) =
                    define "stab"
                      (app' lthy \<^const_name>\<open>mk_stab\<close>
                        (gram_t :: shn_t :: map rhs_of_eq [gtab_eq, states_eq, redtab_eq]))
                      lthy;
                  val (sinit_eq, lthy) =
                    define "sinit" (app' lthy \<^const_name>\<open>sinit\<close> [rhs_of_eq stab_eq]) lthy;
                  val (sclos_eq, lthy) =
                    define "sclos"
                      (app' lthy \<^const_name>\<open>sclosure\<close> (map rhs_of_eq [stab_eq, sinit_eq]))
                      lthy;
                in
                  ((@{thm dparse_via_tables_s} OF
                    [states_eq, gtab_eq, redtab_eq, i0_eq, fresh_th, stab_eq, sinit_eq, sclos_eq],
                    [fresh_th RS @{thm eqTrueI}]), lthy)
                end
            | NONE =>
                let
                  val (xinit_eq, lthy) = xinit lthy;
                  val (xclos_eq, lthy) =
                    define "xclos" (app' lthy \<^const_name>\<open>dclosure\<close> [gram_t, rhs_of_eq xinit_eq])
                      lthy;
                  val (dtab_eq, lthy) =
                    define "dtab" (app' lthy \<^const_name>\<open>dtab\<close> [gram_t]) lthy;
                in
                  ((@{thm dparse_via_tables_nh_c} OF
                    [states_eq, gtab_eq, redtab_eq, xinit_eq, xclos_eq, i0_eq, dtab_eq], []), lthy)
                end)
        | SOME cyc =>
            let
              val _ =
                warning ("parser: the grammar has a derivation \<open>" ^ hd cyc ^ " \<Rightarrow>\<^sup>+ " ^
                  hd cyc ^ "\<close> that consumes nothing (" ^ space_implode " \<rightarrow> " cyc ^
                  "), so the code of \<open>" ^ Binding.name_of parse_bind ^
                  "\<close> records the configurations since the last shift to stop on a \
                  \repeat (drun_hist), which is slow on long chains of reduces");
              val (xinit_eq, lthy) = xinit lthy;
              val (xclos_eq, lthy) =
                table "xclos"
                  (app' lthy \<^const_name>\<open>xclosure_auto\<close> [gram_t, rhs_of_eq xinit_eq])
                  [xinit_eq] lthy;
            in
              ((@{thm dparse_via_tables} OF
                [states_eq, gtab_eq, redtab_eq, xinit_eq, xclos_eq, i0_eq], []), lthy)
            end)
      end;

    val _ =
      if simple then ()
      else
        writeln ("parser: the code equation of \<open>" ^ Binding.name_of parse_bind ^
          "\<close> runs the set-anchored driver (LR_Driver)");
    val ((dlr_specialized, fresh_checks), lthy) =
      (case simple_checks of
        SOME sc => timed lthy "simple tables" (simple_tables sc) lthy |>> rpair []
      | NONE => set_tables lthy);

    fun post ({parse_def_th, ...}: Parser_Generators.post_input) lthy =
      let
        val parse_alt_th =
          timed lthy "post: unfold tables" (Local_Defs.unfold lthy [dlr_specialized]) parse_def_th;

        val _ =
          if Thm.eq_thm_prop (parse_alt_th, parse_def_th) then
            error ("parser: table inlining did not fire for \<open>" ^
              Binding.name_of parse_bind ^ "\<close>; the code equation would \
              \recompute the LR tables on every call")
          else ();

        val parse_alt_global =
          (case Grammar_Common.def_axiom lthy (parse_bind, Thm.def_binding parse_bind) of
            SOME ax => Local_Defs.unfold lthy [dlr_specialized] ax
          | NONE => parse_alt_th);
      in
        timed lthy "post: declare code" (fn () =>
          lthy
          |> Code.declare_eqns [(parse_alt_th, true)]
          |> Grammar_Common.declare_code_global {default = false} [parse_alt_global]) ()
      end;
  in
    ({parse_body = parse_body, post = post, checks = [rlalr_eq, acc_eq, paths_eq] @ fresh_checks}, lthy)
  end;

(** explaining a non-empty check (LR_Parser: explain_rp / explain_acc) **)

(* decoding evaluated literals *)

fun dest_nat (Const (\<^const_name>\<open>Suc\<close>, _) $ t) = dest_nat t + 1
  | dest_nat t = snd (HOLogic.dest_number t);

fun dest_option (Const (\<^const_name>\<open>None\<close>, _)) = NONE
  | dest_option (Const (\<^const_name>\<open>Some\<close>, _) $ x) = SOME x
  | dest_option t = raise TERM ("dest_option", [t]);

fun dest_ctor t =
  (case Term.strip_comb t of
    (Const (c, _), args) => (c, args)
  | _ => raise TERM ("dest_ctor", [t]));

datatype tsym = SNt of string | STm of term;

fun dest_sym t =
  (case dest_ctor t of
    (c, [n]) =>
      if c = \<^const_name>\<open>Nt\<close> then SNt (HOLogic.dest_string n)
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

fun string_of_sym _ _ (SNt n) = n
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
      val syms = map (fn (s, a) => sym s ^ Grammar_Common.string_of_ann a) (#rhs p);
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

fun dest_path t = Option.map (map dest_sym o HOLogic.dest_list) (dest_option t);
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
fun act_key ctxt (XShift (a, _)) = "s" ^ Syntax.string_of_term ctxt a
  | act_key _ (XReduce (i, _)) = "r" ^ string_of_int i;

(* one line per action pair of a state, shift first as in every other generator's
   report, with the set of lookaheads the pair fires on; a lookahead all of whose cell
   variants constrain both sides is layout-dependent, which the line says as a suffix
   of the set, with the relations of the first such variant *)
fun pretty_pairs ctxt gram items prs =
  let
    fun norm (la, a1, a2) =
      (case (a1, a2) of (XReduce _, XShift _) => (la, a2, a1) | _ => (la, a1, a2));
    val prs = map norm prs;
    fun pair_key (_, a1, a2) = act_key ctxt a1 ^ "|" ^ act_key ctxt a2;
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
  let val state = state_text ctxt gram (dest_path path_t)
  in (state, Pretty.chunks (Pretty.str state :: lines)) end;

(* the path alone, so without the colon that introduces a state's lines *)
fun pretty_path ctxt gram entry =
  Pretty.str (perhaps (try (unsuffix ":"))
    (state_text ctxt gram (dest_path (snd (HOLogic.dest_prod entry)))));

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
      ([Pretty.str (state_text ctxt gram (dest_path path_t)),
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
      Syntax.check_term ctxt (Term.list_comb (Const (c, dummyT), [gram_t, HOLogic.mk_string shn]));
    (* the symbol paths of the reported states: a value of the checks bundle *)
    fun paths_term () =
      Syntax.check_term ctxt (Term.list_comb (Const (\<^const_name>\<open>explain_paths\<close>, dummyT),
        [gram_t, HOLogic.mk_string shn, conflicts_term \<^const_name>\<open>rlalr_conflicts\<close>]));
    val fresh_simps = @{thms fresh_name_def is_cfg.make_def} @ [gram_def_th];
    val fresh_tac =
      SOLVED' (asm_full_simp_tac (ctxt addsimps fresh_simps));

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
          (Term.list_comb (Const (head, dummyT), [gram_t, HOLogic.mk_string shn, v]))));
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
                 val (t, entries) = Timing.timing (map (pretty_rp ctxt gram) o rp_entries) [p];
                 val state = (case entries of (_, s, _) :: _ => s | [] => "no entry:");
               in
                 writeln ("[parser] explain_rp state " ^ string_of_int (k + 1) ^ ", " ^ state ^
                   " " ^ Timing.message t);
                 entries
               end) (map_index I searched))
          else map (pretty_rp ctxt gram) (rp_value "explain_rp" searched);
        val (witnessed, unwitnessed) = List.partition #1 full;
        val brief =
          if null rest orelse not explain_on then []
          else
            map (pretty_brief ctxt gram)
              (explained "explain_rp_brief" \<^const_name>\<open>explain_rp_brief\<close>
                (HOLogic.mk_list stateT rest));
        val paths =
          if explain_on then []
          else
            (case check_value (paths_term ()) of
              SOME v => map (pretty_path ctxt gram) (HOLogic.dest_list v)
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
                    map (pretty_acc ctxt gram)
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
   discharge_tac    = lr_discharge};

end;

val _ = Theory.setup
  (Parser_Generators.register "LR" LR_Backend.lr_gen #> Parser_Generators.set_default "LR");
