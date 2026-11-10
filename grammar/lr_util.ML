(* the LR backend, shared helpers: evaluated literals, table constants defined by
   their terms, token numbering, the table options and size reports *)

structure LR_Util =
struct

fun timed lthy label = Grammar_Common.timed lthy "parser" label;

fun dest_tuple 1 t = [t]
  | dest_tuple n t =
      let val (a, b) = HOLogic.dest_prod t in a :: dest_tuple (n - 1) b end;

fun dest_nat (Const (\<^const_name>\<open>Suc\<close>, _) $ t) = dest_nat t + 1
  | dest_nat t = snd (HOLogic.dest_number t);

fun dest_option (Const (\<^const_name>\<open>None\<close>, _)) = NONE
  | dest_option (Const (\<^const_name>\<open>Some\<close>, _) $ x) = SOME x
  | dest_option t = raise TERM ("dest_option", [t]);

(* `(a, bs) = (c, ds)`  ~>  `a = c` + the rest *)
fun split_tuple_eq 1 th = [th]
  | split_tuple_eq n th =
      let val conj = th RS @{thm prod.inject [THEN iffD1]} in
        (conj RS @{thm conjunct1}) :: split_tuple_eq (n - 1) (conj RS @{thm conjunct2})
      end;

(* evaluate `t` to a literal and prove `t = literal` by the code generator; `prof` runs
   the evaluation under the profiler of \<open>[[grammar_profile]]\<close> *)
fun value_lit lthy prof label t =
  let
    val run =
      if prof then Grammar_Common.profiled lthy (Value_Command.value lthy)
      else Value_Command.value lthy;
  in timed lthy ("value " ^ label) run t end;

fun prove_lit lthy label t lit =
  timed lthy ("eval " ^ label) (fn () =>
    Goal.prove_sorry lthy [] [] (HOLogic.mk_Trueprop (HOLogic.mk_eq (t, lit)))
      (fn {context, ...} => HEADGOAL (Parser_Generators.eval_tac context))) ();

fun eval_lit lthy prof label t =
  let val lit = value_lit lthy prof label t
  in (lit, prove_lit lthy label t lit) end;

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
   i-th constructor, computed with the tables (`map (num P) ctrs = ns`), and
   `num p_tab = p_tnum` proved constructor by constructor, for `num` pnum or vnum *)
fun tnum_case lthy parse_b (sugar: Ctr_Sugar.ctr_sugar) (num_c, tab_eq, nums_e, nums_l) prior_eqs =
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
    val tab_c = snd (HOLogic.dest_eq (HOLogic.dest_Trueprop (Thm.prop_of tab_eq)));
    val conjs =
      HOLogic.conj_elims
        (Simplifier.full_simplify
          (put_simpset HOL_basic_ss lthy' |> Simplifier.add_simps @{thms list.map list.inject simp_thms}) nums_eq);
    val num_t = Syntax.check_term lthy' (Const (num_c, dummyT) $ tab_c);
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
    val goal = HOLogic.mk_Trueprop (HOLogic.mk_eq (num_t $ y, tnum_c $ y));
    val th =
      Goal.prove_sorry lthy' ["y"] [] goal (fn {context = ctxt, ...} =>
        HEADGOAL (resolve_tac ctxt
          [infer_instantiate ctxt [(yv, Thm.cterm_of ctxt y)] exhaust])
        THEN ALLGOALS (fn i =>
          hyp_subst_tac ctxt i
          THEN simp_tac (put_simpset HOL_basic_ss ctxt
            |> Simplifier.add_simps (def_eq :: conjs @ #case_thms sugar @ @{thms simp_thms})) i));
  in (@{thm ext} OF [th], tnum_c, lthy') end;

val parser_int_tables = Attrib.setup_config_bool \<^binding>\<open>parser_int_tables\<close> (K false);

(* the six tables as evaluated literals, as before they were definitions by their terms *)
val parser_literal_tables =
  Attrib.setup_config_bool \<^binding>\<open>parser_literal_tables\<close> (K false);

(* the report of a non-empty check: \<open>[[grammar_explain = false]]\<close> lists the states by
   their symbol paths only; otherwise the first \<open>[[grammar_explain_states]]\<close> states get
   the witness search and the rest their action pairs *)
val explain = Attrib.setup_config_bool \<^binding>\<open>grammar_explain\<close> (K true);
val explain_states = Attrib.setup_config_int \<^binding>\<open>grammar_explain_states\<close> (K 8);

(* \<open>[[grammar_timing]]\<close> only: the sizes, by one evaluation of \<open>sizes_t\<close>, which shares
   the state list between the rows of the three tables *)
fun report_sizes lthy (gram: Grammar_Common.grammar) sizes_t (rlalr_l, acc_l) =
  let
    fun nats t = map dest_nat (HOLogic.dest_list t);
    val (items, gotos, cells, xclos) =
      (case dest_tuple 4 (timed lthy "value (sizes)" (Value_Command.value lthy) sizes_t) of
        [a, b, c, d] => (nats a, nats b, nats c, dest_nat d)
      | _ => raise Fail "report_sizes: tuple literal");
    fun sum xs = fold (curry (op +)) xs 0;
    (* the grammar the tables are built from *)
    val (n_prods, n_nts) =
      (case #restricted (Grammar_Common.artifacts_of gram) of
        SOME {counts, ...} => Lazy.force counts
      | NONE => (length (#prods gram), Symtab.size (#nonterms gram)));
    val sizes =
      [("productions", n_prods),
       ("nonterminals", n_nts),
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

end;
