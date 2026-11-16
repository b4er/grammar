(* Author: Basil Fürer *)

(* the LR backend, the build step: the parse body over the table constants, the
   diagnostics and recovery constants, and the static checks *)

structure LR_Build =
struct

open LR_Util LR_Diagnostics;

fun lr_build_parse
  ({gram, parse_bind, shn, options, errors, recover, repair, on_error_reduce, token_info}:
    Parser_Generators.build_input) lthy =
  let
    val {isgT, wordT, astT, ...} = Grammar_Common.get_desc gram;
    (* the binding of p_recover and the error token of \<open>recover\<close> *)
    val recover =
      if not (member (op =) options "diagnostics") then NONE
      else
        Option.mapPartial (fn name =>
          (case AList.lookup (op =) (map swap (spellings lthy gram)) name of
            SOME e => SOME (Binding.map_name (fn n => n ^ "_recover") parse_bind, e)
          | NONE =>
              (warning ("parser: recover: " ^ quote name ^
                 " is not a terminal of the grammar; it is ignored"); NONE))) recover;
    (* the terminals to avoid and the token of an inserted terminal, of \<open>repair\<close> *)
    val repair =
      if not (member (op =) options "diagnostics") then NONE
      else
        Option.map (fn {token, avoid} =>
          let
            val spelled = map swap (spellings lthy gram);
            fun terminal name =
              (case AList.lookup (op =) spelled name of
                SOME t => SOME t
              | NONE =>
                  (warning ("parser: avoid: " ^ quote name ^
                     " is not a terminal of the grammar; it is ignored"); NONE));
            val av = HOLogic.mk_list (#tokT gram) (map_filter terminal avoid);
            val mk =
              (case token of
                SOME f => Const (\<^const_name>\<open>rtoken_user\<close>, dummyT) $ Syntax.read_term lthy f
              | NONE => Const (\<^const_name>\<open>rtoken\<close>, dummyT));
          in (av, mk) end) repair;
    val start_nt = #start gram;

    val gram_t = #gram_t (Grammar_Common.artifacts_of gram);
    val shn_t = Grammar_Common.fresh_term gram shn;
    val decoder = Grammar_Defs.decoder_of lthy gram start_nt;
    (* the start's carrier, or its tree under \<open>parser (ast)\<close> *)
    val start_cT =
      (case range_type (fastype_of decoder) of
        Type (\<^type_name>\<open>option\<close>, [T]) => T
      | _ => raise Fail "lr_build_parse: decoder type");

    val optT = Grammar_Common.mk_optionT;
    val dlr_c = Const (\<^const_name>\<open>dparse\<close>,
      isgT --> Grammar_Common.name_typ gram --> wordT --> optT astT);
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
       cells and the precise automaton between its values (the paths of the reported
       states are the report's cheapest level, free here, and the numbers of the
       token constructors are for the state-indexed driver), and
       \<^text>\<open>lr_checks_eq\<close> transports them to the terms the theorems name. *)
    val checks_t = app \<^const_name>\<open>lr_checks\<close> [gram_t, shn_t, ctrs_t];
    (* the words of an errors block; with no coverage and no on_error_reduce their
       errors come from this evaluation too (lr_checks_keys), so that the tables are
       built once for both *)
    val err_words =
      if member (op =) options "diagnostics" andalso not (null errors)
      then error_words lthy gram (token_maker lthy gram token_info) errors
      else [];
    val key_words =
      if null on_error_reduce andalso Config.get lthy parser_errors_budget <= 0
      then map #3 err_words else [];
    (* without errors-block keys the simple driver's values come with the checks:
       \<^const>\<open>lr_checks_simple\<close> takes them from the same tables, the token numbers
       and, under parser_literal_tables, its start state and action table *)
    val literal = Config.get lthy parser_literal_tables;
    val ((checks_l, checks_th), given_keys, simple_given) =
      if null key_words then
        let
          val (all_l, all_th) =
            eval_lit lthy true "(checks)"
              (app \<^const_name>\<open>lr_checks_simple\<close>
                [gram_t, shn_t, ctrs_t, if literal then \<^term>\<open>True\<close> else \<^term>\<open>False\<close>]);
          val (checks_l, simple_l) = HOLogic.dest_prod all_l;
        in
          ((checks_l, @{thm lr_checks_simple_checks} OF [all_th]), NONE,
           SOME (dest_option simple_l, all_th))
        end
      else
        let
          val keys_t =
            app \<^const_name>\<open>lr_checks_keys\<close>
              [gram_t, shn_t, ctrs_t, HOLogic.mk_list tokT (Vector.foldr (op ::) [] (#terminals gram)),
               HOLogic.mk_list wordT key_words];
          fun ints t = map (snd o HOLogic.dest_number) (HOLogic.dest_list t);
        in
          (case Exn.result (fn () => value_lit lthy true "(checks, errors)" keys_t) () of
            Exn.Res lit =>
              let
                val (cl, kl) = HOLogic.dest_prod lit;
                val ks = map ints (HOLogic.dest_list kl);
              in
                ((cl, prove_lit lthy "(checks)" checks_t cl),
                 if length ks = length key_words then SOME ks else NONE, NONE)
              end
          | Exn.Exn exn =>
              if Exn.is_interrupt exn then Exn.reraise exn
              else (eval_lit lthy true "(checks)" checks_t, NONE, NONE))
        end;
    val checks_eq = @{thm trans} OF [@{thm lr_checks_eq} RS @{thm sym}, checks_th];
    val (rlalr_l, acc_l, ii_l, wany_l, vnums_l) =
      (case dest_tuple 6 checks_l of
        [a, b, c, d, _, f] => (a, b, c, d, f)
      | _ => raise Fail "lr_build_parse: checks literal");
    val (rlalr_eq, acc_eq, ii_eq, wany_eq, paths_eq, vnums_eq) =
      (case split_tuple_eq 6 checks_eq of
        [a, b, c, d, e, f] => (a, b, c, d, e, f)
      | _ => raise Fail "lr_build_parse: checks equations");

    (* the simple driver of LR_Simple applies when the grammar has no layout
       annotations, the determinism check is empty, and no reduce cell that
       names a token constrains its width; its further values came with the
       checks, else they are evaluated now *)
    val simple =
      is_const \<^const_name>\<open>True\<close> ii_l andalso
      is_const \<^const_name>\<open>List.list.Nil\<close> rlalr_l andalso
      is_const \<^const_name>\<open>True\<close> wany_l;
    fun simple_fail () = raise Fail "lr_build_parse: simple checks literal";
    val (simple_checks, simple_tabs) =
      if not simple then
        (case simple_given of
          SOME (SOME _, _) => simple_fail ()
        | _ => (NONE, NONE))
      else
        (case simple_given of
          SOME (SOME v, all_th) =>
            let val (nums_l, tabs_l) = HOLogic.dest_prod v in
              (SOME (nums_l, @{thm lr_checks_simple_nums} OF [all_th]),
               Option.map (fn lits_l => (lits_l, @{thm lr_checks_simple_tables} OF [all_th]))
                 (dest_option tabs_l))
            end
        | SOME (NONE, _) => simple_fail ()
        | NONE =>
            (SOME (eval_lit lthy false "(simple checks)"
               (app \<^const_name>\<open>lr_simple_checks\<close> [gram_t, shn_t, ctrs_t])),
             if literal
             then
               SOME (eval_lit lthy false "(simple tables)"
                 (app \<^const_name>\<open>lr_simple_tables\<close> [gram_t, shn_t]))
             else NONE));

    (* under parser_literal_tables the tables the code names are evaluated literals:
       the six tables, from one evaluation of \<^const>\<open>lr_tables\<close>, and for the simple
       driver its action table, from \<^const>\<open>lr_simple_tables\<close>.  Without diagnostics,
       which name the six, the simple driver's code names only its start state, also
       from \<^const>\<open>lr_simple_tables\<close>, and lr_tables is not evaluated *)
    val simple_lits =
      if literal andalso simple then
        (case simple_tabs of
          SOME (lits_l, lits_th) =>
            split_tuple_eq 2 (@{thm trans} OF [@{thm lr_simple_tables_eq} RS @{thm sym}, lits_th])
              ~~ dest_tuple 2 lits_l
        | NONE => simple_fail ())
      else [];
    val literal_tabs =
      if literal andalso simple andalso not (member (op =) options "diagnostics")
      then SOME [("i0", hd simple_lits)]
      else if literal then
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
          (case AList.lookup (op =) tab nm of
            SOME lit => define_literal parse_bind nm lit prior lthy
          | NONE => define_term parse_bind nm rhs lthy));
    val define = define_term parse_bind;

    val (states_eq, lthy) = table "states" states_t [] lthy;
    val sts = rhs_of_eq states_eq;
    val (gtab_eq, lthy) =
      table "gtab" (app' lthy \<^const_name>\<open>pgtab\<close> [gram_t, sts]) [states_eq] lthy;
    (* the reduce table over the constants for the states and the goto table, so its
       code does not build the automaton again; its equation keeps the shape
       red_buckets G Shn (length sts) = c (red_buckets_tables) *)
    val (redtab_eq, lthy) =
      (case literal_tabs of
        SOME _ =>
          table "redtab" (app' lthy \<^const_name>\<open>red_buckets\<close> [gram_t, shn_t, size_of sts])
            [states_eq] lthy
      | NONE =>
          let
            val gt = rhs_of_eq gtab_eq;
            val rhs = app' lthy \<^const_name>\<open>cell_buckets\<close>
              [app' lthy \<^const_name>\<open>la_fix_gen\<close> [gram_t, shn_t, gt, sts], size_of sts];
            val (def_eq, lthy) = define_term parse_bind "redtab" rhs lthy;
          in
            (@{thm trans} OF [@{thm red_buckets_tables} OF [states_eq, gtab_eq], def_eq], lthy)
          end);
    val (i0_eq, lthy) =
      table "i0" (app' lthy \<^const_name>\<open>st_find\<close> [sts, lr0_start_t]) [states_eq] lthy;

    (* LR_Lab: the arrays reduce to positions in a list of names, and the decoders,
       composed with the map back to names, compare integers.  The result rewrites the
       code equation's bind of the run and the start decoder.  NONE outside a theory
       target, under parser (ast), or when a decoder's equations do not have the shape
       of define_decoders *)
    fun lab_rewrite atabs_t lthy0 =
      let
        val arts = Grammar_Common.artifacts_of gram;
        fun base_dec (Const (\<^const_name>\<open>comp\<close>, _) $ d $ _) = d
          | base_dec d = d;
        val decs = map (apsnd base_dec) (#decs arts);
        val start_dec = base_dec decoder;
        val _ =
          Named_Target.is_theory lthy0 andalso is_Const start_dec andalso
            exists (fn (_, d) => d aconv start_dec) decs andalso
            forall (fn (_, d) => is_Const d andalso
              fst (dest_Const d) <> \<^const_name>\<open>Some\<close>) decs
          orelse raise Fail "labels: not applicable";
        val thy = Proof_Context.theory_of lthy0;
        fun simps d = Global_Theory.get_thms thy (fst (dest_Const d) ^ ".simps");
        val nameT = Grammar_Common.name_typ gram;
        val integerT = \<^typ>\<open>integer\<close>;
        val astT' =
          (case astT of
            Type (a, [m, ch, _, t]) => Type (a, [m, ch, integerT, t])
          | _ => raise Fail "labels: tree type");
        fun subT T =
          if T = astT then astT'
          else (case T of Type (a, Ts) => Type (a, map subT Ts) | _ => T);
        val name_lits = map (Grammar_Common.name_term gram o fst) decs;
        val ds = HOLogic.mk_list nameT name_lits;
        val define = define_term parse_bind;
        fun define_nocode nm rhs lthy =
          let
            val b = Binding.map_name (fn n => n ^ "_" ^ nm) parse_bind;
            val ((_, def_th), lthy') =
              Grammar_Defs.define_const false (b, Thm.def_binding b, rhs) lthy;
          in (Thm.symmetric def_th RS @{thm meta_eq_to_obj_eq}, lthy') end;
        fun remdups_app lthy xs ys =
          app' lthy \<^const_name>\<open>remdups\<close> [app' lthy \<^const_name>\<open>append\<close> [xs, ys]];
        fun prove lthy goal tac =
          Goal.prove lthy (filter_out (Variable.is_fixed lthy) (Term.add_free_names goal [])) [] goal
            (fn {context, ...} => tac context);

        (* the names of the arrays, and for a restricted grammar the names of the decoders *)
        val (names_eq, latabs_eq, finish, lthy) =
          (case #restricted arts of
            NONE =>
              let
                val (names_eq, lthy) =
                  define "lnames"
                    (remdups_app lthy0 (app' lthy0 \<^const_name>\<open>alabels\<close> [atabs_t]) ds) lthy0;
                val names = rhs_of_eq names_eq;
                val (latabs_eq, lthy) =
                  define "latabs"
                    (app' lthy \<^const_name>\<open>alab\<close> [app' lthy \<^const_name>\<open>lix\<close> [names], atabs_t]) lthy;
              in (names_eq, latabs_eq, fn nd => @{thm bind_nrun_lab} OF [names_eq, latabs_eq, nd], lthy) end
          | SOME {orig, ...} =>
              let
                val rs = HOLogic.mk_list HOLogic.stringT [HOLogic.mk_string "#"];
                val (rnames_eq, lthy) =
                  define "rnames"
                    (remdups_app lthy0 (app' lthy0 \<^const_name>\<open>alabels\<close> [atabs_t]) rs) lthy0;
                val rnames = rhs_of_eq rnames_eq;
                val (latabs_eq, lthy) =
                  define "latabs"
                    (app' lthy \<^const_name>\<open>alab\<close> [app' lthy \<^const_name>\<open>lix\<close> [rnames], atabs_t]) lthy;
                val (names_eq, lthy) =
                  define "lnames"
                    (remdups_app lthy (app' lthy \<^const_name>\<open>map\<close> [orig, rnames]) ds) lthy;
                val names = rhs_of_eq names_eq;
                val n_v = Free ("n", HOLogic.stringT);
                val (oarr_eq, lthy) =
                  define "oarr"
                    (app' lthy \<^const_name>\<open>IArray\<close>
                      [app' lthy \<^const_name>\<open>map\<close>
                        [Term.lambda n_v (app' lthy \<^const_name>\<open>lix\<close> [names, orig $ n_v]), rnames]])
                    lthy;
                val rs_ne =
                  prove lthy (HOLogic.mk_Trueprop (HOLogic.mk_not (HOLogic.mk_eq
                      (rs, HOLogic.mk_list HOLogic.stringT []))))
                    (fn ctxt => simp_tac (put_simpset HOL_basic_ss ctxt |> Simplifier.add_simps @{thms list.distinct simp_thms}) 1);
              in
                (names_eq, latabs_eq,
                 fn nd => Proof_Context.get_thm lthy0 "LR_Prec_Parse.bind_nrun_lab_plain" OF [rnames_eq, rs_ne, latabs_eq, names_eq, oarr_eq, nd],
                 lthy)
              end);
        val names = rhs_of_eq names_eq;

        (* per nonterminal: its position and its decoder over integer trees *)
        val relab_t =
          Const (\<^const_name>\<open>relab\<close>, (integerT --> nameT) --> astT' --> astT) $
            app' lthy \<^const_name>\<open>lnm\<close> [names];
        val ((ix_eqs, nd_eqs), lthy) =
          fold_map (fn (A, d) => fn lthy =>
              let
                val id = Grammar_Common.ident_in gram A;
                val (ix_eq, lthy) =
                  define ("ix_" ^ id)
                    (app' lthy \<^const_name>\<open>lix\<close> [names, Grammar_Common.name_term gram A]) lthy;
                val T = range_type (fastype_of d);
                val (nd_eq, lthy) =
                  define_nocode ("ndec_" ^ id)
                    (Const (\<^const_name>\<open>comp\<close>, (astT --> T) --> (astT' --> astT) --> astT' --> T)
                      $ d $ relab_t) lthy;
              in ((ix_eq, nd_eq), lthy) end) decs lthy
          |>> split_list;
        val ndecs = map rhs_of_eq nd_eqs;
        val decmap = map snd decs ~~ ndecs;
        val nd_rev = map (fn th => th RS @{thm sym}) nd_eqs;

        val inf_th =
          prove lthy (HOLogic.mk_Trueprop
              (Const (\<^const_name>\<open>Not\<close>, HOLogic.boolT --> HOLogic.boolT) $
                (Const (\<^const_name>\<open>finite\<close>, HOLogic.mk_setT nameT --> HOLogic.boolT) $
                  HOLogic.mk_UNIV nameT)))
            (fn ctxt => simp_tac (put_simpset HOL_basic_ss ctxt
              |> Simplifier.add_simps @{thms infinite_UNIV_listI infinite_UNIV_nat simp_thms}) 1);

        (*case_ast's node branch binds the name: retype it to integer; it must be unused*)
        fun retype_case (Const (c as \<^const_name>\<open>case_ast\<close>,
                Type ("fun", [lf, Type ("fun", [Type ("fun", [_, nr]), rest])])) $ f $ g) =
              let
                val g' =
                  (case g of
                    Abs (n, _, b) =>
                      if Term.loose_bvar1 (b, 0) then raise Fail "labels: name used"
                      else Abs (n, integerT, retype_case b)
                  | _ => raise Fail "labels: case_ast branch")
              in
                Const (c, lf --> (integerT --> nr) --> rest) $ retype_case f $ g'
              end
          | retype_case (t $ u) = retype_case t $ retype_case u
          | retype_case (Abs (n, T, b)) = Abs (n, T, retype_case b)
          | retype_case t = t;
        fun subst_t t =
          t
          |> retype_case
          |> Term.map_aterms (fn c as Const _ =>
                (case AList.lookup (op aconv) decmap c of SOME c' => c' | NONE => c)
              | x => x)
          |> Term.map_types subT;
        val Node' = Const (\<^const_name>\<open>Node\<close>, integerT --> HOLogic.listT astT' --> astT');
        val tokenT = #tokenT gram;
        val Leaf' = Const (\<^const_name>\<open>Leaf\<close>, tokenT --> astT');

        fun eqns (k, ((d, nd), ix_eq)) =
          let
            val (node_eq, leaf_eq) =
              (case simps d of
                [a, b] => (a, b)
              | _ => raise Fail "labels: decoder equations");
            val (_, rhs) = HOLogic.dest_eq (HOLogic.dest_Trueprop (Thm.prop_of node_eq));
            val (ifc, cond, body, none) =
              (case rhs of
                (ifc as Const (\<^const_name>\<open>If\<close>, _)) $ (Const (\<^const_name>\<open>HOL.eq\<close>, _) $ _ $ _) $ b $ n =>
                  (ifc, (), b, n)
              | _ => raise Fail "labels: decoder shape");
            val _ = cond;
            val xsv =
              (case HOLogic.dest_Trueprop (Thm.prop_of node_eq) of
                Const (\<^const_name>\<open>HOL.eq\<close>, _) $ (_ $ (_ $ _ $ xs)) $ _ => xs
              | _ => raise Fail "labels: decoder lhs");
            val i = Free ("lab_i", integerT);
            val xs' = Free ("lab_xs", HOLogic.listT astT');
            val body' = Term.subst_atomic [(subst_t xsv, xs')] (subst_t body);
            val goal_node =
              HOLogic.mk_Trueprop (HOLogic.mk_eq (nd $ (Node' $ i $ xs'),
                ifc $ HOLogic.mk_eq (i, rhs_of_eq ix_eq) $ body' $ none));
            val split_th =
              prove lthy (HOLogic.mk_Trueprop (HOLogic.mk_eq (ds,
                  app' lthy \<^const_name>\<open>append\<close>
                    [HOLogic.mk_list nameT (take k name_lits),
                     HOLogic.mk_list nameT (drop k name_lits)])))
                (fn ctxt => simp_tac (put_simpset HOL_basic_ss ctxt
                  |> Simplifier.add_simps @{thms append_Cons append_Nil}) 1);
            val iff = @{thm lnm_ds} OF [names_eq, inf_th, split_th];
            val rules =
              nd_rev @ [ix_eq RS @{thm sym}, node_eq, iff] @
              @{thms relab.simps o_apply case_list_map case_ast_relab
                yield_span_def list.map ast_yield_relab};
            val th_node =
              prove lthy goal_node (fn ctxt =>
                simp_tac (put_simpset HOL_basic_ss ctxt |> Simplifier.add_simps rules) 1);
            val w = Free ("lab_w", tokenT);
            val goal_leaf = HOLogic.mk_Trueprop (HOLogic.mk_eq (nd $ (Leaf' $ w), none));
            val th_leaf =
              prove lthy goal_leaf (fn ctxt =>
                simp_tac (put_simpset HOL_basic_ss ctxt
                  |> Simplifier.add_simps (nd_rev @ [leaf_eq] @ @{thms relab.simps o_apply})) 1);
          in [th_node, th_leaf] end;
        val code_eqs =
          flat (Par_List.map eqns (map_index I (map snd decs ~~ ndecs ~~ ix_eqs)));
        val lthy =
          lthy
          |> Code.declare_eqns (map (rpair true) code_eqs)
          |> Grammar_Common.declare_code_global {default = false} code_eqs;
        val nd_start_eq = the (AList.lookup (op aconv) (map snd decs ~~ nd_eqs) start_dec);
        val nd_start = rhs_of_eq nd_start_eq;
        val lab_th = finish nd_start_eq;

        (* LR_Fuse: the run computes the decoders' values itself.  The action of a
           nonterminal is its integer decoder's body with the children's values in place
           of the children: a decoder ndec_B c becomes fproj ix_B pj_B u, a leaf test on c
           a leaf test on u.  One equation per nonterminal says that the decoder of a
           node is its action on the values of its children (fuse_tree); bind_frun then
           rewrites the code equation.  NONE for restricted grammars and @span *)
        fun fuse lthy =
          let
            fun ofn nm th ths = th OF ths
              handle THM _ => raise Fail ("OF " ^ nm);
            val _ = Config.get lthy parser_fuse andalso is_none (#restricted arts)
              orelse raise Fail "fuse: not applicable";
            val (mT, chT, tT) =
              (case astT' of Type (_, [m, ch, _, t]) => (m, ch, t) | _ => raise Fail "fuse: tree type");
            fun dest_optT (Type (\<^type_name>\<open>option\<close>, [T])) = T
              | dest_optT _ = raise Fail "fuse: decoder type";
            fun optT T = Type (\<^type_name>\<open>option\<close>, [T]);
            val carTs = map (fn nd => dest_optT (range_type (fastype_of nd))) ndecs;
            val (valT, injs) = Grammar_Decoders.mk_val_sum (distinct (op =) carTs);
            fun inj_of T = fst (the (AList.lookup (op =) injs T));
            fun proj_of T = snd (the (AList.lookup (op =) injs T));
            val fvT = Type (\<^type_name>\<open>fv\<close>, [mT, chT, tT, valT]);
            val fvLT = HOLogic.listT fvT;
            fun fproj_c T =
              Const (\<^const_name>\<open>fproj\<close>, integerT --> (valT --> optT T) --> fvT --> optT T);
            fun map_option_c T =
              Const (\<^const_name>\<open>map_option\<close>, (T --> valT) --> optT T --> optT valT);
            val ixs = map rhs_of_eq ix_eqs;
            val ndmap = ndecs ~~ (ixs ~~ carTs);
            fun subF T =
              if T = astT' then fvT
              else (case T of Type (a, Ts) => Type (a, map subF Ts) | _ => T);
            fun tr t =
              (case Term.strip_comb t of
                (h, args) =>
                  (case AList.lookup (op aconv) ndmap h of
                    SOME (ix, U) =>
                      (case args of
                        [u] => fproj_c U $ ix $ proj_of U $ tr u
                      | _ => raise Fail "fuse: decoder use")
                  | NONE => tr_other t))
            and tr_other t =
              (case Term.strip_comb t of
                (Const (n, T), args) =>
                      if n = \<^const_name>\<open>case_ast\<close> then
                        (case args of
                          [f, Abs (_, _, Abs (_, _, b)), u] =>
                            let
                              val _ = not (Term.loose_bvar1 (b, 0) orelse Term.loose_bvar1 (b, 1))
                                orelse raise Fail "fuse: node branch";
                              val R = subF (range_type (domain_type T));
                              val cT = (tokenT --> R) --> (integerT --> optT valT --> R) --> fvT --> R;
                            in
                              Const (\<^const_name>\<open>case_fv\<close>, cT) $ tr f $
                                Abs ("i", integerT, Abs ("y", optT valT, tr b)) $ tr u
                            end
                        | _ => raise Fail "fuse: leaf test")
                      else if n = \<^const_name>\<open>yield_span\<close> then raise Fail "fuse: span"
                      else Term.list_comb (Const (n, subF T), map tr args)
              | (Abs (x, T, b), args) => Term.list_comb (Abs (x, subF T, tr b), map tr args)
              | (Free (x, T), args) => Term.list_comb (Free (x, subF T), map tr args)
              | (h, args) => Term.list_comb (h, map tr args));
            val us_v = Free ("lab_xs", fvLT);
            (* the body of a decoder's node equation, over the children xs *)
            fun node_parts th =
              (case HOLogic.dest_Trueprop (Thm.prop_of th) of
                Const (\<^const_name>\<open>HOL.eq\<close>, _) $ (_ $ (_ $ _ $ xs)) $
                  (Const (\<^const_name>\<open>If\<close>, _) $ _ $ b $ _) => (xs, b)
              | _ => raise Fail "fuse: decoder equation");
            val node_ths = map (fn k => nth code_eqs (2 * k)) (0 upto length ndecs - 1);
            val leaf_ths = map (fn k => nth code_eqs (2 * k + 1)) (0 upto length ndecs - 1);
            val kbodies =
              map2 (fn th => fn T =>
                  let
                    val (xs, b0) = node_parts th;
                    val b = tr (Term.subst_atomic [(xs, Free ("lab_xs", HOLogic.listT astT'))] b0)
                      |> Term.subst_atomic [(Free ("lab_xs", fvLT), us_v)];
                    val _ = not (Term.exists_type (Term.exists_subtype (fn U => U = astT')) b)
                      orelse raise Fail "fuse: a child is used as a tree";
                  in Term.lambda us_v (map_option_c T $ inj_of T $ b) end)
                node_ths carTs
              handle ListPair.UnequalLengths => raise Fail "fuse: decoders";
            (* one constant per action: the lists below mention only constants *)
            val ((ks, fk_eqs), lthy) =
              fold_map (fn ((A, _), b) => fn lthy =>
                  let val (eq, lthy) = define ("fk_" ^ Grammar_Common.ident_in gram A) b lthy
                  in ((rhs_of_eq eq, eq), lthy) end)
                (decs ~~ kbodies) lthy
              |>> split_list;
            val hs =
              map2 (fn nd => fn T =>
                  Abs ("t", astT', map_option_c T $ inj_of T $ (nd $ Bound 0))) ndecs carTs;
            val hT = astT' --> optT valT;
            val kT = fvLT --> optT valT;
            val trT = HOLogic.mk_prodT (integerT, HOLogic.mk_prodT (hT, kT));
            val tr_lit =
              HOLogic.mk_list trT
                (map (fn ((i, h), k) => HOLogic.mk_prod (i, HOLogic.mk_prod (h, k))) (ixs ~~ hs ~~ ks));
            val (ftr_eq, lthy) = timed lthy "fuse: define ftr" (fn () => define_nocode "ftr" tr_lit lthy) ();
            val ftr = rhs_of_eq ftr_eq;
            val ftr_unfold = Thm.symmetric (mk_meta_eq ftr_eq);
            val fks_lit =
              HOLogic.mk_list (HOLogic.mk_prodT (integerT, kT)) (map HOLogic.mk_prod (ixs ~~ ks));
            val (fntab_eq, lthy) =
              define "fntab"
                (Const (\<^const_name>\<open>ftab\<close>,
                    HOLogic.natT --> HOLogic.listT (HOLogic.mk_prodT (integerT, kT)) -->
                      Type (\<^type_name>\<open>iarray\<close>, [optT kT])) $
                  (Const (\<^const_name>\<open>size\<close>, fastype_of names --> HOLogic.natT) $ names) $
                  fks_lit) lthy;
            val fntab = rhs_of_eq fntab_eq;
            val ct = Thm.cterm_of lthy;
            val [mf_cons, mf_nil, ml_cons, ml_nil, mk_cons, mk_nil] =
              map mk_meta_eq @{thms map_fst_lix};
            fun spine cons_th nil_th hd_conv ctm =
              (Conv.rewr_conv nil_th else_conv
                (Conv.rewr_conv cons_th then_conv
                  Conv.combination_conv (Conv.arg_conv hd_conv) (spine cons_th nil_th hd_conv))) ctm;
            val ix_rw = Conv.rewrs_conv (map mk_meta_eq ix_eqs);
            fun list_arg_conv cv = Conv.arg_conv cv;
            (* map fst ftr = map (lix names) ds, both [ix_A, ...] *)
            val l1 =
              (list_arg_conv (Conv.rewr_conv ftr_unfold) then_conv spine mf_cons mf_nil Conv.all_conv)
                (ct (Const (\<^const_name>\<open>map\<close>, (trT --> integerT) --> HOLogic.listT trT --> HOLogic.listT integerT) $
                  Const (\<^const_name>\<open>fst\<close>, trT --> integerT) $ ftr));
            val l2 = spine ml_cons ml_nil ix_rw
              (ct (Const (\<^const_name>\<open>map\<close>, (nameT --> integerT) --> HOLogic.listT nameT --> HOLogic.listT integerT) $
                  (Const (\<^const_name>\<open>lix\<close>, fastype_of names --> nameT --> integerT) $ names) $ ds));
            val mapfst_meta = Thm.transitive l1 (Thm.symmetric l2);
            val mapfst_eq = mapfst_meta RS @{thm meta_eq_to_obj_eq};
            val ds_dist = timed lthy "fuse: distinct names" (fn () =>
              prove lthy (HOLogic.mk_Trueprop
                  (Const (\<^const_name>\<open>distinct\<close>, HOLogic.listT nameT --> HOLogic.boolT) $ ds))
                (fn ctxt => SOLVED' (simp_tac (put_simpset HOL_basic_ss ctxt
                  |> Simplifier.add_simps @{thms distinct.simps list.set insert_iff empty_iff
                      list.inject list.distinct char.inject simp_thms})) 1
                  ORELSE simp_tac ctxt 1)) ();
            val sub_th = ofn "names_sub" @{thm names_sub} [names_eq];
            val dist_tr =
              Conv.fconv_rule (Conv.arg_conv (Conv.arg_conv (Conv.rewr_conv (Thm.symmetric mapfst_meta))))
                (ofn "distinct_lix" @{thm distinct_lix} [ds_dist, sub_th]);
            (* per nonterminal: kof (map hpart ftr) ix_A x = h_A x *)
            val kt =
              Conv.fconv_rule (Conv.arg_conv (Conv.arg_conv (Conv.rewr_conv ftr_unfold)))
                (ofn "kof_tr" @{thm kof_tr} [dist_tr]);
            fun dest_tall th =
              (case HOLogic.dest_Trueprop (Thm.prop_of th) of
                _ $ _ $ (Const (\<^const_name>\<open>Nil\<close>, _)) => []
              | _ =>
                  Conv.fconv_rule (Thm.beta_conversion true) (ofn "tallD1" @{thm tallD1} [th]) ::
                    dest_tall (ofn "tallD2" @{thm tallD2} [th]));
            val dl_ths = map (fn th => (th RS @{thm conjunct1}) RS @{thm spec}) (dest_tall kt);
            val pj_ths =
              map (fn (U, (inj, pj)) =>
                let
                  val x = Free ("x", optT U);
                  val goal = HOLogic.mk_Trueprop (HOLogic.mk_eq
                    (Const (\<^const_name>\<open>Option.bind\<close>, optT valT --> (valT --> optT U) --> optT U) $
                      (map_option_c U $ inj $ x) $ pj, x));
                in
                  (U, Goal.prove lthy ["x"] [] goal (fn {context = ctxt, ...} =>
                    HEADGOAL (Induct_Tacs.case_tac ctxt "x" [] NONE) THEN ALLGOALS (asm_full_simp_tac ctxt)))
                end) injs;
            val Ls =
              map2 (fn ((dl, nth_), lth) => fn T =>
                  let
                    val nd = (case HOLogic.dest_Trueprop (Thm.prop_of lth) of
                      Const (\<^const_name>\<open>HOL.eq\<close>, _) $ (nd $ _) $ _ => nd
                    | _ => raise Fail "fuse: leaf equation");
                    val ix = the (AList.lookup (op aconv) (ndecs ~~ ixs) nd);
                    val iv = Free ("i", integerT) and csv = Free ("cs", HOLogic.listT astT');
                    val other = Goal.prove lthy [] []
                      (Logic.all iv (Logic.all csv
                        (Logic.mk_implies (HOLogic.mk_Trueprop (HOLogic.mk_not (HOLogic.mk_eq (iv, ix))),
                          HOLogic.mk_Trueprop (HOLogic.mk_eq (nd $ (Node' $ iv $ csv),
                            Const (\<^const_name>\<open>None\<close>, optT T)))))))
                      (fn {context = ctxt, ...} => asm_full_simp_tac (put_simpset HOL_basic_ss ctxt
                        |> Simplifier.add_simps (nth_ :: @{thms if_False simp_thms})) 1);
                    val dlt =
                      (case HOLogic.dest_Trueprop (Thm.prop_of dl) of
                        Const (\<^const_name>\<open>HOL.eq\<close>, _) $ (dlt $ _ $ _) $ _ => dlt
                      | _ => raise Fail "fuse: kof equation");
                    val fv_i = Drule.infer_instantiate lthy
                      [(("dl", 0), ct dlt), (("ix", 0), ct ix), (("nd", 0), ct nd)] @{thm fproj_vof};
                  in
                    ofn "fproj_vof" fv_i [dl, the (AList.lookup (op =) pj_ths T), other, lth]
                    |> (fn th => (case Seq.pull (ALLGOALS (assume_tac lthy) th) of
                          SOME (th', _) => th'
                        | NONE => raise Fail "fuse: other labels"))
                    |> tap (fn th => Thm.nprems_of th = 0 orelse raise Fail "fuse: other labels")
                  end)
                (dl_ths ~~ node_ths ~~ leaf_ths) carTs;
            (* the equation of each nonterminal: its decoder on a node is its action *)
            val fuse_i = Drule.infer_instantiate lthy [(("tr", 0), ct ftr)] @{thm fuse_tree};
            val P =
              (case HOLogic.dest_Trueprop (nth (Thm.prems_of fuse_i) 1) of
                _ $ P $ _ => P
              | _ => raise Fail "fuse: fuse_tree");
            val basic = Simplifier.add_simps
              (Ls @ @{thms case_list_map case_fv_vof if_True simp_thms});
            val Hs = timed lthy "fuse: equations" (fn () =>
              Par_List.map (fn ((((i, h), k), nth_), fk_eq) =>
                  let val goal = HOLogic.mk_Trueprop (Envir.beta_norm (P $ i $ h $ k)) in
                    prove lthy goal (fn ctxt =>
                      resolve_tac ctxt @{thms allI} 1 THEN
                      simp_tac (put_simpset HOL_basic_ss ctxt |> basic
                        |> Simplifier.add_simps [nth_, fk_eq RS @{thm sym}]) 1)
                  end)
                (ixs ~~ hs ~~ ks ~~ node_ths ~~ fk_eqs)) ();
            val tallI_P = Drule.infer_instantiate lthy [(("P", 0), ct P)] @{thm tallI};
            val tallNil_P = Drule.infer_instantiate lthy [(("P", 0), ct P)] @{thm tallNil};
            val H_lit =
              fold_rev (fn ((((i, h), k), Hth)) => fn acc =>
                  let
                    val r = Drule.infer_instantiate lthy
                      [(("i", 0), ct i), (("h", 0), ct h), (("k", 0), ct k)] tallI_P
                      |> Conv.fconv_rule (Conv.implies_conv (Thm.beta_conversion true) Conv.all_conv);
                  in ofn "r" r [Hth, acc] end)
                (ixs ~~ hs ~~ ks ~~ Hs) tallNil_P;
            val H_tr =
              Conv.fconv_rule (Conv.arg_conv (Conv.arg_conv (Conv.rewr_conv (Thm.symmetric ftr_unfold)))) H_lit;
            val V = ofn "fuse_i" fuse_i [dist_tr, H_tr];
            (* the array of the actions *)
            val kp =
              (Conv.arg_conv (Conv.arg_conv (Conv.rewr_conv ftr_unfold) then_conv
                spine mk_cons mk_nil Conv.all_conv))
                (ct (Const (\<^const_name>\<open>ftab\<close>,
                    HOLogic.natT --> HOLogic.listT (HOLogic.mk_prodT (integerT, kT)) -->
                      Type (\<^type_name>\<open>iarray\<close>, [optT kT])) $
                  (Const (\<^const_name>\<open>size\<close>, fastype_of names --> HOLogic.natT) $ names) $
                  (Const (\<^const_name>\<open>map\<close>, (trT --> HOLogic.mk_prodT (integerT, kT)) -->
                      HOLogic.listT trT --> HOLogic.listT (HOLogic.mk_prodT (integerT, kT))) $
                    Const (\<^const_name>\<open>kpart\<close>, trT --> HOLogic.mk_prodT (integerT, kT)) $ ftr)));
            val fn_eq = ofn "trans" @{thm trans} [kp RS @{thm meta_eq_to_obj_eq}, fntab_eq];
            val range_th = ofn "lix_keys_range" @{thm lix_keys_range} [mapfst_eq, sub_th];
            val fnk = ofn "fnode_kof" @{thm fnode_kof} [fn_eq, range_th];
            val L_start = the (AList.lookup (op aconv) (ndecs ~~ Ls) nd_start);
            val th = ofn "bind_frun" @{thm bind_frun} [V, L_start, fnk];
            (* LR_Kern: the padded tables, a constant, and the run on them *)
            val lat = rhs_of_eq latabs_eq;
            val utabsT =
              (case fastype_of lat of Type (_, Ts) => Type (\<^type_name>\<open>utabs\<close>, Ts)
              | _ => raise Fail "fuse: tables type");
            val (utabs_eq, lthy) =
              define "utabs" (Const (\<^const_name>\<open>upad\<close>, fastype_of lat --> utabsT) $ lat) lthy;
            val uk = ofn "frun_ukrun" @{thm frun_ukrun} [fnk];
          in ([th, uk, utabs_eq], lthy) end;
        val (ths, fuse_msg, lthy) =
          (case timed lthy "fuse" (fn lthy => SOME (fuse lthy)
              handle Fail msg => (if msg = "fuse: not applicable" orelse msg = "fuse: span" then ()
                  else warning ("parser: fused actions: " ^ msg); NONE)
                | THM (msg, _, _) => (warning ("parser: fused actions: " ^ msg); NONE)
                | TERM (msg, _) => (warning ("parser: fused actions: " ^ msg); NONE)
                | ERROR msg => (warning ("parser: fused actions: " ^ msg); NONE)
                | Option.Option => (warning "parser: fused actions: lookup failed"; NONE)
                | Subscript => (warning "parser: fused actions: subscript"; NONE)
                | TYPE (msg, _, _) => (warning ("parser: fused actions: " ^ msg); NONE)) lthy of
            SOME (ths, lthy) => (lab_th :: ths, ", with fused actions", lthy)
          | NONE => ([lab_th], "", lthy));
      in SOME ((ths, fuse_msg), lthy) end
      handle ERROR msg => (warning ("parser: integer labels: " ^ msg); NONE)
        | Fail msg => (if msg = "labels: not applicable" then ()
            else warning ("parser: integer labels: " ^ msg); NONE)
        | THM (msg, _, _) => (warning ("parser: integer labels: " ^ msg); NONE)
        | TERM (msg, _) => (warning ("parser: integer labels: " ^ msg); NONE);

    fun simple_tables (nums_l, nums_th) lthy =
      let
        val arts = Grammar_Common.artifacts_of gram;
        val fresh_th =
          (case #restricted arts of
            SOME {fresh, ...} => fresh
          | NONE =>
              Goal.prove_sorry lthy [] []
                (HOLogic.mk_Trueprop (app \<^const_name>\<open>fresh_name\<close> [gram_t, shn_t]))
                (fn {context, ...} => HEADGOAL (fresh_name_tac context (#gram_def arts))));
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
        val (tabs_eqs, via, tabs_msg, driver, arr_th, lthy) =
          if Config.get lthy parser_int_tables then
            let val (ztabs_eq, lthy) = define "ztabs" (app' lthy \<^const_name>\<open>ztabs_of\<close> [ltabs]) lthy
            in
              ([ztabs_eq], @{thm dparse_via_int_tables}, "integer tables (LR_Simple, LR_Int)",
               NONE, NONE, lthy)
            end
          else
            let
              val (jtabs_eq, lthy) = define "jtabs" (app' lthy \<^const_name>\<open>jtabs_of\<close> [ltabs]) lthy;
              val (ktabs_eq, lthy) =
                define "ktabs" (app' lthy \<^const_name>\<open>ktabs_of\<close> [rhs_of_eq jtabs_eq]) lthy;
              val (ptabs_eq, lthy) =
                (case simple_lits of
                  [_, lit] =>
                    define_literal parse_bind "ptabs" lit
                      [states_eq, gtab_eq, redtab_eq, pc_eq, pf_eq, ltabs_eq, jtabs_eq, ktabs_eq]
                      lthy
                | _ => define "ptabs" (app' lthy \<^const_name>\<open>ptabs_of\<close> [rhs_of_eq ktabs_eq]) lthy);
              (* the evaluated \<^const>\<open>lr_simple_checks\<close> over the constants: its let
                 chain unfolded, then every table term rewritten to its constant *)
              val nums_e =
                nums_th
                |> Local_Defs.unfold lthy @{thms lr_simple_checks_def Let_def}
                |> Local_Defs.unfold lthy
                     [states_eq, gtab_eq, redtab_eq, pc_eq, pf_eq, ltabs_eq, jtabs_eq, ktabs_eq,
                      ptabs_eq];
              val (tnum_th, tnum_msg, f, tnum_def, lthy) =
                (case tok_sugar of
                  NONE =>
                    (@{thm refl}, "a search",
                     app' lthy \<^const_name>\<open>pnum\<close> [rhs_of_eq ptabs_eq], NONE, lthy)
                | SOME sugar =>
                    let
                      val (th, tnum_c, def_eq, lthy) =
                        timed lthy "tnum" (fn () =>
                          tnum_case lthy parse_bind sugar
                            (\<^const_name>\<open>pnum\<close>, ptabs_eq, nums_e, nums_l) []) ();
                    in (th, "a case distinction", tnum_c, SOME def_eq, lthy) end);
              (* the code equation runs on arrays indexed by integers (LR_Arr), computed
                 once from the tries; the diagnostics keep the run on the tries *)
              val (atabs_eq, lthy) =
                define "atabs" (app' lthy \<^const_name>\<open>atabs_of\<close> [rhs_of_eq ptabs_eq]) lthy;
              val (g_th, lthy) =
                (case (tok_sugar, tnum_def) of
                  (SOME sugar, SOME def_eq) =>
                    let
                      val (th, _, lthy) =
                        timed lthy "ztnum" (fn () =>
                          ztnum_case lthy parse_bind sugar (f, def_eq, nums_l)) ();
                    in (th, lthy) end
                | _ => (@{thm anum_via} OF [atabs_eq], lthy));
              (* without a nullable cycle no configuration repeats between two shifts,
                 and the code runs with no loop check (nrun, brun_arr_nrun); the answer
                 only decides the termination of the generated code *)
              val cycle = timed lthy "cycle check" nullable_cycle gram;
              val (arr_th, loop_msg) =
                (case cycle of
                  NONE =>
                    (@{thm trans} OF [@{thm brun_via_arr} OF [ptabs_eq, atabs_eq, g_th],
                      @{thm brun_arr_nrun}], "no loop check")
                | SOME _ => (@{thm brun_via_arr} OF [ptabs_eq, atabs_eq, g_th],
                    "a loop check (a nullable cycle)"));
              (* the run without a loop check then builds trees over integer labels, and
                 the decoders compare integers (LR_Lab) *)
              val (lab_ths, lab_msg, lthy) =
                (case cycle of
                  NONE =>
                    (case timed lthy "labels" (lab_rewrite (rhs_of_eq atabs_eq)) lthy of
                      SOME ((ths, fmsg), lthy) => (ths, ", over integer labels" ^ fmsg, lthy)
                    | NONE => ([], "", lthy))
                | SOME _ => ([], "", lthy));
              (* the start state as an integer constant: computed once, when the code loads,
                 not on every call from a Peano number *)
              val (zi0_eq, lthy) =
                define_term parse_bind "zi0"
                  (Const (\<^const_name>\<open>integer_of_nat\<close>, HOLogic.natT --> \<^typ>\<open>integer\<close>) $ rhs_of_eq i0_eq) lthy;
            in
              ([jtabs_eq, ktabs_eq, ptabs_eq, tnum_th], @{thm dparse_via_plain},
               "an action table over the states, numbering tokens by " ^ tnum_msg ^
               ", with " ^ loop_msg ^ lab_msg ^
               " (LR_Simple, LR_Trie, LR_Tok, LR_Prod, LR_Loop, LR_Plain, LR_Arr" ^
               (if null lab_ths then ")"
                else if length lab_ths > 1 then ", LR_Lab, LR_Fuse, LR_Kern)" else ", LR_Lab)"),
               SOME (Plain (rhs_of_eq ptabs_eq, rhs_of_eq i0_eq, f)), SOME (arr_th :: lab_ths @ [zi0_eq]), lthy)
            end;
        val _ =
          writeln ("parser: the code equation of \<open>" ^ Binding.name_of parse_bind ^
            "\<close> runs the simple driver on " ^ tabs_msg);
      in
        ((via OF
           ([static_th, states_eq, gtab_eq, redtab_eq, pc_eq, pf_eq, i0_eq, ltabs_eq] @ tabs_eqs),
          driver, arr_th), lthy)
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
          in
            if not (#nat_labels gram) andalso
              (shn = start_nt orelse member (op =) (maps nts (#prods gram)) shn)
            then NONE
            else if is_some (#restricted (Grammar_Common.artifacts_of gram))
            then Option.map #fresh (#restricted (Grammar_Common.artifacts_of gram))
            else
              SOME (Goal.prove_sorry lthy [] []
                (HOLogic.mk_Trueprop (app \<^const_name>\<open>fresh_name\<close> [gram_t, shn_t]))
                (fn {context, ...} =>
                  HEADGOAL (fresh_name_tac context (#gram_def (Grammar_Common.artifacts_of gram)))))
          end;
      in
        (* without a cycle the driver keeps no history: linear on reduce chains.  With
           a fresh start name it runs the state-indexed driver (vrun_k, LR_Vec: vrun_u on
           the lookahead numbered once, kernel-only frames) over the bundles vtab and
           vktab, restarting on sparse closures (sdrun, LR_Sparse) over the bundle
           stab, the initial kernel and its closure should two reductions be live at
           once; each a constant defined by its term;
           otherwise on the dense ones (drun_nh_c, LR_Fast).  With a cycle it stops on
           a repeated configuration (drun_hist) *)
        (case timed lthy "cycle check" nullable_cycle gram of
          NONE =>
            (case timed lthy "fresh_name" fresh lthy of
              SOME fresh_th =>
                let
                  (* under parser_literal_tables the five tables below are evaluated
                     literals as well, from one evaluation of \<^const>\<open>lr_vec_tables\<close>, which
                     makes the sparse tables literal too *)
                  val vec_tabs =
                    if Config.get lthy parser_literal_tables then
                      let
                        val (bundle_l, bundle_th) =
                          eval_lit lthy false "(vector tables)"
                            (app \<^const_name>\<open>lr_vec_tables\<close> [gram_t, shn_t]);
                        val tabs_eq =
                          @{thm trans} OF [@{thm lr_vec_tables_eq} RS @{thm sym}, bundle_th];
                      in
                        SOME (["stab", "vtab", "vktab", "sinit", "sclos"] ~~
                          (split_tuple_eq 5 tabs_eq ~~ dest_tuple 5 bundle_l))
                      end
                    else NONE;
                  fun vtable nm rhs prior lthy =
                    (case vec_tabs of
                      NONE => define nm rhs lthy
                    | SOME tab =>
                        define_literal parse_bind nm (the (AList.lookup (op =) tab nm)) prior lthy);
                  val base = [states_eq, gtab_eq, redtab_eq];
                  val (stab_eq, lthy) =
                    vtable "stab"
                      (app' lthy \<^const_name>\<open>mk_stab\<close>
                        (gram_t :: shn_t :: map rhs_of_eq [gtab_eq, states_eq, redtab_eq]))
                      base lthy;
                  val (vtab_eq, lthy) =
                    vtable "vtab"
                      (app' lthy \<^const_name>\<open>mk_vtab\<close>
                        (gram_t :: shn_t ::
                          map rhs_of_eq [stab_eq, states_eq, gtab_eq, redtab_eq]))
                      (base @ [stab_eq]) lthy;
                  val (vktab_eq, lthy) =
                    vtable "vktab" (app' lthy \<^const_name>\<open>mk_vktab\<close> [rhs_of_eq vtab_eq])
                      (base @ [stab_eq, vtab_eq]) lthy;
                  val (sinit_eq, lthy) =
                    vtable "sinit" (app' lthy \<^const_name>\<open>sinit\<close> [rhs_of_eq stab_eq])
                      (base @ [stab_eq]) lthy;
                  val (sclos_eq, lthy) =
                    vtable "sclos"
                      (app' lthy \<^const_name>\<open>sclosure\<close> (map rhs_of_eq [stab_eq, sinit_eq]))
                      (base @ [stab_eq, sinit_eq]) lthy;
                  (* tokens numbered by a case distinction if the token type allows it *)
                  val (tnum_th, f, lthy) =
                    (case tok_sugar of
                      NONE =>
                        (@{thm refl}, app' lthy \<^const_name>\<open>vnum\<close> [rhs_of_eq vtab_eq], lthy)
                    | SOME sugar =>
                        let
                          val nums_e =
                            @{thm vnums_map} OF [states_eq, redtab_eq, vtab_eq, vnums_eq];
                        in
                          timed lthy "tnum" (fn () =>
                            tnum_case lthy parse_bind sugar
                              (\<^const_name>\<open>vnum\<close>, vtab_eq, nums_e, vnums_l) []) ()
                          |> (fn (th, c, _, lthy) => (th, c, lthy))
                        end);
                  val _ =
                    writeln ("parser: the code equation of \<open>" ^ Binding.name_of parse_bind ^
                      "\<close> runs the state-indexed driver (LR_Vec), and the sparse one \
                      \(LR_Sparse) should two reductions be live at once");
                in
                  ((@{thm dparse_via_tables_vkn} OF
                    [states_eq, gtab_eq, redtab_eq, i0_eq, fresh_th, stab_eq, vtab_eq, vktab_eq,
                     sinit_eq, sclos_eq, tnum_th],
                    [fresh_th RS @{thm eqTrueI}],
                    SOME (Vec (rhs_of_eq vtab_eq, rhs_of_eq vktab_eq, rhs_of_eq stab_eq,
                      rhs_of_eq sinit_eq, rhs_of_eq sclos_eq, rhs_of_eq i0_eq, f, tnum_th))), lthy)
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
                    [states_eq, gtab_eq, redtab_eq, xinit_eq, xclos_eq, i0_eq, dtab_eq], [],
                    SOME (Dense (gram_t, shn_t, rhs_of_eq gtab_eq, rhs_of_eq states_eq,
                      rhs_of_eq redtab_eq, rhs_of_eq dtab_eq, rhs_of_eq xinit_eq,
                      rhs_of_eq xclos_eq, rhs_of_eq i0_eq))), lthy)
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
                [states_eq, gtab_eq, redtab_eq, xinit_eq, xclos_eq, i0_eq], [],
                SOME (Hist (gram_t, shn_t, rhs_of_eq gtab_eq, rhs_of_eq states_eq,
                  rhs_of_eq redtab_eq, rhs_of_eq xinit_eq, rhs_of_eq xclos_eq,
                  rhs_of_eq i0_eq))), lthy)
            end)
      end;

    val _ =
      if simple then ()
      else
        writeln ("parser: the code equation of \<open>" ^ Binding.name_of parse_bind ^
          "\<close> runs the set-anchored driver (LR_Driver)");
    val ((dlr_specialized, fresh_checks, driver, arr_th), lthy) =
      (case simple_checks of
        SOME sc =>
          timed lthy "simple tables" (simple_tables sc) lthy |>> (fn (th, d, a) => (th, [], d, a))
      | NONE => set_tables lthy |>> (fn (th, f, d) => (th, f, d, NONE)));

    fun post ({parse_const, parse_def_th}: Parser_Generators.post_input) lthy =
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
        (* the simple driver's code runs on the arrays (LR_Arr); parse_alt_th, the run
           on the tries, stays the view of the diagnostics *)
        fun to_code th =
          (case arr_th of
            NONE => th
          | SOME rws =>
              fold (fn a => fn th =>
                let val th' = Local_Defs.unfold lthy [a] th in
                  if Thm.eq_thm_prop (th', th) then
                    error ("parser: the array driver did not fire for \<open>" ^
                      Binding.name_of parse_bind ^ "\<close>: " ^
                      Thm.string_of_thm lthy a)
                  else th'
                end) rws th);
      in
        timed lthy "post: declare code" (fn () =>
          lthy
          |> Code.declare_eqns [(to_code parse_alt_th, true)]
          |> Grammar_Common.declare_code_global {default = false} [to_code parse_alt_global]) ()
        |> (if member (op =) options "diagnostics"
            then
              timed lthy "post: diagnostics"
                (define_diagnostics gram sts (not (null errors), err_words, given_keys) recover repair on_error_reduce token_info
                  {gram_t = gram_t, shn_t = shn_t, gt_t = rhs_of_eq gtab_eq,
                   rt_t = rhs_of_eq redtab_eq, i0_t = rhs_of_eq i0_eq}
                  (not simple) parse_bind parse_const parse_alt_th decoder driver)
            else I)
      end;
  in
    ({parse_body = parse_body, post = post, checks = [rlalr_eq, acc_eq, paths_eq] @ fresh_checks,
      recover = recover}, lthy)
  end;

end;
