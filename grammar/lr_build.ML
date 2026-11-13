(* Author: Basil Fürer, Claude *)

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
        val (tabs_eqs, via, tabs_msg, driver, lthy) =
          if Config.get lthy parser_int_tables then
            let val (ztabs_eq, lthy) = define "ztabs" (app' lthy \<^const_name>\<open>ztabs_of\<close> [ltabs]) lthy
            in
              ([ztabs_eq], @{thm dparse_via_int_tables}, "integer tables (LR_Simple, LR_Int)",
               NONE, lthy)
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
              val (tnum_th, tnum_msg, f, lthy) =
                (case tok_sugar of
                  NONE =>
                    (@{thm refl}, "a search",
                     app' lthy \<^const_name>\<open>pnum\<close> [rhs_of_eq ptabs_eq], lthy)
                | SOME sugar =>
                    let
                      val (th, tnum_c, lthy) =
                        timed lthy "tnum" (fn () =>
                          tnum_case lthy parse_bind sugar
                            (\<^const_name>\<open>pnum\<close>, ptabs_eq, nums_e, nums_l) []) ();
                    in (th, "a case distinction", tnum_c, lthy) end);
            in
              ([jtabs_eq, ktabs_eq, ptabs_eq, tnum_th], @{thm dparse_via_plain},
               "an action table over the states, numbering tokens by " ^ tnum_msg ^
               " (LR_Simple, LR_Trie, LR_Tok, LR_Prod, LR_Loop, LR_Plain)",
               SOME (Plain (rhs_of_eq ptabs_eq, rhs_of_eq i0_eq, f)), lthy)
            end;
        val _ =
          writeln ("parser: the code equation of \<open>" ^ Binding.name_of parse_bind ^
            "\<close> runs the simple driver on " ^ tabs_msg);
      in
        ((via OF
           ([static_th, states_eq, gtab_eq, redtab_eq, pc_eq, pf_eq, i0_eq, ltabs_eq] @ tabs_eqs),
          driver), lthy)
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
    val ((dlr_specialized, fresh_checks, driver), lthy) =
      (case simple_checks of
        SOME sc =>
          timed lthy "simple tables" (simple_tables sc) lthy |>> (fn (th, d) => (th, [], d))
      | NONE => set_tables lthy);

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
      in
        timed lthy "post: declare code" (fn () =>
          lthy
          |> Code.declare_eqns [(parse_alt_th, true)]
          |> Grammar_Common.declare_code_global {default = false} [parse_alt_global]) ()
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
