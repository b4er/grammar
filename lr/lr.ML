(* the LR backend of the parser command: the parse body over the tables
   precomputed at definition time, the determinism and accept/reduce
   premises discharged by evaluating the static checks, and the printers
   that explain a non-empty check *)

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

fun eval_all lthy exprs =
  let
    val n = length exprs;
    val tuple = HOLogic.mk_tuple exprs;
    val literal = timed lthy "value (tables + checks)" (Value_Command.value lthy) tuple;
    val prop = HOLogic.mk_Trueprop (HOLogic.mk_eq (tuple, literal));
    val th =
      timed lthy "eval (tables + checks)" (fn () =>
        Goal.prove lthy [] [] prop
          (fn {context, ...} => HEADGOAL (Parser_Generators.eval_tac context))) ();
  in (dest_tuple n literal, split_tuple_eq n th) end;

fun lhs_of_eq th = fst (HOLogic.dest_eq (HOLogic.dest_Trueprop (Thm.prop_of th)));

(* register the literal as a constant and turn `expr = literal` into
   `expr = c`, with earlier table equations folded into `expr` *)
fun define_table parse_b nm (expr_eq, literal) prior_eqs lthy =
  timed lthy ("define_table " ^ nm) (fn () =>
  let
    val b = Binding.map_name (fn n => n ^ "_" ^ nm) parse_b;
    val ((_, def_th), lthy') =
      Grammar_Defs.define_const true
        (b, Thm.def_binding b, literal) lthy;

    val def_ax =
      the_default def_th (Grammar_Common.def_axiom lthy' (b, Thm.def_binding b));
    val eq_folded = Local_Defs.fold lthy' [def_ax] expr_eq;
    val eq_th =
      if null prior_eqs then eq_folded
      else Local_Defs.unfold lthy' prior_eqs eq_folded;
  in (eq_th, lthy') end) ();

val parser_int_tables = Attrib.setup_config_bool \<^binding>\<open>parser_int_tables\<close> (K false);

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

    (* the tables, each a per-parser constant with its `_eq` lemma *)
    fun app c args =
      Syntax.check_term lthy (Term.list_comb (Const (c, dummyT), args));

    val states_t = app \<^const_name>\<open>lr0_states\<close> [gram_t, shn_t];
    val gtab_t   = app \<^const_name>\<open>la_gtab\<close> [gram_t, states_t];
    val redtab_t = app \<^const_name>\<open>red_buckets\<close>
      [gram_t, shn_t, HOLogic.size_const (fastype_of states_t) $ states_t];
    val xinit_t  = app \<^const_name>\<open>xinit\<close> [gram_t, shn_t];
    val xclos_t  = app \<^const_name>\<open>xclosure_auto\<close> [gram_t, xinit_t];
    val i0_t     = app \<^const_name>\<open>st_find\<close>
      [states_t, app \<^const_name>\<open>lr0_start\<close> [gram_t, shn_t]];

    val rlalr_t = app \<^const_name>\<open>rlalr_conflicts\<close> [gram_t, shn_t];
    val acc_t = app \<^const_name>\<open>acc_conflicts\<close> [gram_t, shn_t];
    val ii_t = app \<^const_name>\<open>ii\<close> [gram_t];

    val (literals, eqs) =
      eval_all lthy
        [states_t, gtab_t, redtab_t, xinit_t, xclos_t, i0_t, rlalr_t, acc_t, ii_t];
    val (states_l, gtab_l, redtab_l, xinit_l, xclos_l, i0_l, rlalr_l, ii_l) =
      (case literals of
        [a, b, c, d, e, f, g, _, i] => (a, b, c, d, e, f, g, i)
      | _ => raise Fail "lr_build_parse: tuple literal");
    val (states_e, gtab_e, redtab_e, xinit_e, xclos_e, i0_e, rlalr_eq, acc_eq, ii_eq) =
      (case eqs of
        [a, b, c, d, e, f, g, h, i] => (a, b, c, d, e, f, g, h, i)
      | _ => raise Fail "lr_build_parse: tuple equations");

    val (states_eq, lthy) = define_table parse_bind "states" (states_e, states_l) [] lthy;
    val (((gtab_eq, redtab_eq), i0_eq), lthy) = lthy
      |>   define_table parse_bind "gtab" (gtab_e, gtab_l) [states_eq]
      ||>> define_table parse_bind "redtab" (redtab_e, redtab_l) [states_eq]
      ||>> define_table parse_bind "i0" (i0_e, i0_l) [states_eq];

    (* the simple driver of LR_Simple applies when the grammar has no layout
       annotations, the determinism check is empty, and no reduce cell that
       names a token constrains its width *)
    fun is_const c (Const (d, _)) = c = d
      | is_const _ _ = false;
    fun cell_ok c =
      (case dest_tuple 4 c of
        [_, _, t, tau] =>
          is_const \<^const_name>\<open>None\<close> t orelse is_const \<^const_name>\<open>WAny\<close> tau
      | _ => false);
    val simple =
      is_const \<^const_name>\<open>True\<close> ii_l andalso
      is_const \<^const_name>\<open>List.list.Nil\<close> rlalr_l andalso
      forall (forall cell_ok o HOLogic.dest_list) (HOLogic.dest_list redtab_l);

    fun simple_tables lthy =
      let
        val arts = Grammar_Common.artifacts_of gram;
        val fresh_simps = @{thms fresh_name_def is_cfg.make_def} @ [#gram_def arts];
        val fresh_th =
          Goal.prove lthy [] []
            (HOLogic.mk_Trueprop (app \<^const_name>\<open>fresh_name\<close> [gram_t, shn_t]))
            (fn {context, ...} => HEADGOAL (asm_full_simp_tac (context addsimps fresh_simps)));
        val wany_th =
          timed lthy "prove wany_ok" (fn () =>
            Goal.prove lthy [] []
              (HOLogic.mk_Trueprop (app \<^const_name>\<open>wany_ok\<close> [redtab_t]))
              (fn {context, ...} =>
                Local_Defs.unfold_tac context [states_eq, redtab_eq]
                THEN HEADGOAL (Parser_Generators.eval_tac context))) ();
        val static_th =
          @{thm sstaticI} OF [ii_eq RS @{thm eqTrueE}, rlalr_eq, fresh_th, wany_th];

        val psts_t = app \<^const_name>\<open>pr0_states\<close> [gram_t, shn_t];
        val pgt_t  = app \<^const_name>\<open>pgtab\<close> [gram_t, psts_t];
        val pc_t   = app \<^const_name>\<open>pcomps\<close> [gram_t, psts_t];
        val pf_t   = app \<^const_name>\<open>pfins\<close> [shn_t, psts_t];
        val p0_t   = app \<^const_name>\<open>st_find\<close>
          [psts_t, app \<^const_name>\<open>lr0_start\<close> [gram_t, shn_t]];
        val (literals2, eqs2) = eval_all lthy [psts_t, pgt_t, pc_t, pf_t, p0_t];
        val (psts_l, pgt_l, pc_l, pf_l, p0_l) =
          (case literals2 of
            [a, b, c, d, e] => (a, b, c, d, e)
          | _ => raise Fail "lr_build_parse: tuple literal");
        val (psts_e, pgt_e, pc_e, pf_e, p0_e) =
          (case eqs2 of
            [a, b, c, d, e] => (a, b, c, d, e)
          | _ => raise Fail "lr_build_parse: tuple equations");
        val (psts_eq, lthy) = define_table parse_bind "psts" (psts_e, psts_l) [] lthy;
        val ((((pgt_eq, pc_eq), pf_eq), p0_eq), lthy) = lthy
          |>   define_table parse_bind "pgt" (pgt_e, pgt_l) [psts_eq]
          ||>> define_table parse_bind "pcomps" (pc_e, pc_l) [psts_eq]
          ||>> define_table parse_bind "pfins" (pf_e, pf_l) [psts_eq]
          ||>> define_table parse_bind "p0" (p0_e, p0_l) [psts_eq];

        (* the indexed tables: productions and nonterminals numbered, rows keyed
           by terminal or nonterminal number, stored as arrays by parse_itabs *)
        fun rhs_of_eq th = snd (HOLogic.dest_eq (HOLogic.dest_Trueprop (Thm.prop_of th)));
        fun app' ctxt c args =
          Syntax.check_term ctxt (Term.list_comb (Const (c, dummyT), args));
        val ltabs_t = app' lthy \<^const_name>\<open>mk_ltabs\<close>
          (map rhs_of_eq [gtab_eq, states_eq, redtab_eq, pgt_eq, psts_eq, pc_eq, pf_eq]);
        val (ltabs_l, ltabs_e) =
          (case eval_all lthy [ltabs_t] of
            ([l], [e]) => (l, e)
          | _ => raise Fail "lr_build_parse: tuple literal");
        val (ltabs_eq, lthy) = define_table parse_bind "ltabs" (ltabs_e, ltabs_l) [] lthy;
        (* the tables of the code: by default binary tries (jtabs_of), which
           are static data and need no arithmetic with binary naturals; with
           parser_int_tables, arrays with integer indices (ztabs_of), computed
           when the code is loaded *)
        val int_tables = Config.get lthy parser_int_tables;
        val (tabs_eqs, via, tabs_msg, lthy) =
          if int_tables then
            let
              val tabs_b = Binding.map_name (fn n => n ^ "_ztabs") parse_bind;
              val ((_, tabs_def), lthy) =
                Grammar_Defs.define_const true
                  (tabs_b, Thm.def_binding tabs_b,
                   app' lthy \<^const_name>\<open>ztabs_of\<close> [rhs_of_eq ltabs_eq]) lthy;
              val tabs_ax =
                the_default tabs_def
                  (Grammar_Common.def_axiom lthy (tabs_b, Thm.def_binding tabs_b));
              val tabs_eq =
                Thm.symmetric (Local_Defs.meta_rewrite_rule lthy tabs_ax)
                RS @{thm meta_eq_to_obj_eq};
            in ([tabs_eq], @{thm dparse_via_int_tables}, "integer tables (LR_Simple, LR_Int)", lthy) end
          else
            let
              val jtabs_t = app' lthy \<^const_name>\<open>jtabs_of\<close> [rhs_of_eq ltabs_eq];
              val x0_t = HOLogic.mk_prod (rhs_of_eq i0_eq, rhs_of_eq p0_eq);
              (* the pairs, the check and the product tables, evaluated at once
                 with the tries and the pairs shared by let *)
              fun c n = Const (n, dummyT);
              fun pair a b = c \<^const_name>\<open>Pair\<close> $ a $ b;
              val let_t = Syntax.check_term lthy
                (c \<^const_name>\<open>Let\<close> $ jtabs_t $ Abs ("J", dummyT,
                  c \<^const_name>\<open>Let\<close> $ (c \<^const_name>\<open>kpairs\<close> $ Bound 0 $ x0_t) $
                    Abs ("kps", dummyT,
                      pair (Bound 0)
                        (pair (c \<^const_name>\<open>kok\<close> $ Bound 1 $ Bound 0 $ x0_t)
                          (pair (c \<^const_name>\<open>ktabs_of\<close> $ Bound 1 $ Bound 0)
                            (c \<^const_name>\<open>kidx\<close> $ Bound 0 $ x0_t))))));
              val let_l = timed lthy "value (product tables)" (Value_Command.value lthy) let_t;
              val let_th =
                timed lthy "eval (product tables)" (fn () =>
                  Goal.prove lthy [] [] (HOLogic.mk_Trueprop (HOLogic.mk_eq (let_t, let_l)))
                    (fn {context, ...} => HEADGOAL (Parser_Generators.eval_tac context))) ();
              val (kps_l, kok_l, ktabs_l, k0_l, kps_e, kok_e, ktabs_e, k0_e) =
                (case (dest_tuple 4 let_l,
                    split_tuple_eq 4 (Local_Defs.unfold lthy @{thms Let_def} let_th)) of
                  ([a, b, c, d], [e, f, g, h]) => (a, b, c, d, e, f, g, h)
                | _ => raise Fail "lr_build_parse: tuple literal");
            in
              if is_const \<^const_name>\<open>True\<close> kok_l then
                let
                  val (kps_eq, lthy) = define_table parse_bind "kpairs" (kps_e, kps_l) [] lthy;
                  val kok_th = Local_Defs.unfold lthy [kps_eq] kok_e RS @{thm eqTrueE};
                  val ((ktabs_eq, k0_eq), lthy) = lthy
                    |>   define_table parse_bind "ktabs" (ktabs_e, ktabs_l) [kps_eq]
                    ||>> define_table parse_bind "k0" (k0_e, k0_l) [kps_eq];
                in
                  ([@{thm refl}, kok_th, ktabs_eq, k0_eq], @{thm dparse_via_prod_tables},
                   "the product automaton (LR_Simple, LR_Trie, LR_Tok, LR_Prod)", lthy)
                end
              else
                let
                  val (jtabs_l, jtabs_e) =
                    (case eval_all lthy [jtabs_t] of
                      ([l], [e]) => (l, e)
                    | _ => raise Fail "lr_build_parse: tuple literal");
                  val (tabs_eq, lthy) = define_table parse_bind "jtabs" (jtabs_e, jtabs_l) [] lthy;
                in
                  ([tabs_eq], @{thm dparse_via_trie_tok_tables},
                   "trie tables (LR_Simple, LR_Trie, LR_Tok)", lthy)
                end
            end;
        val _ =
          writeln ("parser: the code equation of \<open>" ^ Binding.name_of parse_bind ^
            "\<close> runs the simple driver on " ^ tabs_msg);
      in
        (via OF
          ([static_th, states_eq, gtab_eq, redtab_eq, psts_eq, pgt_eq, pc_eq, pf_eq, i0_eq, p0_eq,
            ltabs_eq] @ tabs_eqs),
         lthy)
      end;

    fun set_tables lthy =
      let
        val (xinit_eq, lthy) = define_table parse_bind "xinit" (xinit_e, xinit_l) [] lthy;
        val (xclos_eq, lthy) = define_table parse_bind "xclos" (xclos_e, xclos_l) [xinit_eq] lthy;
      in
        (@{thm dparse_via_tables} OF [states_eq, gtab_eq, redtab_eq, xinit_eq, xclos_eq, i0_eq],
         lthy)
      end;

    val _ =
      if simple then ()
      else
        writeln ("parser: the code equation of \<open>" ^ Binding.name_of parse_bind ^
          "\<close> runs the set-anchored driver (LR_Driver)");
    val (dlr_specialized, lthy) =
      if simple then timed lthy "simple tables" simple_tables lthy
      else set_tables lthy;

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
    ({parse_body = parse_body, post = post, checks = [rlalr_eq, acc_eq]}, lthy)
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
  [(\<^const_name>\<open>WEq\<close>, "column = anchor"),
   (\<^const_name>\<open>WGe\<close>, "column \<ge> anchor"),
   (\<^const_name>\<open>WGt\<close>, "column > anchor"),
   (\<^const_name>\<open>WLe\<close>, "column \<le> anchor"),
   (\<^const_name>\<open>WLt\<close>, "column < anchor"),
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

(* one line per (lookahead, action pair); the cell variants of a pair differ
   only in their column relations, and the layout qualifier is shown only
   when every variant constrains both sides, otherwise the conflict is a
   plain one *)
fun pretty_pairs ctxt gram items prs =
  let
    fun la_key NONE = "$"
      | la_key (SOME a) = Syntax.string_of_term ctxt a;
    val groups =
      fold (fn (la, a1, a2) => fn acc =>
        let val k = la_key la ^ "|" ^ act_key ctxt a1 ^ "|" ^ act_key ctxt a2 in
          (case AList.lookup (op =) acc k of
            NONE => acc @ [(k, (la, a1, a2, [(rel_of a1, rel_of a2)]))]
          | SOME (la', b1, b2, rels) =>
              AList.update (op =) (k, (la', b1, b2, rels @ [(rel_of a1, rel_of a2)])) acc)
        end) prs [];
    fun line (_, (la, b1, b2, rels)) =
      let
        (* shift first, as in every other generator's report *)
        val (a1, a2) = (case (b1, b2) of (XReduce _, XShift _) => (b2, b1) | _ => (b1, b2));
        val rels = (case (b1, b2) of (XReduce _, XShift _) => map swap rels | _ => rels);
        val kind = kind_of a1 ^ "/" ^ kind_of a2 ^
          (case la of NONE => " at end of input" | SOME a => " on " ^ string_of_tm ctxt gram a);
        val layout =
          if is_none la orelse exists (fn (r1, r2) => r1 = "any column" orelse r2 = "any column") rels
          then []
          else
            (case rels of
              (r1, r2) :: _ =>
                [Pretty.str ("  \<comment> layout-dependent: " ^ kind_of a1 ^ " needs " ^ r1 ^
                   ", " ^ kind_of a2 ^ " needs " ^ r2)]
            | [] => []);
      in
        indent 2 (Pretty.block ([Pretty.str (kind ^ ":  "), pretty_act ctxt gram items a1,
          Pretty.str "  vs  ", pretty_act ctxt gram items a2] @ layout))
      end;
  in map line groups end;

fun pretty_witness ctxt gram sample wit =
  (case wit of
    NONE =>
      (case sample of
        NONE => []
      | SOME toks =>
          [indent 2 (Pretty.str ("example input \<open>" ^ toks_text ctxt gram toks ^
             "\<close>: no layout with two live actions found within the search budget \
             \(the check may over-approximate here)"))])
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

(* one entry of explain_rp *)
fun pretty_rp ctxt (gram: Grammar_Common.grammar) _ entry =
  let
    val (_, rest) = HOLogic.dest_prod entry;
    val (items_t, rest) = HOLogic.dest_prod rest;
    val (path_t, rest) = HOLogic.dest_prod rest;
    val (sample_t, rest) = HOLogic.dest_prod rest;
    val (prs_t, wit_t) = HOLogic.dest_prod rest;

    val items = map (apply2 dest_nat o HOLogic.dest_prod) (HOLogic.dest_list items_t);
    val sample = dest_sample sample_t;
    val prs = HOLogic.dest_list prs_t |> map (fn t =>
      let val (la, a1, a2) = dest_triple t
      in (dest_option la, dest_xact a1, dest_xact a2) end);
  in
    Pretty.chunks
      (Pretty.str (state_text ctxt gram (dest_path path_t)) ::
       pretty_pairs ctxt gram items prs @
       pretty_witness ctxt gram sample (dest_option wit_t))
  end;

(* one entry of explain_acc *)
fun pretty_acc ctxt gram _ entry =
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

fun pretty_report header entries =
  Pretty.string_of (Pretty.chunks (Pretty.str header :: entries));

fun lr_discharge
  ({gram, shn, checks}: Parser_Generators.discharge_input) ctxt prem =
  let
    fun get_check t = find_first (fn th => lhs_of_eq th aconv t) checks;
    val gram_short = Binding.name_of (#name gram);
    val arts = Grammar_Common.artifacts_of gram;
    val gram_t = #gram_t arts;
    val gram_def_th = #gram_def arts;
    fun conflicts_term c =
      Syntax.check_term ctxt (Term.list_comb (Const (c, dummyT), [gram_t, HOLogic.mk_string shn]));
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

    fun explain_term c v =
      Syntax.check_term ctxt (Term.list_comb (Const (c, dummyT), [gram_t, HOLogic.mk_string shn, v]));

    fun explained head v pretty_entry =
      (case Exn.result (fn () =>
          map_index (fn (k, e) => pretty_entry ctxt gram (k + 1) e)
            (HOLogic.dest_list (Value_Command.value ctxt (explain_term head v)))) () of
        Exn.Res prts => prts
      | Exn.Exn exn =>
          [Pretty.str ("  (no explanation: " ^ Runtime.exn_message exn ^ ")"),
           Pretty.str ("  " ^ Syntax.string_of_term ctxt v)]);

    fun report_check () =
      let val t = conflicts_term \<^const_name>\<open>rlalr_conflicts\<close> in
        case check_value t of
          SOME (Const (\<^const_name>\<open>List.list.Nil\<close>, _)) =>
            (writeln ("parser: static determinism check empty for \<open>" ^
              gram_short ^ "\<close>; \<open>mdet\<close> discharged - \<open>" ^
              ".complete\<close> is unconditional"); true)
        | SOME v =>
            let val n = length (HOLogic.dest_list v) in
              (warning (pretty_report
                ("parser: \<open>" ^ gram_short ^ "\<close> has LR conflicts in " ^
                  string_of_int n ^ " state" ^ (if n = 1 then "" else "s") ^
                  "; \<open>mdet\<close> kept as an assumption on .complete")
                (explained \<^const_name>\<open>explain_rp\<close> v pretty_rp)); false)
            end
        | NONE => false
      end;

    (* accept/reduce: the relational .complete needs this check as well *)
    val acc_tac = SOLVED' (check_tac (conflicts_term \<^const_name>\<open>acc_conflicts\<close>));

    fun report_acc () =
      let val t = conflicts_term \<^const_name>\<open>acc_conflicts\<close> in
        case check_value t of
          SOME (Const (\<^const_name>\<open>List.list.Nil\<close>, _)) =>
            (writeln ("parser: accept/reduce check empty for \<open>" ^
              gram_short ^ "\<close>; the relational \<open>.complete\<close> is unconditional"); true)
        | SOME v =>
            let val n = length (HOLogic.dest_list v) in
              (warning (pretty_report
                ("parser: \<open>" ^ gram_short ^ "\<close> has accept/reduce conflicts in " ^
                  string_of_int n ^ " state" ^ (if n = 1 then "" else "s") ^
                  "; \<open>acc_conflicts\<close> kept as an assumption on the relational .complete")
                (explained \<^const_name>\<open>explain_acc\<close> v pretty_acc)); false)
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
    if head_name = \<^const_name>\<open>fresh_name\<close> then SOME fresh_tac
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
