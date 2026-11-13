(* Author: Basil Fürer, Dmitriy Traytel *)

(* decoder totality is backend-independent: every completeness theorem of a
   parser that returns an `ast option` and then decodes it carries the premise

     \<And>t. ast_of G (Nt (istart G)) (istart_ind G) t ?w \<Longrightarrow> \<exists>x. dec t = Some x

   and `prover` states it for any nonterminal A (the shape above for the start),
   at the root \<open>(Nt ''A'', 0)\<close> unless A is the start, with one
   wf_ptree induction for all of them *)

signature PARSER_DEC_TOTAL =
sig
  val gram_eqs: Proof.context -> Grammar_Common.grammar -> thm list
  val dec_none: Proof.context -> Grammar_Common.grammar -> string -> thm
  (* dec_none for every nonterminal, in the order of the grammar; shared with the bridge *)
  val dec_nones: Proof.context -> Grammar_Common.grammar -> thm list
  val prover: Proof.context -> Grammar_Common.grammar -> thm list -> string -> thm
end;

structure Parser_Dec_Total: PARSER_DEC_TOTAL =
struct

fun mk_ex T body_fn =
  HOLogic.exists_const T $ Abs ("x", T, body_fn (Bound 0));

(* `iprods G == [...]`, `istart G == ''S''`, `istart_ind G == 0`:
   the selector equations of the grammar constant.

   The tactics rewrite with these instead of the record definition,
   so that the constant stays folded in every hypothesis that is not
   about its productions (for speed) *)
fun gram_eqs ctxt (gram: Grammar_Common.grammar) =
  let
    val {gram_t, gram_def, ...} = Grammar_Common.artifacts_of gram;
    val ctxt' = ctxt |> Simplifier.add_simps ([gram_def] @ @{thms is_cfg.make_def});
    fun eq sel =
      Simplifier.rewrite ctxt'
        (Thm.cterm_of ctxt (Syntax.check_term ctxt (Const (sel, dummyT) $ gram_t)));
  in
    map eq
      [\<^const_name>\<open>iprods\<close>, \<^const_name>\<open>istart\<close>, \<^const_name>\<open>istart_ind\<close>]
  end;

(* `asym t \<noteq> Nt ''A'' \<Longrightarrow> dec_A t = None`:

   the decoder of a wrong alternative reduces to None once the simplifier knows
   the root symbol of the child (asym_erase and the tree hypothesis
   `fst (proot c) = Nt B`) *)
fun dec_none ctxt (gram: Grammar_Common.grammar) A =
  let
    val {astT, symT, ...} = Grammar_Common.get_desc gram;
    val t_nm = the_single (fst (Variable.variant_fixes ["t"] ctxt));
    val t = Free (t_nm, astT);
    val prop =
      Logic.mk_implies
        (HOLogic.mk_Trueprop (HOLogic.mk_not (HOLogic.mk_eq
          (Const (\<^const_name>\<open>asym\<close>, astT --> symT) $ t,
           Const (\<^const_name>\<open>Nt\<close>, Grammar_Common.name_typ gram --> symT) $
             Grammar_Common.name_term gram A))),
         HOLogic.mk_Trueprop (HOLogic.mk_eq
          (Grammar_Defs.decoder_of ctxt gram A $ t,
           Grammar_Common.mk_None (Grammar_Common.carrier_of gram A))));
    fun tac {context, ...} =
      HEADGOAL (Induct_Tacs.case_tac context t_nm [] NONE)
      THEN ALLGOALS (asm_full_simp_tac context);
  in Goal.prove_sorry ctxt [t_nm] [] prop tac end;

(* the wf_ptree induction invariant, one body per nonterminal:

     \<And>pt. wf_ptree gram pt \<Longrightarrow> fst (proot pt) = Nt ''A'' \<Longrightarrow>
           \<exists>x. dec_A (erase pt) = Some x

   start nonterminal, the shape of the dec_total premise:

     \<And>w t. ast_of gram (Nt (istart gram)) (istart_ind gram) t w \<Longrightarrow>
            \<exists>x. dec_start t = Some x

   another nonterminal A, the premise as Parser_Generators.entry_grammar leaves it:

     \<And>w t. ast_of gram (Nt ''A'') 0 t w \<Longrightarrow> \<exists>x. dec_A t = Some x *)
fun prop2 ctxt (gram: Grammar_Common.grammar) start_nt =
  let
    val {isgT, wordT, astT, symT, ...} = Grammar_Common.get_desc gram;
    val gram_t = #gram_t (Grammar_Common.artifacts_of gram);
    val nameT = Grammar_Common.name_typ gram;
    val Nt_c = Const (\<^const_name>\<open>Nt\<close>, nameT --> symT);
    val dec_of = Grammar_Defs.decoder_of ctxt gram;

    val start_cT = Grammar_Common.carrier_of gram start_nt;
    val (istart_t, istart_ind_t) =
      if start_nt = #start gram then
        (Const (\<^const_name>\<open>istart\<close>, isgT --> nameT) $ gram_t,
         Const (\<^const_name>\<open>istart_ind\<close>, isgT --> \<^typ>\<open>nat\<close>) $ gram_t)
      else (Grammar_Common.name_term gram start_nt, \<^term>\<open>0 :: nat\<close>);
    val ast_of_c = Const (\<^const_name>\<open>ast_of\<close>,
      isgT --> symT --> \<^typ>\<open>nat\<close> --> astT --> wordT --> HOLogic.boolT);
    val t = Free ("t", astT);
    val w = Free ("w", wordT);
    val prem2 = ast_of_c $ gram_t $ (Nt_c $ istart_t) $ istart_ind_t $ t $ w;
    val concl2 = mk_ex start_cT (fn x =>
      HOLogic.mk_eq (dec_of start_nt $ t, Grammar_Common.mk_Some start_cT $ x));
  in
    Logic.all w (Logic.all t (Logic.mk_implies
      (HOLogic.mk_Trueprop prem2, HOLogic.mk_Trueprop concl2)))
  end;

fun dec_nones ctxt (gram: Grammar_Common.grammar) =
  Grammar_Common.timed ctxt "parser" "dec_none lemmas"
    (map (dec_none ctxt gram o fst)) (Grammar_Common.nonterms_list gram);

fun prover ctxt (gram: Grammar_Common.grammar) dec_nones =
  let
    val {astT, ptreeT, ...} = Grammar_Common.get_desc gram;
    val gram_t = #gram_t (Grammar_Common.artifacts_of gram);
    val erase_c = Const (\<^const_name>\<open>erase\<close>, ptreeT --> astT);
    val dec_of = Grammar_Defs.decoder_of ctxt gram;
    val nts = Grammar_Common.nonterms_list gram;

    val eqs = gram_eqs ctxt gram;

    (* body_A pt: \<exists>x. dec_A (erase pt) = Some x *)
    fun body (A, _) =
      let val cT = Grammar_Common.carrier_of gram A in
        (A, fn pt => mk_ex cT (fn x =>
          HOLogic.mk_eq (dec_of A $ (erase_c $ pt), Grammar_Common.mk_Some cT $ x)))
      end;

    (* node case: one subgoal per production *)
    fun node_tac ctxt sel_eqs =
      let
        val ctxt1 = ctxt |> Simplifier.add_simps (eqs @ sel_eqs @ @{thms list_all2_Cons1});
        (* ex_bool_eq: for a bool carrier the residue is `\<exists>x. x`, which
           simp_thms do not cover once `True = x` has been rewritten to `x` *)
        val ctxt2 =
          ctxt |> Simplifier.add_simps
            (dec_nones @ sel_eqs @ @{thms asym_erase case_ast_Nt_None ex_bool_eq});
      in
        Clasimp.clarsimp_tac ctxt1
        THEN_ALL_NEW
          (TRY o REPEAT_ALL_NEW (eresolve_tac ctxt @{thms disjE conjE}))
        THEN_ALL_NEW (TRY o Clasimp.clarsimp_tac ctxt1)
        THEN_ALL_NEW (REPEAT_DETERM o eresolve_tac ctxt @{thms proot_Tm_E})
        THEN_ALL_NEW SOLVED' (asm_full_simp_tac ctxt2)
      end;
    val project =
      Grammar_Ptree_Induct.prove ctxt
        {gram_t = gram_t, ptreeT = ptreeT, tokT = #tokT gram,
         nameT = Grammar_Common.name_typ gram, name = Grammar_Common.name_term gram,
         bodies = map body nts}
        node_tac;

    fun tac2 start_th ctxt =
      Method.insert_tac ctxt [start_th] 1
      THEN Local_Defs.unfold_tac ctxt @{thms ast_of_def}
      THEN HEADGOAL (SOLVED' (Clasimp.fast_force_tac (ctxt |> Simplifier.add_simps eqs)));

    fun tot A =
      let val start_th = project A in
        Goal.prove_sorry ctxt [] [] (prop2 ctxt gram A) (fn {context, ...} => tac2 start_th context)
        |> Grammar_Common.close_binders ctxt ["t"]
      end;
  in tot end;

end;
