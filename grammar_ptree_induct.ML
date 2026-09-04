(* induction over wf_ptree with one property per nonterminal, through a fixed
   selector P with one local equation per nonterminal:

     wf_ptree G pt \<Longrightarrow> \<forall>A. fst (proot pt) = Nt A \<longrightarrow> P A pt
     \<And>pt. P ''A'' pt = body_A pt

   P is then instantiated with the if-chain over the names, and the lemma of a
   nonterminal is projected from the closed statement:

     wf_ptree G pt \<Longrightarrow> fst (proot pt) = Nt ''A'' \<Longrightarrow> body_A pt *)

signature GRAMMAR_PTREE_INDUCT =
sig
  type inv =
   {gram_t: term, ptreeT: typ, tokT: typ,
    bodies: (string * (term -> term)) list}
  val prove: Proof.context -> inv ->
    (Proof.context -> thm list -> int -> tactic) -> string -> thm
end;

structure Grammar_Ptree_Induct: GRAMMAR_PTREE_INDUCT =
struct

type inv =
 {gram_t: term, ptreeT: typ, tokT: typ,
  bodies: (string * (term -> term)) list};


(* literal string comparisons and the if-chain over the names, nothing else *)
fun literal_ss ctxt =
  put_simpset HOL_basic_ss ctxt
    addsimps @{thms if_True if_False list.inject list.distinct char.inject simp_thms};

fun mk_If c a b =
  Const (\<^const_name>\<open>If\<close>,
    HOLogic.boolT --> HOLogic.boolT --> HOLogic.boolT --> HOLogic.boolT) $ c $ a $ b;

fun prove ctxt ({gram_t, ptreeT, tokT, bodies}: inv) node_tac =
  let
    val isgT = fastype_of gram_t;
    val symT = Type (\<^type_name>\<open>sym\<close>, [HOLogic.stringT, tokT]);
    val rootT = HOLogic.mk_prodT (symT, \<^typ>\<open>nat\<close>);
    val proot_c = Const (\<^const_name>\<open>proot\<close>, ptreeT --> rootT);
    val wf_c = Const (\<^const_name>\<open>wf_ptree\<close>, isgT --> ptreeT --> HOLogic.boolT);
    val Nt_c = Const (\<^const_name>\<open>Nt\<close>, HOLogic.stringT --> symT);
    val fst_c = Const (\<^const_name>\<open>fst\<close>, rootT --> symT);
    val PT = HOLogic.stringT --> ptreeT --> HOLogic.boolT;

    val (P_nm, pt_nm, A_nm) =
      (case fst (Variable.variant_fixes ["P", "pt", "A"] ctxt) of
        [a, b, c] => (a, b, c)
      | _ => raise Fail "Grammar_Ptree_Induct: fixes");
    val P = Free (P_nm, PT);
    val pt = Free (pt_nm, ptreeT);
    val A_fr = Free (A_nm, HOLogic.stringT);
    fun root_is pt_t A_t = HOLogic.mk_eq (fst_c $ (proot_c $ pt_t), Nt_c $ A_t);

    (* the abstract statement *)
    val eqs =
      bodies |> map (fn (A, body) =>
        Logic.all pt (HOLogic.mk_Trueprop
          (HOLogic.mk_eq (P $ HOLogic.mk_string A $ pt, body pt))));
    val inv =
      HOLogic.mk_all ("A", HOLogic.stringT,
        HOLogic.mk_imp (root_is pt (Bound 0), P $ Bound 0 $ pt));
    val prop =
      Logic.all pt (Logic.mk_implies
        (HOLogic.mk_Trueprop (wf_c $ gram_t $ pt), HOLogic.mk_Trueprop inv));
    fun tac {context, prems} =
      HEADGOAL (eresolve_tac context @{thms wf_ptree.induct})
      (* leaf: `Tm _ = Nt A` is false *)
      THEN HEADGOAL (SOLVED' (asm_full_simp_tac context))
      THEN HEADGOAL (SOLVED' (node_tac context prems));
    val abs_th = Goal.prove ctxt [P_nm] eqs prop tac;

    (* instantiate the selector, discharge the equations *)
    val P_var =
      (case filter (fn (_, T) => T = PT) (Term.add_vars (Thm.prop_of abs_th) []) of
        [v] => v
      | _ => raise Fail "Grammar_Ptree_Induct: selector variable");
    val chain =
      fold_rev (fn (A, body) => fn rest =>
          mk_If (HOLogic.mk_eq (A_fr, HOLogic.mk_string A)) (body pt) rest)
        bodies \<^term>\<open>True\<close>;
    val selector = Term.lambda A_fr (Term.lambda pt chain);
    val inst_th =
      Thm.instantiate (TVars.empty, Vars.make [(P_var, Thm.cterm_of ctxt selector)]) abs_th
      |> Conv.fconv_rule (Thm.beta_conversion true);
    val eq_ths =
      map (fn k =>
          Goal.prove ctxt [] [] (Thm.term_of (Thm.cprem_of inst_th k))
            (fn {context, ...} => HEADGOAL (simp_tac (literal_ss context))))
        (1 upto length bodies);
    val closed = inst_th OF eq_ths;

    (* the lemma of one nonterminal: spec, mp, evaluate the chain *)
    val spec_th = closed RS @{thm spec} RS @{thm mp};
    val A_var =
      (case filter (fn (_, T) => T = HOLogic.stringT) (Term.add_vars (Thm.prop_of spec_th) []) of
        [v] => v
      | _ => raise Fail "Grammar_Ptree_Induct: name variable");
    fun project A =
      Thm.instantiate
        (TVars.empty, Vars.make [(A_var, Thm.cterm_of ctxt (HOLogic.mk_string A))]) spec_th
      |> Conv.fconv_rule (Conv.concl_conv ~1 (Simplifier.rewrite (literal_ss ctxt)));
  in project end;

end;
