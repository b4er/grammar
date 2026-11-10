(* induction over wf_ptree with one property per nonterminal, through a fixed
   selector P with one local equation per nonterminal:

     wf_ptree G pt \<Longrightarrow> \<forall>A. fst (proot pt) = Nt A \<longrightarrow> P A pt
     \<And>pt. P ''A'' pt = body_A pt

   P is then instantiated with the if-chain over the names, and the lemma of a
   nonterminal is projected from the closed statement:

     wf_ptree G pt \<Longrightarrow> fst (proot pt) = Nt ''A'' \<Longrightarrow> body_A pt *)

signature GRAMMAR_PTREE_INDUCT =
sig
  (* name: a nonterminal in HOL, of type nameT (Grammar_Common.name_term) *)
  type inv =
   {gram_t: term, ptreeT: typ, tokT: typ, nameT: typ, name: string -> term,
    bodies: (string * (term -> term)) list}
  val prove: Proof.context -> inv ->
    (Proof.context -> thm list -> int -> tactic) -> string -> thm

  (* the node of a tree witness, shared by the relation and the bridge *)
  val rhs_term: Grammar_Common.grammar -> Grammar_Common.prod -> term
  val node_intros: Proof.context -> {witness: term, rhs: term, pts: term} -> thm * thm
end;

structure Grammar_Ptree_Induct: GRAMMAR_PTREE_INDUCT =
struct

type inv =
 {gram_t: term, ptreeT: typ, tokT: typ, nameT: typ, name: string -> term,
  bodies: (string * (term -> term)) list};

(* the annotated right-hand side of a production, as the isg holds it *)
fun rhs_term (gram: Grammar_Common.grammar) (p: Grammar_Common.prod) =
  let
    val {symT, ...} = Grammar_Common.get_desc gram;
    val terminals = #terminals gram;
    val Nt_c = Const (\<^const_name>\<open>Nt\<close>, Grammar_Common.name_typ gram --> symT);
    val Tm_c = Const (\<^const_name>\<open>Tm\<close>, #tokT gram --> symT);
    fun sym (Grammar_Common.RN n) = Nt_c $ Grammar_Common.name_term gram n
      | sym (Grammar_Common.RC i) = Tm_c $ Vector.sub (terminals, i)
      | sym (Grammar_Common.RT i) = Tm_c $ Vector.sub (terminals, i);
  in
    HOLogic.mk_list (HOLogic.mk_prodT (symT, \<^typ>\<open>irel\<close>))
      (map (fn (rs, ann) => HOLogic.mk_prod (sym rs, Grammar_Common.irel_term ann)) (#rhs p))
  end;

(* exI for the witness \<open>PNode A i pts\<close>, and wf_node at its right-hand side and
   children *)
fun node_intros ctxt {witness, rhs, pts} =
  (infer_instantiate' ctxt [NONE, SOME (Thm.cterm_of ctxt witness)] @{thm exI},
   Drule.infer_instantiate ctxt
     [(("rhs", 0), Thm.cterm_of ctxt rhs), (("pts", 0), Thm.cterm_of ctxt pts)] @{thm wf_node});


(* literal string or numeral comparisons and the if-chain over the names, nothing
   else; the bodies in the branches are left alone (if_weak_cong) *)
fun literal_ss ctxt =
  put_simpset HOL_basic_ss ctxt
    |> Simplifier.add_simps @{thms if_True if_False list.inject list.distinct char.inject simp_thms
      num.inject num.distinct numeral_eq_iff numeral_eq_one_iff one_eq_numeral_iff
      zero_neq_numeral numeral_neq_zero zero_neq_one one_neq_zero}
  |> Simplifier.add_cong @{thm if_weak_cong};

fun mk_If c a b =
  Const (\<^const_name>\<open>If\<close>,
    HOLogic.boolT --> HOLogic.boolT --> HOLogic.boolT --> HOLogic.boolT) $ c $ a $ b;

fun prove ctxt ({gram_t, ptreeT, tokT, nameT, name, bodies}: inv) node_tac =
  let
    val isgT = fastype_of gram_t;
    val symT = Type (\<^type_name>\<open>sym\<close>, [nameT, tokT]);
    val rootT = HOLogic.mk_prodT (symT, \<^typ>\<open>nat\<close>);
    val proot_c = Const (\<^const_name>\<open>proot\<close>, ptreeT --> rootT);
    val wf_c = Const (\<^const_name>\<open>wf_ptree\<close>, isgT --> ptreeT --> HOLogic.boolT);
    val Nt_c = Const (\<^const_name>\<open>Nt\<close>, nameT --> symT);
    val fst_c = Const (\<^const_name>\<open>fst\<close>, rootT --> symT);
    val PT = nameT --> ptreeT --> HOLogic.boolT;

    val (P_nm, pt_nm, A_nm) =
      (case fst (Variable.variant_fixes ["P", "pt", "A"] ctxt) of
        [a, b, c] => (a, b, c)
      | _ => raise Fail "Grammar_Ptree_Induct: fixes");
    val P = Free (P_nm, PT);
    val pt = Free (pt_nm, ptreeT);
    val A_fr = Free (A_nm, nameT);
    fun root_is pt_t A_t = HOLogic.mk_eq (fst_c $ (proot_c $ pt_t), Nt_c $ A_t);

    (* the abstract statement *)
    val eqs =
      bodies |> map (fn (A, body) =>
        Logic.all pt (HOLogic.mk_Trueprop
          (HOLogic.mk_eq (P $ name A $ pt, body pt))));
    val inv =
      HOLogic.mk_all ("A", nameT,
        HOLogic.mk_imp (root_is pt (Bound 0), P $ Bound 0 $ pt));
    val prop =
      Logic.all pt (Logic.mk_implies
        (HOLogic.mk_Trueprop (wf_c $ gram_t $ pt), HOLogic.mk_Trueprop inv));
    fun tac {context, prems} =
      HEADGOAL (eresolve_tac context @{thms wf_ptree.induct})
      (* leaf: `Tm _ = Nt A` is false *)
      THEN HEADGOAL (SOLVED' (asm_full_simp_tac context))
      THEN HEADGOAL (SOLVED' (node_tac context prems));
    val abs_th = Goal.prove_sorry ctxt [P_nm] eqs prop tac;

    (* instantiate the selector, discharge the equations *)
    val P_var =
      (case filter (fn (_, T) => T = PT) (Term.add_vars (Thm.prop_of abs_th) []) of
        [v] => v
      | _ => raise Fail "Grammar_Ptree_Induct: selector variable");
    val chain =
      fold_rev (fn (A, body) => fn rest =>
          mk_If (HOLogic.mk_eq (A_fr, name A)) (body pt) rest)
        bodies \<^term>\<open>True\<close>;
    val selector = Term.lambda A_fr (Term.lambda pt chain);
    val inst_th =
      Thm.instantiate (TVars.empty, Vars.make [(P_var, Thm.cterm_of ctxt selector)]) abs_th
      |> Conv.fconv_rule (Thm.beta_conversion true);
    val eq_ths =
      map (fn k =>
          Goal.prove_sorry ctxt [] [] (Thm.term_of (Thm.cprem_of inst_th k))
            (fn {context, ...} => HEADGOAL (simp_tac (literal_ss context))))
        (1 upto length bodies);
    val closed = inst_th OF eq_ths;

    (* the lemma of one nonterminal: spec, mp, evaluate the chain *)
    val spec_th = closed RS @{thm spec} RS @{thm mp};
    val A_var =
      (case filter (fn (_, T) => T = nameT) (Term.add_vars (Thm.prop_of spec_th) []) of
        [v] => v
      | _ => raise Fail "Grammar_Ptree_Induct: name variable");
    fun project A =
      Thm.instantiate
        (TVars.empty, Vars.make [(A_var, Thm.cterm_of ctxt (name A))]) spec_th
      |> Conv.fconv_rule (Conv.concl_conv ~1 (Simplifier.rewrite (literal_ss ctxt)));
  in project end;

end;
