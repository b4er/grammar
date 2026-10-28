(* the bridge from a parser's language-level theorems to the relation
   family of the grammar: decoder soundness by wf_ptree induction and the
   relation-to-decoder direction by the family's induction, component by
   component; `prover` shares both inductions between the start symbols of a
   multi-entry parser *)

signature PARSER_REL_BRIDGE =
sig
  type bridge = {pred_P: term, dec_sound: thm, rel_dec: thm}
  val prove: Proof.context -> Grammar_Common.grammar ->
    Grammar_Common.rel_info -> bridge
  val prover: Proof.context -> Grammar_Common.grammar ->
    Grammar_Common.rel_info -> string -> bridge
end;

structure Parser_Rel_Bridge: PARSER_REL_BRIDGE =
struct

type bridge = {pred_P: term, dec_sound: thm, rel_dec: thm};

val zero_nat = \<^term>\<open>0 :: nat\<close>;

(** the grammar's types and constants **)

type setup =
 {gram: Grammar_Common.grammar,
  gram_t: term, gram_eqs: thm list,
  preds: (string * term) list, insensitive: bool,
  astT: typ, ptreeT: typ, wordT: typ, tokenT: typ, symT: typ,
  carrier_of: string -> typ, dec_of: string -> term,
  proot_c: term, erase_c: term, pyield_c: term, wf_c: term, Nt_c: term, Tm_c: term};

fun setup ctxt (gram: Grammar_Common.grammar) preds : setup =
  let
    val {isgT, wordT, astT, tokenT, ...} = Grammar_Common.get_desc gram;
    val arts = Grammar_Common.artifacts_of gram;
    val gram_t = #gram_t arts;
    val tokT = #tokT gram;
    val Ts = (case astT of Type (_, Ts) => Ts | _ => raise Fail "Parser_Rel_Bridge: astT");
    val ptreeT = Type (\<^type_name>\<open>ptree\<close>, Ts);
    val symT = Type (\<^type_name>\<open>sym\<close>, [HOLogic.stringT, tokT]);
    val rootT = HOLogic.mk_prodT (symT, HOLogic.natT);
  in
    {gram = gram, gram_t = gram_t, gram_eqs = Parser_Dec_Total.gram_eqs ctxt gram,
     preds = preds, insensitive = Grammar_Defs.is_indent_insensitive gram,
     astT = astT, ptreeT = ptreeT, wordT = wordT, tokenT = tokenT, symT = symT,
     carrier_of = Grammar_Common.carrier_of gram,
     dec_of = Grammar_Defs.decoder_of ctxt gram,
     proot_c = Const (\<^const_name>\<open>proot\<close>, ptreeT --> rootT),
     erase_c = Const (\<^const_name>\<open>erase\<close>, ptreeT --> astT),
     pyield_c = Const (\<^const_name>\<open>pyield\<close>, ptreeT --> wordT),
     wf_c = Const (\<^const_name>\<open>wf_ptree\<close>, isgT --> ptreeT --> HOLogic.boolT),
     Nt_c = Const (\<^const_name>\<open>Nt\<close>, HOLogic.stringT --> symT),
     Tm_c = Const (\<^const_name>\<open>Tm\<close>, tokT --> symT)}
  end;

(* the root of a tree of the start symbol A: by the selectors when A is the
   grammar's start, else (Nt ''A'', 0) as Parser_Generators.entry_grammar leaves it *)
fun start_root (s: setup) start =
  let val isgT = fastype_of (#gram_t s) in
    if start = #start (#gram s) then
      HOLogic.mk_prod
        (#Nt_c s $ (Const (\<^const_name>\<open>istart\<close>, isgT --> HOLogic.stringT) $ #gram_t s),
         Const (\<^const_name>\<open>istart_ind\<close>, isgT --> HOLogic.natT) $ #gram_t s)
    else HOLogic.mk_prod (#Nt_c s $ HOLogic.mk_string start, zero_nat)
  end;

(* P: the relation of the start symbol at the start indentation *)
fun pred_P (s: setup) start =
  let
    val pred = the (AList.lookup (op =) (#preds s) start);
  in
    if #insensitive s then pred
    else
      let
        val w = Free ("__w", #wordT s);
        val x = Free ("__x", #carrier_of s start);
      in Term.lambda w (Term.lambda x (pred $ zero_nat $ w $ x)) end
  end;

(* the annotated right-hand side of a production, as the isg holds it *)
fun rhs_hol (s: setup) (p: Grammar_Common.prod) =
  let
    val terminals = #terminals (#gram s);
    val sym_annT = HOLogic.mk_prodT (#symT s, \<^typ>\<open>irel\<close>);
    fun sym (Grammar_Common.RN n) = #Nt_c s $ HOLogic.mk_string n
      | sym (Grammar_Common.RC i) = #Tm_c s $ Vector.sub (terminals, i)
      | sym (Grammar_Common.RT i) = #Tm_c s $ Vector.sub (terminals, i);
  in
    HOLogic.mk_list sym_annT
      (map (fn (rs, ann) => HOLogic.mk_prod (sym rs, Grammar_Common.irel_term ann)) (#rhs p))
  end;


(** dec_sound: a decoded value satisfies the relation **)

(* body_A pt: \<forall>x. dec_A (erase pt) = Some x \<longrightarrow> pred_A [snd (proot pt)] (pyield pt) x *)
fun b1_body (s: setup) (A, pred) pt =
  let
    val cT = #carrier_of s A;
    val x = Free ("x", cT);
    val root = #proot_c s $ pt;
    val ind = HOLogic.mk_snd root;
    val pred_app =
      if #insensitive s then pred $ (#pyield_c s $ pt) $ x
      else pred $ ind $ (#pyield_c s $ pt) $ x;
    val body =
      HOLogic.mk_imp
        (HOLogic.mk_eq (#dec_of s A $ (#erase_c s $ pt), Grammar_Common.mk_Some cT $ x),
         pred_app);
  in HOLogic.all_const cT $ Term.lambda x body end;

(* node case: one subgoal per production, as in Parser_Dec_Total; what is left
   after the decoder hypothesis is reduced is closed by the production's intro.
   A unit self-loop's intro `G_A j w x ==> i R j ==> G_A i w x` (loops) is not
   in the rule set (see prove): it is applied once when the search fails, its
   premises then closed by the child's induction hypothesis and the relation *)
fun b1_node_tac ctxt (s: setup) (intros, loops) dec_nones sel_eqs =
  let
    val ctxt1 = ctxt addsimps (#gram_eqs s @ sel_eqs @ @{thms list_all2_Cons1});
    val ctxt2 =
      Splitter.add_split @{thm option.split_asm} ctxt
        addsimps (dec_nones @ sel_eqs @
          @{thms bind_eq_Some_conv asym_erase case_ast_Nt_None});
    val ctxt3 = ctxt2 addIs intros;
    val close = Clasimp.fast_force_tac ctxt3;
  in
    Clasimp.clarsimp_tac ctxt1
    THEN_ALL_NEW (TRY o REPEAT_ALL_NEW (eresolve_tac ctxt @{thms disjE conjE}))
    THEN_ALL_NEW (TRY o Clasimp.clarsimp_tac ctxt1)
    THEN_ALL_NEW (REPEAT_DETERM o eresolve_tac ctxt @{thms proot_Tm_E})
    THEN_ALL_NEW (TRY o Clasimp.clarsimp_tac ctxt2)
    THEN_ALL_NEW SOLVED' (close ORELSE' (resolve_tac ctxt loops THEN_ALL_NEW close))
  end;

(* the lemma of a nonterminal A, by projection:
   wf_ptree G pt \<Longrightarrow> fst (proot pt) = Nt A \<Longrightarrow> body_A pt *)
fun prove_b1_all ctxt (s: setup) intros dec_nones =
  Grammar_Ptree_Induct.prove ctxt
    {gram_t = #gram_t s, ptreeT = #ptreeT s, tokT = #tokT (#gram s),
     bodies = map (fn Ap => (fst Ap, b1_body s Ap)) (#preds s)}
    (fn ctxt' => fn sel_eqs => b1_node_tac ctxt' s intros dec_nones sel_eqs);

fun prove_dec_sound ctxt (s: setup) b1_all start =
  let
    val cT = #carrier_of s start;
    val (pt_nm, x_nm) =
      (case Variable.variant_fixes ["pt", "x"] ctxt of
        ([a, b], _) => (a, b)
      | _ => raise Fail "prove_dec_sound: fixes");
    val pt = Free (pt_nm, #ptreeT s);
    val x = Free (x_nm, cT);
    val prop =
      Logic.list_implies
        ([HOLogic.mk_Trueprop (#wf_c s $ #gram_t s $ pt),
          HOLogic.mk_Trueprop (HOLogic.mk_eq (#proot_c s $ pt, start_root s start)),
          HOLogic.mk_Trueprop
            (HOLogic.mk_eq (#dec_of s start $ (#erase_c s $ pt), Grammar_Common.mk_Some cT $ x))],
         HOLogic.mk_Trueprop (Term.betapplys (pred_P s start, [#pyield_c s $ pt, x])));
    val start_th = b1_all start;
    fun tac {context, ...} =
      Method.insert_tac context [start_th] 1
      THEN HEADGOAL (SOLVED' (Clasimp.fast_force_tac (context addsimps #gram_eqs s)));
  in
    Goal.prove_sorry ctxt [pt_nm, x_nm] [] prop tac
    |> Grammar_Common.close_binders ctxt [pt_nm, x_nm]
  end;


(** rel_dec: the relation exhibits a tree the decoder accepts **)

fun b2_body (s: setup) A root_t w x =
  let
    val cT = #carrier_of s A;
    val b = Bound 0;
  in
    HOLogic.mk_exists ("pt", #ptreeT s,
      HOLogic.mk_conj (#wf_c s $ #gram_t s $ b,
        HOLogic.mk_conj
          (HOLogic.mk_eq (#proot_c s $ b, root_t),
           HOLogic.mk_conj
             (HOLogic.mk_eq (#pyield_c s $ b, w),
              HOLogic.mk_eq (#dec_of s A $ (#erase_c s $ b), Grammar_Common.mk_Some cT $ x)))))
  end;

fun nt_root (s: setup) A i_t =
  HOLogic.mk_prod (#Nt_c s $ HOLogic.mk_string A, i_t);

(* the segments of an intro's word: w1 @ (w2 @ ...) *)
fun segments (Const (\<^const_name>\<open>List.append\<close>, _) $ a $ b) = a :: segments b
  | segments (Const (\<^const_name>\<open>List.Nil\<close>, _)) = []
  | segments t = [t];

fun b2_case_tac ctxt (s: setup) (p: Grammar_Common.prod) =
  (REPEAT_DETERM o eresolve_tac ctxt @{thms exE conjE})
  THEN' Subgoal.FOCUS (fn {context = ctxt', prems, concl, ...} =>
    let
      val (ptT, conj) =
        (case HOLogic.dest_Trueprop (Thm.term_of concl) of
          Const (\<^const_name>\<open>Ex\<close>, _) $ Abs (_, T, b) => (T, b)
        | _ => raise Fail "Parser_Rel_Bridge: case conclusion is not an existential");
      val cs = HOLogic.conjuncts conj;
      val (A_t, i_t) =
        (case nth cs 1 of
          Const (\<^const_name>\<open>HOL.eq\<close>, _) $ _ $ r => HOLogic.dest_prod r
        | _ => raise Fail "Parser_Rel_Bridge: root conjunct");
      val A_lit =
        (case A_t of
          Const (\<^const_name>\<open>Nt\<close>, _) $ a => a
        | _ => raise Fail "Parser_Rel_Bridge: root symbol");
      val _ =
        if HOLogic.dest_string A_lit = #lhs p then ()
        else raise Fail "Parser_Rel_Bridge: induction cases out of production order";
      val word =
        (case nth cs 2 of
          Const (\<^const_name>\<open>HOL.eq\<close>, _) $ _ $ w => w
        | _ => raise Fail "Parser_Rel_Bridge: yield conjunct");
      val PLeaf_c = Const (\<^const_name>\<open>PLeaf\<close>, #tokenT s --> ptT);
      val PNode_c =
        Const (\<^const_name>\<open>PNode\<close>, HOLogic.stringT --> HOLogic.natT --> HOLogic.listT ptT --> ptT);
      fun yield_of th =
        (case HOLogic.dest_Trueprop (Thm.prop_of th) of
          Const (\<^const_name>\<open>HOL.eq\<close>, _) $ (Const (\<^const_name>\<open>pyield\<close>, _) $ pt) $ w =>
            SOME (pt, w)
        | _ => NONE) handle TERM _ => NONE;
      val yields = map_filter yield_of prems;
      fun child (Const (\<^const_name>\<open>Cons\<close>, _) $ tok $ Const (\<^const_name>\<open>Nil\<close>, _)) =
            PLeaf_c $ tok
        | child w =
            (case find_first (fn (_, w') => w' aconv w) yields of
              SOME (pt, _) => pt
            | NONE => raise Fail "Parser_Rel_Bridge: no subtree for a nonterminal segment");
      val children = map child (segments word);
      val pts_hol = HOLogic.mk_list ptT children;
      val witness = PNode_c $ A_lit $ i_t $ pts_hol;
      val exI_inst =
        infer_instantiate' ctxt' [NONE, SOME (Thm.cterm_of ctxt' witness)] @{thm exI};
      val wf_node_inst =
        Drule.infer_instantiate ctxt'
          [(("rhs", 0), Thm.cterm_of ctxt' (rhs_hol s p)),
           (("pts", 0), Thm.cterm_of ctxt' pts_hol)] @{thm wf_node};
      (* the decoder conjunct: nonterminal children by their induction
         hypotheses, wrong alternatives by dec_none / case_ast_Nt_None *)
      val simp_ctxt =
        ctxt' addsimps (#gram_eqs s @ @{thms wf_leaf asym_erase case_ast_Nt_None});
    in
      HEADGOAL (resolve_tac ctxt' [exI_inst])
      THEN HEADGOAL (REPEAT_ALL_NEW (resolve_tac ctxt' @{thms conjI}))
      THEN HEADGOAL (resolve_tac ctxt' [wf_node_inst])
      THEN ALLGOALS (Method.insert_tac ctxt' prems)
      THEN ALLGOALS
        (SOLVED' (asm_full_simp_tac simp_ctxt) ORELSE'
         SOLVED' (Clasimp.fast_force_tac (simp_ctxt addSEs @{thms erase_Nt_E2})))
    end handle Fail _ => no_tac) ctxt;

(* one lemma per nonterminal, `pred_A i w x \<Longrightarrow> \<exists>pt. ...` *)
fun prove_b2_all ctxt (s: setup) dec_nones =
  let
    (* the family is defined by one inductive definition per component *)
    fun pred A = (A, the (AList.lookup (op =) (#preds s) A));
    val comps =
      Grammar_Defs.components (#gram s) |> map (fn comp =>
        let val preds = map pred comp
        in (preds, #induct (#2 (Inductive.the_inductive ctxt (snd (hd preds))))) end);
    val prods = #prods (#gram s);
    fun case_tac ctxt' k =
      DETERM (HEADGOAL (SOLVED' (b2_case_tac (ctxt' addsimps dec_nones) s (nth prods k))));
    val ths =
      Grammar_Defs.prove_family ctxt
        {comps = comps, prod_lhss = map #lhs prods, insensitive = #insensitive s,
         wordT = #wordT s, carrier_of = #carrier_of s, norm = I}
        (fn A => fn i_t => fn w => fn x => b2_body s A (nt_root s A i_t) w x)
        case_tac;
  in map (the o AList.lookup (op =) ths o fst) (#preds s) end;

(* the start lemma of b2_all, resolved against the statement once its selector
   applications are rewritten *)
fun prove_rel_dec ctxt (s: setup) b2_all start =
  let
    val cT = #carrier_of s start;
    val (w_nm, x_nm) =
      (case Variable.variant_fixes ["w", "x"] ctxt of
        ([a, b], _) => (a, b)
      | _ => raise Fail "prove_rel_dec: fixes");
    val w = Free (w_nm, #wordT s);
    val x = Free (x_nm, cT);
    val prop =
      Logic.mk_implies
        (HOLogic.mk_Trueprop (Term.betapplys (pred_P s start, [w, x])),
         HOLogic.mk_Trueprop (b2_body s start (start_root s start) w x));
    val start_th = nth b2_all (find_index (fn (A, _) => A = start) (#preds s));
    fun tac {context, ...} =
      HEADGOAL (TRY o simp_tac (put_simpset HOL_basic_ss context addsimps #gram_eqs s))
      THEN HEADGOAL (SOLVED' (eresolve_tac context [start_th]));
  in
    Goal.prove_sorry ctxt [w_nm, x_nm] [] prop tac
    |> Grammar_Common.close_binders ctxt [w_nm, x_nm]
  end;


(** entry point **)

(* the family must match the nonterminals of the record *)
fun validate (gram: Grammar_Common.grammar) (ri: Grammar_Common.rel_info) =
  let
    val nts = map fst (Grammar_Common.nonterms_list gram);
    val pnames = map fst (#preds ri);
  in
    if pnames = nts then ()
    else
      error ("Parser_Rel_Bridge.prove: predicate family for nonterminal(s) " ^
        commas_quote pnames ^ " does not match the nonterminals " ^
        commas_quote nts ^ " of grammar " ^
        quote (Binding.name_of (#name gram)))
  end;

(* report a failed bridge by its name and the first line of the failure *)
fun concise what f =
  f () handle ERROR msg =>
    error ("bridge \<open>" ^ what ^ "\<close>: " ^
      (case split_lines msg of l :: _ => l | [] => msg));

fun prover ctxt (gram: Grammar_Common.grammar) (ri: Grammar_Common.rel_info) =
  let
    val _ = validate gram ri;
    fun timed label f = Grammar_Common.timed ctxt "parser" ("bridge " ^ label) f ();
    val s = timed "setup" (fn () => setup ctxt gram (#preds ri));
    (* the intro of a unit self-loop with identity action.  Insensitive, or under
       ^=, it is `G_A w x \<Longrightarrow> G_A w x`: it closes nothing and sends the classical
       search into an infinite descent, so it is dropped.  Under any other
       relation it is `G_A j w x \<Longrightarrow> i R j \<Longrightarrow> G_A i w x` (the index is the first
       argument), the only rule closing that production's node case: kept, but
       out of the rule set (b1_node_tac) *)
    val args_of = Term.strip_comb o HOLogic.dest_Trueprop;
    fun idx_free t =
      (case args_of t of
        (h, [_, w, x]) => (h, [w, x])
      | h_args => h_args);
    fun self_prem strip th =
      let val (h, args) = strip (Thm.concl_of th) in
        exists (fn p =>
            (case strip p of
              (h', args') => h aconv h' andalso eq_list (op aconv) (args, args'))
            handle TERM _ => false)
          (Thm.prems_of th)
      end;
    val (loops, plain) =
      map (Simplifier.full_simplify ctxt) (#intros ri)
      |> filter_out (self_prem args_of)
      |> List.partition (self_prem idx_free);
    val intros = (plain, loops);
    val dec_nones =
      timed "dec_none lemmas"
        (fn () => map (Parser_Dec_Total.dec_none ctxt gram o fst) (#preds ri));
    val b1_all = concise "dec_sound (decoder agrees with the relation)"
      (fn () => timed "dec_sound" (fn () => prove_b1_all ctxt s intros dec_nones));
    val b2_all = concise "rel_dec (relation decoded by the decoder)"
      (fn () => timed "rel_dec" (fn () => prove_b2_all ctxt s dec_nones));
    fun bridge start : bridge =
      {pred_P = pred_P s start,
       dec_sound = concise "dec_sound"
         (fn () => timed "dec_sound final" (fn () => prove_dec_sound ctxt s b1_all start)),
       rel_dec = concise "rel_dec"
         (fn () => timed "rel_dec final" (fn () => prove_rel_dec ctxt s b2_all start))};
  in bridge end;

fun prove ctxt (gram: Grammar_Common.grammar) ri = prover ctxt gram ri (#start gram);

end;
