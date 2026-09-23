(* the definitions behind a grammar: the grammar constant, the decoders,
   and the mutual inductive relation family with its language theorem *)

signature GRAMMAR_DEFS =
sig
  val define_grammar:
    Grammar_Common.grammar -> local_theory ->
      (term * thm) * local_theory
  val define_const: bool -> binding * binding * term -> local_theory ->
    (term * thm) * local_theory

  type semantics =
   {gram:       term * thm,
    preds:      (string * term) list,
    decs:       (string * term) list,
    intros:     thm list,
    inducts:    thm list,
    sound_thms: thm list}

  val decoder_of: Proof.context -> Grammar_Common.grammar -> string -> term
  val define_decoders:
    Grammar_Common.grammar -> local_theory ->
      (string * term) list * local_theory

  val is_indent_insensitive: Grammar_Common.grammar -> bool
  val prove_family: Proof.context ->
    {preds: (string * term) list, insensitive: bool, induct: thm, wordT: typ,
     carrier_of: string -> typ, norm: term -> term} ->
    (string -> term -> term -> term -> term) -> (Proof.context -> tactic) -> thm list

  val gram_key: Grammar_Common.artifacts -> string
  val lookup_rel: Proof.context -> Grammar_Common.grammar ->
    Grammar_Common.rel_info option

  val define_relation:
    Grammar_Common.grammar -> term * thm -> (string * term) list ->
      local_theory -> semantics * local_theory

  val define_relation_of:
    xstring * Position.T -> local_theory ->
      semantics * local_theory
end;

structure Grammar_Defs: GRAMMAR_DEFS =
struct

open Grammar_Common;

(** shared plumbing **)

fun suffix_bind s b = Binding.map_name (fn n => n ^ s) b;

(* hide constants and facts declared inside from find commands *)
fun with_concealed f lthy =
  lthy
  |> Proof_Context.concealed
  |> f
  ||> Proof_Context.restore_naming lthy;

fun define_const code (b, def_b, rhs) lthy =
  let val ((t, (_, th)), lthy') =
    Local_Theory.define ((b, NoSyn), ((def_b, []), rhs)) lthy
  in
    ((t, th),
     if code then
       lthy' |> Code.declare_default_eqns [(th, true)]
             |> Grammar_Common.declare_def_code_global {default = true} (b, def_b) th
     else lthy')
  end;

fun simp_only ctxt extra =
  asm_full_simp_tac (put_simpset HOL_basic_ss ctxt addsimps extra);


(** grammar constant: the isg / cfg record **)

type gram_encoding =
 {rhs_elemT: typ,
  mk_sym: Grammar_Common.rsym -> term,
  mk_rhs_elem: term * Grammar_Common.ann -> term,
  mk_grammar_term: term -> term -> term};

fun gen_define_grammar (enc: gram_encoding) (g: Grammar_Common.grammar) lthy =
  let
    val {rhs_elemT, mk_sym, mk_rhs_elem, mk_grammar_term} = enc;
    val {name, start, prods, ...} = g;
    val prodT = HOLogic.mk_prodT (HOLogic.stringT, HOLogic.listT rhs_elemT);
    val rhs_terms =
      prods |> map (fn {rhs, ...}: Grammar_Common.prod =>
        HOLogic.mk_list rhs_elemT (map (fn (s, a) => mk_rhs_elem (mk_sym s, a)) rhs));
    val prods_term =
      HOLogic.mk_list prodT
        (map2 (fn ({lhs, ...}: Grammar_Common.prod) => fn rhs_t =>
            HOLogic.mk_prod (HOLogic.mk_string lhs, rhs_t))
          prods rhs_terms);
    val rhs = mk_grammar_term prods_term (HOLogic.mk_string start);
  in define_const true (name, Thm.def_binding name, rhs) lthy end;


fun isg_encoding (gram: Grammar_Common.grammar): gram_encoding =
  let
    val {tokT, terminals, ...} = gram;

    val symbolT = Type (\<^type_name>\<open>sym\<close>, [HOLogic.stringT, tokT]);
    val isgT = Type (\<^type_name>\<open>is_cfg_ext\<close>, [HOLogic.stringT, tokT, \<^typ>\<open>unit\<close>]);
    val rhs_elemT = HOLogic.mk_prodT (symbolT, \<^typ>\<open>irel\<close>);
    val makeT =
      HOLogic.listT (HOLogic.mk_prodT (HOLogic.stringT, HOLogic.listT rhs_elemT))
      --> HOLogic.stringT --> \<^typ>\<open>nat\<close> --> isgT;

    val Nt_c = Const (\<^const_name>\<open>Nt\<close>, HOLogic.stringT --> symbolT);
    val Tm_c = Const (\<^const_name>\<open>Tm\<close>, tokT --> symbolT);
    val make_c = Const (\<^const_name>\<open>is_cfg.make\<close>, makeT);

    fun mk_sym (Grammar_Common.RN n) = Nt_c $ HOLogic.mk_string n
      | mk_sym (Grammar_Common.RC i) = Tm_c $ Vector.sub (terminals, i)
      | mk_sym (Grammar_Common.RT i) = Tm_c $ Vector.sub (terminals, i);
  in
    {rhs_elemT = rhs_elemT,
     mk_sym = mk_sym,
     mk_rhs_elem = fn (sym, ann) => HOLogic.mk_prod (sym, irel_term ann),
     mk_grammar_term = fn ps => fn s => make_c $ ps $ s $ \<^term>\<open>0 :: nat\<close>}
  end;

fun define_grammar (gram: Grammar_Common.grammar) =
  gen_define_grammar (isg_encoding gram) gram;


(** relation: mutual inductive family, one predicate per nonterminal and one
    intro per production; indentation-insensitive grammars (every annotation
    \<^const>\<open>Any\<close>) drop the indentation argument,
    \<open>G_A :: tword \<Rightarrow> \<tau>\<^sub>A \<Rightarrow> bool\<close> **)

fun is_indent_insensitive (gram: Grammar_Common.grammar) =
  forall (fn {rhs, ...}: Grammar_Common.prod => forall (fn (_, a) => a = Any) rhs)
    (#prods gram);

fun ch_span_typ chT = Type (\<^type_name>\<open>Token.span_ext\<close>, [chT, \<^typ>\<open>unit\<close>]);

(* \<open>\<lparr>tok = t, span = sp, \<dots> = m\<rparr>\<close>: the relation quantifies over the record
   extension \<open>m\<close> of every token, so it is stated for any client extension *)
fun mk_token_ext tokT chT moreT =
  let val tokenT = Type (\<^type_name>\<open>Token.token_ext\<close>, [tokT, chT, moreT]) in
    Const (\<^const_name>\<open>Token.token.token_ext\<close>,
      tokT --> ch_span_typ chT --> moreT --> tokenT)
  end;

fun col_rel_term _ Grammar_Common.Any = NONE
  | col_rel_term (segK, seg1) rel =
  let
    val nat_less = Const (\<^const_name>\<open>Orderings.less\<close>, \<^typ>\<open>nat\<close> --> \<^typ>\<open>nat\<close> --> HOLogic.boolT);
    val nat_leq = Const (\<^const_name>\<open>Orderings.less_eq\<close>, \<^typ>\<open>nat\<close> --> \<^typ>\<open>nat\<close> --> HOLogic.boolT);
  in SOME
    (case rel of
      Grammar_Common.Eq => HOLogic.mk_eq (segK, seg1)
    | Grammar_Common.Ge => nat_leq $ seg1 $ segK
    | Grammar_Common.Gt => nat_less $ seg1 $ segK
    | Grammar_Common.Any => raise Match)
  end;

(* the family's induction rule on the mutual statement

     (pred\<^sub>1 i w x \<longrightarrow> body\<^sub>1 i w x) \<and> \<dots> \<and> (pred\<^sub>n i w x \<longrightarrow> body\<^sub>n i w x)

   split into one implication per nonterminal; insensitive grammars fix i at 0 *)
fun prove_family ctxt {preds, insensitive, induct, wordT, carrier_of, norm} body cases_tac =
  let
    val n = length preds;
    val zero = \<^term>\<open>0 :: nat\<close>;
    val fresh =
      Variable.variant_fixes
        (maps (fn k =>
            (if insensitive then [] else ["ii" ^ string_of_int k]) @
            ["ww" ^ string_of_int k, "xx" ^ string_of_int k]) (0 upto n - 1)) ctxt
      |> fst;
    fun chunks [] = []
      | chunks xs =
          let val (a, b) = chop (if insensitive then 2 else 3) xs in a :: chunks b end;
    fun conj_of ((A, pred), names) =
      let
        val (i_t, w_n, x_n) =
          if insensitive then (zero, nth names 0, nth names 1)
          else (Free (nth names 0, HOLogic.natT), nth names 1, nth names 2);
        val w = Free (w_n, wordT);
        val x = Free (x_n, carrier_of A);
        val pred_app = if insensitive then pred $ w $ x else pred $ i_t $ w $ x;
      in HOLogic.mk_imp (pred_app, body A i_t w x) end;
    val prop =
      norm (HOLogic.mk_Trueprop (foldr1 HOLogic.mk_conj (map conj_of (preds ~~ chunks fresh))));
    fun P_of (A, _) =
      let
        val i = Free ("__i", HOLogic.natT);
        val w = Free ("__w", wordT);
        val x = Free ("__x", carrier_of A);
        val lam = Term.lambda w (Term.lambda x (body A (if insensitive then zero else i) w x));
      in norm (if insensitive then lam else Term.lambda i lam) end;
    val induct' =
      if n = 1 then induct
      else
        let
          val p_vars =
            Term.add_vars (Thm.prop_of induct) []
            |> filter (fn ((nm, _), _) =>
                 String.isPrefix "P" nm andalso Int.fromString (unprefix "P" nm) <> NONE)
            |> sort (int_ord o apply2 (fn ((nm, _), _) => the (Int.fromString (unprefix "P" nm))));
          val insts = map2 (fn (v, _) => fn pr => (v, Thm.cterm_of ctxt (P_of pr))) p_vars preds;
        in Drule.infer_instantiate ctxt insts induct end;
    fun tac {context, ...} =
      (if n = 1 then
         HEADGOAL (resolve_tac context @{thms impI}) THEN HEADGOAL (eresolve_tac context [induct])
       else HEADGOAL (resolve_tac context [induct']))
      THEN cases_tac context;
    val th = Goal.prove ctxt fresh [] prop tac;
    fun conjunct k =
      let val rest = funpow k (fn t => @{thm conjunct2} OF [t]) th
      in if k = n - 1 then rest else @{thm conjunct1} OF [rest] end;
  in map (fn k => conjunct k RS @{thm mp}) (0 upto n - 1) end;

datatype iv_child =
    NTc of string
  | ClassTm of term
  | LitTm of term;

fun classify_of (gram: Grammar_Common.grammar) =
  let val {terminals, ...} = gram in
    fn Grammar_Common.RN n => NTc n
     | Grammar_Common.RC i => ClassTm (Vector.sub (terminals, i))
     | Grammar_Common.RT i => LitTm (Vector.sub (terminals, i))
  end;

(** decoder: per-NT mutual \<^text>\<open>fun\<close> reducing an ast to the action value. **)

fun mk_case_ast_c tokenT astT astListT R =
  Const (\<^const_name>\<open>case_ast\<close>,
    (tokenT --> R) --> (HOLogic.stringT --> astListT --> R) --> astT --> R);

fun mk_case_list_c T R =
  Const (\<^const_name>\<open>List.list.case_list\<close>,
    R --> (T --> HOLogic.listT T --> R) --> HOLogic.listT T --> R);

fun mk_case_option_c T R =
  Const (\<^const_name>\<open>case_option\<close>,
    R --> (T --> R) --> mk_optionT T --> R);

fun mk_if_c R =
  Const (\<^const_name>\<open>HOL.If\<close>, HOLogic.boolT --> R --> R --> R);

fun mk_bind_c T R =
  Const (\<^const_name>\<open>Option.bind\<close>,
    mk_optionT T --> (T --> mk_optionT R) --> mk_optionT R);

(* unconstrained type variables of an action (unresolved or ascribed) are unit *)
val ground_typ =
  Term.map_atyps (fn TVar _ => \<^typ>\<open>unit\<close> | TFree _ => \<^typ>\<open>unit\<close> | T => T);
val ground_tvars = Term.map_types ground_typ;

fun body_of_prod_dec (gram: Grammar_Common.grammar)
    (carrier_of: string -> typ) (dec_of: string -> term)
    (p: Grammar_Common.prod) (fresh_names: string list) (cs: term list) =
  let
    val {tokenT, astT, ...} = Grammar_Common.get_desc gram;
    val astListT = HOLogic.listT astT;
    val {tokT, ...} = gram;
    val outT = carrier_of (#lhs p);
    val outOptT = mk_optionT outT;
    val classify = classify_of gram;
    val slots = cs ~~ map (fn (s, _) => classify s) (#rhs p);
    val Tok_tok_c = Const (\<^const_name>\<open>Token.tok\<close>, tokenT --> tokT);
    val none = mk_None outT;

    fun leaf_arm x_v inner =
      mk_case_ast_c tokenT astT astListT outOptT
        $ Term.lambda x_v inner
        $ Abs ("nn", HOLogic.stringT, Abs ("xxs", astListT, none));

    fun build [] _ args_rev =
          mk_Some outT $ Term.betapplys (ground_tvars (#action p), rev args_rev)
      | build ((c, NTc B) :: rest) (v_nm :: nms) args_rev =
          let val cT = carrier_of B;
              val v_v = Free (v_nm, cT);
              val cont = build rest nms (v_v :: args_rev);
          in mk_bind_c cT outT $ (dec_of B $ c) $ Term.lambda v_v cont end
      | build ((c, ClassTm tok_term) :: rest) (x_nm :: nms) args_rev =
          let
            val x_v = Free (x_nm, tokenT);
            val cont = build rest nms (x_v :: args_rev);
            val guarded =
              mk_if_c outOptT $ HOLogic.mk_eq (Tok_tok_c $ x_v, tok_term) $ cont $ none;
          in leaf_arm x_v guarded $ c end
      | build ((c, LitTm tok_term) :: rest) (x_nm :: nms) args_rev =
          let
            val x_v = Free (x_nm, tokenT);
            val cont = build rest nms args_rev;
            val guarded =
              mk_if_c outOptT $ HOLogic.mk_eq (Tok_tok_c $ x_v, tok_term) $ cont $ none;
          in leaf_arm x_v guarded $ c end
      | build _ _ _ = raise Fail "body_of_prod_dec: name list exhausted";
  in build slots fresh_names [] end;

fun chain_prods_dec outT bodies =
  let val outOptT = mk_optionT outT in
    case bodies of
      [] => mk_None outT
    | [b] => b
    | b :: rest =>
        mk_case_option_c outT outOptT
          $ chain_prods_dec outT rest
          $ Abs ("y", outT, mk_Some outT $ Bound 0)
          $ b
  end;

fun length_dispatch_dec astT outT ks body_at_length xs_var =
  let
    val astListT = HOLogic.listT astT;
    val outOptT = mk_optionT outT;
    val max_k = if null ks then 0
      else fold (fn a => fn b => if a > b then a else b) ks 0;

    fun go d acc_children tl_var =
      let
        val nil_arm =
          if member (op =) ks d then body_at_length d (rev acc_children)
          else mk_None outT;
        val cons_arm =
          if d >= max_k then
            Abs ("_", astT, Abs ("_", astListT, mk_None outT))
          else
            let
              val c_v = Free ("c__" ^ string_of_int (d + 1), astT);
              val tl_v = Free ("tl__" ^ string_of_int (d + 1), astListT);
              val body_deeper = go (d + 1) (c_v :: acc_children) tl_v;
            in Term.lambda c_v (Term.lambda tl_v body_deeper) end;
      in
        mk_case_list_c astT outOptT
          $ nil_arm $ cons_arm $ tl_var
      end;
  in go 0 [] xs_var end;

(* the decoder of A on Node n xs, for the decoders dec_of of the nonterminals *)
fun node_body_dec (gram: Grammar_Common.grammar) lthy carrier_of dec_of A n_v xs_v =
  let
    val {astT, ...} = Grammar_Common.get_desc gram;
    val outT = carrier_of A;
    val outOptT = mk_optionT outT;

    val prods_A = filter (fn p => #lhs p = A) (#prods gram);
    val by_len : (int * Grammar_Common.prod list) list =
      fold (fn p =>
          AList.map_default (op =) (length (#rhs p), []) (fn ps => ps @ [p]))
        prods_A [];
    val ks = map fst by_len;

    val name_lit = HOLogic.mk_string A;

    fun body_at_length k cs =
      let
        val prods_k = the (AList.lookup (op =) by_len k);
        val fresh_seeds =
          maps (fn p => map (fn _ => "dz_" ^ A) (#rhs p)) prods_k;
        val (all_names, _) = Variable.variant_fixes fresh_seeds lthy;
        val bodies =
          let
            fun go [] _ = []
              | go (p :: ps) names =
                  let val n = length (#rhs p);
                      val (this, rest) = chop n names;
                      val body =
                        body_of_prod_dec gram carrier_of dec_of p this cs;
                  in body :: go ps rest end;
          in go prods_k all_names end;
      in chain_prods_dec outT bodies end;

  in
    mk_if_c outOptT
      $ HOLogic.mk_eq (n_v, name_lit)
      $ length_dispatch_dec astT outT ks body_at_length xs_v
      $ mk_None outT
  end;

(* the equations of the decoder of A, one for Node and one for Leaf *)
fun eqns_for_nt_dec (gram: Grammar_Common.grammar) lthy carrier_of dec_of A =
  let
    val {tokenT, astT, ...} = Grammar_Common.get_desc gram;
    val astListT = HOLogic.listT astT;
    val dec_free = dec_of A;
    val outT = carrier_of A;
    val n_v = Free ("dnv_" ^ A, HOLogic.stringT);
    val xs_v = Free ("dxs_" ^ A, astListT);
    val node_body = node_body_dec gram lthy carrier_of dec_of A n_v xs_v;

    val Leaf_c = Const (\<^const_name>\<open>Leaf\<close>, tokenT --> astT);
    val Node_c = Const (\<^const_name>\<open>Node\<close>, HOLogic.stringT --> astListT --> astT);

    val lhs_node = dec_free $ (Node_c $ n_v $ xs_v);
    val eq_node = HOLogic.mk_Trueprop (HOLogic.mk_eq (lhs_node, node_body));

    val wildcard = Free ("dwild_" ^ A, tokenT);
    val lhs_leaf = dec_free $ (Leaf_c $ wildcard);
    val eq_leaf = HOLogic.mk_Trueprop (HOLogic.mk_eq (lhs_leaf, mk_None outT));
  in [eq_node, eq_leaf] end;

(* a balanced sum type over the types Ts, with an injection and a projection
   for each of them *)
fun mk_val_sum [U] = (U, [(U, (Abs ("x", U, Bound 0), mk_Some U))])
  | mk_val_sum Ts =
      let
        val (ls, rs) = chop (length Ts div 2) Ts;
        val (LTy, linjs) = mk_val_sum ls;
        val (RTy, rinjs) = mk_val_sum rs;
        val VT = Type (\<^type_name>\<open>sum\<close>, [LTy, RTy]);
        fun lift left (U, (inj, proj)) =
          let
            val optT = mk_optionT U;
            val none = Abs ("v", if left then RTy else LTy, mk_None U);
            val inj_c =
              if left then Const (\<^const_name>\<open>Inl\<close>, LTy --> VT)
              else Const (\<^const_name>\<open>Inr\<close>, RTy --> VT);
            val case_c =
              Const (\<^const_name>\<open>case_sum\<close>,
                (LTy --> optT) --> (RTy --> optT) --> VT --> optT);
            val proj' =
              if left then case_c $ proj $ none else case_c $ none $ proj;
          in
            (U, (Envir.beta_eta_contract (Abs ("x", U, inj_c $ (inj $ Bound 0))),
              proj'))
          end;
      in
        (VT,
          map (lift true) linjs @ map (lift false) rinjs)
      end;

(* The decoders are defined through a single functional G__disp on a selector
   (the index of the nonterminal) and a tree, with values in a sum of the
   carriers, closed by ast_rec: a mutual function over all nonterminals is much
   slower to define. The decoder of A is G__disp's fixpoint at the index of A
   followed by the projection to the carrier of A; its Node and Leaf equations
   are derived. *)
fun define_decoders (gram: Grammar_Common.grammar) lthy =
  let
    val {tokenT, astT, ...} = Grammar_Common.get_desc gram;
    val astListT = HOLogic.listT astT;
    val gram_b = #name gram;
    val nts = Grammar_Common.nonterms_list gram;
    val nnames = map fst nts;
    val carriers = map (#carrier o snd) nts;
    val carrier_of = Grammar_Common.carrier_of gram;
    fun index_of A = HOLogic.mk_nat (find_index (curry (op =) A) nnames);
    fun timed label f x =
      Grammar_Common.timed lthy (Binding.name_of (#name gram)) ("decoders: " ^ label) f x;

    val (valT, injs) = mk_val_sum (distinct (op =) carriers);
    val valOptT = mk_optionT valT;
    fun inj_of A = fst (the (AList.lookup (op =) injs (carrier_of A)));
    fun proj_of A = snd (the (AList.lookup (op =) injs (carrier_of A)));
    fun mk_map_option_c U =
      Const (\<^const_name>\<open>map_option\<close>, (U --> valT) --> mk_optionT U --> valOptT);
    fun dec_via decode A =
      let val c = Free ("c", astT) in
        Term.lambda c
          (mk_bind_c valT (carrier_of A) $ (decode $ index_of A $ c) $ proj_of A)
      end;

    (* G__disp, G__dec_A: distinct from every relation name G_<nonterminal>,
       as a nonterminal cannot start with an underscore *)
    val recT = HOLogic.natT --> astT --> valOptT;
    val dispT = recT --> HOLogic.natT --> HOLogic.stringT --> astListT --> valOptT;
    val f_v = Free ("dfun", recT);
    val sel_v = Free ("dsel", HOLogic.natT);
    val n_v = Free ("dnv", HOLogic.stringT);
    val xs_v = Free ("dxs", astListT);
    val dispatch =
      fold_rev (fn A => fn rest =>
          mk_if_c valOptT $ HOLogic.mk_eq (sel_v, index_of A)
            $ (mk_map_option_c (carrier_of A) $ inj_of A
                $ node_body_dec gram lthy carrier_of (dec_via f_v) A n_v xs_v)
            $ rest)
        nnames (mk_None valT)
      |> Envir.beta_norm;
    val disp_b = suffix_bind "__disp" gram_b;
    val ((disp, disp_def), lthy1) =
      define_const false
        (disp_b, Thm.def_binding disp_b, fold_rev Term.lambda [f_v, sel_v, n_v, xs_v] dispatch)
        lthy;
    val ast_rec_c =
      Const (\<^const_name>\<open>ast_rec\<close>, dispT --> valOptT --> recT);
    val decode = ast_rec_c $ disp $ mk_None valT;

    val dec_bindings = map (fn nm => suffix_bind ("__dec_" ^ nm) gram_b) nnames;
    val (dec_defs, lthy2) =
      fold_map (fn (b, A) =>
          define_const false (b, Thm.def_binding b, dec_via decode A))
        (dec_bindings ~~ nnames) lthy1;
    val decs = map fst dec_defs;
    val dec_def_eqs = map snd dec_defs;
    fun dec_of A = nth decs (find_index (curry (op =) A) nnames);

    (* bind (map_option inj x) proj = x, for each carrier *)
    fun bind_map_lemma (U, (inj, proj)) =
      let
        val x = Free ("x", mk_optionT U);
        val goal =
          HOLogic.mk_Trueprop (HOLogic.mk_eq
            (mk_bind_c valT U $ (mk_map_option_c U $ inj $ x) $ proj, x));
      in
        (U, Goal.prove lthy2 ["x"] [] goal (fn {context = ctxt, ...} =>
          HEADGOAL (Induct_Tacs.case_tac ctxt "x" [] NONE) THEN
          ALLGOALS (asm_full_simp_tac ctxt)) |> mk_meta_eq)
      end;
    val bind_maps = map bind_map_lemma injs;

    (* decide the selector conditions of the dispatch one by one *)
    fun dispatch_conv ctxt ct =
      (Conv.fun_conv (Conv.fun_conv (Conv.arg_conv (Simplifier.rewrite ctxt))) then_conv
        (Conv.rewr_conv @{thm if_True[THEN eq_reflection]} else_conv
          (Conv.rewr_conv @{thm if_False[THEN eq_reflection]} then_conv
            dispatch_conv ctxt))) ct;
    fun lhs_conv ctxt A =
      (Conv.arg1_conv
        (Conv.rewr_conv @{thm ast_rec.simps(1)[THEN eq_reflection]} then_conv
          funpow 4 Conv.fun_conv (Conv.rewr_conv disp_def) then_conv
          Thm.beta_conversion true then_conv
          dispatch_conv ctxt) then_conv
        Conv.rewr_conv (the (AList.lookup (op =) bind_maps (carrier_of A))))
      else_conv
      (Conv.arg1_conv (Conv.rewr_conv @{thm ast_rec.simps(2)[THEN eq_reflection]}) then_conv
        Conv.rewr_conv @{thm Option.bind_lzero[THEN eq_reflection]});
    (* the recursive calls of the functional are on children: decided by the
       case distinctions on the children list *)
    fun children_ctxt ctxt =
      put_simpset HOL_basic_ss ctxt
        addsimps @{thms list.set insert_iff simp_thms if_True}
      |> Simplifier.add_cong @{thm list.case_cong};
    fun prove_eqn A goal =
      let
        val frees =
          Term.add_free_names goal [] |> filter_out (Variable.is_fixed lthy2);
      in
        Goal.prove lthy2 frees [] goal (fn {context = ctxt, ...} =>
          rewrite_goal_tac ctxt dec_def_eqs 1 THEN
          CONVERSION (HOLogic.Trueprop_conv (Conv.arg1_conv (lhs_conv ctxt A))) 1 THEN
          asm_full_simp_tac (children_ctxt ctxt) 1)
      end;
    val eqns = timed "derive equations" (fn () =>
      map (fn A => map (prove_eqn A) (eqns_for_nt_dec gram lthy2 carrier_of dec_of A))
        nnames) ();
    val (_, lthy3) =
      fold_map (fn (b, ths) =>
          Local_Theory.note
            ((Binding.qualify_name true b "simps",
              [Attrib.internal \<^here> (K Simplifier.simp_add)]), ths))
        (dec_bindings ~~ eqns) lthy2;
    (* the equations are the code equations, also of interpretations; inside a
       locale with assumptions they stay conditional and are not declared
       globally *)
    val lthy3 = lthy3
      |> Code.declare_default_eqns (map (rpair true) (flat eqns))
      |> Grammar_Common.declare_code_global {default = true} (flat eqns);
  in ((nnames ~~ decs), lthy3) end;

(* the decoder of nonterminal A of grammar G, from the registered artifacts *)
fun decoder_of _ (gram: Grammar_Common.grammar) A =
  let
    fun unknown () =
      error ("decoder_of: unknown nonterminal " ^ quote A ^ " of grammar " ^
        quote (Binding.name_of (#name gram)) ^ " (nonterminals: " ^
        commas_quote (map fst (Grammar_Common.nonterms_list gram)) ^ ")");
    val _ = Symtab.defined (#nonterms gram) A orelse unknown ();
  in
    (case #artifacts gram of
      SOME arts =>
        (case AList.lookup (op =) (#decs arts) A of
          SOME t => t
        | NONE => unknown ())
    | NONE =>
        error ("decoder_of: grammar " ^ quote (Binding.name_of (#name gram)) ^
          " has no registered artifacts"))
  end;

(** relation families of registered grammars: created with the grammar in its
    artifacts, added later (define_relation_of) in this table, keyed by the
    grammar constant **)

fun gram_key (arts: Grammar_Common.artifacts) =
  (case Term.head_of (#gram_t arts) of
    Const (c, _) => c
  | _ => raise Fail "gram_key: grammar term without head constant");

structure Rel_Data = Generic_Data
(
  type T = Grammar_Common.rel_info Symtab.table;
  val empty = Symtab.empty;
  fun merge data = Symtab.merge (K true) data;
);

fun lookup_rel ctxt (gram: Grammar_Common.grammar) =
  (case #artifacts gram of
    NONE => NONE
  | SOME arts =>
      (case #rel arts of
        SOME ri => SOME ri
      | NONE => Symtab.lookup (Rel_Data.get (Context.Proof ctxt)) (gram_key arts)));

fun store_rel (gram: Grammar_Common.grammar) (ri: Grammar_Common.rel_info) =
  let val key = gram_key (Grammar_Common.artifacts_of gram) in
    Local_Theory.declaration {syntax = false, pervasive = false, pos = Position.none}
      (fn phi =>
        Rel_Data.map (Symtab.update (key, Grammar_Common.morph_rel_info phi ri)))
  end;

fun gen_define_relation gram_t gram_th (gram: Grammar_Common.grammar) lthy =
  let
    val {chT, moreT, wordT, tokenT, isgT, ...} = Grammar_Common.get_desc gram;
    val {name = gram_b, prods, tokT, ...} = gram;
    val nts = Grammar_Common.nonterms_list gram;
    val nnames = map fst nts;
    val carriers = map (#carrier o snd) nts;
    val carrier_of = Grammar_Common.carrier_of gram;

    val ch_spanT = ch_span_typ chT;
    val token_ext_c = mk_token_ext tokT chT moreT;
    val app_c = Const (\<^const_name>\<open>List.append\<close>, wordT --> wordT --> wordT);
    val col_of_c = Const (\<^const_name>\<open>col_of\<close>, wordT --> HOLogic.natT);
    val classify = classify_of gram;
    val insensitive = is_indent_insensitive gram;

    val pred_bindings = map (fn nm => suffix_bind ("_" ^ nm) gram_b) nnames;
    (* the flat relation names can collide across grammars (G with A_B and
       G_A with B both give G_A_B) *)
    val _ =
      pred_bindings |> List.app (fn b =>
        if Sign.declared_const (Proof_Context.theory_of lthy) (Local_Theory.full_name lthy b)
        then error ("grammar " ^ quote (Binding.name_of gram_b) ^ ": the relation constant " ^
          quote (Binding.name_of b) ^ " already exists (another grammar / nonterminal \
          \pair produces the same name); rename the grammar or the nonterminal" ^
          Position.here (Binding.pos_of gram_b))
        else ());
    val pred_types =
      map (fn cT =>
             (if insensitive then wordT --> cT --> HOLogic.boolT
              else HOLogic.natT --> wordT --> cT --> HOLogic.boolT))
        carriers;
    val pred_specs = map2 (fn b => fn T => ((b, T), NoSyn)) pred_bindings pred_types;
    val pred_frees =
      map2 (fn b => fn T => Free (Binding.name_of b, T)) pred_bindings pred_types;
    fun pred_of A = nth pred_frees (find_index (curry (op =) A) nnames);

    fun mk_token tok sp m = token_ext_c $ tok $ sp $ m;
    fun singleton_word tok sp m = HOLogic.mk_list tokenT [mk_token tok sp m];

    fun concat_words [] = HOLogic.mk_list tokenT []
      | concat_words [w] = w
      | concat_words (w :: ws) = app_c $ w $ concat_words ws;

    fun intro_meta ({rhs, ...}: Grammar_Common.prod) =
      let
        val classified = map (fn (s, a) => (classify s, a)) rhs;
        val fresh_names =
          (if insensitive then [] else ["i"]) @
            maps (fn (NTc _, _) =>
                    (if insensitive then ["v", "w"] else ["v", "w", "j"])
                   | (ClassTm _, _) => ["sp", "m"]
                   | (LitTm _, _) => ["sp", "m"]) classified;
        val (names, _) = Variable.variant_fixes fresh_names lthy;
        val (i_name, child_names) =
          if insensitive then ("", names) else (hd names, tl names);
        fun distribute [] [] = []
          | distribute ((NTc A, r) :: cs) (v :: w :: rest) =
              if insensitive then
                (NTc A, r, [v, w]) :: distribute cs rest
              else
                (case rest of
                  j :: ns => (NTc A, r, [v, w, j]) :: distribute cs ns
                | _ => raise Fail "intro_meta: distribute NT")
          | distribute ((ClassTm t, r) :: cs) (sp :: m :: ns) =
              (ClassTm t, r, [sp, m]) :: distribute cs ns
          | distribute ((LitTm t, r) :: cs) (sp :: m :: ns) =
              (LitTm t, r, [sp, m]) :: distribute cs ns
          | distribute _ _ = raise Fail "intro_meta: distribute";
      in (i_name, distribute classified child_names) end;

    fun intro_prop (prod as {lhs, action, ...}: Grammar_Common.prod) =
      let
        val (i_name, assigned) = intro_meta prod;
        val i_term_opt =
          if insensitive then NONE
          else SOME (Free (i_name, \<^typ>\<open>nat\<close>));

        fun seg (NTc _, _, v_w_j) = Free (nth v_w_j 1, wordT)
          | seg (ClassTm tok, _, [sp, m]) =
              singleton_word tok (Free (sp, ch_spanT)) (Free (m, moreT))
          | seg (LitTm tok, _, [sp, m]) =
              singleton_word tok (Free (sp, ch_spanT)) (Free (m, moreT))
          | seg _ = raise Fail "intro_prop: seg";
        val segments = map seg assigned;
        val full_word = concat_words segments;

        fun arg_of (NTc A, _, v_w_j) =
              SOME (Free (nth v_w_j 0, carrier_of A))
          | arg_of (ClassTm tok, _, [sp, m]) =
              SOME (mk_token tok (Free (sp, ch_spanT)) (Free (m, moreT)))
          | arg_of (LitTm _, _, _) = NONE
          | arg_of _ = raise Fail "intro_prop: arg_of";
        val args = map_filter arg_of assigned;
        val value_term = Term.betapplys (action, args);

        val nt_prems =
          if insensitive then
            map_filter (fn (NTc A, _, [v, w]) =>
                          SOME (pred_of A $ Free (w, wordT) $ Free (v, carrier_of A))
                         | _ => NONE) assigned
          else
            map_filter (fn (NTc A, _, [v, w, j]) =>
                          SOME (pred_of A $ Free (j, \<^typ>\<open>nat\<close>)
                                          $ Free (w, wordT)
                                          $ Free (v, carrier_of A))
                        | _ => NONE) assigned;
        val col_prems =
          if insensitive then []
          else
            (case i_term_opt of NONE => [] | SOME i_term =>
              map_filter (fn (elem, segK) =>
                  (case elem of
                    (NTc _, ann, [_, _, j]) =>
                      col_rel_term (Free (j, \<^typ>\<open>nat\<close>), i_term) ann
                  | (ClassTm _, ann, _) =>
                      col_rel_term (col_of_c $ segK, i_term) ann
                  | (LitTm _, ann, _) =>
                      col_rel_term (col_of_c $ segK, i_term) ann
                  | _ => NONE))
                (assigned ~~ segments));
        val concl =
          case i_term_opt of
            NONE => pred_of lhs $ full_word $ value_term
          | SOME i_term => pred_of lhs $ i_term $ full_word $ value_term;
      in
        ground_tvars
          (Logic.list_implies
            (map HOLogic.mk_Trueprop (nt_prems @ col_prems),
             HOLogic.mk_Trueprop concl))
      end;

    fun timed label f x = Grammar_Common.timed lthy (Binding.name_of gram_b) label f x;

    val intro_props =
      timed "build intro_props" (fn () =>
        map_index (fn (p, prod) =>
          let val nm = "intro_" ^ #lhs prod ^ "_" ^ string_of_int p in
            ((Binding.name nm, []), intro_prop prod)
          end) prods) ();

    val add_flags: Inductive.flags =
      {quiet_mode = true, verbose = false, alt_name = Binding.empty,
       coind = false, no_elim = false, no_ind = false, skip_mono = false};

    val (ind_result, lthy) =
      timed "Inductive.add_inductive"
        (with_concealed (Inductive.add_inductive add_flags pred_specs [] intro_props []))
        lthy;

    val cleanup =
      Simplifier.full_simplify
        (put_simpset HOL_basic_ss lthy
         |> fold Simplifier.add_simp
            (@{thms append.simps col_of_Nil col_of_Cons} @ @{thms token.simps}));

    val cleaned_intros =
      timed "cleanup intros" (map cleanup) (#intrs ind_result);

    val cleaned_inducts =
      timed "cleanup inducts" (map cleanup) (#inducts ind_result);

    (** cornerstone lemmas: relate the mutual predicate family to wf_ptree **)
    val symT = Type (\<^type_name>\<open>sym\<close>, [HOLogic.stringT, tokT]);
    val ptreeT = Type (\<^type_name>\<open>ptree\<close>, [moreT, chT, HOLogic.stringT, tokT]);
    val prootT = HOLogic.mk_prodT (symT, HOLogic.natT);
    val wf_ptree_c = Const (\<^const_name>\<open>wf_ptree\<close>, isgT --> ptreeT --> HOLogic.boolT);
    val proot_c = Const (\<^const_name>\<open>proot\<close>, ptreeT --> prootT);
    val pyield_c = Const (\<^const_name>\<open>pyield\<close>, ptreeT --> wordT);
    val Nt_c = Const (\<^const_name>\<open>Nt\<close>, HOLogic.stringT --> symT);

    (* \<exists>pt. wf_ptree G pt \<and> proot pt = (Nt A, i) \<and> pyield pt = w *)
    fun sound_body_of A i_t w_t =
      HOLogic.mk_exists ("pt", ptreeT,
        HOLogic.mk_conj (wf_ptree_c $ gram_t $ Bound 0,
          HOLogic.mk_conj
            (HOLogic.mk_eq (proot_c $ Bound 0,
                            HOLogic.mk_prod (Nt_c $ HOLogic.mk_string A, i_t)),
             HOLogic.mk_eq (pyield_c $ Bound 0, w_t))));

    (* sound direction. prove the mutual conjunction
      \<open>(pred\<^sub>1 i w x \<longrightarrow> body\<^sub>1 i w) \<and> \<dots> \<and> (pred\<^sub>n i w x \<longrightarrow> body\<^sub>n i w)\<close> *)
    val ptreeListT = HOLogic.listT ptreeT;
    val Tm_c = Const (\<^const_name>\<open>Tm\<close>, tokT --> symT);
    val PNode_c = Const (\<^const_name>\<open>PNode\<close>,
      HOLogic.stringT --> HOLogic.natT --> ptreeListT --> ptreeT);
    val PLeaf_c = Const (\<^const_name>\<open>PLeaf\<close>, tokenT --> ptreeT);
    val sym_annT = HOLogic.mk_prodT (symT, \<^typ>\<open>irel\<close>);

    fun rhs_hol_of assigned =
      HOLogic.mk_list sym_annT
        (map (fn (kind, ann, _) =>
            let val sym =
                  (case kind of
                    NTc A => Nt_c $ HOLogic.mk_string A
                  | ClassTm t => Tm_c $ t
                  | LitTm t => Tm_c $ t)
            in HOLogic.mk_prod (sym, irel_term ann) end) assigned);

    val sound_simps =
      @{thms proot.simps pyield.simps list.map(1) list.map(2)
             list.set(1) list.set(2) list.inject list.distinct
             concat.simps append.simps append_Nil2 append_assoc
             col_of_Nil col_of_Cons
             list_all2_Nil list_all2_Cons irel_sat.simps
             wf_leaf is_cfg.make_def is_cfg.select_convs token.select_convs
             HOL.simp_thms fst_conv snd_conv insert_iff empty_iff
             prod.inject sym.inject sym.distinct char.inject};

    fun sound_case_tac ctxt (prod: Grammar_Common.prod, (i_name, assigned)) =
      let
        val nt_count =
          length (filter (fn (NTc _, _, _) => true | _ => false) assigned);
        val rhs_hol = rhs_hol_of assigned;

        val elim_step =
          REPEAT_DETERM_N nt_count (HEADGOAL (eresolve_tac ctxt [@{thm exE}])) THEN
          HEADGOAL (REPEAT_DETERM o eresolve_tac ctxt [@{thm conjE}]);

        val focus = Subgoal.FOCUS_PARAMS (fn {params, context, ...} =>
          let
            val name_map = map (apsnd Thm.term_of) params;
            fun get n =
              (case AList.lookup (op =) name_map n of
                SOME t => t
              | NONE => raise Fail ("sound_case: missing param " ^ n));
            val n_params = length name_map;
            val pt_terms =
              List.drop (name_map, n_params - nt_count) |> map snd;
            val i_t = if insensitive then \<^term>\<open>0 :: nat\<close> else get i_name;
            fun mk_children [] _ = []
              | mk_children ((NTc _, _, _) :: rest) (pt :: pts_rest) =
                  pt :: mk_children rest pts_rest
              | mk_children ((ClassTm t, _, [sp, m]) :: rest) pts_rest =
                  (PLeaf_c $ mk_token t (get sp) (get m)) :: mk_children rest pts_rest
              | mk_children ((LitTm t, _, [sp, m]) :: rest) pts_rest =
                  (PLeaf_c $ mk_token t (get sp) (get m)) :: mk_children rest pts_rest
              | mk_children _ _ = raise Fail "sound_case: mk_children";
            val children = mk_children assigned pt_terms;
            val pts_hol = HOLogic.mk_list ptreeT children;
            val witness =
              PNode_c $ HOLogic.mk_string (#lhs prod) $ i_t $ pts_hol;
            val witness_ct = Thm.cterm_of context witness;
            val rhs_ct = Thm.cterm_of context rhs_hol;
            val pts_ct = Thm.cterm_of context pts_hol;
            val exI_inst =
              infer_instantiate' context [NONE, SOME witness_ct] @{thm exI};
            val wf_node_inst =
              Drule.infer_instantiate context
                [((("rhs", 0)), rhs_ct), ((("pts", 0)), pts_ct)] @{thm wf_node};
          in
            HEADGOAL (resolve_tac context [exI_inst])
            THEN HEADGOAL (resolve_tac context [@{thm conjI}])
            THEN HEADGOAL (resolve_tac context [wf_node_inst])
            THEN ALLGOALS (simp_only context (sound_simps @ [gram_th]))
          end) ctxt;

      in elim_step THEN HEADGOAL focus end;

    val prods_meta = map (fn p => (p, intro_meta p)) prods;

    val sound_thms =
      timed "prove sound_conj" (fn () =>
        prove_family lthy
          {preds = nnames ~~ pred_frees, insensitive = insensitive,
           induct = #induct ind_result, wordT = wordT, carrier_of = carrier_of,
           norm = ground_tvars}
          (fn A => fn i_t => fn w => fn _ => sound_body_of A i_t w)
          (fn ctxt => EVERY (map (sound_case_tac ctxt) prods_meta))) ();

    val (_, lthy) =
      timed "Local_Theory.notes (intros + inducts)"
        (Local_Theory.notes
          [((qualify_bind gram_b "intros", []),  [(cleaned_intros, [])]),
           ((qualify_bind gram_b "inducts", []),  [(cleaned_inducts, [])])]) lthy;

    (* completeness for each NT \<open>A\<^sub>k\<close>:
      \<open>wf_ptree G pt \<Longrightarrow> fst (proot pt) = Nt A\<^sub>k \<longrightarrow> (\<exists>x. pred\<^sub>k [snd (proot pt)] (pyield pt) x)\<close>. *)

    val gram_folded_th = Local_Defs.unfold lthy @{thms is_cfg.make_def} gram_th;

    val snd_root_c = Const (\<^const_name>\<open>snd\<close>, prootT --> HOLogic.natT);

    (* body_A pt: \<open>\<exists>x. pred\<^sub>A [snd (proot pt)] (pyield pt) x\<close> *)
    fun complete_body_of A pt_t =
      let val cT = carrier_of A in
        HOLogic.mk_exists ("x", cT,
          if insensitive
          then pred_of A $ (pyield_c $ pt_t) $ Bound 0
          else pred_of A $ (snd_root_c $ (proot_c $ pt_t))
                        $ (pyield_c $ pt_t) $ Bound 0)
        |> ground_tvars
      end;

    val intros_rev = rev cleaned_intros;

    (* production cases of the root-indexed induction (Grammar_Ptree_Induct): the
       selector equations rewrite the conclusion and the induction hypotheses
       to the bodies *)
    fun complete_prod0_tac ctxt sel_eqs k =
      SELECT_GOAL (unfold_tac ctxt @{thms prod.inject}) THEN'
      eresolve_tac ctxt @{thms conjE} THEN'
      Hypsubst.hyp_subst_tac_thin false ctxt THEN'
      simp_only ctxt (sel_eqs @ @{thms list_all2_Nil pyield.simps list.map concat.simps}) THEN'
      resolve_tac ctxt @{thms exI} THEN'
      resolve_tac ctxt [nth intros_rev k];

    fun complete_prod1_tac ctxt sel_eqs k =
      SELECT_GOAL (unfold_tac ctxt @{thms prod.inject sym.inject fst_conv}) THEN'
      REPEAT_ALL_NEW (ematch_tac ctxt @{thms conjE}) THEN'
      Hypsubst.hyp_subst_tac_thin true ctxt THEN'
      SELECT_GOAL (unfold_tac ctxt @{thms list_all2_Cons1 list_all2_Nil}) THEN'
      (REPEAT_DETERM o ematch_tac ctxt @{thms exE conjE}) THEN'
      SELECT_GOAL (unfold_tac ctxt @{thms fst_conv snd_conv sym.inject sym.distinct}) THEN'
      (REPEAT_DETERM o ematch_tac ctxt @{thms exE}) THEN'
      SELECT_GOAL (Local_Defs.fold_tac ctxt [gram_folded_th]) THEN'
      Hypsubst.hyp_subst_tac_thin true ctxt THEN'
      simp_only ctxt (sel_eqs @ @{thms sym.inject sym.distinct simp_thms}) THEN'
      Subgoal.FOCUS_PARAMS (fn {context = ctxt', ...} =>
        (REPEAT_DETERM o HEADGOAL)
          (dresolve_tac ctxt' @{thms wf_ptree_Tm_leaf}
           THEN' assume_tac ctxt')
        THEN (REPEAT_DETERM o HEADGOAL) (eresolve_tac ctxt' @{thms exE conjE})
        THEN HEADGOAL
          (simp_only ctxt'
             @{thms pyield.simps list.map concat.simps append.simps append_Nil2})
        (* a unit self-loop (A = A) is closed by the simp step already *)
        THEN COND (has_fewer_prems 1) all_tac
         (HEADGOAL
            (Subgoal.FOCUS_PARAMS (fn {params = ps, ...} =>
               (HEADGOAL o EVERY')
                 (map (fn (_, ct) => EqSubst.eqsubst_tac ctxt' [0]
                   [infer_instantiate' ctxt' [SOME ct] @{thm token.surjective}])
                   (* the token parameters only *)
                   (filter (fn (_, ct) =>
                      (case Thm.typ_of_cterm ct of
                        Type (\<^type_name>\<open>Token.token_ext\<close>, _) => true
                      | _ => false)) ps)))
               ctxt')
          THEN (REPEAT_DETERM o HEADGOAL)
            (eresolve_tac ctxt' @{thms exE conjE impE[OF _ refl]})
          THEN HEADGOAL
            (simp_only ctxt' @{thms token.simps}
             THEN' (Hypsubst.hyp_subst_tac_thin true ctxt' ORELSE' K all_tac)
             THEN' resolve_tac ctxt' @{thms exI})
          THEN HEADGOAL
            (resolve_tac ctxt' [nth intros_rev k]
             THEN_ALL_NEW (assume_tac ctxt' ORELSE'
               (simp_only ctxt' @{thms irel_sat.simps proot.simps snd_conv}
                THEN_ALL_NEW assume_tac ctxt'))))) ctxt;

    fun complete_prod_tac ctxt sel_eqs (k, prod: Grammar_Common.prod) =
      if null (#rhs prod)
      then complete_prod0_tac ctxt sel_eqs k
      else complete_prod1_tac ctxt sel_eqs k;

    (* the node case: the conclusion to \<open>P A (PNode A i pts)\<close>, the membership
       to a disjunction over the productions, one case each *)
    fun complete_node_tac ctxt sel_eqs =
      simp_only ctxt @{thms proot.simps fst_conv sym.inject simp_thms}
      THEN' simp_only ctxt
              (@{thms prod.inject sym.inject
                      is_cfg.make_def is_cfg.select_convs list.set
                      insert_iff singleton_iff empty_iff}
               @ [gram_th])
      THEN' REPEAT_ALL_NEW (eresolve_tac ctxt @{thms disjE[OF disj_commute[THEN iffD1]]})
      THEN' eresolve_tac ctxt @{thms FalseE}
      THEN' EVERY' (map_index (SOLVED' o complete_prod_tac ctxt sel_eqs) (rev prods));

    val complete_of =
      timed "prove complete_conj" (fn () =>
        Grammar_Ptree_Induct.prove lthy
          {gram_t = ground_tvars gram_t, ptreeT = ground_typ ptreeT, tokT = ground_typ tokT,
           bodies = map (fn A => (A, complete_body_of A)) nnames}
          complete_node_tac) ();

    val start = #start gram;
    val start_lit = HOLogic.mk_string start;
    val zero_nat = \<^term>\<open>0 :: nat\<close>;
    val istart_c = Const (\<^const_name>\<open>istart\<close>, isgT --> HOLogic.stringT);
    val istart_ind_c = Const (\<^const_name>\<open>istart_ind\<close>, isgT --> HOLogic.natT);

    val gram_simp = Local_Defs.unfold lthy @{thms is_cfg.make_def} gram_th;

    val istart_eq_prop =
      HOLogic.mk_Trueprop (HOLogic.mk_eq (istart_c $ gram_t, start_lit));
    val istart_eq_th =
      Goal.prove lthy [] [] istart_eq_prop
        (fn {context, ...} =>
           HEADGOAL (asm_full_simp_tac
             (context addsimps [gram_simp])));

    val istart_ind_eq_prop =
      HOLogic.mk_Trueprop (HOLogic.mk_eq (istart_ind_c $ gram_t, zero_nat));
    val istart_ind_eq_th =
      Goal.prove lthy [] [] istart_ind_eq_prop
        (fn {context, ...} =>
           HEADGOAL (asm_full_simp_tac
             (context addsimps [gram_simp])));

    val start_idx = find_index (curry (op =) start) nnames;
    val sound_start = nth sound_thms start_idx;
    val complete_start = complete_of start;

    val start_carrier = carrier_of start;
    val lang_th =
      let
        val (lang_fresh, lthy_gen) =
          Variable.variant_fixes ["w_lang"] lthy;
        val w_nm = hd lang_fresh;
        val w_v = Free (w_nm, wordT);
        val pred_start = pred_of start;
        val ex_body =
          HOLogic.mk_exists ("x", start_carrier,
             if insensitive then pred_start $ w_v $ Bound 0
             else pred_start $ zero_nat $ w_v $ Bound 0);

        val ilang_c =
          Const (\<^const_name>\<open>ilang\<close>, isgT --> HOLogic.mk_setT wordT);
        val mem_body = HOLogic.mk_mem (w_v, ilang_c $ gram_t);
        val prop =
          HOLogic.mk_Trueprop (HOLogic.mk_eq (ex_body, mem_body))
          |> ground_tvars;
        val lang_simps =
          (gram_simp :: istart_eq_th :: istart_ind_eq_th ::
            @{thms ilang_iff_ast ast_of_def});
        val complete_folded =
          Local_Defs.fold lthy @{thms atomize_imp} complete_start;

        val bridge_focus = Subgoal.FOCUS (fn {context = ctxt', prems, ...} =>
          let
            fun is_root_eq th =
              (case Thm.concl_of th of
                Const (\<^const_name>\<open>Trueprop\<close>, _) $
                  (Const (\<^const_name>\<open>HOL.eq\<close>, _) $
                     (Const (\<^const_name>\<open>proot\<close>, _) $ _) $ _) => true
              | _ => false);
            fun is_wf th =
              (case Thm.concl_of th of
                Const (\<^const_name>\<open>Trueprop\<close>, _) $
                  (Const (\<^const_name>\<open>wf_ptree\<close>, _) $ _ $ _) => true
              | _ => false);
            val root_eq = the (find_first is_root_eq prems);
            val wf_prem = the (find_first is_wf prems);
            val fst_eq =
              (root_eq RS @{thm fstI})
              |> Local_Defs.unfold ctxt' [istart_eq_th];
            val snd_eq =
              (root_eq RS @{thm sndI})
              |> Local_Defs.unfold ctxt' [istart_ind_eq_th];
            val bridged =
              (complete_folded OF [wf_prem, fst_eq])
              |> Local_Defs.unfold ctxt' [snd_eq];
          in HEADGOAL (resolve_tac ctxt' [bridged]) end);
        val backward_step =
          eresolve_tac lthy_gen [@{thm lang_of_complete}]
          THEN' bridge_focus lthy_gen;
        val raw_th =
          timed "prove lang" (fn () =>
            Goal.prove lthy_gen [] [] prop
              (fn {context, ...} =>
                 HEADGOAL (resolve_tac context [@{thm iffI}])
                 (*Forward: \<open>\<exists>x. pred w x \<Longrightarrow> w \<in> ilang G\<close>.*)
                 THEN HEADGOAL (eresolve_tac context [@{thm exE}])
                 THEN HEADGOAL (dresolve_tac context [sound_start])
                 THEN HEADGOAL (asm_full_simp_tac
                   (context addsimps lang_simps))
                 (*Backward: \<open>w \<in> ilang G \<Longrightarrow> \<exists>x. pred w x\<close>.*)
                 THEN HEADGOAL backward_step)) ();
      in singleton (Proof_Context.export lthy_gen lthy) raw_th end;

    val (_, lthy) =
      timed "Local_Theory.notes (lang)"
        (Local_Theory.notes
          [((qualify_bind gram_b "lang", []), [([lang_th], [])])]) lthy;

  in (nnames ~~ #preds ind_result, cleaned_intros, cleaned_inducts, sound_thms, lthy)
  end;


(** public entry: grammar + relation + theorem
    (grammar constant and decoders are reused when already defined) **)

type semantics =
 {gram:       term * thm,
  preds:      (string * term) list,
  decs:       (string * term) list,
  intros:     thm list,
  inducts:    thm list,
  sound_thms: thm list};

fun semantics_of (arts: Grammar_Common.artifacts) (ri: Grammar_Common.rel_info)
    : semantics =
  {gram = (#gram_t arts, #gram_def arts), decs = #decs arts,
   preds = #preds ri, intros = #intros ri,
   inducts = #inducts ri, sound_thms = #sound_thms ri};

fun rel_info_of ({preds, intros, inducts, sound_thms, ...}: semantics)
    : Grammar_Common.rel_info =
  {preds = preds, intros = intros,
   inducts = inducts, sound_thms = sound_thms};

(* the relation family of an elaborated grammar; the grammar constant, its
   definition and the decoders are passed in *)
fun define_relation (gram: Grammar_Common.grammar) (gram_t, gram_th) decs lthy =
  let
    fun timed label f x = Grammar_Common.timed lthy (Binding.name_of (#name gram)) label f x;
    val (preds, intros, inducts_ths, sound_ths, lthy) =
      timed "gen_define_relation" (gen_define_relation gram_t gram_th gram) lthy;
  in
    ({gram = (gram_t, gram_th), preds = preds,
      decs = decs, intros = intros, inducts = inducts_ths,
      sound_thms = sound_ths}, lthy)
  end;

(* add a relation family to a registered grammar; idempotent *)
fun define_relation_of name_ref lthy =
  let
    val (_, gram) = Grammar_Common.check_grammar lthy name_ref;
    val arts = Grammar_Common.artifacts_of gram;
  in
    (case lookup_rel lthy gram of
      SOME ri => (semantics_of arts ri, lthy)
    | NONE =>
        let
          val (sem, lthy) =
            define_relation gram (#gram_t arts, #gram_def arts) (#decs arts) lthy;
          val lthy = store_rel gram (rel_info_of sem) lthy;
        in (sem, lthy) end)
  end;

end;
