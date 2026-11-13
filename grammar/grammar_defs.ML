(* Author: Basil Fürer, Dmitriy Traytel, Claude *)

(* the definitions behind a grammar: the grammar constant and the decoders;
   the relation family is in grammar_rel.ML *)

signature GRAMMAR_DECODERS =
sig
  val define_grammar:
    Grammar_Common.grammar -> local_theory ->
      (term * thm) * local_theory
  val define_const: bool -> binding * binding * term -> local_theory ->
    (term * thm) * local_theory
  val decoder_of: Proof.context -> Grammar_Common.grammar -> string -> term
  val define_decoders:
    Grammar_Common.grammar -> local_theory ->
      (string * term) list * local_theory

  (* shared with the relation (grammar_rel.ML) *)
  val suffix_bind: string -> binding -> binding
  val with_concealed: (local_theory -> 'a * local_theory) -> local_theory -> 'a * local_theory
  val simp_only: Proof.context -> thm list -> int -> tactic
  datatype iv_child =
      NTc of string
    | ClassTm of term
    | LitTm of term
  val classify_of: Grammar_Common.grammar -> Grammar_Common.rsym -> iv_child
  val ground_typ: typ -> typ
  val ground_tvars: term -> term
end;

structure Grammar_Decoders: GRAMMAR_DECODERS =
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
  asm_full_simp_tac (put_simpset HOL_basic_ss ctxt |> Simplifier.add_simps extra);


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
    val prodT = HOLogic.mk_prodT (Grammar_Common.name_typ g, HOLogic.listT rhs_elemT);
    val rhs_terms =
      prods |> map (fn {rhs, ...}: Grammar_Common.prod =>
        HOLogic.mk_list rhs_elemT (map (fn (s, a) => mk_rhs_elem (mk_sym s, a)) rhs));
    val prods_term =
      HOLogic.mk_list prodT
        (map2 (fn ({lhs, ...}: Grammar_Common.prod) => fn rhs_t =>
            HOLogic.mk_prod (Grammar_Common.name_term g lhs, rhs_t))
          prods rhs_terms);
    val rhs = mk_grammar_term prods_term (Grammar_Common.name_term g start);
  in define_const true (name, Thm.def_binding name, rhs) lthy end;


fun isg_encoding (gram: Grammar_Common.grammar): gram_encoding =
  let
    val {tokT, terminals, ...} = gram;

    val symbolT = Type (\<^type_name>\<open>sym\<close>, [Grammar_Common.name_typ gram, tokT]);
    val isgT = Type (\<^type_name>\<open>is_cfg_ext\<close>, [Grammar_Common.name_typ gram, tokT, \<^typ>\<open>unit\<close>]);
    val rhs_elemT = HOLogic.mk_prodT (symbolT, \<^typ>\<open>irel\<close>);
    val makeT =
      HOLogic.listT (HOLogic.mk_prodT (Grammar_Common.name_typ gram, HOLogic.listT rhs_elemT))
      --> Grammar_Common.name_typ gram --> \<^typ>\<open>nat\<close> --> isgT;

    val Nt_c = Const (\<^const_name>\<open>Nt\<close>, Grammar_Common.name_typ gram --> symbolT);
    val Tm_c = Const (\<^const_name>\<open>Tm\<close>, tokT --> symbolT);
    val make_c = Const (\<^const_name>\<open>is_cfg.make\<close>, makeT);

    fun mk_sym (Grammar_Common.RN n) = Nt_c $ Grammar_Common.name_term gram n
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

fun mk_case_ast_c nameT tokenT astT astListT R =
  Const (\<^const_name>\<open>case_ast\<close>,
    (tokenT --> R) --> (nameT --> astListT --> R) --> astT --> R);

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
    val {tokenT, astT, chT, ...} = Grammar_Common.get_desc gram;
    val astListT = HOLogic.listT astT;
    val {tokT, ...} = gram;
    val outT = carrier_of (#lhs p);
    (* \<open>@span\<close>: the span of the children's yield, the action's first argument *)
    val span_args =
      if #span p then
        [Const (\<^const_name>\<open>yield_span\<close>,
            astListT --> Type (\<^type_name>\<open>TIGER_Token.span_ext\<close>, [chT, \<^typ>\<open>unit\<close>]))
          $ HOLogic.mk_list astT cs]
      else [];
    val outOptT = mk_optionT outT;
    val classify = classify_of gram;
    val slots = cs ~~ map (fn (s, _) => classify s) (#rhs p);
    val Tok_tok_c = Const (\<^const_name>\<open>TIGER_Token.tok\<close>, tokenT --> tokT);
    val none = mk_None outT;

    fun leaf_arm x_v inner =
      mk_case_ast_c (Grammar_Common.name_typ gram) tokenT astT astListT outOptT
        $ Term.lambda x_v inner
        $ Abs ("nn", Grammar_Common.name_typ gram, Abs ("xxs", astListT, none));

    fun build [] _ args_rev =
          mk_Some outT $ Term.betapplys (ground_tvars (#action p), span_args @ rev args_rev)
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

    val name_lit = Grammar_Common.name_term gram A;

    fun body_at_length k cs =
      let
        val prods_k = the (AList.lookup (op =) by_len k);
        val fresh_seeds =
          maps (fn p => map (fn _ => "dz_" ^ ident_in gram A) (#rhs p)) prods_k;
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
    val n_v = Free ("dnv_" ^ ident_in gram A, Grammar_Common.name_typ gram);
    val xs_v = Free ("dxs_" ^ ident_in gram A, astListT);
    val node_body = node_body_dec gram lthy carrier_of dec_of A n_v xs_v;

    val Leaf_c = Const (\<^const_name>\<open>Leaf\<close>, tokenT --> astT);
    val Node_c = Const (\<^const_name>\<open>Node\<close>, Grammar_Common.name_typ gram --> astListT --> astT);

    val lhs_node = dec_free $ (Node_c $ n_v $ xs_v);
    val eq_node = HOLogic.mk_Trueprop (HOLogic.mk_eq (lhs_node, node_body));

    val wildcard = Free ("dwild_" ^ ident_in gram A, tokenT);
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
   are derived, in parallel over the nonterminals. *)
fun define_decoders (gram: Grammar_Common.grammar) lthy =
  let
    val {astT, ...} = Grammar_Common.get_desc gram;
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
    val dispT = recT --> HOLogic.natT --> Grammar_Common.name_typ gram --> astListT --> valOptT;
    val f_v = Free ("dfun", recT);
    val sel_v = Free ("dsel", HOLogic.natT);
    val n_v = Free ("dnv", Grammar_Common.name_typ gram);
    val xs_v = Free ("dxs", astListT);
    val dispatch = timed "dispatch term" (fn () =>
      fold_rev (fn A => fn rest =>
          mk_if_c valOptT $ HOLogic.mk_eq (sel_v, index_of A)
            $ (mk_map_option_c (carrier_of A) $ inj_of A
                $ node_body_dec gram lthy carrier_of (dec_via f_v) A n_v xs_v)
            $ rest)
        nnames (mk_None valT)
      |> Envir.beta_norm) ();
    val disp_b = suffix_bind "__disp" gram_b;
    val ((disp, disp_def), lthy1) =
      timed "define dispatch" (define_const false
        (disp_b, Thm.def_binding disp_b, fold_rev Term.lambda [f_v, sel_v, n_v, xs_v] dispatch))
        lthy;
    val ast_rec_c =
      Const (\<^const_name>\<open>ast_rec\<close>, dispT --> valOptT --> recT);
    val decode = ast_rec_c $ disp $ mk_None valT;

    val dec_bindings = map (fn nm => suffix_bind ("__dec_" ^ ident_in gram nm) gram_b) nnames;
    val (dec_defs, lthy2) =
      timed "define decoders" (fold_map (fn (b, A) =>
          define_const false (b, Thm.def_binding b, dec_via decode A))
        (dec_bindings ~~ nnames)) lthy1;
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
        (U, Goal.prove_sorry lthy2 ["x"] [] goal (fn {context = ctxt, ...} =>
          HEADGOAL (Induct_Tacs.case_tac ctxt "x" [] NONE) THEN
          ALLGOALS (asm_full_simp_tac ctxt)) |> mk_meta_eq)
      end;
    val bind_maps = timed "bind_map lemmas" (map bind_map_lemma) injs;

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
        |> Simplifier.add_simps @{thms list.set insert_iff simp_thms if_True}
      |> Simplifier.add_cong @{thm list.case_cong};
    fun prove_eqn A goal =
      let
        val frees =
          Term.add_free_names goal [] |> filter_out (Variable.is_fixed lthy2);
      in
        Goal.prove_sorry lthy2 frees [] goal (fn {context = ctxt, ...} =>
          rewrite_goal_tac ctxt dec_def_eqs 1 THEN
          CONVERSION (HOLogic.Trueprop_conv (Conv.arg1_conv (lhs_conv ctxt A))) 1 THEN
          asm_full_simp_tac (children_ctxt ctxt) 1)
      end;
    val eqns = timed "derive equations" (fn () =>
      Par_List.map (fn A =>
          map_index (fn (k, goal) =>
              timed ("equation " ^ A ^ " " ^ string_of_int (k + 1)) (prove_eqn A) goal)
            (eqns_for_nt_dec gram lthy2 carrier_of dec_of A))
        nnames) ();
    val (_, lthy3) =
      timed "note simps" (Local_Theory.notes (map (fn (b, ths) =>
          ((Binding.qualify_name true b "simps",
              [Attrib.internal \<^here> (K Simplifier.simp_add)]), [(ths, [])]))
        (dec_bindings ~~ eqns))) lthy2;
    (* the equations are the code equations, also of interpretations; inside a
       locale with assumptions they stay conditional and are not declared
       globally *)
    val lthy3 = timed "code equations" (fn lthy => lthy
      |> Code.declare_default_eqns (map (rpair true) (flat eqns))
      |> Grammar_Common.declare_code_global {default = true} (flat eqns)) lthy3;
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

end;
