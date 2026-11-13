(* Author: Basil Fürer *)

(* precedence declarations in the parser command: the declarations of a grammar become
   the constant `p_prec`, the grammar the constant `p_gram = restricted G p_prec`, which
   the backend is handed in place of G, and each decoder of G is composed with
   plain_ast orig_name.  The constants are per parser since an entry restricts from its
   own start.  Theorems: LR_Prec_Parse.  The restriction is the label-intersect-read-back
   construction of \<^cite>\<open>\<open>Sect.~3\<close> in "adams2017-tree-automata"\<close>. *)

structure LR_Prec: sig end =
struct

val orig_string = Grammar_Common.orig_string;

val anns = [Grammar_Common.Eq, Grammar_Common.Ge, Grammar_Common.Gt, Grammar_Common.Any];

(* the productions of the restricted grammar, for reports: a literal of `iprods Gr` in
   the record's terms, under the names of the grammar the user wrote, and its numbers of
   productions and nonterminals *)
fun restricted_prods ctxt (gr: Grammar_Common.grammar) gr_c =
  let
    val {isgT, ...} = Grammar_Common.get_desc gr;
    val altsT =
      HOLogic.listT (HOLogic.mk_prodT (HOLogic.stringT,
        HOLogic.listT (HOLogic.mk_prodT
          (Type (\<^type_name>\<open>sym\<close>, [HOLogic.stringT, #tokT gr]), \<^typ>\<open>irel\<close>))));
    val ts = Vector.foldr (op ::) [] (#terminals gr);
    fun rsym (Const (\<^const_name>\<open>Nt\<close>, _) $ n) = Grammar_Common.RN (orig_string (HOLogic.dest_string n))
      | rsym (Const (\<^const_name>\<open>Tm\<close>, _) $ t) =
          (case find_index (fn u => u aconv t) ts of
            ~1 => raise Fail "restricted_prods: a terminal of no declaration"
          | i => Grammar_Common.RT i)
      | rsym t = raise TERM ("restricted_prods", [t]);
    fun ann t = the (find_first (fn a => Grammar_Common.irel_term a aconv t) anns);
    fun prod i p =
      let val (l, r) = HOLogic.dest_prod p in
        {no = i, lhs = orig_string (HOLogic.dest_string l),
         rhs = map (fn e => let val (s, a) = HOLogic.dest_prod e in (rsym s, ann a) end)
           (HOLogic.dest_list r),
         action = Term.dummy, span = false, pos = Position.none}: Grammar_Common.prod
      end;
    val raw =
      Lazy.lazy (fn () =>
        Const (\<^const_name>\<open>iprods\<close>, isgT --> altsT) $ gr_c
        |> Value_Command.value ctxt |> HOLogic.dest_list);
    fun counts () =
      let val ps = Lazy.force raw in
        (length ps,
         length (distinct (op =) (map (HOLogic.dest_string o fst o HOLogic.dest_prod) ps)))
      end;
  in
    (Lazy.lazy (fn () => map_index (uncurry prod) (Lazy.force raw)), Lazy.lazy counts)
  end;

fun global_const lthy b =
  (case Grammar_Common.def_axiom lthy (b, Thm.def_binding b) of
    SOME ax => ax
  | NONE => raise Fail "LR_Prec: no foundation for a constant of the parser");

fun lhs_of ax = #1 (Logic.dest_equals (Thm.prop_of ax));

fun decl_term (gr: Grammar_Common.grammar) alts ({chains, forbids}: Grammar_Common.prec_info) =
  let
    val altT = fastype_of (hd alts);
    val assocT = \<^typ>\<open>passoc\<close>;
    fun assoc "left" = \<^const>\<open>ALeft\<close>
      | assoc "right" = \<^const>\<open>ARight\<close>
      | assoc "nonassoc" = \<^const>\<open>ANon\<close>
      | assoc "open" = \<^const>\<open>AOpen\<close>
      | assoc "list" = \<^const>\<open>AList\<close>
      | assoc s = raise Fail ("LR_Prec: associativity " ^ s);
    fun kind "direct" = \<^const>\<open>FDirect\<close>
      | kind "right" = \<^const>\<open>FRight\<close>
      | kind "left" = \<^const>\<open>FLeft\<close>
      | kind s = raise Fail ("LR_Prec: forbid " ^ s);
    val itemT = HOLogic.mk_prodT (altT, HOLogic.boolT);
    val levelT = HOLogic.mk_prodT (assocT, HOLogic.listT itemT);
    fun item (p, s) =
      HOLogic.mk_prod (nth alts p, if s then \<^term>\<open>True\<close> else \<^term>\<open>False\<close>);
    fun level (a, items) = HOLogic.mk_prod (assoc a, HOLogic.mk_list itemT (map item items));
    val forbidT = HOLogic.mk_prodT (altT, HOLogic.mk_prodT (HOLogic.natT,
      HOLogic.mk_prodT (\<^typ>\<open>fkind\<close>, altT)));
    fun forbid (p, k, kd, c) =
      HOLogic.mk_prod (nth alts p, HOLogic.mk_prod (HOLogic.mk_number HOLogic.natT k,
        HOLogic.mk_prod (kind kd, nth alts c)));
    val chainsT = HOLogic.listT (HOLogic.listT levelT);
    val forbidsT = HOLogic.listT forbidT;
    val declT = Type (\<^type_name>\<open>prec_decl_ext\<close>, [HOLogic.stringT, #tokT gr, HOLogic.unitT]);
  in
    Const (\<^const_name>\<open>prec_decl.make\<close>, chainsT --> forbidsT --> declT) $
      HOLogic.mk_list (HOLogic.listT levelT) (map (HOLogic.mk_list levelT o map level) chains) $
      HOLogic.mk_list forbidT (map forbid forbids)
  end;

fun prepare parse_b shn (gr: Grammar_Common.grammar) lthy =
  let
    val info = the (#prec gr);
    val arts = Grammar_Common.artifacts_of gr;
    val {gram_t, gram_def, ...} = arts;
    val {isgT, astT, ...} = Grammar_Common.get_desc gr;
    val alts =
      (case Term.strip_comb (snd (Logic.dest_equals (Thm.prop_of gram_def))) of
        (_, [ps, _, _]) => HOLogic.dest_list ps
      | _ => raise Fail "LR_Prec: grammar definition");
    val decl_t = decl_term gr alts info;
    val declT = fastype_of decl_t;
    val suffixed = fn s => Binding.map_name (fn n => n ^ s) parse_b;
    val prec_b = suffixed "_prec";
    val gram_b = suffixed "_gram";
    val (_, lthy) = Grammar_Defs.define_const true (prec_b, Thm.def_binding prec_b, decl_t) lthy;
    val d_c = lhs_of (global_const lthy prec_b);
    val restrict_t = Const (\<^const_name>\<open>restricted\<close>, isgT --> declT --> isgT) $ gram_t $ d_c;
    val (_, lthy) =
      Grammar_Defs.define_const true (gram_b, Thm.def_binding gram_b, restrict_t) lthy;
    val gr_ax = global_const lthy gram_b;
    val gr_c = lhs_of gr_ax;
    val gr_eq = gr_ax RS @{thm meta_eq_to_obj_eq};

    val shn_t = HOLogic.mk_string shn;
    val fresh =
      Goal.prove_sorry lthy [] []
        (HOLogic.mk_Trueprop
          (Const (\<^const_name>\<open>fresh_name\<close>, isgT --> HOLogic.stringT --> HOLogic.boolT) $ gr_c $ shn_t))
        (fn {context = ctxt, ...} =>
          Local_Defs.unfold_tac ctxt [gr_ax]
          THEN HEADGOAL (resolve_tac ctxt @{thms fresh_name_restricted}
            THEN' asm_full_simp_tac ctxt));

    val orig = \<^const>\<open>orig_name\<close>;
    val plain =
      Const (\<^const_name>\<open>plain_ast\<close>,
        (HOLogic.stringT --> HOLogic.stringT) --> astT --> astT) $ orig;
    fun decode dec =
      let val T = range_type (fastype_of dec)
      in Const (\<^const_name>\<open>comp\<close>, (astT --> T) --> (astT --> astT) --> astT --> T) $ dec $ plain end;
    val (prods, counts) = restricted_prods lthy gr gr_c;
    val arts' : Grammar_Common.artifacts =
      {gram_t = gr_c, gram_def = gr_ax, decs = map (apsnd decode) (#decs arts), rel = #rel arts,
       restricted = SOME
        {orig = orig, fresh = fresh,
         prods = prods, counts = counts}};

    fun inst ctxt =
      Drule.infer_instantiate ctxt
        [(("G", 0), Thm.cterm_of ctxt gram_t), (("d", 0), Thm.cterm_of ctxt d_c)];

    fun discharge ctxt prem =
      if prem aconv Thm.prop_of gr_eq then SOME (resolve_tac ctxt [gr_eq])
      else
        (case prem of
          \<^Const_>\<open>Trueprop for \<^Const_>\<open>no_self_unit _ _ for _\<close>\<close> =>
            SOME (resolve_tac ctxt @{thms no_self_unitI} THEN'
              asm_full_simp_tac (ctxt |> Simplifier.add_simps (gram_def :: @{thms is_cfg.make_def})))
        | _ => NONE);
  in
    ({gram = Grammar_Common.put_artifacts arts' gr, inst = inst, discharge = discharge}, lthy)
  end;

val _ = Theory.setup (Parser_Generators.set_prec_hook
  {prepare = prepare,
   sound_lang = @{thm parse_fn_lang},
   complete_lang = @{thm parse_fn_complete_lang},
   sound = @{thm parse_fn_tree},
   complete = @{thm parse_fn_complete},
   no_error = @{thm parse_fn_no_error},
   ast =
    {complete_lang = @{thm parse_fn_ast_complete_lang},
     sound = @{thm parse_fn_ast_tree},
     complete = @{thm parse_fn_ast_complete},
     no_error = @{thm parse_fn_ast_no_error}}});

end;
