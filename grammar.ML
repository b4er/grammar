(* the grammar command: parsing and elaboration of a specification
   (terminals, productions, semantic actions) into the grammar record, then
   the definitions through Grammar_Defs *)

signature GRAMMAR_COMMAND =
sig
  datatype gram_opt = Opt_Relation
  val grammar_cmd: gram_opt list -> Grammar_Common.spec -> local_theory -> local_theory
end;

structure Grammar_Command: GRAMMAR_COMMAND =
struct

open Grammar_Common;

datatype gram_opt = Opt_Relation;

(** elaboration **)


fun read_carrier_type ctxt (b, src) =
  let
    val T = Syntax.read_typ ctxt (Syntax.implode_input src);
    val _ =
      Term.exists_subtype (fn TFree _ => true | TVar _ => true | _ => false) T
        andalso error ("Carrier of nonterminal " ^ quote (Binding.name_of b) ^
          " is not ground: the ascribed type " ^
          cartouche (Syntax.string_of_typ ctxt T) ^
          " has type variables; ascribe a ground type" ^ Position.here (Input.pos_of src));
  in T end;

fun read_term_typed ctxt expT src =
  Syntax.parse_term ctxt (Syntax.implode_input src)
  |> Type.constraint expT
  |> Syntax.check_term ctxt;

(* inferred carrier of each nonterminal witness (class witnesses are typed) *)
fun collect_witness_types class_prefix eqns =
  let
    fun step (Free (n, T)) tab =
          if String.isPrefix class_prefix n then tab else Symtab.update (n, T) tab
      | step (t $ u) tab = step u (step t tab)
      | step (Abs (_, _, body)) tab = step body tab
      | step _ tab = tab;
  in fold step eqns Symtab.empty end;

fun elaborate ({name, tok_typ, terminals = terminal_decls, productions}: spec) lthy =
  let
    (** nonterminal tables **)
    val nt_bindings = map (#1 o #1) productions;
    val nnames = map Binding.name_of nt_bindings;
    val nt_idx_tab =
      fold_index (fn (i, n) => Symtab.update (n, i)) nnames Symtab.empty;
    fun is_nt n = Symtab.defined nt_idx_tab n;
    val start =
      (case nnames of n :: _ => n
       | [] => error ("grammar " ^ quote (Binding.name_of name) ^
                      " has no productions" ^ Position.here (Binding.pos_of name)));

    (** token type: a ground \<open>('tok, 'ch, 'more) token_scheme\<close> from the
      \<open>tokens\<close> clause; a type \<open>T\<close> that is not a token scheme abbreviates
      \<open>(T, unit) token\<close>, the default is \<open>(string, unit) token\<close> **)
    fun plain_token_type T =
      Type (\<^type_name>\<open>Token.token_ext\<close>, [T, \<^typ>\<open>unit\<close>, \<^typ>\<open>unit\<close>]);
    val (tokT, tokenT) =
      (case tok_typ of
        NONE => (HOLogic.stringT, plain_token_type HOLogic.stringT)
      | SOME src =>
          let val T = Syntax.read_typ lthy (Syntax.implode_input src) in
            Term.exists_subtype (fn TFree _ => true | TVar _ => true | _ => false) T
              andalso error ("The ascribed token type is not ground" ^
                             Position.here (Input.pos_of src));
            (case T of
              Type (\<^type_name>\<open>Token.token_ext\<close>, [tok, _, _]) => (tok, T)
            | _ => (T, plain_token_type T))
          end);

    (** terminal-decl tables **)
    val fixed_tab =
      Symtab.make (map_filter (fn Fixed p => SOME p | _ => NONE) terminal_decls);
    val class_tab =
      Symtab.make_set
        (map_filter (fn Class b => SOME (Binding.name_of b) | _ => NONE) terminal_decls);

    fun source_of (n, pos) = Input.source false n (pos, pos);
    fun class_tok (n, pos) =
      if tokT = HOLogic.stringT then HOLogic.mk_string n
      else read_term_typed lthy tokT (source_of (n, pos));
    fun lit_tok (s, pos) =
      (case Symtab.lookup fixed_tab s of
        SOME src => read_term_typed lthy tokT src
      | NONE =>
          if tokT = HOLogic.stringT then HOLogic.mk_string s
          else error ("Undeclared fixed terminal " ^ quote s ^
            ": declare  " ^ quote s ^ " = <token value>  in the terminals block"
            ^ Position.here pos));
    fun inline_tok src = read_term_typed lthy tokT src;

    val nt_ns : unit Name_Space.table =
      fold (fn b => fn tab =>
          #2 (Name_Space.define (Context.Proof lthy) true (b, ()) tab))
        nt_bindings (Name_Space.empty_table "grammar_nt");

    fun report_nt_ref (n, pos) =
      ignore (Name_Space.check (Context.Proof lthy) nt_ns (n, pos));

    fun class_parseable (n, pos) =
      tokT = HOLogic.stringT orelse
      (case try (fn () => read_term_typed lthy tokT (source_of (n, pos))) () of
        SOME t => null (Term.add_frees t []) andalso null (Term.add_vars t [])
      | NONE => false);

    fun check_ref (n, pos) =
      if is_nt n then report_nt_ref (n, pos)
      else if Symtab.defined class_tab n then ()
      else if class_parseable (n, pos) then ()
      else error ("Undeclared symbol " ^ quote n ^ ": neither a nonterminal of "
        ^ quote (Binding.name_of name) ^ ", a terminal in the terminals block, \
        \nor a value of type " ^ Syntax.string_of_typ lthy tokT
        ^ Position.here pos);
    fun check_lit (s, pos) =
      if Symtab.defined fixed_tab s orelse tokT = HOLogic.stringT then ()
      else error ("Fixed spelling " ^ quote s ^ " has no token declaration in \
        \the terminals block, and the token type is not string"
        ^ Position.here pos);
    val _ =
      productions |> List.app (fn (_, alts) =>
        alts |> List.app (fn (syms, _) =>
          syms |> List.app
            (fn (Ref rp, _) => check_ref rp
              | (Lit lp, _) => check_lit lp
              | (Tok _, _) => ())));

    val prods_flat =
      productions |> maps (fn ((b, _), alts) =>
        let val lhs = Binding.name_of b
            val pos = Binding.pos_of b in
          map_index (fn (i, (syms, act)) => (lhs, i, syms, act, pos)) alts
        end);

    val parsed_actions =
      prods_flat |> map (fn (_, _, _, act_src, _) =>
        Option.map (Syntax.parse_term lthy o Syntax.implode_input) act_src);

    (** carrier inference: **)
    val witness_prefix = "_carrier_" ^ Binding.name_of name ^ "_";
    val class_prefix = witness_prefix ^ "class_";
    (* class terminals as they occur in the productions *)
    val class_names =
      productions
      |> maps (fn (_, alts) => maps (map_filter (fn (Ref (n, _), _) => SOME n | _ => NONE) o fst) alts)
      |> filter_out is_nt |> distinct (op =);
    fun witness_name b = witness_prefix ^ Binding.name_of b;
    val witnesses_tab =
      productions
      |> map (fn ((b, opt_src), _) =>
          let val T =
            case opt_src of
              SOME src => read_carrier_type lthy (b, src)
            | NONE => dummyT
          in (Binding.name_of b, Free (witness_name b, T)) end)
      |> Symtab.make;
    fun witness_of A = the (Symtab.lookup witnesses_tab A);

    fun value_arg (Ref (n, _)) =
          if is_nt n then SOME (witness_of n)
          else SOME (Free (class_prefix ^ n, tokenT))
      | value_arg (Lit _) = NONE
      | value_arg (Tok _) = NONE;
    val eq_c =
      Const (\<^const_name>\<open>HOL.eq\<close>, dummyT --> dummyT --> HOLogic.boolT);
    fun mk_carrier_eqn (parsed, (lhs, _, syms, _, pos)) =
      let val w_A = witness_of lhs
          val value_args = map_filter (value_arg o fst) syms in
        case parsed of
          SOME t => eq_c $ Term.betapplys (t, value_args) $ w_A
        | NONE =>
            (case value_args of
              [w] => eq_c $ w $ w_A
            | _ =>
                error ("Alternative for " ^ quote lhs ^ " without action must have \
                  \exactly one value symbol" ^ Position.here pos))
      end;

    (** diagnostics for a failed action check **)
    fun string_of_sym (Ref (n, _)) = n
      | string_of_sym (Lit (s, _)) = quote s
      | string_of_sym (Tok src) = cartouche (Syntax.implode_input src);
    fun string_of_prod lhs syms =
      lhs ^ " = " ^ space_implode " " (map (string_of_sym o fst) syms);
    fun value_syms syms =
      map_filter (fn (Ref (n, _), _) => SOME n | _ => NONE) syms;
    fun replace_all (old, new) s =
      let
        fun go s acc =
          (case first_field old s of
            NONE => acc ^ s
          | SOME (pre, post) => go post (acc ^ pre ^ new));
      in if old = "" then s else go s "" end;
    fun unwitness msg =
      msg
      |> fold (fn n => replace_all (class_prefix ^ n, n)) class_names
      |> fold (fn n => replace_all (witness_prefix ^ n, n)) nnames;
    fun plural n s = string_of_int n ^ " " ^ s ^ (if n = 1 then "" else "s");
    (* leading \<lambda>-binders of the parsed action, through the parser's type constraints *)
    fun binders (Const ("_type_constraint_", _) $ t) = binders t
      | binders (Abs (_, _, b)) = 1 + binders b
      | binders _ = 0;
    (* arity of the action on its own; definite when the result is not a type
       variable or the action binds exactly that many variables *)
    fun action_arity t =
      let
        val T = Term.fastype_of (Syntax.check_term lthy t);
        val k = length (Term.binder_types T);
        val definite =
          not (Term.is_TVar (Term.body_type T) orelse Term.is_TFree (Term.body_type T))
          orelse binders t = k;
      in SOME (k, definite) end
      handle ERROR _ => NONE;
    fun action_error what (lhs, pos, syms, parsed) msg =
      let
        val vals = value_syms syms;
        val n = length vals;
        val where_ = " of production \<open>" ^ string_of_prod lhs syms ^ "\<close>" ^
          Position.here pos;
        val rule =
          "one argument per nonterminal and per bare-name class terminal of \
          \the right-hand side" ^
          (if n = 0 then "" else " (here " ^ commas vals ^ ")") ^
          "; quoted and cartouche terminals are fixed spellings and are not \
          \passed to the action";
      in
        (case Option.mapPartial action_arity parsed of
          SOME (k, true) =>
            if k < n then
              error (what ^ ": the action" ^ where_ ^ " takes " ^
                plural k "argument" ^ ", but the right-hand side has " ^
                plural n "value symbol" ^ ": " ^ rule ^ ".")
            else error (what ^ ": type error in the action" ^ where_ ^ ":\n" ^
              unwitness msg ^ "\nThe action receives " ^ rule ^ ".")
        | _ =>
            error (what ^ ": type error in the action" ^ where_ ^ ":\n" ^
              unwitness msg ^ "\nThe action receives " ^ rule ^ "."))
      end;

    fun isolate_check what infos eqns =
      Syntax.check_terms lthy eqns
      handle ERROR msg =>
        let
          fun try_one (info, eqn) =
            (Syntax.check_term lthy eqn; NONE)
            handle ERROR msg' => SOME (info, msg')
        in
          case get_first try_one (infos ~~ eqns) of
            SOME (info, msg') => action_error what info msg'
          | NONE => error msg
        end;

    val prod_infos =
      map2 (fn parsed => fn (lhs, _, syms, _, pos) => (lhs, pos, syms, parsed))
        parsed_actions prods_flat;
    val checked_eqns =
      isolate_check "Carrier inference" prod_infos
        (map mk_carrier_eqn (parsed_actions ~~ prods_flat));

    val free_types = collect_witness_types class_prefix checked_eqns;

    fun infer_carrier (b, opt_src) =
      case opt_src of
        SOME src => read_carrier_type lthy (b, src)
      | NONE =>
          let val pos = Binding.pos_of b
              val nm = Binding.name_of b in
            case Symtab.lookup free_types (witness_name b) of
              NONE =>
                error ("Cannot infer carrier of nonterminal " ^ quote nm ^
                       ": no productions" ^ Position.here pos)
            | SOME cT =>
                (Term.exists_subtype
                    (fn TFree _ => true | TVar _ => true | _ => false) cT
                  andalso error ("Cannot infer carrier of nonterminal " ^ quote nm ^
                                 ": ascribe the type" ^ Position.here pos);
                 cT)
          end;

    val carrier_tab =
      productions
      |> map (fn ((b, opt_src), _) => (Binding.name_of b, infer_carrier (b, opt_src)))
      |> Symtab.make;
    fun carrier_of A = the (Symtab.lookup carrier_tab A);

    (** re-check every action against its concrete expected type: **)
    fun rhs_binding_types syms =
      syms |> map_filter
        (fn (Ref (n, _), _) =>
              if is_nt n then SOME (carrier_of n) else SOME tokenT
          | (Lit _, _) => NONE
          | (Tok _, _) => NONE);

    datatype action_slot = NeedCheck of term | Identity of term;

    val slots =
      map (fn (parsed, (lhs, _, syms, _, pos)) =>
          let val argTs = rhs_binding_types syms
              val expT = argTs ---> carrier_of lhs in
            case parsed of
              SOME t => NeedCheck (Type.constraint expT t)
            | NONE =>
                case argTs of
                  [aT] => Identity (Abs ("x", aT, Bound 0))
                | _ =>
                    error ("Alternative for " ^ quote lhs ^ " without action must \
                      \have exactly one value symbol" ^ Position.here pos)
          end)
        (parsed_actions ~~ prods_flat);

    val to_check_infos =
      map_filter (fn (NeedCheck _, info) => SOME info | _ => NONE)
        (slots ~~ prod_infos);
    val to_check_terms =
      map_filter (fn NeedCheck t => SOME t | Identity _ => NONE) slots;

    val checked_terms = isolate_check "Action type-check" to_check_infos to_check_terms;

    (* a free variable not fixed in the context: the function package would
       reject the decoder equation later without naming the production *)
    val _ =
      (to_check_infos ~~ checked_terms) |> List.app (fn ((lhs, pos, syms, _), t) =>
        (case filter_out (Variable.is_fixed lthy) (map #1 (Term.add_frees t [])) of
          [] => ()
        | xs =>
            error ("Free variable" ^ (if length xs = 1 then " " else "s ") ^
              commas_quote (sort_strings xs) ^ " in the action of production \<open>" ^
              string_of_prod lhs syms ^ "\<close>" ^ Position.here pos ^
              ": bind " ^ (if length xs = 1 then "it" else "them") ^
              " in the action, or fix " ^ (if length xs = 1 then "it" else "them") ^
              " in the context")));

    fun place (NeedCheck _) (t :: rest) = (t, rest)
      | place (NeedCheck _) [] =
          raise Fail "grammar: action reassembly ran out of terms"
      | place (Identity t) ts = (t, ts);

    val (actions_ordered, leftover) = fold_map place slots checked_terms;

    val _ = null leftover orelse
      raise Fail "grammar: action reassembly left over terms";

    val action_vec = Vector.fromList actions_ordered;

    fun default_ann NONE = Any
      | default_ann (SOME a) = a;

    datatype presym = PN of string | PC of term | PT of term;

    fun presym (Ref (n, pos), a) =
          if is_nt n then (PN n, default_ann a)
          else (PC (class_tok (n, pos)), default_ann a)
      | presym (Lit (s, pos), a) = (PT (lit_tok (s, pos)), default_ann a)
      | presym (Tok src, a) = (PT (inline_tok src), default_ann a);
    val pre_rhss = map (fn (_, _, syms, _, _) => map presym syms) prods_flat;

    val (terminals_rev, term_idx_tab) =
      let
        fun add t (acc, tab) =
          case Termtab.lookup tab t of
            SOME _ => (acc, tab)
          | NONE => (t :: acc, Termtab.update (t, length acc) tab);
        fun add_sym (PC t, _) = add t
          | add_sym (PT t, _) = add t
          | add_sym _ = I;
      in fold (fold add_sym) pre_rhss ([], Termtab.empty) end;
    (* two spellings of one token value (\<open>1\<close> and \<open>Suc 0\<close>) are one terminal,
       decided by evaluating the equality matrix; when the token type is not
       executable here the syntactic identification stands *)
    val terminals0 = rev terminals_rev;
    val (firsts, canonical) =
      let
        val n = length terminals0;
        fun mk_map aT bT f =
          Const (\<^const_name>\<open>List.map\<close>,
            (aT --> bT) --> HOLogic.listT aT --> HOLogic.listT bT) $ f;
        fun dest_bool \<^Const_>\<open>True\<close> = true
          | dest_bool \<^Const_>\<open>False\<close> = false
          | dest_bool t = raise TERM ("dest_bool", [t]);
        fun eq_matrix () =
          let
            val ts = HOLogic.mk_list tokT terminals0;
            val row =
              Abs ("t", tokT,
                mk_map tokT HOLogic.boolT
                  (Abs ("u", tokT, HOLogic.eq_const tokT $ Bound 1 $ Bound 0)) $ ts);
          in
            Value_Command.value lthy (mk_map tokT (HOLogic.listT HOLogic.boolT) row $ ts)
            |> HOLogic.dest_list |> map (map dest_bool o HOLogic.dest_list)
          end;
        val firsts =
          (case (if n < 2 then NONE else try eq_matrix ()) of
            NONE => 0 upto n - 1
          | SOME rows =>
              if length rows = n andalso forall (fn r => length r = n) rows
              then map (find_index I) rows else 0 upto n - 1);
        val canonical = filter (fn i => nth firsts i = i) (0 upto n - 1);
        val _ =
          (0 upto n - 1) |> List.app (fn i =>
            let val j = nth firsts i in
              if j = i then ()
              else
                warning ("grammar " ^ quote (Binding.name_of name) ^ ": the terminals \<open>" ^
                  Pretty.unformatted_string_of (Syntax.pretty_term lthy (nth terminals0 j)) ^
                  "\<close> and \<open>" ^
                  Pretty.unformatted_string_of (Syntax.pretty_term lthy (nth terminals0 i)) ^
                  "\<close> have the same token value; they are one terminal")
            end);
      in (firsts, canonical) end;
    fun canon_idx i = find_index (fn j => j = nth firsts i) canonical;
    val terminals_vec = Vector.fromList (map (nth terminals0) canonical);
    fun idx_of t =
      case Termtab.lookup term_idx_tab t of
        SOME i => canon_idx i
      | NONE => raise Fail "grammar: token missing from terminals vector";

    (** build prods and nonterms **)
    fun rhs_of pre =
      pre |> map
        (fn (PN n, a) => (RN n, a)
          | (PC t, a) => (RC (idx_of t), a)
          | (PT t, a) => (RT (idx_of t), a));

    val prods_full : prod list =
      map_index
        (fn (p_no, ((lhs, _, _, _, pos), pre_rhs)) =>
          {no = p_no, lhs = lhs, rhs = rhs_of pre_rhs,
           action = Vector.sub (action_vec, p_no), pos = pos})
        (prods_flat ~~ pre_rhss);

    val nt_prods_tab =
      fold (fn {no, lhs, ...}: prod => Symtab.cons_list (lhs, no))
        prods_full Symtab.empty
      |> Symtab.map (K rev);

    fun prods_of A = the_default [] (Symtab.lookup nt_prods_tab A);

    val nonterms_tab =
      productions
      |> map_index (fn (i, ((b, _), _)) =>
          let val nm = Binding.name_of b in
            (nm, {no = i, binding = b, carrier = carrier_of nm, prods = prods_of nm}
                  : nonterm)
          end)
      |> Symtab.make;

    (* the token value of each Fixed terminal with its spelling, for reports *)
    val lit_names_tab =
      map_filter (fn Fixed (spelling, src) => SOME (read_term_typed lthy tokT src, spelling)
                   | _ => NONE) terminal_decls;

    val grammar : grammar =
      {name = name,
       tokT = tokT,
       tokenT = tokenT,
       start = start,
       terminals = terminals_vec,
       lit_names = lit_names_tab,
       nonterms = nonterms_tab,
       prods = prods_full,
       artifacts = NONE};
  in (grammar, lthy) end;


(* terminals by token value *)
fun sym_key (RN n) = "N " ^ n
  | sym_key (RC i) = "T " ^ string_of_int i
  | sym_key (RT i) = "T " ^ string_of_int i;

(* duplicate productions: same lhs, same rhs *)
fun check_duplicate_prods (gram: Grammar_Common.grammar) =
  let
    fun key ({lhs, rhs, ...}: prod) =
      (lhs, map (fn (s, a) => (sym_key s, a)) rhs);
    fun check (p as {lhs, pos, ...}: prod) seen =
      if member (op =) seen (key p) then
        error ("Duplicate production for " ^ quote lhs ^
          ": the same right-hand side is listed twice" ^ Position.here pos)
      else key p :: seen;
  in ignore (fold check (#prods gram) []) end;

(* alternatives that differ only in their annotations: the decoder works on
   the erased tree and applies the action of the first one, so the actions
   must agree *)
fun check_shape_clash ctxt (gram: Grammar_Common.grammar) =
  let
    val gname = Binding.name_of (#name gram);
    fun shape ({lhs, rhs, ...}: prod) = (lhs, map (sym_key o fst) rhs);
    fun string_of_sym (RN n) = n
      | string_of_sym (RC i) = Syntax.string_of_term ctxt (Vector.sub (#terminals gram, i))
      | string_of_sym (RT i) = Syntax.string_of_term ctxt (Vector.sub (#terminals gram, i));
    fun string_of_prod ({lhs, rhs, ...}: prod) =
      lhs ^ " = " ^ space_implode " " (map (fn (s, a) => string_of_sym s ^ string_of_ann a) rhs);
    fun check (p: prod) seen =
      (case AList.lookup (op =) seen (shape p) of
        SOME (q: prod) =>
          if #action p aconv #action q then seen
          else
            error ("grammar " ^ quote gname ^ ": the alternatives \<open>" ^
              string_of_prod q ^ "\<close> and \<open>" ^ string_of_prod p ^
              "\<close> differ only in their indentation annotations but have \
              \different actions; the parser decodes the erased syntax tree, \
              \which does not record annotations, so it could not tell them \
              \apart.  Give them the same action, or distinguish their \
              \right-hand sides" ^ Position.here (#pos p))
      | NONE => (shape p, p) :: seen);
  in ignore (fold check (#prods gram) []) end;

(* unproductive / unreachable nonterminals, by fixpoint on the record *)
fun analyze_grammar (gram: Grammar_Common.grammar) =
  let
    val gname = Binding.name_of (#name gram);
    val prods = #prods gram;
    val nts = map fst (Grammar_Common.nonterms_list gram);
    fun nt_syms rhs = map_filter (fn (RN n, _) => SOME n | _ => NONE) rhs;
    fun lfp f x = let val x' = f x in if length x' = length x then x else lfp f x' end;
    fun prod_step productive =
      fold (fn ({lhs, rhs, ...}: prod) => fn acc =>
          if member (op =) acc lhs then acc
          else if forall (member (op =) acc) (nt_syms rhs) then lhs :: acc
          else acc)
        prods productive;
    val productive = lfp prod_step [];
    val unproductive = filter_out (member (op =) productive) nts;
    fun reach_step reachable =
      fold (fn ({lhs, rhs, ...}: prod) => fn acc =>
          if member (op =) acc lhs
          then fold (insert (op =)) (nt_syms rhs) acc else acc)
        prods reachable;
    val reachable = lfp reach_step [#start gram];
    val unreachable = filter_out (member (op =) reachable) nts;
    val _ =
      if member (op =) unproductive (#start gram) then
        warning ("grammar " ^ quote gname ^ ": the start symbol " ^
          quote (#start gram) ^ " derives no word - the language is empty \
          \and every parser theorem about this grammar holds vacuously")
      else ();
    val _ =
      (case filter_out (curry (op =) (#start gram)) unproductive of
        [] => ()
      | ds =>
          warning ("grammar " ^ quote gname ^ ": unproductive nonterminal(s) " ^
            commas_quote ds ^ " (they derive no word)"));
    val _ =
      (case unreachable of
        [] => ()
      | ds =>
          warning ("grammar " ^ quote gname ^ ": nonterminal(s) " ^
            commas_quote ds ^ " unreachable from the start symbol " ^
            quote (#start gram)));
  in () end;

(* check, elaborate, define; the artifacts are registered with the record *)
fun grammar_cmd opts (spec: spec) lthy =
  let
    val _ = Grammar_Common.check_spec spec;
    fun timed label f x = Grammar_Common.timed lthy (Binding.name_of (#name spec)) label f x;
    val (gr, lthy) = timed "elaborate" (elaborate spec) lthy;
    val _ = check_duplicate_prods gr;
    val _ = check_shape_clash lthy gr;
    val _ = analyze_grammar gr;
    val ((gram_t, gram_def), lthy) =
      timed "define_grammar" (Grammar_Defs.define_grammar gr) lthy;
    val (decs, lthy) = timed "define_decoders" (Grammar_Defs.define_decoders gr) lthy;
    val (rel, lthy) =
      if member (op =) opts Opt_Relation then
        Grammar_Defs.define_relation gr (gram_t, gram_def) decs lthy
        |>> (fn sem => SOME
              ({preds = #preds sem, intros = #intros sem,
                inducts = #inducts sem, sound_thms = #sound_thms sem}
               : Grammar_Common.rel_info))
      else (NONE, lthy);
    val gr' =
      Grammar_Common.put_artifacts
        {gram_t = gram_t, gram_def = gram_def, decs = decs, rel = rel} gr;
  in lthy |> Grammar_Common.register (#name gr) gr' end;

(** outer syntax **)

val annotation =
  (Parse.control -- (Parse.not_eof >> Token.content_of) :|--
    (fn (ctl, s) =>
      if #1 (#name ctl) = "sup" andalso null (#body ctl) then
        (case s of
          "=" => Scan.succeed Eq
        | "\<ge>" => Scan.succeed Ge
        | ">" => Scan.succeed Gt
        | "*" => Scan.succeed Any
        | _ => Scan.fail)
      else Scan.fail)) ||
  Parse.$$$ "^=" >> K Eq ||
  Parse.$$$ "^>=" >> K Ge ||
  Parse.$$$ "^>" >> K Gt ||
  Parse.$$$ "^*" >> K Any;

val gsym =
  Parse.position Parse.string >> Lit ||
  Parse.position Parse.name >> Ref ||
  Parse.input Parse.cartouche >> Tok;

val arrow_action =
  (Parse.$$$ "\<Rightarrow>" || Parse.$$$ "=>") |-- Parse.input Parse.term;

val alternative : alternative parser =
  Scan.repeat1 (gsym -- Scan.option annotation) -- Scan.option arrow_action ||
  arrow_action >> (fn a => ([], SOME a));

val terminal_decl : terminal_decl parser =
  Parse.string --| Parse.$$$ "=" -- Parse.input Parse.term >> Fixed ||
  Parse.binding >> Class;

val production_group : production_group parser =
  Parse.binding --
    Scan.option (Parse.$$$ "::" |-- Parse.input Parse.typ) --|
    Parse.$$$ "=" -- Parse.enum1 "|" alternative;

val option_name : gram_opt parser =
  Parse.position Parse.name >> (fn (s, pos) =>
    if s = "relation" then Opt_Relation
    else error ("Unknown grammar option: " ^ quote s ^ Position.here pos));

val options_parser =
  Parse.$$$ "(" |-- Parse.enum1 "," option_name --| Parse.$$$ ")";

val grammar_parser =
  Scan.optional options_parser [] --
  Parse.binding --| Parse.$$$ "=" --
  Scan.option (Parse.$$$ "tokens" |-- Parse.input Parse.typ) --
  Scan.optional (Parse.$$$ "terminals" |-- Parse.and_list1 terminal_decl) [] --
  (Parse.$$$ "productions" |-- Parse.and_list1 production_group);

val _ =
  Outer_Syntax.local_theory \<^command_keyword>\<open>grammar\<close>
    "validate a grammar spec: parse, type-check semantic actions and register the \
    \resolved grammar. Always defines the grammar constant and the per-nonterminal \
    \decoders. Option (relation) also defines the mutual inductive relation family \
    \(slower)."
    (grammar_parser >> (fn ((((opts, name), ttyp), ts), ps) =>
      grammar_cmd opts {name = name, tok_typ = ttyp, terminals = ts, productions = ps}));

end;
