(* Author: Basil Fürer *)

(* the grammar command: elaboration of a specification (terminals, productions,
   semantic actions, precedence) into the grammar record, then the definitions
   through Grammar_Defs; the outer syntax is in grammar_syntax.ML *)

signature GRAMMAR_COMMAND =
sig
  datatype gram_opt = Opt_Relation
  val grammar_cmd: gram_opt list -> Grammar_Common.spec -> local_theory -> local_theory
  val grammar_surface_cmd: gram_opt list -> Grammar_Common.surface -> local_theory -> local_theory
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

fun elaborate (exp: expansion)
    ({name, tok_typ, terminals = terminal_decls, productions, prec = own_prec, ...}: spec) lthy =
  let
    (** nonterminal tables **)
    val nnames = map (Binding.name_of o #1 o #1) productions;
    (* the generated nonterminals of templates and operators (Grammar_Expand) *)
    val gen_ident = AList.lookup (op =) (#generated exp);
    fun is_generated n = is_some (gen_ident n);
    fun is_silent n = member (op =) (#silent exp) n;
    val nt_bindings =
      filter_out (is_generated o Binding.name_of) (map (#1 o #1) productions);
    val nt_idx_tab =
      fold_index (fn (i, n) => Symtab.update (n, i)) nnames Symtab.empty;
    fun is_local n = Symtab.defined nt_idx_tab n;
    val start =
      (case nnames of n :: _ => n
       | [] => error ("grammar " ^ quote (Binding.name_of name) ^
                      " has no productions" ^ Position.here (Binding.pos_of name)));

    (** token type: a ground \<open>('tok, 'ch, 'more) token_scheme\<close> from the
      \<open>tokens\<close> clause; a type \<open>T\<close> that is not a token scheme abbreviates
      \<open>(T, unit) token\<close>, the default is \<open>(string, unit) token\<close> **)
    fun plain_token_type T =
      Type (\<^type_name>\<open>TIGER_Token.token_ext\<close>, [T, \<^typ>\<open>unit\<close>, \<^typ>\<open>unit\<close>]);
    val (tokT, tokenT) =
      (case tok_typ of
        NONE => (HOLogic.stringT, plain_token_type HOLogic.stringT)
      | SOME src =>
          let val T = Syntax.read_typ lthy (Syntax.implode_input src) in
            Term.exists_subtype (fn TFree _ => true | TVar _ => true | _ => false) T
              andalso error ("The ascribed token type is not ground" ^
                             Position.here (Input.pos_of src));
            (case T of
              Type (\<^type_name>\<open>TIGER_Token.token_ext\<close>, [tok, _, _]) => (tok, T)
            | _ => (T, plain_token_type T))
          end);

    datatype presym = PN of string | PC of term | PT of term;
    (* the type of \<open>@span\<close>: \<open>'ch span\<close> of the token type *)
    val spanT =
      (case tokenT of
        Type (_, [_, chT, _]) => Type (\<^type_name>\<open>TIGER_Token.span_ext\<close>, [chT, \<^typ>\<open>unit\<close>])
      | _ => raise Fail "grammar: token type");

    (** terminal-decl tables **)
    val fixed_tab =
      Symtab.make (map_filter (fn Fixed p => SOME p | _ => NONE) terminal_decls);
    val class_tab =
      Symtab.make_set
        (map_filter (fn Class b => SOME (Binding.name_of b) | _ => NONE) terminal_decls);

    fun source_of (n, pos) = Input.source false n (pos, pos);

    (** composition by reference: \<open>a.X\<close> names the nonterminal \<open>X\<close> of an earlier
      grammar \<open>a\<close>; the productions of \<open>a\<close> reachable from \<open>X\<close> are copied, under the
      names \<open>a.Y\<close> (a copy that \<open>a\<close> itself made, \<open>c.Z\<close>, keeps its name, so a
      nonterminal reached along two paths is copied once) **)
    val all_refs =
      productions |> maps (fn (_, alts) =>
        maps (map_filter (fn (Ref rp, _) => SOME rp | _ => NONE) o fst) alts);
    fun ext_ref (n, pos) =
      if is_local n orelse Symtab.defined class_tab n orelse not (Long_Name.is_qualified n)
      then NONE
      else
        (case try (check_grammar lthy) (Long_Name.qualifier n, pos) of
          NONE => NONE
        | SOME (full, gr: grammar) =>
            let val x = Long_Name.base_name n in
              if Symtab.defined (#nonterms gr) x andalso not (Long_Name.is_qualified x) then
                (if #tokenT gr = tokenT then ()
                 else error ("Nonterminal " ^ quote n ^ ": grammar " ^ quote full ^
                   " has the token type " ^ Syntax.string_of_typ lthy (#tokenT gr) ^
                   ", this grammar " ^ Syntax.string_of_typ lthy tokenT ^ Position.here pos);
                 SOME (n, (full, gr, x)))
              else if tokT <> HOLogic.stringT andalso
                is_some (try (read_term_typed lthy tokT) (source_of (n, pos))) then NONE
              else
                error ("Grammar " ^ quote full ^ " has no nonterminal " ^ quote x ^
                  " (a reference a.X names a nonterminal that a defines)" ^ Position.here pos)
            end);
    val ext_refs =
      fold (fn rp => fn acc =>
          if AList.defined (op =) acc (#1 rp) then acc
          else (case ext_ref rp of SOME e => acc @ [e] | NONE => acc))
        all_refs [];
    fun disp_name full m =
      if is_copy_name m then m else Long_Name.base_name full ^ "." ^ m;
    fun copy_ident full gr m =
      if is_copy_name m then ident_in gr m
      else Long_Name.base_name full ^ "_" ^ ident_in gr m;
    fun copy_sym (_: grammar) full (RN m, a) = (PN (disp_name full m), a)
      | copy_sym gr _ (RC i, a) = (PC (Vector.sub (#terminals gr, i)), a)
      | copy_sym gr _ (RT i, a) = (PT (Vector.sub (#terminals gr, i)), a);
    fun eq_presym ((PN m, a), (PN m', a')) = m = m' andalso a = a'
      | eq_presym ((PC t, a), (PC t', a')) = t aconv t' andalso a = a'
      | eq_presym ((PT t, a), (PT t', a')) = t aconv t' andalso a = a'
      | eq_presym _ = false;
    fun eq_copy_prod ((rhs, act, sp, _), (rhs', act', sp', _)) =
      eq_list eq_presym (rhs, rhs') andalso act aconv act' andalso sp = sp';
    (* (display name, (carrier, [(rhs, action, span, pos)])) in discovery order, and the
       source production numbers: (grammar, number) to the number among the copies *)
    fun visit pos (full, gr: grammar) m (copies, nos) =
      let
        val d = disp_name full m;
        val {carrier, prods = pnos, ...} = the (Symtab.lookup (#nonterms gr) m);
        val ps = map (nth (#prods gr)) pnos;
        val cps =
          map (fn {rhs, action, span, pos, ...} => (map (copy_sym gr full) rhs, action, span, pos)) ps;
        val kids = distinct (op =) (maps (fn {rhs, ...} =>
          map_filter (fn (RN k, _) => SOME k | _ => NONE) rhs) ps);
        fun number base nos =
          nos @ map2 (fn i => fn k => ((full, i), k)) pnos (base upto base + length pnos - 1);
      in
        (case AList.lookup (op =) copies d of
          SOME (carrier', cps', base, _) =>
            if carrier = carrier' andalso eq_list eq_copy_prod (cps, cps') then
              if null pnos orelse AList.defined (op =) nos (full, hd pnos) then (copies, nos)
              else fold (visit pos (full, gr)) kids (copies, number base nos)
            else
              error ("Nonterminal " ^ quote d ^ " is reached along two references with \
                \different productions (two grammars of one name?)" ^ Position.here pos)
        | NONE =>
            let
              val base = fold (fn (_, (_, cps, _, _)) => fn k => k + length cps) copies 0;
            in
              fold (visit pos (full, gr)) kids
                (copies @ [(d, (carrier, cps, base, copy_ident full gr m))], number base nos)
            end)
      end;
    val (copies, copy_nos) =
      fold (fn (n, (full, gr, x)) =>
          visit (the (AList.lookup (op =) all_refs n)) (full, gr) x)
        ext_refs ([], []);
    val cnames = map #1 copies;
    (* the identifier of each nonterminal in the defined constants *)
    val ident_tab =
      Symtab.make
        (map (fn n => (n, the_default n (gen_ident n))) nnames @
         map (fn (d, (_, _, _, i)) => (d, i)) copies);
    fun ident n = the_default (ident_of n) (Symtab.lookup ident_tab n);
    val _ =
      (case duplicates (op =) (map ident (nnames @ cnames)) of
        [] => ()
      | d :: _ =>
          error ("grammar " ^ quote (Binding.name_of name) ^ ": the nonterminals " ^
            commas_quote (filter (fn n => ident n = d) (nnames @ cnames)) ^
            " have one name " ^ quote d ^ " in the defined constants" ^
            Position.here (Binding.pos_of name)));
    val ext_tab = Symtab.make (map (fn (n, (full, _, x)) => (n, disp_name full x)) ext_refs);
    fun is_nt n = is_local n orelse Symtab.defined ext_tab n;
    fun nt_name n = if is_local n then n else the (Symtab.lookup ext_tab n);
    (* the fixed spellings of the copied productions' terminals travel with them *)
    val copy_terms =
      maps (fn (_, (_, cps, _, _)) => maps (fn (rhs, _, _, _) =>
        map_filter (fn (PC t, _) => SOME t | (PT t, _) => SOME t | _ => NONE) rhs) cps) copies;
    (* the spellings of a template of another grammar that this grammar does not
       declare are that grammar's *)
    val used_spellings =
      productions |> maps (fn (_, alts) =>
        maps (map_filter (fn (Lit (s, _), _) => SOME s | _ => NONE) o fst) alts);
    fun owner_lits acc =
      fold (fn owner => fn acc =>
          (case get_grammar_global (Proof_Context.theory_of lthy) owner of
            NONE => acc
          | SOME (gr: grammar) =>
              fold (fn (t, sp) => fn acc =>
                  if not (member (op =) used_spellings sp) orelse AList.defined (op =) acc sp
                    orelse Symtab.defined fixed_tab sp
                  then acc
                  else acc @ [(sp, (t, owner))])
                (#lit_names gr) acc))
        (#owners exp) acc;
    val inherited_lits =
      fold (fn (_, (full, gr: grammar, _)) => fn acc =>
          fold (fn (t, sp) => fn acc =>
              if not (member (op aconv) copy_terms t) then acc
              else
                (case AList.lookup (op =) acc sp of
                  NONE => acc @ [(sp, (t, full))]
                | SOME (t', full') =>
                    if t aconv t' then acc
                    else error ("The spelling " ^ quote sp ^ " is the token " ^
                      Syntax.string_of_term lthy t' ^ " in grammar " ^ quote full' ^ " and " ^
                      Syntax.string_of_term lthy t ^ " in grammar " ^ quote full ^
                      Position.here (Binding.pos_of name))))
            (#lit_names gr) acc)
        ext_refs []
      |> owner_lits;
    fun class_tok (n, pos) =
      if tokT = HOLogic.stringT then HOLogic.mk_string n
      else read_term_typed lthy tokT (source_of (n, pos));
    fun lit_tok (s, pos) =
      (case Symtab.lookup fixed_tab s of
        SOME src => read_term_typed lthy tokT src
      | NONE =>
          if AList.defined (op =) inherited_lits s then
            #1 (the (AList.lookup (op =) inherited_lits s))
          else if tokT = HOLogic.stringT then HOLogic.mk_string s
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
      if is_generated n then ()
      else if is_local n then report_nt_ref (n, pos)
      else if is_nt n then ()
      else if Symtab.defined class_tab n then ()
      else if class_parseable (n, pos) then ()
      else error ("Undeclared symbol " ^ quote n ^ ": neither a nonterminal of "
        ^ quote (Binding.name_of name) ^ ", a terminal in the terminals block, \
        \nor a value of type " ^ Syntax.string_of_typ lthy tokT
        ^ Position.here pos);
    fun check_lit (s, pos) =
      if Symtab.defined fixed_tab s orelse AList.defined (op =) inherited_lits s orelse
        tokT = HOLogic.stringT then ()
      else error ("Fixed spelling " ^ quote s ^ " has no token declaration in \
        \the terminals block, and the token type is not string"
        ^ Position.here pos);
    val _ =
      productions |> List.app (fn (_, alts) =>
        alts |> List.app (fn (syms, _) =>
          syms |> List.app
            (fn (Ref rp, _) => check_ref rp
              | (Lit lp, _) => check_lit lp
              | (Tok _, _) => ()
              | (Span pos, a) =>
                  if is_some a then
                    error ("@span is not a grammar symbol and takes no annotation" ^
                      Position.here pos)
                  else ())));
    val _ =
      productions |> List.app (fn ((b, _), alts) =>
        alts |> List.app (fn (syms, _) =>
          (case map_filter (fn (Span pos, _) => SOME pos | _ => NONE) syms of
            _ :: pos :: _ =>
              error ("Alternative for " ^ quote (Binding.name_of b) ^
                " has @span twice" ^ Position.here pos)
          | _ => ())));

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
    fun witness_name b = witness_prefix ^ ident (Binding.name_of b);
    (* an instance's ascription may have type variables, which are inferred *)
    fun is_pattern b = member (op =) (#patterns exp) (Binding.name_of b);
    fun read_pattern src =
      Syntax.read_typ lthy (Syntax.implode_input src)
      |> Term.map_atyps (fn TFree _ => dummyT | T => T);
    val witnesses_tab =
      productions
      |> map (fn ((b, opt_src), _) =>
          let val T =
            case opt_src of
              SOME src =>
                if is_pattern b then read_pattern src else read_carrier_type lthy (b, src)
            | NONE => dummyT
          in (Binding.name_of b, Free (witness_name b, T)) end)
      |> fold (fn (d, (T, _, _, _)) => cons (d, Free (witness_prefix ^ ident d, T))) copies
      |> Symtab.make;
    fun witness_of A = the (Symtab.lookup witnesses_tab A);

    fun value_arg (Ref (n, _)) =
          if is_nt n then
            (if is_silent (nt_name n) then NONE else SOME (witness_of (nt_name n)))
          else SOME (Free (class_prefix ^ n, tokenT))
      | value_arg (Lit _) = NONE
      | value_arg (Tok _) = NONE
      | value_arg (Span _) = SOME (Free (witness_prefix ^ "span", spanT));
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
      | string_of_sym (Tok src) = cartouche (Syntax.implode_input src)
      | string_of_sym (Span _) = "@span";
    fun string_of_prod lhs syms =
      lhs ^ " = " ^ space_implode " " (map (string_of_sym o fst) syms);
    fun value_syms syms =
      map_filter (fn (Ref (n, _), _) =>
          if is_nt n andalso is_silent (nt_name n) then NONE else SOME n
        | (Span _, _) => SOME "@span"
        | _ => NONE) syms;
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
      |> fold (fn n => replace_all (witness_prefix ^ ident n, n)) (nnames @ cnames);
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
          | NONE => error (what ^ ": " ^ unwitness msg)
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
        SOME src =>
          if is_pattern b then infer_carrier (b, NONE) else read_carrier_type lthy (b, src)
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
      |> fold (fn (d, (T, _, _, _)) => cons (d, T)) copies
      |> Symtab.make;
    fun carrier_of A = the (Symtab.lookup carrier_tab A);

    (** re-check every action against its concrete expected type: **)
    fun rhs_binding_types syms =
      syms |> map_filter
        (fn (Ref (n, _), _) =>
              if is_nt n then
                (if is_silent (nt_name n) then NONE else SOME (carrier_of (nt_name n)))
              else SOME tokenT
          | (Lit _, _) => NONE
          | (Tok _, _) => NONE
          | (Span _, _) => SOME spanT);

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

    fun presym (Ref (n, pos), a) =
          if is_nt n then SOME (PN (nt_name n), default_ann a)
          else SOME (PC (class_tok (n, pos)), default_ann a)
      | presym (Lit (s, pos), a) = SOME (PT (lit_tok (s, pos)), default_ann a)
      | presym (Tok src, a) = SOME (PT (inline_tok src), default_ann a)
      | presym (Span _, _) = NONE;
    val copy_prods =
      maps (fn (d, (_, cps, _, _)) => map (fn (rhs, act, sp, pos) => (d, rhs, act, sp, pos)) cps)
        copies;
    val pre_rhss =
      map (fn (_, _, syms, _, _) => map_filter presym syms) prods_flat @ map #2 copy_prods;

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

    (* the record's action takes a value for every nonterminal: one that binds nothing
       (Grammar_Expand's operators over symbols without values) is passed and dropped;
       the span of \<open>@span\<close> comes first, wherever the alternative writes it *)
    datatype slot = Silent of typ | Value of typ | Span_Slot;
    fun has_span syms = exists (fn (Span _, _) => true | _ => false) syms;
    fun full_action syms t =
      let
        val slots =
          syms |> map_filter
            (fn (Ref (n, _), _) =>
                  if is_nt n then
                    SOME (if is_silent (nt_name n) then Silent (carrier_of (nt_name n))
                      else Value (carrier_of (nt_name n)))
                  else SOME (Value tokenT)
              | (Span _, _) => SOME Span_Slot
              | _ => NONE);
        fun plain (Value _) = true
          | plain _ = false;
      in
        if forall plain slots then t
        else
          let
            val sp = Free ("_sp", spanT);
            val vs =
              map_index (fn (i, sl) =>
                (case sl of
                  Silent T => (NONE, SOME (Free ("_v" ^ string_of_int i, T)))
                | Value T =>
                    let val v = Free ("_v" ^ string_of_int i, T) in (SOME v, SOME v) end
                | Span_Slot => (SOME sp, NONE))) slots;
            val body = Term.betapplys (t, map_filter #1 vs);
            val lam = fold_rev (fn v => fn b => Term.lambda v b) (map_filter #2 vs) body;
          in if has_span syms then Term.lambda sp lam else lam end
      end;
    val prods_full : prod list =
      map_index
        (fn (p_no, ((lhs, action, span, pos), pre_rhs)) =>
          {no = p_no, lhs = lhs, rhs = rhs_of pre_rhs, action = action, span = span,
           pos = pos})
        ((map_index (fn (i, (lhs, _, syms, _, pos)) =>
              (lhs, full_action syms (Vector.sub (action_vec, i)), has_span syms, pos))
            prods_flat @
          map (fn (d, _, act, sp, pos) => (d, act, sp, pos)) copy_prods) ~~ pre_rhss);

    (* \<open>@span\<close> needs a first token: an alternative with it must have a symbol that
       derives no empty word *)
    val _ =
      if not (exists (fn {span, ...}: prod => span) prods_full) then ()
      else
        let
          fun derives_empty nl ({rhs, ...}: prod) =
            forall (fn (RN n, _) => member (op =) nl n | _ => false) rhs;
          fun fix nl =
            let
              val nl' =
                fold (fn p as {lhs, ...}: prod => fn acc =>
                    if member (op =) acc lhs orelse not (derives_empty acc p) then acc
                    else lhs :: acc)
                  prods_full nl;
            in if length nl' = length nl then nl else fix nl' end;
          val nullable = fix [];
        in
          (prods_full ~~ (map SOME prods_flat @ map (K NONE) copy_prods)) |> List.app
            (fn (p as {span = true, ...}: prod, SOME (lhs, _, syms, _, _)) =>
                if derives_empty nullable p then
                  error ("@span in an alternative whose yield can be empty, \<open>" ^
                    string_of_prod lhs syms ^ "\<close>: it has no first token; @span needs a \
                    \symbol that derives no empty word" ^
                    Position.here
                      (the_default (#pos p)
                        (get_first (fn (Span pos, _) => SOME pos | _ => NONE) syms)))
                else ()
              | _ => ())
        end;

    val nt_prods_tab =
      fold (fn {no, lhs, ...}: prod => Symtab.cons_list (lhs, no))
        prods_full Symtab.empty
      |> Symtab.map (K rev);

    fun prods_of A = the_default [] (Symtab.lookup nt_prods_tab A);

    val nonterms_tab =
      productions
      |> map_index (fn (i, ((b, _), _)) =>
          let
            val nm = Binding.name_of b;
            val b' = if is_generated nm then Binding.name (ident nm) else b;
          in
            (nm, {no = i, binding = b', carrier = carrier_of nm, prods = prods_of nm}
                  : nonterm)
          end)
      |> fold (fn (j, d) =>
          cons (d, {no = length productions + j, binding = Binding.name (ident d),
            carrier = carrier_of d, prods = prods_of d} : nonterm)) (map_index I cnames)
      |> Symtab.make;

    (* the token value of each Fixed terminal with its spelling, for reports *)
    val own_lits =
      map_filter (fn Fixed (spelling, src) => SOME (read_term_typed lthy tokT src, spelling)
                   | _ => NONE) terminal_decls;
    val _ =
      inherited_lits |> List.app (fn (sp, (t, full)) =>
        (case AList.lookup (op =) (map swap own_lits) sp of
          SOME t' =>
            if t aconv t' then ()
            else error ("The spelling " ^ quote sp ^ " is the token " ^
              Syntax.string_of_term lthy t' ^ " here and " ^ Syntax.string_of_term lthy t ^
              " in grammar " ^ quote full ^ Position.here (Binding.pos_of name))
        | NONE => ()));
    val lit_names_tab =
      own_lits @ map_filter (fn (sp, (t, _)) =>
        if exists (fn (t', sp') => t aconv t' andalso sp = sp') own_lits then NONE
        else SOME (t, sp)) inherited_lits;

    (* the precedence declarations of the copied productions, renumbered *)
    val nown = length prods_flat;
    fun remap_prec (full, gr: grammar) =
      (case #prec gr of
        NONE => ([], [])
      | SOME {chains, forbids} =>
          let
            fun m i = Option.map (fn k => nown + k) (AList.lookup (op =) copy_nos (full, i));
            val chains' =
              chains
              |> map (map_filter (fn (assoc, ps) =>
                  (case map_filter (fn (i, st) => Option.map (rpair st) (m i)) ps of
                    [] => NONE
                  | ps' => SOME (assoc, ps'))))
              |> filter_out null;
            val forbids' =
              forbids |> map_filter (fn (p, k, kind, c) =>
                (case (m p, m c) of
                  (SOME p', SOME c') => SOME (p', k, kind, c')
                | _ => NONE));
          in (chains', forbids') end);
    val copied_prec =
      (case
        fold (fn (_, (full, gr, _)) => fn (cs, fs) =>
            let val (cs', fs') = remap_prec (full, gr)
            in (merge (op =) (cs, cs'), merge (op =) (fs, fs')) end)
          ext_refs ([], []) of
        ([], []) => NONE
      | (cs, fs) => SOME {chains = cs, forbids = fs});

    val grammar : grammar =
      {name = name,
       tokT = tokT,
       tokenT = tokenT,
       start = start,
       (* the restriction of LR_Prec builds names: strings only *)
       nat_labels =
         Config.get lthy Grammar_Common.nat_labels andalso is_none own_prec andalso
           is_none copied_prec,
       terminals = terminals_vec,
       lit_names = lit_names_tab,
       nonterms = nonterms_tab,
       prods = prods_full,
       prec = copied_prec,
       artifacts = NONE};

    (* per referenced grammar: the nonterminals named, and its productions with their
       numbers here *)
    val links =
      fold (fn (_, (full, gr, x)) => fn acc =>
          (case AList.lookup (op =) acc full of
            SOME (gr, xs) => AList.update (op =) (full, (gr, xs @ [x])) acc
          | NONE => acc @ [(full, (gr, [x]))]))
        ext_refs []
      |> map (fn (full, (gr, xs)) =>
          (full, gr, distinct (op =) xs,
           map_filter (fn ((f, i), k) => if f = full then SOME (i, nown + k) else NONE)
             copy_nos));
  in ((grammar, links), lthy) end;


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

(** precedence declarations: names to production numbers **)

fun terminal_name (gr: Grammar_Common.grammar) i =
  let val t = Vector.sub (#terminals gr, i) in
    (case AList.lookup (op aconv) (#lit_names gr) t of
      SOME s => SOME s
    | NONE => (case t of Const (c, _) => SOME (Long_Name.base_name c) | _ => NONE))
  end;

(* the name a production goes by: its (prec NAME), else its last terminal *)
fun prod_key gr mark ({rhs, ...}: Grammar_Common.prod) =
  (case mark of
    SOME (n, _) => SOME n
  | NONE =>
      get_first
        (fn (Grammar_Common.RC i, _) => terminal_name gr i
          | (Grammar_Common.RT i, _) => terminal_name gr i
          | _ => NONE) (rev rhs));

(* the lines merge: items of one level stay together, and the order is the
   transitive closure of the lines; levels are numbers from here on *)
fun resolve_levels msg (chains: Grammar_Common.prec_level list list) =
  let
    fun err s pos = error (msg s pos);
    val levels = flat chains;
    fun names (_, items) = map (#1 o #1) items;
    fun add names gs =
      let val (hit, rest) = List.partition (exists (member (op =) names)) gs
      in distinct (op =) (flat hit @ names) :: rest end;
    val groups = rev (fold (add o names) levels []);
    fun group_of n = find_index (fn g => member (op =) g n) groups;
    fun level_group l = group_of (hd (names l));
    val n = length groups;
    fun assoc_of g =
      (case distinct (op =) (map_filter (fn l as ((a, _), _) =>
          if level_group l = g then SOME a else NONE) levels) of
        [a] => a
      | a :: b :: _ =>
          err ("the level of " ^ commas_quote (nth groups g) ^ " is both " ^ a ^ " and " ^ b)
            Position.none
      | [] => raise Fail "resolve_levels");
    val edges =
      maps (fn ch => map2 (fn hi => fn lo => (level_group hi, level_group lo))
        (take (length ch - 1) ch) (drop 1 ch)) chains;
    fun below seen g =
      fold (fn (a, b) => fn s => if a = g andalso not (member (op =) s b) then below (b :: s) b else s)
        edges seen;
    val belows = map (below []) (0 upto n - 1);
    val _ =
      (0 upto n - 1) |> List.app (fn g =>
        if member (op =) (nth belows g) g then
          err ("the precedences are cyclic through " ^ commas_quote (nth groups g)) Position.none
        else ());
    fun gt a b = member (op =) (nth belows a) b;
    fun comparable a b = a = b orelse gt a b orelse gt b a;
    (* loosest first: a level comes after everything below it *)
    val order = sort (int_ord o apply2 (length o nth belows)) (0 upto n - 1);
    val pairs = maps (fn a => map_filter (fn b => if gt a b then SOME (a, b) else NONE) order) order;
    fun cover [] acc = rev acc
      | cover ((a, b) :: rest) acc =
          let
            val chain =
              fold (fn g => fn ch => if forall (comparable g) ch then insert (op =) g ch else ch)
                order [a, b];
            val ordered = filter (member (op =) chain) order;
            val uncovered =
              filter_out (fn (x, y) => member (op =) chain x andalso member (op =) chain y) rest;
          in cover uncovered (ordered :: acc) end;
    val covered = cover pairs [];
    val alone = filter_out (fn g => exists (fn ch => member (op =) ch g) covered) order;
    val all_chains =
      if forall (fn a => forall (comparable a) order) order then [order]
      else covered @ map single alone;
  in (groups, assoc_of, all_chains) end;

fun resolve_prec (spec: spec) (gr: Grammar_Common.grammar) =
  (case #prec spec of
    NONE => gr
  | SOME {chains, forbids, alts} =>
      let
        val gname = Binding.name_of (#name gr);
        fun message s pos = "grammar " ^ quote gname ^ ": " ^ s ^ Position.here pos;
        fun err s pos = error (message s pos);
        val prods = #prods gr;
        val own = take (length alts) prods;
        val keys = map2 (prod_key gr) alts own;
        fun prods_of n =
          map_filter I (map2 (fn k => fn ({no, ...}: Grammar_Common.prod) =>
            if k = SOME n then SOME no else NONE) keys own);
        fun prods_at (n, pos) =
          (case prods_of n of
            [] => err ("no production goes by " ^ quote n ^
              " (a production goes by its (prec NAME), else its last terminal)") pos
          | ps => ps);
        val _ =
          (case filter (fn {lhs, rhs, ...}: Grammar_Common.prod =>
              (case rhs of [(Grammar_Common.RN m, _)] => m = lhs | _ => false)) prods of
            {lhs, pos, ...} :: _ =>
              err ("the production " ^ lhs ^ " = " ^ lhs ^ " cannot have declarations") pos
          | [] => ());
        val items =
          maps (maps (fn (_, its) => its)) chains;
        val (groups, assoc_of, numbered) = resolve_levels message chains;
        fun strict n = exists (fn ((m, _), s) => m = n andalso s) items;
        fun pos_of n =
          (case find_first (fn ((m, _), _) => m = n) items of
            SOME ((_, p), _) => p
          | NONE => Position.none);
        fun level g =
          (assoc_of g,
           maps (fn n => map (rpair (strict n)) (prods_at (n, pos_of n))) (nth groups g));
        fun forbid ((p, pos), k, (kind, kpos), cs) =
          let
            val _ =
              member (op =) ["direct", "left", "right"] kind orelse
                err ("forbid: " ^ quote kind ^ " is not one of direct, left, right") kpos;
          in
            maps (fn pn =>
              let
                val {rhs, ...} = nth prods pn;
                val _ =
                  k < length rhs orelse
                    err ("forbid: position " ^ string_of_int k ^ " of a production with " ^
                      string_of_int (length rhs) ^ " symbols") pos;
              in
                maps (fn c => map (fn cn => (pn, k, kind, cn)) (prods_at c)) cs
              end) (prods_at (p, pos))
          end;
        val (cs0, fs0) =
          (case #prec gr of SOME {chains, forbids} => (chains, forbids) | NONE => ([], []));
      in
        Grammar_Common.put_prec
          (SOME {chains = map (map level) numbered @ cs0, forbids = maps forbid forbids @ fs0}) gr
      end);

(* the link theorems of composition by reference: for a nonterminal X of an earlier
   grammar a used here as a.X, \<open>b_a_X i w x \<longleftrightarrow> a_X i w x\<close>, by induction over the
   copied components in both directions, lower components first; the case of a
   production is the other relation's intro of the same production *)
fun prove_link_dir ctxt insensitive wordT carrier_of comps src_pred tgt_pred
    induct_of prod_lhss intro_of =
  let
    val zero = \<^term>\<open>0 :: nat\<close>;
    fun app pred i w x = if insensitive then pred $ w $ x else pred $ i $ w $ x;
    fun p_index nm =
      if nm = "P" then SOME 0
      else if String.isPrefix "P" nm then Int.fromString (unprefix "P" nm)
      else NONE;
    fun prove_nt names lowers A =
      let
        val (i_n, w_n, x_n) =
          (case fst (Variable.variant_fixes ["i", "w", "x"] ctxt) of
            [i, w, x] => (i, w, x)
          | _ => raise Fail "prove_link_dir");
        val i = if insensitive then zero else Free (i_n, HOLogic.natT);
        val w = Free (w_n, wordT);
        val x = Free (x_n, carrier_of A);
        val goal =
          Logic.mk_implies (HOLogic.mk_Trueprop (app (src_pred A) i w x),
            HOLogic.mk_Trueprop (app (tgt_pred A) i w x));
        val induct = induct_of A;
        val p_vars =
          Term.add_vars (Thm.prop_of induct) []
          |> filter (is_some o p_index o #1 o #1)
          |> sort (int_ord o apply2 (the o p_index o #1 o #1));
        fun lam B =
          let
            val i' = Free ("__i", HOLogic.natT);
            val w' = Free ("__w", wordT);
            val x' = Free ("__x", carrier_of B);
            val l = Term.lambda w' (Term.lambda x' (app (tgt_pred B) i' w' x'));
          in if insensitive then l else Term.lambda i' l end;
        val induct' =
          Drule.infer_instantiate ctxt
            (map2 (fn (v, _) => fn B => (v, Thm.cterm_of ctxt (lam B))) p_vars names) induct;
        val idxs =
          map_filter (fn (k, B) => if member (op =) names B then SOME k else NONE)
            (map_index I prod_lhss);
        fun case_tac context k =
          resolve_tac context [intro_of k] THEN_ALL_NEW
            (assume_tac context ORELSE' (resolve_tac context lowers THEN' assume_tac context));
        val fixes = if insensitive then [w_n, x_n] else [i_n, w_n, x_n];
      in
        Goal.prove ctxt fixes [] goal (fn {context, ...} =>
          HEADGOAL (eresolve_tac context [induct'])
          THEN Grammar_Common.PARALLEL_CASES (map (case_tac context) idxs) 1)
      end;
    fun step names (lowers, results) =
      let val ths = map (prove_nt names lowers) names
      in (lowers @ ths, results @ (names ~~ ths)) end;
  in #2 (fold step comps ([], [])) end;

fun prove_links lthy (gr: grammar) (rel_b: rel_info) links =
  links |> maps (fn (full, ga: grammar, xs, nos) =>
    (case Grammar_Defs.lookup_rel lthy ga of
      NONE => []
    | SOME rel_a =>
        let
          val insensitive = Grammar_Defs.is_indent_insensitive gr;
        in
          if Grammar_Defs.is_indent_insensitive ga <> insensitive then []
          else
            let
              val base = Long_Name.base_name full;
              fun b_name m = if Long_Name.is_qualified m then m else base ^ "." ^ m;
              val a_names = map #1 (nonterms_list ga);
              val b_names = map #1 (nonterms_list gr);
              val k_of = AList.lookup (op =) nos;
              val i_of = AList.lookup (op =) (map swap nos);
              val fam_a =
                filter (fn m => exists (is_some o k_of)
                  (#prods (the (Symtab.lookup (#nonterms ga) m)))) a_names;
              val fam_b = map b_name fam_a;
              val a_of = the o AList.lookup (op =) (fam_b ~~ fam_a);
              val wordT = #wordT (get_desc gr);
              fun pred_b d = the (AList.lookup (op =) (#preds rel_b) d);
              fun pred_a m = the (AList.lookup (op =) (#preds rel_a) m);
              fun induct_of names (rel: rel_info) A =
                nth (#inducts rel) (find_index (curry (op =) A) names);
              val to_a =
                prove_link_dir lthy insensitive wordT (carrier_of gr)
                  (filter (fn c => member (op =) fam_b (hd c)) (Grammar_Defs.components gr))
                  pred_b (pred_a o a_of) (induct_of b_names rel_b) (map #lhs (#prods gr))
                  (fn k => nth (#intros rel_a) (the (i_of k)));
              val to_b =
                prove_link_dir lthy insensitive wordT (carrier_of ga)
                  (filter (fn c => member (op =) fam_a (hd c)) (Grammar_Defs.components ga))
                  pred_a (pred_b o b_name) (induct_of a_names rel_a) (map #lhs (#prods ga))
                  (fn i => nth (#intros rel_b) (the (k_of i)));
              fun iff x =
                let
                  val d = b_name x;
                  val th1 = the (AList.lookup (op =) to_a d);
                  val th2 = the (AList.lookup (op =) to_b x);
                  val (i_n, w_n, x_n) =
                    (case fst (Variable.variant_fixes ["i", "w", "x"] lthy) of
                      [i, w, x] => (i, w, x)
                    | _ => raise Fail "prove_links");
                  val i = Free (i_n, HOLogic.natT);
                  val w = Free (w_n, wordT);
                  val v = Free (x_n, carrier_of gr d);
                  fun app pred = if insensitive then pred $ w $ v else pred $ i $ w $ v;
                  val goal =
                    HOLogic.mk_Trueprop (HOLogic.mk_eq (app (pred_b d), app (pred_a x)));
                  val fixes = if insensitive then [w_n, x_n] else [i_n, w_n, x_n];
                  val th =
                    Goal.prove lthy fixes [] goal (fn {context, ...} =>
                      HEADGOAL (resolve_tac context @{thms iffI}) THEN
                      HEADGOAL (eresolve_tac context [th1]) THEN
                      HEADGOAL (eresolve_tac context [th2]));
                in
                  (Binding.qualify true (Binding.name_of (#name gr))
                    (Binding.name (ident_in gr d ^ "_iff")), th)
                end;
            in map iff xs end
        end));

(* check, elaborate, define; the artifacts are registered with the record *)
fun grammar_exp_cmd opts (exp: expansion) (spec: spec) lthy =
  let
    val _ =
      Grammar_Common.check_spec
        {name = #name spec, tok_typ = #tok_typ spec, terminals = #terminals spec,
         productions =
           filter_out (fn ((b, _), _) =>
             AList.defined (op =) (#generated exp) (Binding.name_of b)) (#productions spec),
         prec = #prec spec};
    fun timed label f x = Grammar_Common.timed lthy (Binding.name_of (#name spec)) label f x;
    val ((gr, links), lthy) = timed "elaborate" (elaborate exp spec) lthy;
    val gr = resolve_prec spec gr;
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
    val lthy =
      (case rel of
        NONE => lthy
      | SOME rel_b =>
          let val ths = timed "link theorems" (prove_links lthy gr rel_b) links in
            if null ths then lthy
            else #2 (Local_Theory.notes (map (fn (b, th) => ((b, []), [([th], [])])) ths) lthy)
          end);
    val gr' =
      Grammar_Common.put_artifacts
        {gram_t = gram_t, gram_def = gram_def, decs = decs, rel = rel, restricted = NONE} gr;
  in lthy |> Grammar_Common.register (#name gr) gr' end;

(* a spec without templates and operators, as built in ML *)
fun grammar_cmd opts spec = grammar_exp_cmd opts Grammar_Common.no_expansion spec;

(* templates and operators expand to an ordinary spec; a grammar of templates only
   registers them and defines nothing *)
fun grammar_surface_cmd opts (surf: surface) lthy =
  let
    val (res, templates) = Grammar_Expand.expand lthy surf;
    val lthy = Grammar_Expand.register_templates templates lthy;
  in
    (case res of
      NONE =>
        (if null opts then lthy
         else error ("grammar " ^ quote (Binding.name_of (#name surf)) ^
           " has templates only; an option has nothing to define" ^
           Position.here (Binding.pos_of (#name surf))))
    | SOME (spec, exp) => grammar_exp_cmd opts exp spec lthy)
  end;

end;
