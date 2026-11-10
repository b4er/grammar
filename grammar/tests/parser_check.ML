(*  Title:      tests/parser_check.ML

The test command parser_check: a closed boolean term is evaluated in the ML
compiler, like "by eval", but proves nothing.

"by eval" generates, compiles and runs the code of the whole term each time, so
every check of a parser computes the parser's tables again, and the code
preprocessor's cache lives only as long as one theory version.  Here the first
check that mentions a constant compiles the constant's program (functions and
datatypes) into an ML structure of the theory and registers the datatypes for
the evaluation target, as code_reflect does.  A check then abstracts the
compiled constants out of its term, so that only the remaining small term goes
through the code generator, and applies the result to the compiled values.
*)

signature PARSER_CHECK =
sig
  val put_bool: (unit -> bool) -> Proof.context -> Proof.context
  val reflect: string list -> theory -> theory
  val eval: Proof.context -> term -> bool
  val check: string list -> theory -> theory
end;

structure Parser_Check : PARSER_CHECK =
struct

(* the compiled constants with their ML names (NONE: not compiled, e.g. it takes
   dictionaries) and the registered datatypes, keyed "type:" ^ name, and a counter
   for the module names.  Two theories that compiled different things may have
   registered the same datatype twice, and a merge keeps one of the two printings
   (Code_Symbol.merge_data): then nothing compiled before is kept. *)

structure Data = Theory_Data
(
  type T = string option Symtab.table * int;
  val empty = (Symtab.empty, 0);
  fun merge ((s1, n1), (s2, n2)) =
    let fun sub (a, b) = Symtab.forall (fn (k, v) => Symtab.lookup b k = SOME v) a
    in (if sub (s1, s2) then s2 else if sub (s2, s1) then s1 else Symtab.empty, Int.max (n1, n2)) end;
);

fun type_key tyco = "type:" ^ tyco;

val target = Code_Runtime.target;

fun add_eval_tyco (tyco, tyco') thy =
  let
    val k = Sign.arity_number thy tyco;
    fun pr _ _ [] = Pretty.str tyco'
      | pr pr' _ [ty] = Code_Printer.concat [pr' Code_Printer.BR ty, Pretty.str tyco']
      | pr pr' _ tys =
          Code_Printer.concat [Pretty.enum "," "(" ")" (map (pr' Code_Printer.BR) tys),
            Pretty.str tyco'];
  in Code_Target.set_printings (Code_Symbol.Type_Constructor (tyco, [(target, SOME (k, pr))])) thy end;

fun add_eval_constr (const, const') thy =
  let
    val k = Code.args_number thy const;
    fun pr pr' fxy ts = Code_Printer.brackify fxy
      (Pretty.str const' :: the_list (Code_Printer.tuplify pr' Code_Printer.BR (map fst ts)));
  in
    Code_Target.set_printings (Code_Symbol.Constant (const,
      [(target, SOME (Code_Printer.simple_const_syntax (k, pr)))])) thy
  end;

(* the statements a check can refer to: datatypes with their constructors, and
   functions without sort constraints (an argument gets no dictionaries) *)

fun candidates program =
  let
    fun cand (sym as Code_Symbol.Type_Constructor _) =
          (case Code_Symbol.Graph.get_node program sym of
            Code_Thingol.Datatype _ => SOME (sym, false)
          | _ => NONE)
      | cand (sym as Code_Symbol.Constant _) =
          (case Code_Symbol.Graph.get_node program sym of
            stmt as Code_Thingol.Fun (((vs, _), _), _) =>
              if forall (null o snd) vs andalso not (Code_Thingol.is_case stmt)
              then SOME (sym, false) else NONE
          | Code_Thingol.Datatypecons _ => SOME (sym, true)
          | _ => NONE)
      | cand _ = NONE;
  in map_filter cand (Code_Symbol.Graph.keys program) end;

fun reflect consts thy =
  let
    val (done, n) = Data.get thy;
    val consts' = filter_out (Symtab.defined done) consts;
  in
    if null consts' then thy
    else
      let
        val module_name = "Parser_Check_" ^ Context.theory_base_name thy ^ "_" ^ string_of_int n;
        val thy0 = Code_Target.add_reserved target module_name thy;
        val ctxt0 = Proof_Context.init_global thy0;
        val program = Code_Thingol.consts_program ctxt0 consts';
        val cands = candidates program;
        val (ml_modules, names) =
          Code_Target.produce_code_for ctxt0 target module_name NONE [] program false
            (map fst cands);
        val code = space_implode "\n\n" (map (Bytes.content o snd) ml_modules);
        val named = map_filter (fn ((sym, is_constr), SOME name) => SOME (sym, is_constr, name)
          | _ => NONE) (cands ~~ names);
        fun register (Code_Symbol.Type_Constructor tyco, _, name) = add_eval_tyco (tyco, name)
          | register (Code_Symbol.Constant c, true, name) = add_eval_constr (c, name)
          | register _ = I;
        val compiled = map_filter (fn (Code_Symbol.Constant c, false, name) => SOME (c, name)
          | _ => NONE) named;
        val tycos = map_filter (fn (Code_Symbol.Type_Constructor tyco, _, name) =>
            SOME (type_key tyco, SOME name) | _ => NONE) named;
        val done' = done
          |> fold Symtab.update tycos
          |> fold (fn c => Symtab.default (c, NONE)) consts'
          |> fold (fn (c, name) => Symtab.update (c, SOME name)) compiled;
      in
        thy0
        |> Context.theory_map (ML_Context.exec (fn () =>
            ML_Compiler0.ML ML_Env.context
              {line = 0, file = "generated code", verbose = false, debug = false} code))
        |> fold register named
        |> Data.put (done', n + 1)
      end
  end;

(* evaluation: the compiled constants become arguments *)

structure Bool_Result = Proof_Data
(
  type T = unit -> bool;
  fun init _ () = raise Fail "Parser_Check.Bool_Result";
);

val put_bool = Bool_Result.put;
val cookie = (Bool_Result.get, put_bool, "Parser_Check.put_bool");

fun eval ctxt t =
  let
    val (done, _) = Data.get (Proof_Context.theory_of ctxt);
    val cTs = Term.add_consts t []
      |> filter (fn (c, _) => is_some (the_default NONE (Symtab.lookup done c)));
    val xs = Name.variant_list (Term.add_free_names t [])
      (map (fn (c, _) => "x_" ^ Name.desymbolize NONE (Long_Name.base_name c)) cTs);
    val frees = map2 (fn x => fn (_, T) => Free (x, T)) xs cTs;
    val t' = t
      |> Term.map_aterms (fn u as Const cT =>
            (case AList.lookup (op =) (cTs ~~ frees) cT of SOME v => v | NONE => u)
          | u => u)
      |> fold_rev lambda frees;
    val args = map (fn (c, _) => the (the (Symtab.lookup done c))) cTs;
  in Code_Runtime.dynamic_value_strict cookie ctxt NONE (K I) t' args end;

(* a check *)

fun check1 s thy =
  let
    val ctxt = Proof_Context.init_global thy;
    val t = Syntax.parse_term ctxt s |> Type.constraint HOLogic.boolT |> Syntax.check_term ctxt;
    val _ = if null (Term.add_frees t []) andalso null (Term.add_vars t []) then ()
      else error "parser_check: the term has free variables";
    val thy' = reflect (Term.add_const_names t []) thy;
    val ctxt' = Proof_Context.init_global thy';
    fun verify () =
      if eval ctxt' t then ()
      else
        let
          val value = (case t of
              Const (\<^const_name>\<open>HOL.eq\<close>, _) $ lhs $ _ =>
                [Pretty.fbrk, Pretty.str "where the left-hand side is", Pretty.brk 1,
                  Syntax.pretty_term ctxt' (Code_Evaluation.dynamic_value_strict ctxt' lhs)]
            | _ => []);
        in
          error (Pretty.string_of (Pretty.block
            ([Pretty.str "parser_check failed:", Pretty.brk 1, Syntax.pretty_term ctxt t] @ value)))
        end;
    (* the evaluation runs in a forked proof of True, as the proof of a lemma would,
       and the theory waits for it at its end *)
    val thm = Goal.prove_future ctxt' [] [] \<^prop>\<open>True\<close>
      (fn {context, ...} => (verify (); resolve_tac context @{thms TrueI} 1));
  in Global_Theory.add_thms_lazy "" (Binding.empty, Lazy.value [thm]) thy' end;

fun check ss = fold check1 ss;

val _ =
  Outer_Syntax.command \<^command_keyword>\<open>parser_check\<close>
    "evaluate closed boolean terms with cached code (tests only, proves nothing)"
    (Parse.enum1 "and" (Scan.repeat1 Parse.term) >> (fn ss => Toplevel.theory (check (flat ss))));

end;
