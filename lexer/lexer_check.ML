(* Author: Basil Fürer *)

(* the test command lexer_check (grammar's tests/parser_check.ML, renamed): closed boolean
   terms evaluated in the ML compiler with the code of their constants compiled once per
   theory chain; and the diagnostic lex, which prints the tokens of a text *)

signature LEXER_CHECK =
sig
  val put_bool: (unit -> bool) -> Proof.context -> Proof.context
  val put_term: (unit -> term) -> Proof.context -> Proof.context
  val reflect: string list -> theory -> theory
  val eval: Proof.context -> term -> bool
  val value: Proof.context -> term -> term
  val verify: Proof.context -> term -> unit
  val check: string list -> theory -> theory
  val lex: Proof.context -> term -> Input.source -> Pretty.T
end;

structure Lexer_Check: LEXER_CHECK =
struct

(** compiled constants **)

(* the compiled constants with their ML names (NONE: not compiled, e.g. it takes
   dictionaries), the registered datatypes keyed "type:" ^ name, and a counter for the
   module names. Two theories that compiled different things may have registered the same
   datatype twice, and a merge keeps one of the two printings (Code_Symbol.merge_data):
   then nothing compiled before is kept. *)

structure Data = Theory_Data
(
  type T = string option Symtab.table * int;
  val empty = (Symtab.empty, 0);
  fun merge ((s1, n1), (s2, n2)) =
    let fun sub (a, b) = Symtab.forall (fn (k, v) => Symtab.lookup b k = SOME v) a in
      (if sub (s1, s2) then s2 else if sub (s2, s1) then s1 else Symtab.empty,
       Int.max (n1, n2))
    end;
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
  in
    Code_Target.set_printings (Code_Symbol.Type_Constructor (tyco, [(target, SOME (k, pr))]))
      thy
  end;

fun add_eval_constr (const, const') thy =
  let
    val k = Code.args_number thy const;
    fun pr pr' fxy ts = Code_Printer.brackify fxy
      (Pretty.str const' :: the_list (Code_Printer.tuplify pr' Code_Printer.BR (map fst ts)));
  in
    Code_Target.set_printings (Code_Symbol.Constant (const,
      [(target, SOME (Code_Printer.simple_const_syntax (k, pr)))])) thy
  end;

(* the statements a check can refer to: datatypes with their constructors, and functions
   without sort constraints (an argument gets no dictionaries) *)
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
        val module_name =
          "Lexer_Check_" ^ Context.theory_base_name thy ^ "_" ^ string_of_int n;
        val thy0 = Code_Target.add_reserved target module_name thy;
        val ctxt0 = Proof_Context.init_global thy0;
        val program = Code_Thingol.consts_program ctxt0 consts';
        val cands = candidates program;
        val (ml_modules, names) =
          Code_Target.produce_code_for ctxt0 target module_name NONE [] program false
            (map fst cands);
        val code = space_implode "\n\n" (map (Bytes.content o snd) ml_modules);
        val named =
          map_filter (fn ((sym, is_constr), SOME name) => SOME (sym, is_constr, name)
            | _ => NONE) (cands ~~ names);
        fun register (Code_Symbol.Type_Constructor tyco, _, name) = add_eval_tyco (tyco, name)
          | register (Code_Symbol.Constant c, true, name) = add_eval_constr (c, name)
          | register _ = I;
        val compiled =
          map_filter (fn (Code_Symbol.Constant c, false, name) => SOME (c, name) | _ => NONE)
            named;
        val tycos =
          map_filter (fn (Code_Symbol.Type_Constructor tyco, _, name) =>
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


(** evaluation: the compiled constants become arguments **)

structure Bool_Result = Proof_Data
(
  type T = unit -> bool;
  fun init _ () = raise Fail "lexer_check: no boolean result";
);

structure Term_Result = Proof_Data
(
  type T = unit -> term;
  fun init _ () = raise Fail "lexer_check: no term result";
);

val put_bool = Bool_Result.put;
val bool_cookie = (Bool_Result.get, put_bool, \<^unchecked_name>\<open>Lexer_Check.put_bool\<close>);
val put_term = Term_Result.put;
val term_cookie = (Term_Result.get, put_term, \<^unchecked_name>\<open>Lexer_Check.put_term\<close>);

(* t with its compiled constants abstracted (f applied to the body), and their ML names *)
fun abstract ctxt f t =
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
      |> f
      |> fold_rev lambda frees;
  in (t', map (fn (c, _) => the (the (Symtab.lookup done c))) cTs) end;

fun eval ctxt t =
  let val (t', args) = abstract ctxt I t
  in Code_Runtime.dynamic_value_strict bool_cookie ctxt NONE (K I) t' args end;

fun value ctxt t =
  let val (t', args) = abstract ctxt (fn u => HOLogic.mk_term_of (fastype_of u) u) t
  in Code_Runtime.dynamic_value_strict term_cookie ctxt NONE I t' args end;


(** lexer_check **)

fun verify ctxt t =
  if eval ctxt t then ()
  else
    let
      val lhs =
        (case t of
          Const (\<^const_name>\<open>HOL.eq\<close>, _) $ lhs $ _ =>
            [Pretty.fbrk, Pretty.str "where the left-hand side is", Pretty.brk 1,
              Syntax.pretty_term ctxt (value ctxt lhs)]
        | _ => []);
    in
      error (Pretty.string_of (Pretty.block
        ([Pretty.str "lexer_check failed:", Pretty.brk 1, Syntax.pretty_term ctxt t] @ lhs)))
    end;

fun check1 s thy =
  let
    val ctxt = Proof_Context.init_global thy;
    val t = Syntax.parse_term ctxt s |> Type.constraint HOLogic.boolT |> Syntax.check_term ctxt;
    val _ =
      if null (Term.add_frees t []) andalso null (Term.add_vars t []) then ()
      else error "lexer_check: the term has free variables";
    val thy' = reflect (Term.add_const_names t []) thy;
    val ctxt' = Proof_Context.init_global thy';
    (* the evaluation runs in a forked proof of True, as the proof of a lemma would, and
       the theory waits for it at its end *)
    val thm = Goal.prove_future ctxt' [] [] \<^prop>\<open>True\<close>
      (fn {context, ...} => (verify ctxt' t; resolve_tac context @{thms TrueI} 1));
  in Global_Theory.add_thms_lazy "" (Binding.empty, Lazy.value [thm]) thy' end;

fun check ss = fold check1 ss;

val _ =
  Outer_Syntax.command \<^command_keyword>\<open>lexer_check\<close>
    "evaluate closed boolean terms with cached code (tests only, proves nothing)"
    (Parse.enum1 "and" (Scan.repeat1 Parse.term) >> (fn ss => Toplevel.theory (check (flat ss))));


(** lex **)

fun utf8 c =
  if c < 0x80 then [c]
  else if c < 0x800 then [0xC0 + c div 0x40, 0x80 + c mod 0x40]
  else if c < 0x10000 then
    [0xE0 + c div 0x1000, 0x80 + c div 0x40 mod 0x40, 0x80 + c mod 0x40]
  else
    [0xF0 + c div 0x40000, 0x80 + c div 0x1000 mod 0x40, 0x80 + c div 0x40 mod 0x40,
     0x80 + c mod 0x40];

(* the input word of the lexer s for the symbols of a text (codepoints, or the bytes of
   their UTF-8 encoding), with the units of each symbol *)
fun input s syms =
  let val cps = map Pattern.codepoint syms in
    (case domain_type (fastype_of s) of
      Type (\<^type_name>\<open>list\<close>, [\<^typ>\<open>char\<close>]) =>
        (HOLogic.mk_list \<^typ>\<open>char\<close> (map HOLogic.mk_char (maps utf8 cps)),
         map (length o utf8) cps)
    | _ =>
        (HOLogic.mk_list HOLogic.natT (map (HOLogic.mk_number HOLogic.natT) cps),
         map (K 1) cps))
  end;

(* the predicate L.final of the lexer L_lex, if it is one *)
fun final_of ctxt (Const (c, _)) =
      (case try (unsuffix "_lex") c of
        SOME l =>
          (case Sign.const_type (Proof_Context.theory_of ctxt) (l ^ ".final") of
            SOME T => SOME (Const (l ^ ".final", T))
          | NONE => NONE)
      | NONE => NONE)
  | final_of _ _ = NONE;

fun dest_nat t = snd (HOLogic.dest_number t);

fun show_syms syms =
  quote (implode (map (fn ("\n", _) => "\\n" | ("\t", _) => "\\t" | ("\r", _) => "\\r"
    | ("\"", _) => "\\\"" | ("\\", _) => "\\\\" | (s, _) => s) syms));

fun lex ctxt s src =
  let
    val syms = Input.source_explode src;
    val (w, units) = input s syms;
    val starts = fst (fold_map (fn u => fn n => (n, n + u)) units 0);
    (* the symbols from unit a to unit b *)
    fun slice a b =
      let fun idx u = length (take_prefix (fn x => x < u) starts)
      in drop (idx a) (take (idx b) syms) end;
    val fin = final_of ctxt s;
    val summary =
      Syntax.check_term ctxt (Const (\<^const_name>\<open>lex_summary\<close>, dummyT) $ (s $ w) $
        the_default (Abs ("m", dummyT, \<^Const>\<open>False\<close>)) fin);
    val (h, (ts, (r, (st, top_final)))) =
      value ctxt summary
      |> HOLogic.dest_prod ||> HOLogic.dest_prod ||> apsnd HOLogic.dest_prod
      ||> apsnd (apsnd HOLogic.dest_prod)
      |> (fn (h, (ts, (r, (st, b)))) =>
        (dest_nat h, (HOLogic.dest_list ts, (dest_nat r, (st, b = \<^Const>\<open>True\<close>)))));
    val total = fold (curry op +) units 0;
    val str =
      Protocol_Message.clean_output o Pretty.unformatted_string_of o Syntax.pretty_term ctxt;
    fun token t =
      (case HOLogic.strip_tuple t of
        [k, line, col, off, len, triv] =>
          let
            val (a, b) = (dest_nat off, dest_nat off + dest_nat len);
            val lexeme = slice a b;
            val _ =
              if null lexeme then ()
              else
                Context_Position.report_text ctxt
                  (Position.range_position (Symbol_Pos.range lexeme)) Markup.typing (str k);
          in
            [str k, string_of_int (dest_nat line) ^ ":" ^ string_of_int (dest_nat col),
             show_syms lexeme, show_syms (slice b (b + dest_nat triv))]
          end
      | _ => raise TERM ("lex", [t]));
    val rows = map token ts;
    val width = fold (fn row => fn n => Int.max (n, size (hd row))) rows 0;
    fun line [k, lc, lexeme, triv] =
          Pretty.str (StringCvt.padRight #" " width k ^ "  " ^ StringCvt.padRight #" " 7 lc ^
            " " ^ lexeme ^ (if triv = "\"\"" then "" else "  trivia " ^ triv))
      | line _ = raise Fail "lex";
    val final_text =
      (case fin of
        NONE => ""
      | SOME _ => if top_final then " (the top is final)" else " (the top is not final)");
  in
    Pretty.chunks
      ((if h = 0 then [] else [Pretty.str ("header " ^ show_syms (slice 0 h))]) @
       map line rows @
       [Pretty.str ("residue " ^ show_syms (slice (total - r) total)),
        Pretty.block [Pretty.str "stack ", Syntax.pretty_term ctxt st,
          Pretty.str final_text]])
  end;

val _ =
  Outer_Syntax.command \<^command_keyword>\<open>lex\<close>
    "print the tokens of a text by a lexer of the lexer command"
    (Parse.term -- Parse.input Parse.cartouche >> (fn (s, src) =>
      Toplevel.keep (fn st =>
        let val ctxt = Toplevel.context_of st
        in Pretty.writeln (lex ctxt (Syntax.read_term ctxt s) src) end)));

end;
