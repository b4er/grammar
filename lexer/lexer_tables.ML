(* Author: Basil Fürer, Claude *)

(* the tables of a lexer spec by evaluation, one per distinct rule list, the executable
   lexer on them and its correctness theorem, and a warning for each rule that wins in no
   state of a mode *)

signature LEXER_TABLES =
sig
  val accepted: term -> int list
  val tables_cmd: (string * Position.T) list -> binding -> string * Position.T ->
    (term * Position.T list) list -> local_theory -> local_theory
end;

structure Lexer_Tables: LEXER_TABLES =
struct

fun err pos msg = error ("Lexer: " ^ msg ^ Position.here pos);

val natT = HOLogic.natT;

fun dest_listT (Type (\<^type_name>\<open>list\<close>, [T])) = T
  | dest_listT T = raise TYPE ("dest_listT", [T], []);


(** the lexer spec **)

fun dest_eq th = HOLogic.dest_eq (HOLogic.dest_Trueprop (Thm.prop_of th));

(* the spec constant of L, its equations and the modes in their order *)
fun read_lexer ctxt (name, pos) =
  let
    val simps =
      Proof_Context.get_thms ctxt (name ^ ".spec.simps")
        handle ERROR _ => err pos (quote name ^ " is no lexer");
    val spec = fst (Term.dest_comb (fst (dest_eq (hd simps))));
    fun const c = Proof_Context.read_const {proper = true, strict = true} ctxt (name ^ "." ^ c);
  in
    {spec = spec, simps = simps, start = const "start", final = const "final",
     is_newline = const "is_newline"}
  end;

(* the modes grouped by their rule lists, in the order of the first mode of each group *)
fun group_modes simps =
  let
    fun add th groups =
      let val (lhs, rhs) = dest_eq th; val v = snd (Term.dest_comb lhs) in
        (case find_index (fn (r, _) => r aconv rhs) groups of
          ~1 => groups @ [(rhs, [(v, th)])]
        | k => nth_map k (apsnd (fn vs => vs @ [(v, th)])) groups)
      end;
  in fold add simps [] end;

(* the split rules of the mode type and of the types of its constructors' arguments *)
fun mode_splits ctxt T =
  let
    val (sugar, _) = Lexer_Command.ctr_sugar ctxt Position.none T;
    val argTs = distinct (op =) (maps (binder_types o fastype_of) (#ctrs sugar));
  in #split sugar :: maps (mode_splits ctxt) argTs end;


(** the byte instance: classes above 0xFF **)

val top_cp = 0x10FFFF;

fun dest_cls t =
  try (map (apply2 (snd o HOLogic.dest_number) o HOLogic.dest_prod) o HOLogic.dest_list) t;

(* an interval reaching above the bytes but not to the end of the codepoints is out of
   range; one that reaches the end is the rest of the alphabet (as in _ and [^...]) *)
fun out_of_range ps = exists (fn (_, b) => b > 0xFF andalso b <> top_cp) ps;

fun hex n = "0x" ^ Int.fmt StringCvt.HEX n;

fun string_of_cls ps =
  "[" ^ commas (map (fn (a, b) => if a = b then hex a else hex a ^ "-" ^ hex b) ps) ^ "]";

(* the classes of the atoms of a regex term *)
fun atoms_of (Const (\<^const_name>\<open>Atom\<close>, _) $ c) = [c]
  | atoms_of (f $ x) = atoms_of f @ atoms_of x
  | atoms_of (Abs (_, _, b)) = atoms_of b
  | atoms_of _ = [];

(* the values of class terms, by one evaluation *)
fun eval_classes ctxt ts =
  if null ts then []
  else
    Value_Command.value ctxt (HOLogic.mk_list \<^typ>\<open>nat cls\<close> ts)
    |> HOLogic.dest_list |> map (the o dest_cls);

(* the classes of the byte instance: the entries of L the rules use, then the classes
   the rules read *)
fun check_bytes ctxt pos spec groups =
  let
    val thy = Proof_Context.theory_of ctxt;
    val qual = Long_Name.qualifier (fst (dest_Const spec));
    val space = Consts.space_of (Sign.consts_of thy);
    fun meta th =
      if can Logic.dest_equals (Thm.prop_of th) then th else th RS @{thm eq_reflection};
    val defs =
      fold (fn (rules, _) => Term.add_const_names rules) groups []
      |> filter (fn c => Long_Name.qualifier c = qual)
      |> map_filter (fn c => Option.map (pair c o meta)
          (try (Global_Theory.get_thm thy) (c ^ "_def")));
    val classes =
      filter (fn (_, th) => fastype_of (Thm.term_of (Thm.rhs_of th)) = \<^typ>\<open>nat cls\<close>) defs;
    fun report what ps =
      what ^ " = " ^ string_of_cls ps ^ " reaches above 0xFF (classes of the byte instance \
        \end at 0xFF or at 0x10FFFF)";
    val _ =
      map2 (fn (c, _) => fn ps =>
          if out_of_range ps then
            err (Name_Space.the_entry_pos space c) (report ("the class " ^
              quote (Long_Name.base_name c)) ps)
          else ())
        classes (eval_classes ctxt (map (Thm.term_of o Thm.rhs_of o snd) classes));
    fun check_group (rules, (v, _) :: _) =
          let
            val atoms = distinct (op aconv)
              (atoms_of (Raw_Simplifier.rewrite_term thy (map snd defs) [] rules));
          in
            (case find_first out_of_range (eval_classes ctxt atoms) of
              SOME ps =>
                err pos (report ("a class of a rule in mode " ^ Syntax.string_of_term ctxt v) ps)
            | NONE => ())
          end
      | check_group _ = ();
  in List.app check_group groups end;


(** instances **)

type instance =
  {name: string, tables: term, tablesT: typ, spec: term -> term, newline: term -> term,
   lexer: term, correct: thm, unfolds: thm list};

fun instance pos name =
  (case name of
    "codepoints" =>
      {name = name, tables = \<^Const>\<open>cp_tables dummyT dummyT\<close>, tablesT = \<^typ>\<open>cp_tables\<close>,
       spec = I, newline = I, lexer = Const (\<^const_name>\<open>cp_lexer\<close>, dummyT),
       correct = @{thm cp_lexer_iff_lexes_in_range}, unfolds = []}
  | "char" =>
      {name = name, tables = \<^Const>\<open>char_tables dummyT dummyT\<close>,
       tablesT = \<^typ>\<open>char_tables\<close>,
       spec = fn sp => Const (\<^const_name>\<open>char_spec\<close>, dummyT) $ sp,
       newline = fn nl => Abs ("c", \<^typ>\<open>char\<close>, nl $ \<^Const>\<open>of_char natT for \<open>Bound 0\<close>\<close>),
       lexer = Const (\<^const_name>\<open>char_lexer\<close>, dummyT),
       correct = @{thm char_lexer_iff_lexes}, unfolds = @{thms char_spec_def}}
  | _ => err pos ("unknown option " ^ quote name ^ " (sketch, no_check, codepoints or char)"));

fun read_instance pos opts =
  (case opts of
    [] => instance pos "codepoints"
  | [(name, pos')] => instance pos' name
  | _ :: (_, pos') :: _ => err pos' "one instance only");


(** the command **)

fun check ctxt = Syntax.check_term ctxt;

fun prove ctxt t tac = Goal.prove ctxt [] [] (HOLogic.mk_Trueprop t) (fn {context, ...} =>
  tac context);

fun note (b, ths) = Local_Theory.note ((b, []), ths) #> snd;

(* the sizes of a table literal: intervals of the class table, minterms and states *)
fun literal_size lit =
  let
    val len = length o HOLogic.dest_list o snd o Term.dest_comb;
    val (C, T) = (case HOLogic.strip_tuple lit of C :: T :: _ => (C, T) | _ => raise Match);
    val rows = HOLogic.dest_list (snd (Term.dest_comb T));
  in [len C, (case rows of r :: _ => len r | [] => 0), length rows] end;

(* the rules that win in some state: the entries of the accept array of a table literal *)
fun accepted lit =
  (case HOLogic.strip_tuple lit of
    _ :: _ :: A :: _ =>
      HOLogic.dest_list (snd (Term.dest_comb A))
      |> map_filter (fn Const (\<^const_name>\<open>Some\<close>, _) $ i => SOME (snd (HOLogic.dest_number i))
           | _ => NONE)
      |> distinct (op =)
  | _ => raise TERM ("accepted", [lit]));

(* flex's "rule cannot be matched" \<^cite>\<open>\<open>Sect.~23\<close> in "paxson2026-flex-manual"\<close>, per mode: a rule of the group that wins in no state of
   its table, with the modes of the group *)
fun unreachable ctxt positions (rules, vs) lit =
  let
    val n = length (HOLogic.dest_list rules);
    val acc = accepted lit;
    val poss = the_default [] (AList.lookup (op aconv) positions (fst (hd vs)));
    val modes = map (Pretty.unformatted_string_of o Syntax.pretty_term ctxt o fst) vs;
  in
    filter_out (member (op =) acc) (0 upto n - 1)
    |> map_filter (fn i => try (nth poss) i)
    |> map (rpair modes)
  end;

fun warn_unreachable reports =
  let
    val by_pos =
      fold (fn (pos, ms) => AList.map_default (op =) (pos, []) (fn ms' => ms' @ ms)) reports [];
    fun plural [_] = "mode " | plural _ = "modes ";
  in
    List.app (fn (pos, ms) =>
      warning ("Lexer: rule cannot be matched in " ^ plural ms ^ commas ms ^
        " (rules of higher priority match each of its lexemes)" ^ Position.here pos)) (rev by_pos)
  end;
(* s.tables_k, with the code equation s.tables_k = v for the value v of its definition,
   and a report of its modes, sizes and time *)
fun define_table s qual (inst: instance) sp k (_, vs) lthy =
  let
    val n = "tables_" ^ string_of_int k;
    val b = qual n;
    val rhs = check lthy (#tables inst $ (#spec inst sp $ fst (hd vs)));
    val (time, eq) = Timing.timing (eval_eq lthy) rhs;
    val ((t, def), lthy) = Lexer_Command.define (b, rhs) lthy;
    val code_th = @{thm trans} OF [def RS @{thm meta_eq_to_obj_eq}, eq];
    val (_, lthy) =
      Local_Theory.note ((Binding.suffix_name "_code" b, @{attributes [code]}), [code_th]) lthy;
    val lit = snd (HOLogic.dest_eq (HOLogic.dest_Trueprop (Thm.prop_of eq)));
    val size = literal_size lit;
    val sizes =
      map2 (fn i => fn w => string_of_int i ^ " " ^ w) size ["intervals", "minterms", "states"];
    val _ =
      writeln (Binding.name_of s ^ "." ^ n ^ " for " ^
        commas (map (Pretty.unformatted_string_of o Syntax.pretty_term lthy o fst) vs) ^ ": " ^
        commas sizes ^ ", " ^
        Time.fmt 2 (#elapsed time) ^ " s");
  in (((t, def), lit), lthy) end;

fun tables check_rules (inst: instance) b (lname, lpos) positions lthy =
  let
    val {spec, simps, start, final, is_newline} = read_lexer lthy (lname, lpos);
    val modeT = domain_type (fastype_of spec);
    val groups = group_modes simps;
    val _ = if #name inst = "char" then check_bytes lthy lpos spec groups else ();
    val qual = fn n => Binding.qualify_name true b n;

    val (tables, lthy) =
      fold_map (fn (k, g) => define_table b qual inst spec k g) (map_index I groups) lthy;
    val _ =
      if check_rules then
        warn_unreachable (flat (map2 (unreachable lthy positions) groups (map snd tables)))
      else ();
    val tables = map fst tables;
    val tablesT = #tablesT inst;
    val arrT = Type (\<^type_name>\<open>iarray\<close>, [tablesT]);
    val ((tt, tt_def), lthy) =
      Lexer_Command.define (qual "tables",
        Const (\<^const_name>\<open>IArray\<close>, HOLogic.listT tablesT --> arrT) $
          HOLogic.mk_list tablesT (map fst tables)) lthy;
    fun index_of v =
      find_index (fn (_, vs) => exists (fn (v', _) => v' aconv v) vs) groups;
    val ((ix, ix_def), lthy) =
      Lexer_Command.define (qual "index",
        Lexer_Command.case_fun lthy natT (HOLogic.mk_number natT o index_of) modeT) lthy;

    (* the index of each mode holds its tables *)
    val sp = check lthy (#spec inst spec);
    fun tab rules = check lthy (#tables inst $ rules);
    val sub = Const (\<^const_name>\<open>IArray.sub\<close>, arrT --> natT --> tablesT);
    val len = Const (\<^const_name>\<open>IArray.length\<close>, arrT --> natT);
    fun at k = HOLogic.mk_number natT k;
    val k_facts = flat (map_index (fn (k, (t, _)) =>
      [prove lthy (HOLogic.mk_eq (sub $ tt $ at k, t)) (fn ctxt =>
         simp_tac (Simplifier.add_simps [tt_def] ctxt) 1),
       prove lthy (\<^Const>\<open>less natT for \<open>at k\<close> \<open>len $ tt\<close>\<close>) (fn ctxt =>
         simp_tac (Simplifier.add_simps [tt_def] ctxt) 1)]) tables);
    val v_facts = flat (map2 (fn (_, vs) => fn (t, def) =>
      map (fn (v, th) =>
        prove lthy (HOLogic.mk_eq (tab (sp $ v), t)) (fn ctxt =>
          simp_tac (Simplifier.add_simps (def :: th :: #unfolds inst @
              (if v aconv fst (hd vs) then [] else [snd (hd vs)]))
            (put_simpset HOL_ss ctxt)) 1)) vs) groups tables);
    val m = Free ("m", modeT);
    val index_prop =
      HOLogic.all_const modeT $ Term.lambda m (HOLogic.mk_conj
        (\<^Const>\<open>less natT for \<open>ix $ m\<close> \<open>len $ tt\<close>\<close>,
         HOLogic.mk_eq (sub $ tt $ (ix $ m), tab (sp $ m))));
    val index_th = prove lthy index_prop (fn ctxt =>
      resolve_tac ctxt @{thms allI} 1 THEN
      asm_full_simp_tac (fold Splitter.add_split (mode_splits ctxt modeT)
        (Simplifier.add_simps (ix_def :: k_facts @ v_facts) (put_simpset HOL_ss ctxt))) 1);
    val lthy = note (qual "index_tables", [index_th]) lthy;

    (* the lexer, its success and its correctness *)
    val start_pos = Syntax.read_term lthy "\<lparr>line = 0, col = 0, off = 0\<rparr> :: pos";
    val nl = check lthy (#newline inst is_newline);
    val stack = HOLogic.mk_list modeT [start];
    val ((s, s_def), lthy) =
      Lexer_Command.define (b, check lthy (#lexer inst $ tt $ ix $ sp $ nl $ stack $ start_pos))
        lthy;
    val wT = domain_type (fastype_of s);
    val w = Free ("w", wT);
    val (lT, rT, stT) =
      (case HOLogic.strip_tupleT (range_type (fastype_of s)) of
        [lT, rT, stT] => (lT, rT, stT)
      | _ => raise Fail "lexer result");
    val (l, r, st) = (Free ("l", lT), Free ("r", rT), Free ("st", stT));
    val ok_rhs =
      Term.lambda w (HOLogic.tupled_lambda (HOLogic.mk_tuple [l, r, st])
        (HOLogic.mk_conj (HOLogic.mk_eq (r, HOLogic.mk_list (dest_listT rT) []),
          final $ \<^Const>\<open>hd modeT for st\<close>)) $ (s $ w));
    val (_, lthy) = Lexer_Command.define (qual "ok", ok_rhs) lthy;
    val correct =
      (#correct inst OF [index_th])
      |> infer_instantiate lthy
        [(("is_newline", 0), Thm.cterm_of lthy nl), (("st", 0), Thm.cterm_of lthy stack),
         (("q", 0), Thm.cterm_of lthy start_pos)]
      |> Local_Defs.fold lthy [s_def];
    val lthy = note (qual "correct", [correct]) lthy;
  in (length groups, lthy) end;

fun tables_cmd opts b (lname, lpos) positions lthy =
  let
    val (no_check, opts') = List.partition (fn (n, _) => n = "no_check") opts;
    val inst = read_instance lpos opts';
    val (time, (n, lthy)) =
      Timing.timing (tables (null no_check) inst b (lname, lpos) positions) lthy;
    val _ =
      writeln (Binding.name_of b ^ ": " ^ string_of_int n ^ " tables, " ^
        Time.fmt 2 (#elapsed time) ^ " s in total");
  in lthy end;

end;
