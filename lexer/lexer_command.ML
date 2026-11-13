(* Author: Basil Fürer *)

(* the lexer command: the classes and regexes of a lexer spec, its mode type and its
   rules as definitions, with markup for the names *)

signature LEXER_COMMAND =
sig
  datatype pattern = Cartouche of Input.source | Literal of Input.source
  datatype action = Skip | Fail | Act of Input.source
  datatype mode_op =
    Keep | Begin of Input.source | Push of Input.source | Pop | Stack of Input.source
  type rule =
    {pattern: pattern, arrow: Position.T, action: action, guard: Input.source option,
     mode_op: mode_op}
  datatype item = Rule of Input.source list * rule | Scope of Input.source list * item list
  datatype modes = No_Modes | Mode_Names of binding list | Mode_Type of Input.source
  type definition = ((string * Position.T) * (string * Position.T) list) * Input.source
  type spec =
    {name: binding, tok: Input.source, modes: modes, start: Input.source option,
     exclusive: Input.source list, final: Input.source list option,
     after: Input.source option, newline: (string * Position.T) option,
     defs: definition list, items: item list}
  val lexer_cmd: spec -> local_theory -> (term * Position.T list) list * local_theory
  val define: binding * term -> local_theory -> (term * thm) * local_theory
  val ctr_sugar: Proof.context -> Position.T -> typ -> Ctr_Sugar.ctr_sugar * typ list
  val case_fun: Proof.context -> typ -> (term -> term) -> typ -> term
end;

structure Lexer_Command: LEXER_COMMAND =
struct

datatype pattern = Cartouche of Input.source | Literal of Input.source;
datatype action = Skip | Fail | Act of Input.source;
datatype mode_op =
  Keep | Begin of Input.source | Push of Input.source | Pop | Stack of Input.source;

type rule =
  {pattern: pattern, arrow: Position.T, action: action, guard: Input.source option,
   mode_op: mode_op};

datatype item = Rule of Input.source list * rule | Scope of Input.source list * item list;
datatype modes = No_Modes | Mode_Names of binding list | Mode_Type of Input.source;

type definition = ((string * Position.T) * (string * Position.T) list) * Input.source;

type spec =
  {name: binding, tok: Input.source, modes: modes, start: Input.source option,
   exclusive: Input.source list, final: Input.source list option,
   after: Input.source option, newline: (string * Position.T) option,
   defs: definition list, items: item list};

fun err pos msg = error ("Lexer: " ^ msg ^ Position.here pos);

val clsT = \<^typ>\<open>nat cls\<close>;
val natT = HOLogic.natT;
val wordT = HOLogic.listT natT;


(** terms read from the source **)

fun parse_term ctxt src = Syntax.parse_term ctxt (Syntax.implode_input src);

fun check_closed ctxt src what t =
  (case Term.add_frees t [] of
    [] => t
  | (x, _) :: _ =>
      err (Input.pos_of src)
        ("unknown " ^ what ^ " " ^ quote x ^ " in " ^ Syntax.string_of_term ctxt t));

fun read_typed ctxt what T src =
  Syntax.check_term ctxt (Type.constraint T (parse_term ctxt src))
  |> check_closed ctxt src what;


(** modes **)

fun ctr_sugar ctxt pos T =
  (case T of
    Type (n, Ts) =>
      (case Ctr_Sugar.ctr_sugar_of ctxt n of
        SOME sugar => (sugar, Ts)
      | NONE => err pos ("the mode type " ^ Syntax.string_of_typ ctxt T ^ " is no datatype"))
  | _ => err pos ("the mode type " ^ Syntax.string_of_typ ctxt T ^ " is no datatype"));

fun instantiate_ctrs ctxt T ({T = T0, ctrs, ...}: Ctr_Sugar.ctr_sugar) =
  let val tyenv = Sign.typ_match (Proof_Context.theory_of ctxt) (T0, T) Vartab.empty
  in map (map_types (Envir.subst_type tyenv)) ctrs end;

(* the values of a datatype whose constructors take values of such datatypes, with the
   case theorems of every type involved *)
fun enumerate ctxt pos seen T =
  let
    val _ =
      if member (op =) seen T
      then err pos ("the mode type " ^ Syntax.string_of_typ ctxt T ^ " is recursive") else ();
    val (sugar, _) = ctr_sugar ctxt pos T;
    fun values_of c =
      let
        val argTs = binder_types (fastype_of c);
        val (argss, thmss) = split_list (map (enumerate ctxt pos (T :: seen)) argTs);
      in (map (curry list_comb c) (Library.foldr (fn (xs, yss) =>
            maps (fn x => map (cons x) yss) xs) (argss, [[]])), flat thmss)
      end;
    val (valss, thmss) = split_list (map values_of (instantiate_ctrs ctxt T sugar));
  in (flat valss, #case_thms sugar @ flat thmss) end;

(* the function on T by nested case distinction whose value at v is f v *)
fun case_fun ctxt resT f T =
  let
    val (sugar, Ts) = ctr_sugar ctxt Position.none T;
    val casex = Ctr_Sugar.mk_case Ts resT (#casex sugar);
    fun branch c [] = f c
      | branch c (A :: As) = case_fun ctxt (As ---> resT) (fn v => branch (c $ v) As) A;
  in
    list_comb (casex,
      map (fn c => branch c (binder_types (fastype_of c))) (instantiate_ctrs ctxt T sugar))
  end;

fun define_mode_type name ctrs lthy =
  let
    val b = Binding.suffix_name "_mode" name;
    val spec =
      (((([], b), NoSyn), map (fn c => (((Binding.empty, c), []), NoSyn)) ctrs),
        (Binding.empty, Binding.empty, Binding.empty));
    val lthy' =
      BNF_FP_Def_Sugar.co_datatypes BNF_Util.Least_FP BNF_LFP.construct_lfp
        (Ctr_Sugar.default_ctr_options, [(spec, [])]) lthy;
  in (Type (Local_Theory.full_name lthy b, []), lthy') end;

(* a HOL pattern of a value: constructors and dummies *)
fun matches (Var _) _ = true
  | matches (Const (a, _)) (Const (b, _)) = a = b
  | matches (f $ x) (g $ y) = matches f g andalso matches x y
  | matches _ _ = false;

fun read_mode_pattern ctxt modeT values src =
  let
    val pctxt = Proof_Context.set_mode Proof_Context.mode_pattern ctxt;
    val p =
      Syntax.check_term pctxt (Type.constraint modeT (parse_term ctxt src))
      |> check_closed ctxt src "mode constructor";
  in
    (case filter (matches p) values of
      [] => err (Input.pos_of src) ("the pattern " ^ Syntax.string_of_term ctxt p ^
        " matches no mode")
    | vs => vs)
  end;

fun read_mode ctxt modeT values src =
  let val t = read_typed ctxt "mode constructor" modeT src in
    if member (op aconv) values t then t
    else err (Input.pos_of src) (Syntax.string_of_term ctxt t ^ " is no mode")
  end;

fun union_modes values vss = filter (fn v => exists (fn vs => member (op aconv) vs v) vss) values;


(** definitions **)

fun define (b, rhs) lthy =
  let
    val ((t, (_, th)), lthy') =
      Local_Theory.define ((b, NoSyn), ((Thm.def_binding b, []), rhs)) lthy;
  in ((t, th), Code.declare_default_eqns [(th, true)] lthy') end;

fun qualify name (n, pos) = Binding.qualify true (Binding.name_of name) (Binding.make (n, pos));

(* the where entries in order, each one seeing those before it *)
fun define_entries name defs lthy =
  let
    val names = map (#1 o #1 o #1) defs;
    val ns =
      fold (fn (((n, pos), _), _) =>
          #2 o Name_Space.define (Context.Proof lthy) true (Binding.make (n, pos), ()))
        defs (Name_Space.empty_table "lexer definition");
    fun env lthy entries (n, pos) =
      if member (op =) names n then
        (Name_Space.check (Context.Proof lthy) ns (n, pos);
         (case Symtab.lookup entries n of
           SOME e => e
         | NONE => err pos (quote n ^ " is used before its definition")))
      else Pattern.const_env lthy (n, pos);
    fun entry (((n, pos), params), src) (entries, lthy) =
      let val ast = Pattern.parse lthy src in
        if null params then
          let
            val (kind, rhs) = Pattern.elaborate (env lthy entries) ast;
            val ((t, _), lthy') = define (qualify name (n, pos), rhs) lthy;
          in (Symtab.update (n, {kind = kind, params = [], term = t}) entries, lthy') end
        else (Symtab.update (n, Pattern.template (env lthy entries) params ast) entries, lthy)
      end;
    val (entries, lthy') = fold entry defs (Symtab.empty, lthy);
  in (env lthy' entries, lthy') end;


(** rules **)

fun flatten tags (Rule (tags', r)) = [(tags @ tags', r)]
  | flatten tags (Scope (tags', items)) = maps (flatten (tags @ tags')) items;

fun pattern_pos (Cartouche src) = Input.pos_of src
  | pattern_pos (Literal src) = Input.pos_of src;

fun read_match lthy env (Cartouche src) = Pattern.regex_of (Pattern.read lthy env src)
  | read_match _ _ (Literal src) =
      Pattern.literal (map Pattern.codepoint (Input.source_explode src));

datatype elab_action = Kind of term * term | Full of term;

fun read_action lthy tokT modeT (Act src) =
      let
        val t = parse_term lthy src;
        fun known (Free (x, _)) = err (Input.pos_of src) ("unknown token constructor " ^ quote x)
          | known u = u;
        fun try_type T = Option.map known (try (Syntax.check_term lthy) (Type.constraint T t));
        val fullT =
          wordT --> HOLogic.listT modeT -->
            HOLogic.mk_prodT (\<^Type>\<open>option tokT\<close>, HOLogic.listT modeT);
        val always = Abs ("u", wordT, \<^Const>\<open>True\<close>);
      in
        (case try_type tokT of
          SOME k => Kind (Abs ("u", wordT, \<^Const>\<open>Some tokT for k\<close>), always)
        | NONE =>
            (case try_type (wordT --> tokT) of
              SOME g => Kind (Abs ("u", wordT, \<^Const>\<open>Some tokT for \<open>g $ Bound 0\<close>\<close>), always)
            | NONE =>
                (case try_type fullT of
                  SOME a => Full a
                | NONE =>
                    err (Input.pos_of src) ("the action must be a token, a function from the \
                      \lexeme to a token, or an action of type " ^
                      Syntax.string_of_typ lthy fullT))))
        |> (fn Kind (k, g) => Kind (check_closed lthy src "name" k, g)
             | Full a => Full (check_closed lthy src "name" a))
      end
  | read_action _ tokT _ Skip =
      Kind (Abs ("u", wordT, \<^Const>\<open>None tokT\<close>), Abs ("u", wordT, \<^Const>\<open>True\<close>))
  | read_action _ tokT _ Fail =
      Kind (Abs ("u", wordT, \<^Const>\<open>None tokT\<close>), Abs ("u", wordT, \<^Const>\<open>False\<close>));

fun read_effect lthy modeT values mode_op =
  (case mode_op of
    Keep => \<^Const>\<open>Keep modeT\<close>
  | Begin src => \<^Const>\<open>Begin modeT for \<open>read_mode lthy modeT values src\<close>\<close>
  | Push src => \<^Const>\<open>Push modeT for \<open>read_mode lthy modeT values src\<close>\<close>
  | Pop => \<^Const>\<open>Pop modeT\<close>
  | Stack src =>
      \<^Const>\<open>Stack modeT for
        \<open>read_typed lthy "name" (HOLogic.listT modeT --> HOLogic.listT modeT) src\<close>\<close>);

fun report_act lthy pos act =
  Context_Position.report_text lthy pos Markup.typing
    (Pretty.string_of (Pretty.block [Pretty.str "act =", Pretty.brk 1,
      Syntax.pretty_term lthy act]));

(* the rule term of a rule and the modes it is active in *)
fun elab_rule lthy env {tokT, modeT, values, inclusive, hook} (tags, r: rule) =
  let
    val pos = pattern_pos (#pattern r);
    val active =
      if null tags then inclusive
      else union_modes values (map (read_mode_pattern lthy modeT values) tags);
    val _ = if null active then err pos "the rule is active in no mode" else ();
    val match = read_match lthy env (#pattern r);
    val guard =
      Option.map (read_typed lthy "name" (wordT --> HOLogic.boolT)) (#guard r);
    val plain = is_none guard andalso (case #mode_op r of Keep => true | _ => false);
    val _ =
      (case #action r of
        Fail => if plain then () else err (#arrow r) "error takes no guard and no mode operation"
      | _ => ());
    val act =
      (case read_action lthy tokT modeT (#action r) of
        Kind (kind, always) =>
          \<^Const>\<open>mk_act tokT modeT natT for hook kind \<open>the_default always guard\<close>
            \<open>read_effect lthy modeT values (#mode_op r)\<close>\<close>
      | Full a =>
          if plain then a
          else err (#arrow r) "a full action takes no guard and no mode operation");
    val _ = report_act lthy (#arrow r) act;
    val unitT = HOLogic.unitT;
  in (\<^Const>\<open>rule_ext clsT natT modeT tokT unitT for match act \<^Const>\<open>Unity\<close>\<close>, active) end;


(** the command **)

(* rewriting at the head only, so that the rule lists are never traversed *)
fun head_rewr thms ct = (Conv.rewrs_conv thms else_conv Conv.fun_conv (head_rewr thms)) ct;

(* L.spec v = rules, by unfolding and the case equations of the mode types *)
fun spec_eq ctxt spec_def case_thms spec_t v =
  let
    val conv =
      Conv.fun_conv (Conv.rewr_conv spec_def) then_conv
        Conv.repeat_conv (head_rewr (map mk_meta_eq case_thms));
  in conv (Thm.cterm_of ctxt (spec_t $ v)) RS @{thm meta_eq_to_obj_eq} end;

fun lexer_cmd (spec: spec) lthy =
  let
    val name = #name spec;
    val qual = qualify name;
    val pos = Binding.pos_of name;
    val tokT = Syntax.read_typ lthy (Syntax.implode_input (#tok spec));
    val (modeT, lthy) =
      (case #modes spec of
        No_Modes => (HOLogic.unitT, lthy)
      | Mode_Names ctrs => define_mode_type name ctrs lthy
      | Mode_Type src => (Syntax.read_typ lthy (Syntax.implode_input src), lthy));
    val mpos = (case #modes spec of Mode_Type src => Input.pos_of src | _ => pos);
    val (values, case_thms) = enumerate lthy mpos [] modeT;
    val read_patterns = maps (read_mode_pattern lthy modeT values);
    val exclusive = read_patterns (#exclusive spec);
    val inclusive = filter_out (member (op aconv) exclusive) values;
    val start =
      (case #start spec of
        SOME src => read_mode lthy modeT values src
      | NONE => hd values);
    val final =
      (case #final spec of
        SOME srcs => union_modes values [read_patterns srcs]
      | NONE => inclusive);
    val tok_optT = \<^Type>\<open>option tokT\<close>;
    val hook =
      (case #after spec of
        SOME src => read_typed lthy "name" (tok_optT --> modeT --> modeT) src
      | NONE => Abs ("k", tok_optT, Abs ("m", modeT, Bound 0)));

    val (env, lthy) = define_entries name (#defs spec) lthy;
    val newline =
      (case #newline spec of
        SOME np =>
          (case env np of
            {kind = Pattern.Class, params = [], term} => term
          | _ => err (#2 np) (quote (#1 np) ^ " is no class"))
      | NONE => Pattern.class_term [(10, 10)]);

    val ctxt = {tokT = tokT, modeT = modeT, values = values, inclusive = inclusive, hook = hook};
    val flat_rules = maps (flatten []) (#items spec);
    val rules = map (elab_rule lthy env ctxt) flat_rules;
    val positions = map (pattern_pos o #pattern o snd) flat_rules;
    val unitT = HOLogic.unitT;
    val ruleT = body_type (fastype_of \<^Const>\<open>rule_ext clsT natT modeT tokT unitT\<close>);
    fun rules_of v =
      HOLogic.mk_list ruleT (map_filter (fn (t, ms) =>
        if member (op aconv) ms v then SOME t else NONE) rules);

    val ((spec_t, spec_def), lthy) =
      define (qual ("spec", pos), case_fun lthy (HOLogic.listT ruleT) rules_of modeT) lthy;
    val simps = map (spec_eq lthy spec_def case_thms spec_t) values;
    val (_, lthy) =
      Local_Theory.notes [((Binding.qualify_name true (qual ("spec", pos)) "simps",
        @{attributes [simp]}), [(simps, [])])] lthy;
    val (_, lthy) = define (qual ("start", pos), start) lthy;
    val m = Free ("m", modeT);
    val (_, lthy) =
      define (qual ("final", pos),
        Term.lambda m (HOLogic.mk_mem (m, HOLogic.mk_set modeT final))) lthy;
    val c = Free ("c", natT);
    val (_, lthy) =
      define (qual ("is_newline", pos), Term.lambda c \<^Const>\<open>in_cls natT for newline c\<close>) lthy;
    fun positions_of v =
      map_filter (fn ((_, ms), p) => if member (op aconv) ms v then SOME p else NONE)
        (rules ~~ positions);
  in (map (fn v => (v, positions_of v)) values, lthy) end;

end;
