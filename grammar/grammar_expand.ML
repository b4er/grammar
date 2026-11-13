(* Author: Basil Fürer *)

(* parametric nonterminals and EBNF operators, by desugaring: a template \<open>P(X, \<dots>)\<close> is
   instantiated once per distinct argument tuple as an ordinary nonterminal named
   \<open>P(a, \<dots>)\<close>; \<open>s*\<close>, \<open>s+\<close>, \<open>s?\<close> over a symbol or a group \<open>(s\<^sub>1 \<dots> s\<^sub>n)\<close> are generated
   left-recursive lists and options; a bare group is inlined. The result is an ordinary
   spec for Grammar_Command.elaborate. Templates are registered under their grammar's
   name, so that a later grammar instantiates them too (Grammar_Prelude) *)

signature GRAMMAR_EXPAND =
sig
  type template
  (* the spec of the grammar (NONE for a grammar of templates only), what was generated,
     and the grammar's own templates *)
  val expand: Proof.context -> Grammar_Common.surface ->
    (Grammar_Common.spec * Grammar_Common.expansion) option * (binding * template) list
  val register_templates: (binding * template) list -> local_theory -> local_theory
end;

structure Grammar_Expand: GRAMMAR_EXPAND =
struct

open Grammar_Common;

type template =
  {owner: string,              (* full name of the grammar that defines it *)
   params: string list,
   ascr: Input.source option,
   alts: salternative list,
   siblings: string list,      (* the templates of the owner *)
   nts: string list,           (* the nonterminals of the owner *)
   pos: Position.T};

structure Data = Generic_Data
(
  type T = template Name_Space.table;
  val empty: T = Name_Space.empty_table "grammar template";
  fun merge data: T = Name_Space.merge_tables data;
);

(* \<open>P\<close> of grammar \<open>g\<close> is \<open>g.P\<close>, and \<open>P\<close> where no other template is called so *)
fun register_templates tps lthy =
  fold (fn (b, tp) =>
      Local_Theory.declaration {syntax = false, pervasive = false, pos = Binding.pos_of b}
        (fn phi => fn context =>
          Data.map (#2 o Name_Space.define context true (Morphism.binding phi b, tp))
            context))
    tps lthy;

fun lookup_template ctxt (n, pos) =
  let val tab = Data.get (Context.Proof ctxt) in
    (case Name_Space.lookup tab n of
      SOME tp => (n, tp)
    | NONE =>
        (case try (Name_Space.check (Context.Proof ctxt) tab) (n, pos) of
          SOME r => r
        | NONE =>
            error ("Undefined template " ^ quote n ^
              " (a template is a nonterminal with parameters, P(X) = ...)" ^ Position.here pos)))
  end;

(* the precedence declarations of a spec, NONE without any; a mark then has nothing to do *)
fun prec_of chains forbids (alts: (string * Position.T) option list) =
  if null chains andalso null forbids then
    (case map_filter I alts of
      (n, pos) :: _ =>
        (warning ("(prec " ^ n ^ "): the grammar has no precedence declaration; it is ignored" ^
           Position.here pos); NONE)
    | [] => NONE)
  else SOME {chains = chains, forbids = forbids, alts = alts};

fun sanitize s =
  let
    fun ch c =
      if Char.isAlphaNum c orelse c = #"_" then String.str c
      else "x" ^ StringCvt.padLeft #"0" 2 (Int.fmt StringCvt.HEX (Char.ord c));
    val r = String.translate ch s;
  in if r = "" then "e" else if Char.isDigit (String.sub (r, 0)) then "t" ^ r else r end;

fun ann_string NONE = ""
  | ann_string (SOME Eq) = "^="
  | ann_string (SOME Ge) = "^>="
  | ann_string (SOME Gt) = "^>"
  | ann_string (SOME Any) = "";

fun expand ctxt ({name, opens, tok_typ, terminals, groups, chains, forbids}: surface) =
  let
    val gname = Binding.name_of name;
    val gfull = Local_Theory.full_name ctxt name;
    val (tgroups, ugroups) = List.partition (not o null o #2 o #1 o #1) groups;
    val local_names = map (Binding.name_of o #1 o #1 o #1) ugroups;
    val tnames = map (Binding.name_of o #1 o #1 o #1) tgroups;
    val _ =
      (case duplicates (op =) (local_names @ tnames) of
        [] => ()
      | d :: _ => error ("Duplicate nonterminal/template declaration " ^ quote d ^
          Position.here (Binding.pos_of name)));
    val templates =
      tgroups |> map (fn (((b, params), ascr), alts) =>
        let
          val ps = map #1 params;
          val _ =
            (case duplicates (op =) ps of
              [] => ()
            | d :: _ => error ("Template " ^ quote (Binding.name_of b) ^ ": parameter " ^
                quote d ^ " twice" ^ Position.here (Binding.pos_of b)));
          val _ =
            alts |> List.app (fn (_, mark) =>
              (case mark of
                SOME (n, pos) =>
                  error ("(prec " ^ n ^ "): a template alternative has no precedence mark; \
                    \mark the alternatives that use the instance" ^ Position.here pos)
              | NONE => ()));
        in
          (Binding.qualify false gname (Binding.name (Binding.name_of b)),
           {owner = gfull, params = ps, ascr = ascr, alts = alts, siblings = tnames,
            nts = local_names, pos = Binding.pos_of b}: template)
        end);
    val local_tab = Symtab.make (map (fn (b, tp) => (Binding.name_of b, tp)) templates);

    (* \<open>open a\<close>: the grammars whose own nonterminals and templates bare names may name *)
    val class_names =
      map_filter (fn Class b => SOME (Binding.name_of b) | _ => NONE) terminals;
    val opened =
      opens |> map (fn (n, pos) =>
        let
          val (full, gr) = check_grammar ctxt (n, pos);
          val own =
            filter (fn m => not (is_copy_name m) andalso not (String.isSubstring "(" m))
              (Symtab.keys (#nonterms gr));
        in (full, (n, own)) end);
    val _ =
      (case duplicates (op =) (map #1 opened) of
        [] => ()
      | d :: _ => error ("Grammar " ^ quote d ^ " is opened twice" ^ Position.here (Binding.pos_of name)));
    (* a bare name: a local nonterminal or terminal class, else the one opened grammar
       that defines it, else as written (a token term) *)
    fun resolve (n, pos) =
      if Long_Name.is_qualified n orelse member (op =) local_names n orelse
        member (op =) class_names n
      then n
      else
        (case filter (fn (_, (_, own)) => member (op =) own n) opened of
          [] => n
        | [(_, (written, _))] => written ^ "." ^ n
        | fs =>
            error ("Nonterminal " ^ quote n ^ " is defined by the opened grammars " ^
              commas_quote (map (Long_Name.base_name o #1) fs) ^ "; qualify it, " ^
              Long_Name.base_name (#1 (hd fs)) ^ "." ^ n ^ Position.here pos));
    (* a reference \<open>a.X\<close> as the full name of its grammar, so that \<open>a.X\<close> and \<open>X\<close> under
       \<open>open a\<close> give one instance key *)
    fun canon n =
      if not (Long_Name.is_qualified n) orelse String.isSubstring "(" n then n
      else
        (case try (check_grammar ctxt) (Long_Name.qualifier n, Position.none) of
          SOME (full, _) => full ^ "." ^ Long_Name.base_name n
        | NONE => n);

    (* generated nonterminals by key, in order of their first use *)
    val gens = Unsynchronized.ref ([] : (string * (string * string)) list);   (* key, (display, ident) *)
    val gen_groups = Unsynchronized.ref ([] : production_group list);
    val silent = Unsynchronized.ref ([] : string list);
    val patterns = Unsynchronized.ref ([] : string list);
    val owners = Unsynchronized.ref ([] : string list);
    val counters = Unsynchronized.ref ([] : (string * int) list);
    val used_idents = Unsynchronized.ref (local_names : string list);
    fun fresh_ident base =
      let
        fun go k =
          let val c = if k = 1 then base else base ^ "_" ^ string_of_int k
          in if member (op =) (! used_idents) c then go (k + 1) else c end;
        val c = go 1;
      in (used_idents := c :: ! used_idents; c) end;
    fun fresh_display d =
      let
        fun go s = if exists (fn (_, (d', _)) => d' = s) (! gens) then go (s ^ "'") else s;
      in go d end;
    fun ident_of_name n =
      (case find_first (fn (_, (d, _)) => d = n) (! gens) of
        SOME (_, (_, i)) => i
      | NONE => ident_of n);
    fun is_silent n = member (op =) (! silent) n;

    (* a nonterminal of another grammar, \<open>Thy.g.X\<close>, shows as \<open>g.X\<close> *)
    fun disp_sym (Ref (n, _)) =
          if length (Long_Name.explode n) > 2 andalso not (String.isSubstring "(" n) then
            Long_Name.base_name (Long_Name.qualifier n) ^ "." ^ Long_Name.base_name n
          else n
      | disp_sym (Lit (s, _)) = s
      | disp_sym (Tok src) = Input.text_of src
      | disp_sym (Span _) = "@span";
    fun key_sym (Ref (n, _)) = "N" ^ canon n
      | key_sym (Lit (s, _)) = "L" ^ s
      | key_sym (Tok src) = "T" ^ Input.text_of src
      | key_sym (Span _) = "S";
    fun ident_sym (Ref (n, _)) = ident_of_name n
      | ident_sym (Lit (s, _)) = sanitize s
      | ident_sym (Tok _) = "tok"
      | ident_sym (Span _) = "span";
    fun binds (Ref (n, _), _) = not (is_silent n)
      | binds _ = false;

    (* the scope of a template body: its parameters bound to resolved symbols, and,
       for a template of another grammar, that grammar's names *)
    type scope =
      {params: (string * (gsym * ann option) list) list,
       foreign: (string * string list * string list) option,   (* owner, siblings, nts *)
       ctx: string,
       depth: int};

    (* a generated nonterminal: its name is taken before its body is expanded, which may
       generate further nonterminals; its group is placed at its first use *)
    fun reserve key display ident is_silent_gen is_pattern =
      let val d = fresh_display display in
        gens := ! gens @ [(key, (d, fresh_ident ident))];
        if is_silent_gen then silent := d :: ! silent else ();
        if is_pattern then patterns := d :: ! patterns else ();
        d
      end;
    fun push d ascr pos =
      (gen_groups := ! gen_groups @ [((Binding.make (d, pos), ascr), [])];
       length (! gen_groups) - 1);
    fun fill slot alts =
      gen_groups :=
        map_index (fn (i, g as ((b, a), _)) => if i = slot then ((b, a), alts) else g)
          (! gen_groups);

    fun next_ctx_ident ctx =
      let
        val k = the_default 0 (AList.lookup (op =) (! counters) ctx) + 1;
        val _ = counters := AList.update (op =) (ctx, k) (! counters);
      in ctx ^ "_" ^ string_of_int k end;

    fun expand_item (sc: scope) (it, ann) : (gsym * ann option) list =
      (case it of
        Sym (Ref (n, pos)) =>
          (case AList.lookup (op =) (#params sc) n of
            SOME [(g, a)] =>
              (case (a, ann) of
                (SOME _, SOME _) =>
                  error ("Parameter " ^ quote n ^ ": the argument has an annotation already" ^
                    Position.here pos)
              | _ => [(g, if is_some ann then ann else a)])
          | SOME gs =>
              if is_some ann then
                error ("Parameter " ^ quote n ^ " stands for a group of " ^
                  string_of_int (length gs) ^ " symbols, which has no annotation; \
                  \annotate its symbols" ^ Position.here pos)
              else gs
          | NONE =>
              (case #foreign sc of
                SOME (owner, _, nts) =>
                  if member (op =) nts n then [(Ref (owner ^ "." ^ n, pos), ann)]
                  else [(Ref (resolve (n, pos), pos), ann)]
              | NONE => [(Ref (resolve (n, pos), pos), ann)]))
      | Sym (Span pos) =>
          if is_some ann then
            error ("@span is not a grammar symbol and takes no annotation" ^ Position.here pos)
          else [(Span pos, NONE)]
      | Sym g => [(g, ann)]
      | Group (items, pos) =>
          if is_some ann then
            error ("An annotation of a group applies to no symbol; annotate the symbols \
              \inside, or apply an operator (* + ?) to the group" ^ Position.here pos)
          else maps (expand_item sc) items
      | App ((n, pos), args) => [(Ref (instance sc (n, pos) args, pos), ann)]
      | Rep (opr, operand, pos) => [(Ref (repetition sc opr operand pos, pos), ann)])

    and instance (sc: scope) (n, pos) args =
      let
        val _ =
          AList.defined (op =) (#params sc) n andalso
            error ("Parameter " ^ quote n ^ " is not a template" ^ Position.here pos);
        val _ = #depth sc > 64 andalso
          error ("Template " ^ quote n ^ ": instantiation does not terminate (an instance \
            \whose arguments grow, P(X) = ... P(List(X)) ...)" ^ Position.here pos);
        val (full, tp: template) =
          (case #foreign sc of
            SOME (owner, siblings, _) =>
              if member (op =) siblings n then lookup_template ctxt (owner ^ "." ^ n, pos)
              else lookup_template ctxt (n, pos)
          | NONE =>
              (case Symtab.lookup local_tab n of
                SOME tp => (gfull ^ "." ^ n, tp)
              | NONE =>
                  let val tab = Data.get (Context.Proof ctxt) in
                    (* a template of an opened grammar before one of another grammar *)
                    (case map_filter (fn (full, _) =>
                        Option.map (pair (full ^ "." ^ n)) (Name_Space.lookup tab (full ^ "." ^ n)))
                        opened of
                      [r] => r
                    | [] => lookup_template ctxt (n, pos)
                    | rs =>
                        error ("Template " ^ quote n ^ " is defined by the opened grammars " ^
                          commas_quote (map (Long_Name.base_name o Long_Name.qualifier o #1) rs) ^
                          "; qualify it" ^ Position.here pos))
                  end));
        val _ =
          length args = length (#params tp) orelse
            error ("Template " ^ quote n ^ " has " ^ string_of_int (length (#params tp)) ^
              " parameter(s), applied to " ^ string_of_int (length args) ^ Position.here pos);
        val rargs = map (fn a => expand_item sc (a, NONE)) args;
        val _ =
          rargs |> List.app (List.app (fn (Span p, _) =>
              error ("@span is not a template argument; write it in the alternative" ^
                Position.here p)
            | _ => ()));
        fun disp_arg [(g, a)] = disp_sym g ^ ann_string a
          | disp_arg gs = "(" ^ space_implode " " (map (fn (g, a) => disp_sym g ^ ann_string a) gs) ^ ")";
        fun key_arg gs = "[" ^ space_implode " " (map (fn (g, a) => key_sym g ^ ann_string a) gs) ^ "]";
        val key = "I" ^ full ^ "(" ^ commas (map key_arg rargs) ^ ")";
        val base = Long_Name.base_name full;
      in
        (case AList.lookup (op =) (! gens) key of
          SOME (d, _) => d
        | NONE =>
            let
              val display = base ^ "(" ^ commas (map disp_arg rargs) ^ ")";
              val ident = space_implode "_" (base :: map (space_implode "_" o map (ident_sym o #1)) rargs);
              val is_local = (#owner tp = gfull);
              val _ = if is_local then () else owners := insert (op =) (#owner tp) (! owners);
              val sc' : scope =
                {params = #params tp ~~ rargs,
                 foreign = if is_local then NONE else SOME (#owner tp, #siblings tp, #nts tp),
                 ctx = ident, depth = #depth sc + 1};
              val d = reserve key display ident false (is_some (#ascr tp));
              val slot = push d (#ascr tp) pos;
              val _ = fill slot (map (expand_alt sc') (#alts tp));
            in d end)
      end

    and repetition (sc: scope) opr operand pos =
      let
        val syms =
          (case operand of
            Group (items, _) => maps (expand_item sc) items
          | _ => expand_item sc (operand, NONE));
        val _ = null syms andalso
          error ("Operator " ^ opr ^ " applied to an empty group" ^ Position.here pos);
        val _ =
          syms |> List.app (fn (Span p, _) =>
              error ("@span inside an operator's group: the span of the whole alternative is \
                \written at its top level" ^ Position.here p)
            | _ => ());
        val vals = filter binds syms;
        val k = length vals;
        val key = "R" ^ opr ^ "[" ^ space_implode " " (map (fn (g, a) => key_sym g ^ ann_string a) syms) ^ "]";
      in
        (case AList.lookup (op =) (! gens) key of
          SOME (d, _) => d
        | NONE =>
            let
              val plain = space_implode " " (map (disp_sym o #1) syms);
              val annotated = space_implode " " (map (fn (g, a) => disp_sym g ^ ann_string a) syms);
              val display0 =
                (case syms of
                  [(g, _)] => disp_sym g ^ opr
                | _ => "(" ^ plain ^ ")" ^ opr);
              val display =
                if exists (fn (_, (d', _)) => d' = display0) (! gens)
                then "(" ^ annotated ^ ")" ^ opr else display0;
              val suffix = (case opr of "*" => "list" | "+" => "list1" | _ => "opt");
              val ident =
                (case vals of
                  [(Ref (n, _), _)] =>
                    if length syms = 1 then ident_of_name n ^ "_" ^ suffix
                    else next_ctx_ident (#ctx sc)
                | _ => next_ctx_ident (#ctx sc));
              val d = reserve key display ident (k = 0) false;
              val rec_ann = (case syms of (_, a) :: _ => a | [] => NONE);
              val self = (Ref (d, pos), rec_ann);
              val xs = map (fn i => "x" ^ string_of_int i) (1 upto k);
              val tuple =
                (case xs of [x] => x | _ => "(" ^ commas xs ^ ")");
              fun lam vs body = if null vs then body else "\<lambda>" ^ space_implode " " vs ^ ". " ^ body;
              fun act s = SOME (Input.string s);
              val alts =
                if k = 0 then
                  (case opr of
                    "*" => [([], act "()"), (self :: syms, act "()")]
                  | "+" => [(syms, act "()"), (self :: syms, act "()")]
                  | _ => [([], act "()"), (syms, act "()")])
                else
                  (case opr of
                    "*" => [([], act "[]"), (self :: syms, act (lam ("xs" :: xs) ("xs @ [" ^ tuple ^ "]")))]
                  | "+" => [(syms, act (lam xs ("[" ^ tuple ^ "]"))),
                            (self :: syms, act (lam ("xs" :: xs) ("xs @ [" ^ tuple ^ "]")))]
                  | _ => [([], act "None"), (syms, act (lam xs ("Some " ^ tuple)))]);
              val _ = fill (push d NONE pos) alts;
            in d end)
      end

    and expand_alt (sc: scope) ((syms, act), _) : alternative =
      (maps (expand_item sc) syms, act);

    val top : string -> scope = fn ctx => {params = [], foreign = NONE, ctx = ctx, depth = 0};
    val user_groups =
      ugroups |> map (fn (((b, _), ascr), alts) =>
        ((b, ascr), map (expand_alt (top (Binding.name_of b))) alts));
    val marks = maps (map #2 o #2) ugroups;
    val generated = map #2 (! gens);
  in
    (if null ugroups andalso not (null tgroups) then NONE
     else
       SOME
        ({name = name, tok_typ = tok_typ, terminals = terminals,
          productions = user_groups @ ! gen_groups,
          prec = prec_of chains forbids marks}: spec,
         {generated = generated, silent = ! silent, patterns = ! patterns,
          owners = ! owners}: expansion),
     templates)
  end;

end;
