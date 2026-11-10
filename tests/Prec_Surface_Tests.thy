theory Prec_Surface_Tests
  imports LR_Parser.LR_Prec_Parse Parser_Check
begin

section \<open>Precedence declarations in \<^theory_text>\<open>grammar\<close>\<close>

fun toks :: \<open>nat \<Rightarrow> 'tok list \<Rightarrow> ('tok, unit) token list\<close> where
  \<open>toks i [] = []\<close>
| \<open>toks i (x # xs) = \<lparr>tok = x, span = span.make 0 i i 1 []\<rparr> # toks (Suc (Suc i)) xs\<close>

datatype p_tok = PNum | PPlus | PMinus | PStar | PPow | PEq | PLP | PRP | PErr

datatype p_exp =
  N | Add p_exp p_exp | Sub p_exp p_exp | Mul p_exp p_exp | Pow p_exp p_exp
  | Neg p_exp | Equ p_exp p_exp | Bad

subsection \<open>A total order, a name for a level, a nonassociative level\<close>

grammar ep =
  tokens \<open>p_tok\<close>
  terminals
    "+" = \<open>PPlus\<close> and "-" = \<open>PMinus\<close> and "*" = \<open>PStar\<close> and "^" = \<open>PPow\<close> and
    "==" = \<open>PEq\<close> and "(" = \<open>PLP\<close> and ")" = \<open>PRP\<close>
  precedence right "^" > left UMINUS > left "*" > left "+" "-" > nonassoc "=="
  productions
    E :: \<open>p_exp\<close>
      = E "==" E \<Rightarrow> \<open>\<lambda>a b. Equ a b\<close>
      | E "+" E \<Rightarrow> \<open>\<lambda>a b. Add a b\<close>
      | E "-" E \<Rightarrow> \<open>\<lambda>a b. Sub a b\<close>
      | E "*" E \<Rightarrow> \<open>\<lambda>a b. Mul a b\<close>
      | "-" E (prec UMINUS) \<Rightarrow> \<open>\<lambda>a. Neg a\<close>
      | E "^" E \<Rightarrow> \<open>\<lambda>a b. Pow a b\<close>
      | A
  and
    A :: \<open>p_exp\<close>
      = PNum \<Rightarrow> \<open>\<lambda>_. N\<close>
      | "(" E ")" \<Rightarrow> \<open>\<lambda>e. e\<close>

parser ep_parse for ep

thm ep_parse.sound ep_parse.complete ep_parse.sound_lang ep_parse.complete_lang

parser_check \<open>ep_parse (toks 0 [PNum, PPlus, PNum, PStar, PNum]) = Some (Add N (Mul N N))\<close>
parser_check \<open>ep_parse (toks 0 [PNum, PStar, PNum, PPlus, PNum]) = Some (Add (Mul N N) N)\<close>
parser_check \<open>ep_parse (toks 0 [PNum, PMinus, PNum, PPlus, PNum]) = Some (Add (Sub N N) N)\<close>
parser_check \<open>ep_parse (toks 0 [PNum, PPow, PNum, PPow, PNum]) = Some (Pow N (Pow N N))\<close>
parser_check \<open>ep_parse (toks 0 [PMinus, PNum, PPow, PNum]) = Some (Neg (Pow N N))\<close>
parser_check \<open>ep_parse (toks 0 [PMinus, PNum, PStar, PNum]) = Some (Mul (Neg N) N)\<close>
parser_check \<open>ep_parse (toks 0 [PNum, PEq, PNum]) = Some (Equ N N)\<close>
parser_check \<open>ep_parse (toks 0 [PNum, PEq, PNum, PEq, PNum]) = None\<close>
parser_check \<open>ep_parse (toks 0 [PLP, PNum, PEq, PNum, PRP, PEq, PNum]) = Some (Equ (Equ N N) N)\<close>

subsection \<open>Several lines; an entry; a nonterminal below the prefix\<close>

grammar eq =
  tokens \<open>p_tok\<close>
  terminals "+" = \<open>PPlus\<close> and "*" = \<open>PStar\<close> and "(" = \<open>PLP\<close> and ")" = \<open>PRP\<close>
  precedence left "*" > left "+"
  productions
    S :: \<open>p_exp\<close> = E
  and
    E :: \<open>p_exp\<close>
      = E "+" E \<Rightarrow> \<open>\<lambda>a b. Add a b\<close>
      | E "*" E \<Rightarrow> \<open>\<lambda>a b. Mul a b\<close>
      | PNum \<Rightarrow> \<open>\<lambda>_. N\<close>
      | "(" E ")" \<Rightarrow> \<open>\<lambda>e. e\<close>

parser eq_s for eq and eq_e for eq (E)

thm eq_e.sound eq_e.complete

parser_check \<open>eq_s (toks 0 [PNum, PPlus, PNum, PStar, PNum]) = Some (Add N (Mul N N))\<close>
parser_check \<open>eq_e (toks 0 [PNum, PStar, PNum, PPlus, PNum]) = Some (Add (Mul N N) N)\<close>

subsection \<open>Merged lines and transitivity\<close>

grammar em =
  tokens \<open>p_tok\<close>
  terminals "+" = \<open>PPlus\<close> and "*" = \<open>PStar\<close> and "^" = \<open>PPow\<close>
  precedence left "*" > left "+"
  precedence right "^" > left "*"
  productions
    E :: \<open>p_exp\<close>
      = E "+" E \<Rightarrow> \<open>\<lambda>a b. Add a b\<close>
      | E "*" E \<Rightarrow> \<open>\<lambda>a b. Mul a b\<close>
      | E "^" E \<Rightarrow> \<open>\<lambda>a b. Pow a b\<close>
      | PNum \<Rightarrow> \<open>\<lambda>_. N\<close>

parser em_parse for em

parser_check \<open>em_parse (toks 0 [PNum, PPow, PNum, PPlus, PNum]) = Some (Add (Pow N N) N)\<close>

subsection \<open>Diagnostics and recovery\<close>

grammar er =
  tokens \<open>p_tok\<close>
  terminals "+" = \<open>PPlus\<close> and "*" = \<open>PStar\<close> and "(" = \<open>PLP\<close> and ")" = \<open>PRP\<close>
  precedence left "*" > left "+"
  productions
    E :: \<open>p_exp\<close>
      = E "+" E \<Rightarrow> \<open>\<lambda>a b. Add a b\<close>
      | E "*" E \<Rightarrow> \<open>\<lambda>a b. Mul a b\<close>
      | PNum \<Rightarrow> \<open>\<lambda>_. N\<close>
      | "(" E ")" \<Rightarrow> \<open>\<lambda>e. e\<close>
      | PErr \<Rightarrow> \<open>\<lambda>_. Bad\<close>

parser (diagnostics) er_parse for er recover PErr

thm er_parse_recover.clean er_parse_recover.no_error er_parse.sound

parser_check \<open>er_parse_recover (toks 0 [PNum, PPlus, PNum, PStar, PNum]) =
    ([], Some (Add N (Mul N N)))\<close>

parser_check \<open>(case er_parse_recover (toks 0 [PNum, PPlus, PRP, PStar, PNum]) of
    ([e], Some x) \<Rightarrow> pe_index e = 2 \<and> x = Add N (Mul Bad N)
  | _ \<Rightarrow> False)\<close>

value \<open>er_parse_recover (toks 0 [PNum, PPlus, PRP, PStar, PNum])\<close>
value \<open>er_parse_diag (toks 0 [PNum, PPlus, PPlus])\<close>

text \<open>The raw error speaks of the grammar: \<^const>\<open>pe_stack\<close> holds no symbol of \<open>G'\<close>.\<close>

parser_check \<open>(case er_parse_diag (toks 0 [PNum, PPlus, PPlus]) of
    Inl e \<Rightarrow> map fst (pe_stack e) = [Tm PPlus, Nt ''E''] | Inr _ \<Rightarrow> False)\<close>

parser_check \<open>(case er_parse_recover (toks 0 [PNum, PPlus, PRP, PStar, PNum]) of
    ([e], _) \<Rightarrow> map fst (pe_stack e) = [Tm PPlus, Nt ''E''] | _ \<Rightarrow> False)\<close>

subsection \<open>Without layout the chains are \<^const>\<open>Any\<close>, and the simple driver runs\<close>

parser_check \<open>ii ep_parse_gram\<close>

ML_val \<open>
  val ths = Proof_Context.get_thms \<^context> "ep_parse_ptabs_def"
  val _ = \<^assert> (not (null ths))
\<close>

text \<open>The tables are those of the restricted grammar, the text is about the grammar.\<close>

value \<open>case er_parse_diag (toks 0 [PNum, PPlus, PPlus]) of
    Inl e \<Rightarrow> perr_render er_parse_info (\<lambda>_. '''') e | _ \<Rightarrow> ''''\<close>

parser_check \<open>case er_parse_diag (toks 0 [PNum, PPlus, PPlus]) of
    Inl e \<Rightarrow> sym_text er_parse_info (fst (pe_stack e ! 1)) = ''E''
  | _ \<Rightarrow> False\<close>

subsection \<open>Layout\<close>

grammar el =
  tokens \<open>p_tok\<close>
  terminals "+" = \<open>PPlus\<close> and "*" = \<open>PStar\<close>
  precedence left "*" > left "+"
  productions
    E :: \<open>p_exp\<close>
      = E\<^sup>= "+"\<^sup>> E\<^sup>= \<Rightarrow> \<open>\<lambda>a b. Add a b\<close>
      | E\<^sup>= "*"\<^sup>> E\<^sup>= \<Rightarrow> \<open>\<lambda>a b. Mul a b\<close>
      | PNum\<^sup>\<ge> \<Rightarrow> \<open>\<lambda>_. N\<close>

parser el_parse for el

parser_check \<open>el_parse (toks 0 [PNum, PPlus, PNum, PStar, PNum]) = Some (Add N (Mul N N))\<close>

subsection \<open>Unordered levels stay ambiguous, the report says so under the names of the grammar\<close>

grammar eu =
  tokens \<open>p_tok\<close>
  terminals "+" = \<open>PPlus\<close> and "*" = \<open>PStar\<close> and "^" = \<open>PPow\<close> and "-" = \<open>PMinus\<close>
  precedence left "*" > left "+"
  precedence right "^" > left "-"
  productions
    E :: \<open>p_exp\<close>
      = E "+" E \<Rightarrow> \<open>\<lambda>a b. Add a b\<close>
      | E "*" E \<Rightarrow> \<open>\<lambda>a b. Mul a b\<close>
      | E "^" E \<Rightarrow> \<open>\<lambda>a b. Pow a b\<close>
      | E "-" E \<Rightarrow> \<open>\<lambda>a b. Sub a b\<close>
      | PNum \<Rightarrow> \<open>\<lambda>_. N\<close>

parser eu_parse for eu

subsection \<open>A relation family stays out of it\<close>

grammar (relation) ev =
  tokens \<open>p_tok\<close>
  terminals "+" = \<open>PPlus\<close> and "*" = \<open>PStar\<close>
  precedence left "*" > left "+"
  productions
    E :: \<open>p_exp\<close>
      = E "+" E \<Rightarrow> \<open>\<lambda>a b. Add a b\<close>
      | E "*" E \<Rightarrow> \<open>\<lambda>a b. Mul a b\<close>
      | PNum \<Rightarrow> \<open>\<lambda>_. N\<close>

parser ev_parse for ev

thm ev_parse.sound ev_parse.complete

subsection \<open>Errors of the declarations\<close>

ML \<open>
fun command_error src =
  let val thy = \<^theory> in
    (fold Toplevel.command_exception (Outer_Syntax.parse_text thy (K {skip_theory = false, theory = thy}) Position.none src)
       (Toplevel.make_state (SOME (Context.Theory thy))); NONE)
    handle Runtime.EXCURSION_FAIL (exn, _) => SOME (Runtime.exn_message exn)
  end;

fun decl_grammar decls alts =
  "grammar bad = tokens p_tok terminals \"+\" = PPlus and \"*\" = PStar " ^ decls ^
  " productions E :: p_exp = E \"+\" E \<Rightarrow> \<open>\<lambda>a b. Add a b\<close>" ^
  " | E \"*\" E \<Rightarrow> \<open>\<lambda>a b. Mul a b\<close> | PNum \<Rightarrow> \<open>\<lambda>_. N\<close>" ^ alts;

fun rejected frag decls alts =
  (case command_error (decl_grammar decls alts) of
    NONE => error ("accepted: " ^ decls ^ alts)
  | SOME msg =>
      if String.isSubstring frag msg then () else error ("unexpected: " ^ msg));
\<close>

ML_val \<open>
  val ok = decl_grammar "precedence left \"*\" > left \"+\"" "";
  val _ = \<^assert> (is_none (command_error ok));
  val _ = rejected "cyclic" "precedence left \"*\" > left \"+\" precedence left \"+\" > left \"*\"" "";
  val _ = rejected "is both" "precedence left \"+\" precedence right \"+\"" "";
  val _ = rejected "no production goes by" "precedence left \"%\"" "";
  val _ = rejected "not one of" "precedence sideways \"+\"" "";
  val _ = rejected "forbid: position 9" "precedence left \"+\" forbid \"+\" @ 9 right \"*\"" "";
  val _ = rejected "is not one of direct" "precedence left \"+\" forbid \"+\" @ 0 sideways \"*\"" "";
  val _ = rejected "cannot have declarations" "precedence left \"+\"" " | E \<Rightarrow> \<open>\<lambda>e. e\<close>";
\<close>

text \<open>A \<open>(prec NAME)\<close> without any declaration is accepted and ignored (expected warning).\<close>

ML_val \<open>
  \<^assert> (is_none (command_error (decl_grammar "" " | \"*\" E (prec UMINUS) \<Rightarrow> \<open>\<lambda>a. Neg a\<close>")))
\<close>

subsection \<open>What the command prints about \<open>G'\<close>\<close>

text \<open>The messages of a command, run on a copy of the theory. The output hooks are
  wrapped, not replaced, so everything is still printed; kept are the messages that
  start with the given prefix.\<close>

ML \<open>
fun command_output thy prefix src =
  let
    val buf = Synchronized.var "command_output" ([]: string list);
    fun keep orig xs =
      let val s = XML.content_of (YXML.parse_body (implode xs)) in
        (if String.isPrefix prefix s then Synchronized.change buf (cons s) else (); orig xs)
      end;
    val (w0, l0) = (! Private_Output.warning_fn, ! Private_Output.writeln_fn);
    fun restore () = (Private_Output.warning_fn := w0; Private_Output.writeln_fn := l0);
    val _ = (Private_Output.warning_fn := keep w0; Private_Output.writeln_fn := keep l0);
    val res =
      Exn.capture (fn () =>
        fold Toplevel.command_exception (Outer_Syntax.parse_text thy (K {skip_theory = false, theory = thy}) Position.none src)
          (Toplevel.make_state (SOME (Context.Theory thy)))) ();
    val _ = restore ();
    val _ = Exn.release res;
  in rev (Synchronized.value buf) end;
\<close>

text \<open>Two lines that do not relate \<open>"+"\<close> and \<open>"*"\<close>, which stay ambiguous.\<close>

grammar eh =
  tokens \<open>p_tok\<close>
  terminals "+" = \<open>PPlus\<close> and "*" = \<open>PStar\<close>
  precedence left "+"
  precedence left "*"
  productions
    E :: \<open>p_exp\<close>
      = E "+" E \<Rightarrow> \<open>\<lambda>a b. Add a b\<close>
      | E "*" E \<Rightarrow> \<open>\<lambda>a b. Mul a b\<close>
      | PNum \<Rightarrow> \<open>\<lambda>_. N\<close>

text \<open>The report names the productions of the grammar. A state whose evidence is two
  copies of one production of \<open>G'\<close>, or a unit chain of \<open>G'\<close>, prints them as such
  (the limit of 14a); the example below the line is what explains it. No chain carries
  its \<open>\<^sup>=\<close>, and each state has one line. Under \<open>[[grammar_timing]]\<close> the sizes are
  those of \<open>G'\<close>, the grammar the tables are built from: 6 productions, where \<open>eh\<close> has 3.
  The two commands run one after the other, as each wraps the output hooks.\<close>

ML_val \<open>
  val report = command_output \<^theory> "parser: \<open>eh_t\<close>" "parser eh_t for eh";
  val _ = \<^assert> (report = [cat_lines
    ["parser: \<open>eh_t\<close> (grammar \<open>eh\<close>, start \<open>E\<close>) has LR conflicts in 3 states (3 with a layout witness); \<open>mdet\<close> kept as an assumption on .complete",
     "state after \<open>E \"+\" E \"*\" E\<close>:",
     "  reduce/reduce on \"+\" \"*\":  reduce \<open>E = E \"*\" E\<close>  vs  reduce \<open>E = E \"*\" E\<close>",
     "  example \<open>PNum \"+\" PNum \"*\" PNum \<cdot> \"+\"\<close>: two actions live (all tokens at column 0)",
     "state after \<open>E \"+\" PNum\<close>:",
     "  reduce/reduce on \"+\" \"*\":  reduce \<open>E = PNum\<close>  vs  reduce \<open>E = PNum\<close>",
     "  example \<open>PNum \"+\" PNum \<cdot> \"+\"\<close>: two actions live (all tokens at column 0)",
     "state after \<open>E \"*\" E\<close>:",
     "  reduce/reduce on \"+\" \"*\":  reduce \<open>E = E\<close>  vs  reduce \<open>E = E \"*\" E\<close>",
     "  example \<open>PNum \"*\" PNum \<cdot> \"+\"\<close>: two actions live (all tokens at column 0)"]]);
  val sizes = command_output \<^theory> "[parser] sizes" "declare [[grammar_timing]] parser eh_s for eh";
  val _ = \<^assert> (case sizes of
      [s] => String.isPrefix "[parser] sizes: productions = 6, nonterminals = 3, terminals = 3," s
    | _ => false);
\<close>

end
