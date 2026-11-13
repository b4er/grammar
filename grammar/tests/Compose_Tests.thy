(* Author: Basil Fürer *)

theory Compose_Tests
  imports TIGER_Grammar.LR_Prec_Parse Parser_Check
begin

section \<open>Composition by reference\<close>

text \<open>A grammar may use a nonterminal \<open>a.X\<close> of an earlier grammar \<open>a\<close>. The productions
  of \<open>a\<close> reachable from \<open>X\<close> are copied under the names \<open>a.Y\<close>, so the new grammar is
  closed and goes through the same definitions as any other. With \<open>(relation)\<close> on both,
  \<open>b.a_X_iff\<close> links the copied relation to the original one.\<close>

fun toks :: \<open>nat \<Rightarrow> 'tok list \<Rightarrow> ('tok, unit) token list\<close> where
  \<open>toks i [] = []\<close>
| \<open>toks i (x # xs) = \<lparr>tok = x, span = span.make 0 i i 1 []\<rparr> # toks (Suc (Suc i)) xs\<close>

datatype c_tok = CNum | CPlus | CStar | CLP | CRP | CSemi | CLB | CRB

datatype ex = N | Add ex ex | Mul ex ex

subsection \<open>Two layers\<close>

grammar (relation) cexp =
  tokens \<open>c_tok\<close>
  terminals "+" = \<open>CPlus\<close> and "*" = \<open>CStar\<close> and "(" = \<open>CLP\<close> and ")" = \<open>CRP\<close>
  productions
    E :: \<open>ex\<close> = E "+" T \<Rightarrow> \<open>Add\<close> | T
  and
    T :: \<open>ex\<close> = T "*" F \<Rightarrow> \<open>Mul\<close> | F
  and
    F :: \<open>ex\<close> = CNum \<Rightarrow> \<open>\<lambda>_. N\<close> | "(" E ")"

grammar (relation) cstm =
  tokens \<open>c_tok\<close>
  terminals ";" = \<open>CSemi\<close>
  productions
    S :: \<open>ex list\<close> = cexp.E \<Rightarrow> \<open>\<lambda>e. [e]\<close> | S ";" cexp.E \<Rightarrow> \<open>\<lambda>s e. s @ [e]\<close>

text \<open>The productions are those of \<open>cstm\<close>, then those of \<open>cexp\<close> under the new names, in
  the order of \<open>cexp\<close>.\<close>

lemma \<open>cstm =
  is_cfg.make
   [(''S'', [(Nt ''cexp.E'', Any)]),
    (''S'', [(Nt ''S'', Any), (Tm CSemi, Any), (Nt ''cexp.E'', Any)]),
    (''cexp.E'', [(Nt ''cexp.E'', Any), (Tm CPlus, Any), (Nt ''cexp.T'', Any)]),
    (''cexp.E'', [(Nt ''cexp.T'', Any)]),
    (''cexp.T'', [(Nt ''cexp.T'', Any), (Tm CStar, Any), (Nt ''cexp.F'', Any)]),
    (''cexp.T'', [(Nt ''cexp.F'', Any)]),
    (''cexp.F'', [(Tm CNum, Any)]),
    (''cexp.F'', [(Tm CLP, Any), (Nt ''cexp.E'', Any), (Tm CRP, Any)])]
   ''S'' 0\<close>
  by (simp only: cstm_def)

ML \<open>val _ = @{thms cstm.cexp_E_iff}\<close>

lemma \<open>cstm_cexp_E w x \<longleftrightarrow> cexp_E w x\<close>
  by (fact cstm.cexp_E_iff)

parser cstm_parse for cstm and cstm_parse_e for cstm (cexp.E)

parser_check \<open>cstm_parse (toks 0 [CNum, CPlus, CNum, CSemi, CNum, CStar, CNum]) =
  Some [Add N N, Mul N N]\<close>

parser_check \<open>cstm_parse_e (toks 0 [CLP, CNum, CPlus, CNum, CRP, CStar, CNum]) =
  Some (Mul (Add N N) N)\<close>

text \<open>What the entry of the copy proves is a fact about the original grammar.\<close>

lemma \<open>cstm_parse_e w = Some x \<Longrightarrow> cexp_E w x\<close>
  using cstm_parse_e.sound cstm.cexp_E_iff by blast

lemma \<open>cexp_E w x \<Longrightarrow> cstm_parse_e w = Some x\<close>
  using cstm_parse_e.complete cstm.cexp_E_iff by blast

subsection \<open>A copy of a copy; one nonterminal along two paths\<close>

text \<open>\<open>cblk\<close> uses \<open>cstm.S\<close>, which uses \<open>cexp.E\<close>, and \<open>cexp.E\<close> directly: \<open>cexp.E\<close>,
  \<open>cexp.T\<close>, \<open>cexp.F\<close> are copied once. \<open>"("\<close> is not declared here: the spellings of
  the copied productions' terminals come with them.\<close>

grammar (relation) cblk =
  tokens \<open>c_tok\<close>
  terminals "{" = \<open>CLB\<close> and "}" = \<open>CRB\<close>
  productions
    B :: \<open>ex list\<close>
      = "{" cstm.S "}"
      | "(" cexp.E ")" \<Rightarrow> \<open>\<lambda>e. [e]\<close>

lemma \<open>cblk =
  is_cfg.make
   [(''B'', [(Tm CLB, Any), (Nt ''cstm.S'', Any), (Tm CRB, Any)]),
    (''B'', [(Tm CLP, Any), (Nt ''cexp.E'', Any), (Tm CRP, Any)]),
    (''cstm.S'', [(Nt ''cexp.E'', Any)]),
    (''cstm.S'', [(Nt ''cstm.S'', Any), (Tm CSemi, Any), (Nt ''cexp.E'', Any)]),
    (''cexp.E'', [(Nt ''cexp.E'', Any), (Tm CPlus, Any), (Nt ''cexp.T'', Any)]),
    (''cexp.E'', [(Nt ''cexp.T'', Any)]),
    (''cexp.T'', [(Nt ''cexp.T'', Any), (Tm CStar, Any), (Nt ''cexp.F'', Any)]),
    (''cexp.T'', [(Nt ''cexp.F'', Any)]),
    (''cexp.F'', [(Tm CNum, Any)]),
    (''cexp.F'', [(Tm CLP, Any), (Nt ''cexp.E'', Any), (Tm CRP, Any)])]
   ''B'' 0\<close>
  by (simp only: cblk_def)

lemma
  \<open>cblk_cstm_S w x \<longleftrightarrow> cstm_S w x\<close>
  \<open>cblk_cexp_E w y \<longleftrightarrow> cexp_E w y\<close>
  by (fact cblk.cstm_S_iff cblk.cexp_E_iff)+

parser cblk_parse for cblk

parser_check \<open>cblk_parse (toks 0 [CLB, CNum, CSemi, CLP, CNum, CPlus, CNum, CRP, CRB]) =
  Some [N, Add N N]\<close>

subsection \<open>Precedence declarations travel with the copied productions\<close>

grammar pexp =
  tokens \<open>c_tok\<close>
  terminals "+" = \<open>CPlus\<close> and "*" = \<open>CStar\<close> and "(" = \<open>CLP\<close> and ")" = \<open>CRP\<close>
  precedence left "*" > left "+"
  productions
    E :: \<open>ex\<close>
      = E "+" E \<Rightarrow> \<open>Add\<close>
      | E "*" E \<Rightarrow> \<open>Mul\<close>
      | CNum \<Rightarrow> \<open>\<lambda>_. N\<close>
      | "(" E ")"

text \<open>\<open>puse\<close> declares nothing; the levels of \<open>pexp\<close> apply to its copy of \<open>pexp.E\<close>.\<close>

grammar puse =
  tokens \<open>c_tok\<close>
  terminals "{" = \<open>CLB\<close> and "}" = \<open>CRB\<close>
  productions
    P :: \<open>ex\<close> = "{" pexp.E "}"

ML \<open>
  val (_, gr) = Grammar_Common.check_grammar \<^context> ("puse", Position.none);
  \<^assert> (#prec gr = SOME {chains = [[("left", [(1, false)]), ("left", [(2, false)])]],
    forbids = []})
\<close>

parser puse_parse for puse

parser_check \<open>puse_parse (toks 0 [CLB, CNum, CPlus, CNum, CStar, CNum, CRB]) = Some (Add N (Mul N N))\<close>

parser_check \<open>puse_parse (toks 0 [CLB, CNum, CStar, CNum, CPlus, CNum, CRB]) = Some (Add (Mul N N) N)\<close>

parser_check \<open>puse_parse (toks 0 [CLB, CNum, CPlus, CNum, CPlus, CNum, CRB]) = Some (Add (Add N N) N)\<close>

subsection \<open>Layout: the copy keeps its annotations, the link keeps the indentation\<close>

datatype l_tok = LDo | LId | LSemi

grammar (relation) ldo =
  tokens \<open>l_tok\<close>
  terminals "do" = \<open>LDo\<close>
  productions
      Expr :: \<open>nat\<close>
        = LId\<^sup>>          \<Rightarrow> \<open>\<lambda>_. 0\<close>
        | "do"\<^sup>> Stmts\<^sup>> \<Rightarrow> \<open>\<lambda>n. n\<close>
    and
      Stmts :: \<open>nat\<close>
        = Stmt\<^sup>=          \<Rightarrow> \<open>\<lambda>_. 1\<close>
        | Stmts\<^sup>= Stmt\<^sup>= \<Rightarrow> \<open>\<lambda>n _. Suc n\<close>
    and
      Stmt :: \<open>nat\<close>
        = LId\<^sup>=          \<Rightarrow> \<open>\<lambda>_. 0\<close>
        | "do"\<^sup>= Stmts\<^sup>> \<Rightarrow> \<open>\<lambda>n. n\<close>

grammar (relation) lmain =
  tokens \<open>l_tok\<close>
  terminals ";" = \<open>LSemi\<close>
  productions
    M :: \<open>nat list\<close> = ldo.Expr\<^sup>\<ge> \<Rightarrow> \<open>\<lambda>n. [n]\<close> | M ";" ldo.Expr\<^sup>\<ge> \<Rightarrow> \<open>\<lambda>ms n. ms @ [n]\<close>

lemma \<open>lmain_ldo_Expr i w x \<longleftrightarrow> ldo_Expr i w x\<close>
  by (fact lmain.ldo_Expr_iff)

parser lmain_parse for lmain

definition lt :: \<open>nat \<Rightarrow> l_tok \<Rightarrow> (l_tok, unit) token\<close> where
  \<open>lt c x = \<lparr>tok = x, span = span.make 0 c 0 1 []\<rparr>\<close>

parser_check \<open>lmain_parse [lt 1 LDo, lt 4 LId, lt 4 LId, lt 4 LSemi, lt 6 LId] = Some [2, 0]\<close>

parser_check \<open>lmain_parse [lt 1 LDo, lt 4 LId, lt 5 LId] = None\<close>

subsection \<open>Bare names: \<open>open\<close>\<close>

text \<open>Under \<open>open a\<close>, a bare name that no local nonterminal or terminal class claims and
  that \<open>a\<close> defines is \<open>a\<close>'s: \<open>copen\<close> is \<open>cstm\<close> written without qualifiers.\<close>

grammar copen = open cexp
  tokens \<open>c_tok\<close>
  terminals ";" = \<open>CSemi\<close>
  productions
    S :: \<open>ex list\<close> = E \<Rightarrow> \<open>\<lambda>e. [e]\<close> | S ";" E \<Rightarrow> \<open>\<lambda>s e. s @ [e]\<close>

lemma \<open>copen =
  is_cfg.make
   [(''S'', [(Nt ''cexp.E'', Any)]),
    (''S'', [(Nt ''S'', Any), (Tm CSemi, Any), (Nt ''cexp.E'', Any)]),
    (''cexp.E'', [(Nt ''cexp.E'', Any), (Tm CPlus, Any), (Nt ''cexp.T'', Any)]),
    (''cexp.E'', [(Nt ''cexp.T'', Any)]),
    (''cexp.T'', [(Nt ''cexp.T'', Any), (Tm CStar, Any), (Nt ''cexp.F'', Any)]),
    (''cexp.T'', [(Nt ''cexp.F'', Any)]),
    (''cexp.F'', [(Tm CNum, Any)]),
    (''cexp.F'', [(Tm CLP, Any), (Nt ''cexp.E'', Any), (Tm CRP, Any)])]
   ''S'' 0\<close>
  by (simp only: copen_def)

text \<open>A local nonterminal comes first: \<open>E\<close> here is \<open>cshadow\<close>'s own, \<open>T\<close> is
  \<open>cexp.T\<close>; and \<open>X+\<close> over an opened name is one instance with \<open>cexp.T+\<close>.\<close>

grammar cshadow = open cexp
  tokens \<open>c_tok\<close>
  terminals ";" = \<open>CSemi\<close>
  productions
    E :: \<open>ex list\<close> = T+ | ";" cexp.T+

lemma \<open>cshadow =
  is_cfg.make
   [(''E'', [(Nt ''cexp.T+'', Any)]),
    (''E'', [(Tm CSemi, Any), (Nt ''cexp.T+'', Any)]),
    (''cexp.T+'', [(Nt ''cexp.T'', Any)]),
    (''cexp.T+'', [(Nt ''cexp.T+'', Any), (Nt ''cexp.T'', Any)]),
    (''cexp.T'', [(Nt ''cexp.T'', Any), (Tm CStar, Any), (Nt ''cexp.F'', Any)]),
    (''cexp.T'', [(Nt ''cexp.F'', Any)]),
    (''cexp.F'', [(Tm CNum, Any)]),
    (''cexp.F'', [(Tm CLP, Any), (Nt ''cexp.E'', Any), (Tm CRP, Any)]),
    (''cexp.E'', [(Nt ''cexp.E'', Any), (Tm CPlus, Any), (Nt ''cexp.T'', Any)]),
    (''cexp.E'', [(Nt ''cexp.T'', Any)])]
   ''E'' 0\<close>
  by (simp only: cshadow_def)

subsection \<open>Messages name a copy without its grammar\<close>

text \<open>\<open>cexp.T\<close> shows as \<open>T\<close>. Where a local nonterminal and a copy would show alike, as
  \<open>E\<close> and \<open>cexp.E\<close> in \<open>cshadow\<close>, the copy keeps its qualifier.\<close>

parser (diagnostics) cshadow_diag for cshadow

parser_check \<open>(case cshadow_diag_diag (toks 0 [CLP, CNum, CNum]) of
    Inl e \<Rightarrow> pmsg_lines (perr_message cshadow_diag_info (\<lambda>_. []) e) | Inr _ \<Rightarrow> []) =
  [''0:4: syntax error at '' @ squote ''CNum'',
   ''  expected: '' @ squote ''*'' @ '', '' @ squote '')'' @ '' or '' @ squote ''+'',
   ''  up to here: a T was recognised'']\<close>
ML \<open>
  \<^assert> (Grammar_Common.display_names \<^context> ["S", \<^unchecked_name>\<open>cexp.E\<close>, \<^unchecked_name>\<open>cexp.T\<close>, "cexp.T+"] =
    [(\<^unchecked_name>\<open>cexp.E\<close>, "E"), (\<^unchecked_name>\<open>cexp.T\<close>, "T"), ("cexp.T+", "T+")]);
  \<^assert> (Grammar_Common.display_names \<^context> ["E", \<^unchecked_name>\<open>cexp.E\<close>, \<^unchecked_name>\<open>cexp.T\<close>, "Q(cexp.T, \";\")"] =
    [(\<^unchecked_name>\<open>cexp.T\<close>, "T"), ("Q(cexp.T, \";\")", "Q(T, \";\")")]);
\<close>

subsection \<open>Numbered nonterminals: \<open>grammar_nat_labels\<close>\<close>

text \<open>Under \<open>[[grammar_nat_labels]]\<close> a nonterminal is a number in HOL, in the order of
  \<open>#no\<close>: the grammar's own in their order, then the copies. The numbers skip 1, which
  the simplifier would turn into \<open>Suc 0\<close>. Everything else is as with names,
  and messages still show the names.\<close>

declare [[grammar_nat_labels]]

grammar (relation) nstm = open cexp
  tokens \<open>c_tok\<close>
  terminals ";" = \<open>CSemi\<close>
  productions
    S :: \<open>ex list\<close> = E \<Rightarrow> \<open>\<lambda>e. [e]\<close> | S ";" E \<Rightarrow> \<open>\<lambda>s e. s @ [e]\<close>

lemma \<open>nstm =
  is_cfg.make
   [(0, [(Nt 2, Any)]),
    (0, [(Nt 0, Any), (Tm CSemi, Any), (Nt 2, Any)]),
    (2, [(Nt 2, Any), (Tm CPlus, Any), (Nt 3, Any)]),
    (2, [(Nt 3, Any)]),
    (3, [(Nt 3, Any), (Tm CStar, Any), (Nt 4, Any)]),
    (3, [(Nt 4, Any)]),
    (4, [(Tm CNum, Any)]),
    (4, [(Tm CLP, Any), (Nt 2, Any), (Tm CRP, Any)])]
   0 0\<close>
  by (simp only: nstm_def)

lemma \<open>nstm_cexp_E w x \<longleftrightarrow> cexp_E w x\<close>
  by (fact nstm.cexp_E_iff)

parser nstm_parse for nstm and nstm_parse_e for nstm (cexp.E)

parser_check \<open>nstm_parse (toks 0 [CNum, CPlus, CNum, CSemi, CNum, CStar, CNum]) =
  Some [Add N N, Mul N N]\<close>

parser_check \<open>nstm_parse_e (toks 0 [CLP, CNum, CPlus, CNum, CRP, CStar, CNum]) =
  Some (Mul (Add N N) N)\<close>

lemma \<open>nstm_parse w = Some x \<Longrightarrow> nstm_S w x\<close> \<open>nstm_S w x \<Longrightarrow> nstm_parse w = Some x\<close>
  by (fact nstm_parse.sound nstm_parse.complete)+

lemma \<open>nstm_parse_e w = Some x \<Longrightarrow> cexp_E w x\<close>
  using nstm_parse_e.sound nstm.cexp_E_iff by blast

parser (diagnostics) nstm_diag for nstm

parser_check \<open>(case nstm_diag_diag (toks 0 [CLP, CNum, CNum]) of
    Inl e \<Rightarrow> pmsg_lines (perr_message nstm_diag_info (\<lambda>_. []) e) | Inr _ \<Rightarrow> []) =
  [''0:4: syntax error at '' @ squote ''CNum'',
   ''  expected: '' @ squote ''+'' @ '', '' @ squote ''*'' @ '' or '' @ squote '')'']\<close>

text \<open>The messages name the nonterminals, not their numbers.\<close>

parser_check \<open>map (pi_nt nstm_diag_info) [0, 2, 3, 4] = [''S'', ''E'', ''T'', ''F'']\<close>

text \<open>Under layout.\<close>

grammar (relation) nlay = open ldo
  tokens \<open>l_tok\<close>
  terminals ";" = \<open>LSemi\<close>
  productions
    M :: \<open>nat list\<close> = Expr\<^sup>\<ge> \<Rightarrow> \<open>\<lambda>n. [n]\<close> | M ";" Expr\<^sup>\<ge> \<Rightarrow> \<open>\<lambda>ms n. ms @ [n]\<close>

parser nlay_parse for nlay

parser_check \<open>nlay_parse [lt 1 LDo, lt 4 LId, lt 4 LId, lt 4 LSemi, lt 6 LId] = Some [2, 0]\<close>

lemma \<open>nlay_parse w = Some x \<Longrightarrow> nlay_M 0 w x\<close>
  by (fact nlay_parse.sound)

declare [[grammar_nat_labels = false]]

subsection \<open>Errors\<close>

ML \<open>
fun command_error src =
  let val thy = \<^theory> in
    (fold Toplevel.command_exception (Outer_Syntax.parse_text thy (K {skip_theory = false, theory = thy}) Position.none src)
       (Toplevel.make_state (SOME (Context.Theory thy))); NONE)
    handle Runtime.EXCURSION_FAIL (exn, _) => SOME (Runtime.exn_message exn)
  end;

fun rejected frag src =
  (case command_error src of
    NONE => error ("accepted: " ^ src)
  | SOME msg =>
      if String.isSubstring frag msg then () else error ("unexpected: " ^ msg));
\<close>

ML \<open>
  val _ = \<^assert> (is_none (command_error
    "grammar ok = tokens c_tok productions X :: ex = cexp.E \<Rightarrow> \<open>\<lambda>e. e\<close>"));
  val _ = rejected "has no nonterminal \"Q\""
    "grammar bad = tokens c_tok productions X :: ex = cexp.Q \<Rightarrow> \<open>\<lambda>e. e\<close>";
  val _ = rejected "has the token type"
    "grammar bad = productions X :: ex = cexp.E \<Rightarrow> \<open>\<lambda>e. e\<close>";
  val _ = rejected "a defined nonterminal has a plain name"
    "grammar bad = tokens c_tok productions a.X :: ex = cexp.E \<Rightarrow> \<open>\<lambda>e. e\<close>";
  val _ = rejected "have one name \"cexp_E\""
    "grammar bad = tokens c_tok productions cexp_E :: ex = cexp.E \<Rightarrow> \<open>\<lambda>e. e\<close>";
  val _ = rejected "The spelling \"+\""
    "grammar bad = tokens c_tok terminals \"+\" = CStar productions X :: ex = cexp.E \<Rightarrow> \<open>\<lambda>e. e\<close>";
  val _ = rejected "is defined by the opened grammars \"cexp\", \"pexp\""
    "grammar bad = open cexp pexp tokens c_tok productions X :: ex = E \<Rightarrow> \<open>\<lambda>e. e\<close>";
  val _ = rejected "is opened twice"
    "grammar bad = open cexp cexp tokens c_tok productions X :: ex = E \<Rightarrow> \<open>\<lambda>e. e\<close>";
  val _ = rejected "Carrier inference"
    "grammar bad = tokens c_tok productions X :: \<open>ex list\<close> = cexp.E \<Rightarrow> \<open>\<lambda>e. Add e\<close>";
\<close>

end
