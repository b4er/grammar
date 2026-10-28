theory Regression_Tests
  imports LR_Parser.LR_Parser
begin

section \<open>Command-level regression tests\<close>

definition tu :: \<open>nat \<Rightarrow> 'tok \<Rightarrow> char list \<Rightarrow> ('tok, unit) token\<close> where
  \<open>tu i x u = \<lparr>tok = x, span = span.make 0 i 0 (length u) []\<rparr>\<close>

subsection \<open>Aligned \<open>do\<close> blocks: unconditional completeness + layout\<close>

datatype do_tok = DDo | DId

grammar (relation) do =
  tokens \<open>do_tok\<close>
  terminals "do" = \<open>DDo\<close>
  productions
      Expr :: \<open>unit\<close>
        = DId\<^sup>>          \<Rightarrow> \<open>\<lambda>_. ()\<close>
        | "do"\<^sup>> BStmts\<^sup>> \<Rightarrow> \<open>\<lambda>_. ()\<close>
    and
      BStmts :: \<open>unit\<close>
        = BExpr\<^sup>=         \<Rightarrow> \<open>\<lambda>_. ()\<close>
        | BStmts\<^sup>= BExpr\<^sup>= \<Rightarrow> \<open>\<lambda>_ _. ()\<close>
    and
      BExpr :: \<open>unit\<close>
        = DId\<^sup>=          \<Rightarrow> \<open>\<lambda>_. ()\<close>
        | "do"\<^sup>= BStmts\<^sup>> \<Rightarrow> \<open>\<lambda>_. ()\<close>

parser do_parse2 for do

text \<open>Accepted and rejected layouts of adams2013 subsection 5.7.\<close>

lemma \<open>do_parse2 [tu 1 DDo ''do'', tu 4 DDo ''do'', tu 7 DId ''x''] = Some ()\<close>
  by eval

lemma \<open>do_parse2
  [tu 1 DDo ''do'', tu 4 DDo ''do'', tu 7 DId ''x'', tu 2 DId ''y''] = None\<close>
  by eval

lemma \<open>do_parse2
  [tu 1 DDo ''do'', tu 4 DDo ''do'', tu 7 DId ''x'', tu 4 DId ''y''] = Some ()\<close>
  by eval

lemma \<open>do_parse2
  [tu 1 DDo ''do'', tu 4 DDo ''do'', tu 7 DId ''x'', tu 7 DId ''y''] = Some ()\<close>
  by eval

text \<open> The emitted theorems are hypothesis-free: no mentions of \<^const>\<open>mdet\<close> or \<^const>\<open>fresh_name\<close>.\<close>

lemma \<open>w \<in> ilang do \<Longrightarrow> \<exists>x. do_parse2 w = Some x\<close>
  by (fact do_parse2.complete_lang)

text \<open>With \<open>(relation)\<close>, \<open>.sound\<close> / \<open>.complete\<close> are stated against the
  relation of the start symbol, also hypothesis-free: the accept/reduce
  check \<^const>\<open>acc_conflicts\<close> is empty as well.\<close>

lemma \<open>do_parse2 w = Some x \<Longrightarrow> do_Expr 0 w x\<close>
  by (fact do_parse2.sound)

lemma \<open>do_Expr 0 w x \<Longrightarrow> do_parse2 w = Some x\<close>
  by (fact do_parse2.complete)

subsection \<open>The accept/reduce check: a cycle through the start symbol\<close>

text \<open>\<^const>\<open>mdet\<close> alone does not make the relational \<open>.complete\<close> true: the
  conflict report ignores the start production, so a grammar with
  \<open>S \<Rightarrow>⁺ S\<close> passes it, while the relation assigns two values to one word
  and the driver returns the first parse.  \<^const>\<open>acc_conflicts\<close> must be
  non-empty here, and the command keeps it as an assumption (expected
  warning).\<close>

grammar (relation) cyc =
  tokens \<open>do_tok\<close>
  productions
      S :: \<open>nat\<close> = A \<Rightarrow> \<open>\<lambda>a. a + 1\<close> | DId \<Rightarrow> \<open>\<lambda>_. 0\<close>
    and
      A :: \<open>nat\<close> = S \<Rightarrow> \<open>\<lambda>s. s\<close>

parser cyc_parse for cyc

text \<open>The code equation runs on the action table over the states, and
  numbers the tokens by a case distinction.\<close>

term \<open>cyc_parse_ptabs\<close>
lemma \<open>cyc_parse_tnum DId = pnum cyc_parse_ptabs DId\<close>
  by eval

lemma \<open>acc_conflicts cyc ''!'' \<noteq> []\<close>
  by eval

lemma \<open>map (\<lambda>(_, prs, _, _). prs) (explain_acc cyc ''!'' (acc_conflicts cyc ''!'')) = [[2]]\<close>
  by eval

lemma cyc_two_values:
  \<open>cyc_S [tu 1 DId ''x''] 0\<close> \<open>cyc_S [tu 1 DId ''x''] 1\<close>
proof -
  show 0: \<open>cyc_S [tu 1 DId ''x''] 0\<close> unfolding tu_def by (intro cyc.intros)
  have \<open>cyc_S [tu 1 DId ''x''] (0 + 1)\<close> by (intro cyc.intros 0)
  then show \<open>cyc_S [tu 1 DId ''x''] 1\<close> by simp
qed

lemma \<open>cyc_parse [tu 1 DId ''x''] = Some 0\<close>
  by eval

text \<open>So \<open>cyc_S w x \<Longrightarrow> cyc_parse w = Some x\<close> is false, and \<open>.complete\<close> still
  carries the check as a hypothesis:\<close>

lemma \<open>acc_conflicts cyc ''!'' = [] \<Longrightarrow> cyc_S w x \<Longrightarrow> cyc_parse w = Some x\<close>
  by (fact cyc_parse.complete)

text \<open>The simple driver on integer indices (\<open>parser_int_tables\<close>): the same
  parser, whose code equation runs on the integer tables \<open>cyc_parse_int_ztabs\<close>.\<close>

declare [[parser_int_tables]]
parser cyc_parse_int for cyc
declare [[parser_int_tables = false]]

term cyc_parse_int_ztabs

lemma \<open>cyc_parse_int [tu 1 DId ''x''] = Some 0\<close> \<open>cyc_parse_int [tu 1 DDo ''do''] = None\<close>
  by eval+

subsection \<open>The rejection path: an ambiguous grammar keeps \<open>mdet\<close>\<close>

datatype iswim_tok = IWhere | IPlus | IMinus | IEq | ILP | IRP | IId

grammar (relation) iswim =
  tokens \<open>iswim_tok\<close>
  terminals
    "where" = \<open>IWhere\<close> and "+" = \<open>IPlus\<close> and "-" = \<open>IMinus\<close> and
    "="     = \<open>IEq\<close>    and "(" = \<open>ILP\<close>   and ")" = \<open>IRP\<close>
  productions
      Expr :: \<open>unit\<close>
        = Expr\<^sup>= "where"\<^sup>\<ge> IId\<^sup>\<ge> "="\<^sup>\<ge> WExpr\<^sup>\<ge>  \<Rightarrow> \<open>\<lambda>_ _ _. ()\<close>
        | Expr\<^sup>= "+"\<^sup>\<ge> Expr\<^sup>=                 \<Rightarrow> \<open>\<lambda>_ _. ()\<close>
        | "-"\<^sup>\<ge> Expr\<^sup>=                       \<Rightarrow> \<open>\<lambda>_. ()\<close>
        | "("\<^sup>\<ge> Expr\<^sup>* ")"\<^sup>\<ge>                  \<Rightarrow> \<open>\<lambda>_. ()\<close>
        | IId\<^sup>\<ge>                             \<Rightarrow> \<open>\<lambda>_. ()\<close>
    and
      WExpr :: \<open>unit\<close>
        = WExpr\<^sup>= "where"\<^sup>\<ge> IId\<^sup>\<ge> "="\<^sup>\<ge> WExpr\<^sup>\<ge>  \<Rightarrow> \<open>\<lambda>_ _ _. ()\<close>
        | WExpr\<^sup>= "+"\<^sup>\<ge> Expr\<^sup>=                 \<Rightarrow> \<open>\<lambda>_ _. ()\<close>
        | "-"\<^sup>= Expr\<^sup>=                        \<Rightarrow> \<open>\<lambda>_. ()\<close>
        | "("\<^sup>= Expr\<^sup>* ")"\<^sup>\<ge>                   \<Rightarrow> \<open>\<lambda>_. ()\<close>
        | IId\<^sup>=                              \<Rightarrow> \<open>\<lambda>_. ()\<close>

parser iswim_parse2 for iswim

text \<open>\<open>iswim\<close> is genuinely ambiguous, the check
  fires, and the command must NOT emit an unconditional \<open>.complete\<close>:
  \<^const>\<open>mdet\<close> stays as an assumption.  Soundness is unconditional
  regardless.

  The driver still parses unambiguous ISWIM inputs (soundly):
  \<open>- x\<close> at columns 1 3.\<close>

lemma \<open>iswim_parse2 [tu 1 IMinus ''-'', tu 3 IId ''x''] = Some ()\<close>
  by eval


subsection \<open>Haskell \<open>case\<close> layout (adams2013 Figure 4): unconditional\<close>

datatype hc_tok = HCase | HOf | HLC | HRC | HSemi | HId

grammar (relation) hask_case =
  tokens \<open>hc_tok\<close>
  terminals
    "case" = \<open>HCase\<close> and "of" = \<open>HOf\<close>   and
    "{"    = \<open>HLC\<close>   and "}"  = \<open>HRC\<close>   and ";" = \<open>HSemi\<close>
  productions
      Case = "case"\<^sup>> Exp\<^sup>= "of"\<^sup>> AltBlock\<^sup>= \<Rightarrow> \<open>\<lambda>_ _. ()\<close>
    and
      Exp = HId\<^sup>\<ge> \<Rightarrow> \<open>\<lambda>_. ()\<close>
    and
      AltBlock :: \<open>unit\<close>
        = "{"\<^sup>> Alts\<^sup>* "}"\<^sup>* \<Rightarrow> \<open>\<lambda>_. ()\<close>
        | AltLayout\<^sup>>      \<Rightarrow> \<open>\<lambda>_. ()\<close>
    and
      AltLayout :: \<open>unit\<close>
        = Alts\<^sup>=            \<Rightarrow> \<open>\<lambda>_. ()\<close>
        | AltLayout\<^sup>= Alts\<^sup>= \<Rightarrow> \<open>\<lambda>_ _. ()\<close>
    and
      Alts :: \<open>unit\<close>
        = HId\<^sup>=            \<Rightarrow> \<open>\<lambda>_. ()\<close>
        | Alts\<^sup>= ";"\<^sup>\<ge> HId\<^sup>= \<Rightarrow> \<open>\<lambda>_ _. ()\<close>

parser hask_case_parse2 for hask_case

lemma \<open>hask_case_parse2
  [tu 1 HCase ''case'', tu 6 HId ''x'', tu 8 HOf ''of'',
   tu 3 HId ''A'', tu 3 HId ''B''] = Some ()\<close>
  by eval

lemma \<open>hask_case_parse2
  [tu 1 HCase ''case'', tu 6 HId ''x'', tu 8 HOf ''of'',
   tu 3 HId ''A'', tu 4 HId ''B''] = None\<close>
  by eval

subsection \<open>Python suites (adams2013 subsection 3.3.2, adapted): unconditional\<close>

datatype py_tok = PWhile | PColon | PId

grammar (relation) py_suite =
  tokens \<open>py_tok\<close>
  terminals "while" = \<open>PWhile\<close> and ":" = \<open>PColon\<close>
  productions
      WhileStmt = "while"\<^sup>> Test\<^sup>= ":"\<^sup>> Suite\<^sup>= \<Rightarrow> \<open>\<lambda>_ _. ()\<close>
    and
      Test = PId\<^sup>\<ge> \<Rightarrow> \<open>\<lambda>_. ()\<close>
    and
      Suite = Block\<^sup>> \<Rightarrow> \<open>\<lambda>_. ()\<close>
    and
      Block :: \<open>unit\<close>
        = BStatement\<^sup>=        \<Rightarrow> \<open>\<lambda>_. ()\<close>
        | Block\<^sup>= BStatement\<^sup>= \<Rightarrow> \<open>\<lambda>_ _. ()\<close>
    and
      BStatement = PId\<^sup>= \<Rightarrow> \<open>\<lambda>_. ()\<close>

parser py_parse2 for py_suite

lemma \<open>py_parse2
  [tu 1 PWhile ''while'', tu 7 PId ''x'', tu 8 PColon '':'',
   tu 3 PId ''y'', tu 3 PId ''z''] = Some ()\<close>
  by eval

lemma \<open>py_parse2
  [tu 1 PWhile ''while'', tu 7 PId ''x'', tu 8 PColon '':'',
   tu 3 PId ''y'', tu 4 PId ''z''] = None\<close>
  by eval

text \<open>Both are hypothesis-free (\<open>.complete\<close> theorems are unconditional).\<close>

lemma \<open>w \<in> ilang hask_case \<Longrightarrow> \<exists>x. hask_case_parse2 w = Some x\<close>
  by (fact hask_case_parse2.complete_lang)

lemma \<open>w \<in> ilang py_suite \<Longrightarrow> \<exists>x. py_parse2 w = Some x\<close>
  by (fact py_parse2.complete_lang)

lemma \<open>py_suite_WhileStmt 0 w x \<Longrightarrow> py_parse2 w = Some x\<close>
  by (fact py_parse2.complete)

lemma \<open>py_parse2 w = Some x \<Longrightarrow> py_suite_WhileStmt 0 w x\<close>
  by (fact py_parse2.sound)

subsection \<open>Extensible tokens\<close>

text \<open>The token record fixes only \<^const>\<open>tok\<close> and \<^const>\<open>span\<close>. The
  \<^theory_text>\<open>tokens\<close> clause names the (ground) token record type: the plain
  \<open>('tok, 'ch) token\<close>, or a client extension of it whose fields are then
  available to the semantic actions along with \<^const>\<open>tok\<close> and
  \<^const>\<open>span\<close>. A token class type \<open>T\<close>, as in the grammars above,
  abbreviates \<open>(T, unit) token\<close>.\<close>

datatype trivia = Whitespace | Comment

record py_token = \<open>(py_tok, nat) token\<close> +
  trailing :: \<open>(trivia \<times> nat span) list\<close>

datatype out = Foo \<open>(trivia \<times> nat span) list\<close> | Bar

grammar (relation) t_ext =
  tokens \<open>py_token\<close>
  terminals "while" = PWhile and ":" = \<open>PColon\<close>
  productions
    X = Y | "while" \<Rightarrow> \<open>Bar\<close>
  and
    Y = ":" PId \<Rightarrow> \<open>Foo \<circ> trailing\<close>

lemma \<open>(\<exists>x. t_ext_X w x) = (w \<in> ilang t_ext)\<close>
  by (fact t_ext.lang)

parser t_ext_parse for t_ext

lemma \<open>t_ext_parse [\<lparr>tok = PColon, span = \<lparr>s_line = 0, s_col = 0, s_off = 0, s_len = 1, s_txt = []\<rparr>, trailing = []\<rparr>,
                    \<lparr>tok = PId, span = \<lparr>s_line = 0, s_col = 2, s_off = 2, s_len = 1, s_txt = []\<rparr>,
                     trailing = [(Comment, \<lparr>s_line = 0, s_col = 4, s_off = 4, s_len = 3, s_txt = []\<rparr>)]\<rparr>]
       = Some (Foo [(Comment, \<lparr>s_line = 0, s_col = 4, s_off = 4, s_len = 3, s_txt = []\<rparr>)])\<close>
  by eval

text \<open>The plain record with a span payload, spelled out.\<close>

grammar (relation) t_span =
  tokens \<open>(py_tok, nat) token\<close>
  terminals "while" = PWhile and ":" = \<open>PColon\<close>
  productions
    X = Y | "while" \<Rightarrow> \<open>0\<close>
  and
    Y :: \<open>nat\<close> = ":" PId \<Rightarrow> \<open>\<lambda>t. s_col (span t) + length (s_txt (span t))\<close>

parser t_span_parse for t_span

lemma \<open>t_span_parse [\<lparr>tok = PColon, span = \<lparr>s_line = 0, s_col = 0, s_off = 0, s_len = 1, s_txt = [0]\<rparr>\<rparr>,
                     \<lparr>tok = PId, span = \<lparr>s_line = 0, s_col = 2, s_off = 2, s_len = 1, s_txt = [7, 7]\<rparr>\<rparr>]
       = Some 4\<close>
  by eval


subsection \<open>Decoders without \<open>(relation)\<close>\<close>

text \<open>\<^theory_text>\<open>parser\<close> needs only the grammar constant and the decoders,
  both of which every \<^theory_text>\<open>grammar\<close> defines; the \<open>(relation)\<close>
  option is not required for it, and \<open>.complete\<close> is still hypothesis-free.\<close>

grammar not =
  tokens bool
  productions X = \<open>False\<close> \<Rightarrow> \<open>True\<close> | \<open>True\<close> \<Rightarrow> \<open>False\<close>

parser parse_not for not

lemma \<open>parse_not [\<lparr>tok = False, span = \<lparr>s_line = 0, s_col = 0, s_off = 0, s_len = 1, s_txt = []\<rparr>\<rparr>] = Some True\<close>
  and \<open>parse_not [] = None\<close>
  by eval+

lemma \<open>w \<in> ilang not \<Longrightarrow> \<exists>x. parse_not w = Some x\<close>
  by (fact parse_not.complete)



subsection \<open>A terminal alternative listed before a nonterminal one\<close>

datatype abc_tok = PA | PB | PC

grammar (relation) term_first =
  tokens \<open>abc_tok\<close>
  productions S :: \<open>nat\<close> = PA \<Rightarrow> \<open>\<lambda>_. 0\<close> | B \<Rightarrow> \<open>\<lambda>b. b\<close>
    and B :: \<open>nat\<close> = PB \<Rightarrow> \<open>\<lambda>_. 1\<close>

parser term_first_parse for term_first

text \<open>The relational forms unconditional:\<close>

lemma \<open>term_first_S w x \<Longrightarrow> term_first_parse w = Some x\<close>
  by (fact term_first_parse.complete)

lemma \<open>term_first_parse w = Some x \<Longrightarrow> term_first_S w x\<close>
  by (fact term_first_parse.sound)


subsection \<open>Unit self-loop\<close>

grammar (relation) self_loop =
  tokens \<open>abc_tok\<close>
  productions S :: \<open>nat\<close> = S \<Rightarrow> \<open>\<lambda>s. s + 1\<close> | PA \<Rightarrow> \<open>\<lambda>_. 0\<close>

lemma \<open>(\<exists>x. self_loop_S w x) = (w \<in> ilang self_loop)\<close>
  by (fact self_loop.lang)


subsection \<open>\<open>grammar\<close> inside a locale\<close>

locale loc begin

grammar (relation) g =
  tokens \<open>abc_tok\<close>
  productions S :: \<open>nat\<close> = PA \<Rightarrow> \<open>\<lambda>_. 0\<close> | B PB \<Rightarrow> \<open>\<lambda>b _. b + 1\<close>
    and B :: \<open>nat\<close> = PB \<Rightarrow> \<open>\<lambda>_. 1\<close>

lemma \<open>(\<exists>x. g_S w x) = (w \<in> ilang g)\<close>
  by (fact g.lang)

end


subsection \<open>A duplicate production is rejected\<close>

ML \<open>
local
  fun alt v : Grammar_Common.alternative =
    ([(Grammar_Common.Ref ("PC", Position.none), NONE)],
     SOME (Input.string ("\<lambda>_. " ^ string_of_int v)));
  val dup : Grammar_Common.spec =
    {name = Binding.name "dup", tok_typ = SOME (Input.string "abc_tok"), terminals = [],
     productions = [((Binding.name "S", SOME (Input.string "nat")), [alt 0, alt 1])]};
in
val _ =
  (Named_Target.theory_map (Grammar_Command.grammar_cmd [] dup) \<^theory>;
   error "duplicate production accepted")
  handle ERROR msg =>
    if String.isPrefix "Duplicate production" msg then ()
    else error ("unexpected: " ^ msg)
end
\<close>

grammar (relation) one_alt =
  tokens \<open>abc_tok\<close>
  productions S :: \<open>nat\<close> = PC \<Rightarrow> \<open>\<lambda>_. 7\<close>

parser one_alt_parse for one_alt

lemma \<open>one_alt_S w x \<Longrightarrow> one_alt_parse w = Some x\<close>
  by (fact one_alt_parse.complete)


subsection \<open>Backend default, idempotence, input validation\<close>

parser term_first_parse2 for term_first   \<comment> \<open>a second parser for the same grammar\<close>

ML_val \<open>
  val ctxt = \<^context>;
  val thy = Proof_Context.theory_of ctxt;
  (* registering a backend does not change the default *)
  val _ =
    Parser_Generators.default (Parser_Generators.register "pr_dummy" LR_Backend.lr_gen thy)
      = SOME "LR"
    orelse error "register changed the default backend";
  (* define_relation_of returns the existing family *)
  val (sem1, _) = Grammar_Defs.define_relation_of ("term_first", Position.none) ctxt;
  val (sem2, _) = Grammar_Defs.define_relation_of ("term_first", Position.none) ctxt;
  val _ =
    map fst (#preds sem1) = map fst (#preds sem2)
    orelse error "define_relation_of is not idempotent";
  (* inputs are validated against the grammar record *)
  val g1 = snd (Grammar_Common.check_grammar ctxt ("term_first", Position.none));
  val g2 = snd (Grammar_Common.check_grammar ctxt ("self_loop", Position.none));
  val _ =
    (Parser_Rel_Bridge.prove ctxt g2 (the (Grammar_Defs.lookup_rel ctxt g1));
     error "foreign predicate family accepted")
    handle ERROR msg =>
      String.isPrefix "Parser_Rel_Bridge.prove" msg orelse error msg;
  val _ =
    (Grammar_Defs.decoder_of ctxt g1 "Nope"; error "unknown nonterminal accepted")
    handle ERROR msg =>
      String.isPrefix "decoder_of" msg orelse error msg;
\<close>


subsection \<open>Nonterminal names that used to collide with generated names\<close>

grammar (relation) dec_clash =
  tokens \<open>abc_tok\<close>
  productions A :: \<open>nat\<close> = PA \<Rightarrow> \<open>\<lambda>_. 0\<close> | dec_A \<Rightarrow> \<open>\<lambda>x. x\<close>
    and dec_A :: \<open>nat\<close> = PB \<Rightarrow> \<open>\<lambda>_. 1\<close>

parser dec_clash_parse for dec_clash

lemma \<open>dec_clash_A w x \<Longrightarrow> dec_clash_parse w = Some x\<close>
  by (fact dec_clash_parse.complete)

text \<open>The flat relation names can still collide across grammars (\<open>flat\<close> with
  \<open>A_B\<close> and \<open>flat_A\<close> with \<open>B\<close> both give \<open>flat_A_B\<close>); that is reported up
  front.\<close>

grammar (relation) flat =
  tokens \<open>abc_tok\<close>
  productions A_B :: \<open>nat\<close> = PA \<Rightarrow> \<open>\<lambda>_. 0\<close>

ML \<open>
local
  val clash : Grammar_Common.spec =
    {name = Binding.name "flat_A", tok_typ = SOME (Input.string "abc_tok"), terminals = [],
     productions =
      [((Binding.name "B", SOME (Input.string "nat")),
        [([(Grammar_Common.Ref ("PA", Position.none), NONE)], SOME (Input.string "\<lambda>_. 0"))])]};
in
val _ =
  (Named_Target.theory_map
     (Grammar_Command.grammar_cmd [Grammar_Command.Opt_Relation] clash) \<^theory>;
   error "relation name clash not detected")
  handle ERROR msg =>
    if String.isSubstring "already exists" msg then ()
    else error ("unexpected: " ^ msg)
end
\<close>

subsection \<open>\<open>parser\<close> inside a locale with assumptions\<close>

locale box = fixes alive :: bool assumes \<open>alive \<longrightarrow> exp 1 + pi \<in> range real_of_rat\<close>

grammar (in box) (relation) idk =
  tokens do_tok productions X = DId \<Rightarrow> \<open>\<lambda>_. alive\<close>

parser (in box) parse_sealed for idk

global_interpretation box False by unfold_locales simp

lemma \<open>parse_sealed [tu 0 DId ''F''] = Some False\<close> by eval

text \<open>The decoders of a locale with parameters are applied constants, not bare
  ones; the totality premise must still be discharged.\<close>

lemma \<open>idk_X w x \<Longrightarrow> parse_sealed w = Some x\<close>
  by (fact parse_sealed.complete)


subsection \<open>Long right-hand sides\<close>

text \<open>Decoder totality and both bridges were super-linear in the length of rhs:\<close>

grammar (relation) long_rhs =
  tokens \<open>abc_tok\<close>
  productions S :: \<open>nat\<close> = PA PB PC PA PB PC PA PB PC PA PB PC \<Rightarrow> \<open>\<lambda>_ _ _ _ _ _ _ _ _ _ _ _. 12\<close>

parser long_rhs_parse for long_rhs

lemma \<open>long_rhs_S w x \<Longrightarrow> long_rhs_parse w = Some x\<close>
  by (fact long_rhs_parse.complete)


subsection \<open>Unit self-loops with identity actions\<close>

text \<open>The intro of \<open>S = S \<Rightarrow> \<open>\<lambda>n. n\<close>\<close> is \<open>id_loop_S w x \<Longrightarrow> id_loop_S w x\<close>; with it in the
  classical rule set, the depth-first search closing \<open>dec_sound\<close> never
  returned (the \<open>parser\<close> command hung after its \<open>mdet\<close> warning).  Such
  intros are dropped from the rule set: the node they describe is closed by
  the induction hypothesis.  The grammar is ambiguous (every derivation can
  be extended through the loops), so both checks fire: expected warnings,
  a reduce/reduce conflict at end of input after \<open>A\<close> and an accept/reduce
  conflict after \<open>S\<close>.\<close>

grammar (relation) id_loop =
  tokens \<open>abc_tok\<close>
  productions S :: \<open>nat\<close> = S \<Rightarrow> \<open>\<lambda>n. n\<close> | A \<Rightarrow> \<open>\<lambda>_. 0\<close>
    and A :: \<open>unit\<close> = A \<Rightarrow> \<open>\<lambda>u. u\<close> | \<Rightarrow> \<open>()\<close>

parser id_loop_parse for id_loop

lemma \<open>id_loop_parse w = Some x \<Longrightarrow> id_loop_S w x\<close>
  by (fact id_loop_parse.sound)


subsection \<open>A unit self-loop under a relation keeps the relational forms\<close>

text \<open>Under \<open>^>\<close> the loop's intro is \<open>gt_loop_A j w x \<Longrightarrow> i < j \<Longrightarrow> gt_loop_A i w x\<close>:
  not circular, and the only rule closing that node of \<open>dec_sound\<close>.  The
  bridge keeps it out of the classical rule set and applies it once when the
  search fails; dropping it, as for \<open>id_loop\<close>, lost the relational forms.
  Expected warning: an accept/reduce conflict (a cycle through the start
  symbol).\<close>

grammar (relation) gt_loop =
  tokens \<open>abc_tok\<close>
  productions A :: \<open>nat\<close> = A^> \<Rightarrow> \<open>\<lambda>n. n\<close> | PA \<Rightarrow> \<open>\<lambda>_. 0\<close>

parser gt_loop_parse for gt_loop

lemma \<open>gt_loop_parse w = Some x \<Longrightarrow> gt_loop_A 0 w x\<close>
  by (fact gt_loop_parse.sound)

lemma \<open>acc_conflicts gt_loop ''!'' = [] \<Longrightarrow> gt_loop_A 0 w x \<Longrightarrow> gt_loop_parse w = Some x\<close>
  by (fact gt_loop_parse.complete)


subsection \<open>A unit self-loop reduce at end of input terminates\<close>

text \<open>After \<open>B = PB\<close> the frame offers \<open>B = B\<close> before \<open>C = B\<close>; that reduce
  rebuilds the frame it popped, and the fixed-point driver used to run forever
  on \<open>PB\<close>.  Its code equation (\<open>drun_hist\<close>) stops at the repeated
  configuration and returns \<^const>\<open>None\<close>.  Expected warning: a
  reduce/reduce conflict at end of input, so \<open>mdet\<close> stays on \<open>.complete\<close>.\<close>

grammar (relation) uloop =
  tokens \<open>abc_tok\<close>
  productions S :: \<open>nat\<close> = C \<Rightarrow> \<open>\<lambda>c. c\<close>
    and B :: \<open>nat\<close> = B \<Rightarrow> \<open>\<lambda>n. n\<close> | PB \<Rightarrow> \<open>\<lambda>_. 0\<close>
    and C :: \<open>nat\<close> = B \<Rightarrow> \<open>\<lambda>b. b\<close>

parser uloop_parse for uloop

lemma \<open>uloop_parse [tu 1 PB ''x''] = None\<close>
  by eval

lemma \<open>mdet uloop ''!'' \<Longrightarrow> uloop_S w x \<Longrightarrow> uloop_parse w = Some x\<close>
  by (fact uloop_parse.complete)


subsection \<open>A free variable in an action is rejected up front\<close>

text \<open>\<open>S = PA \<Rightarrow> \<open>\<lambda>_. n\<close>\<close> with \<open>n\<close> not fixed used to reach the function package
  (“Variable "n" occurs on right hand side only” about the decoder equation).
  The fixes of a locale (\<open>box\<close> above) and of an unnamed context stay legal.\<close>

ML \<open>
local
  val spec : Grammar_Common.spec =
    {name = Binding.name "free_var", tok_typ = SOME (Input.string "abc_tok"), terminals = [],
     productions =
      [((Binding.name "S", SOME (Input.string "nat")),
        [([(Grammar_Common.Ref ("PA", Position.none), NONE)],
          SOME (Input.string "\<lambda>_. n"))])]};
in
val _ =
  (Named_Target.theory_map (Grammar_Command.grammar_cmd [] spec) \<^theory>;
   error "free variable in an action accepted")
  handle ERROR msg =>
    if String.isPrefix "Free variable \"n\" in the action of production" msg then ()
    else error ("unexpected: " ^ msg)
end
\<close>

context fixes k :: nat begin

grammar (relation) fixed_k =
  tokens \<open>abc_tok\<close>
  productions S :: \<open>nat\<close> = PA \<Rightarrow> \<open>\<lambda>_. k\<close>

lemma \<open>(\<exists>x. fixed_k_S w x) = (w \<in> ilang fixed_k)\<close>
  by (fact fixed_k.lang)

end


subsection \<open>A non-ground carrier ascription names the ascription\<close>

text \<open>\<open>S :: \<open>'a list\<close> = \<dots>\<close> used to say “ascribe the type” although the type was
  ascribed; it now says that the ascription has type variables.\<close>

ML \<open>
local
  val spec : Grammar_Common.spec =
    {name = Binding.name "nonground", tok_typ = SOME (Input.string "abc_tok"), terminals = [],
     productions =
      [((Binding.name "S", SOME (Input.string "'a list")),
        [([(Grammar_Common.Ref ("PA", Position.none), NONE)], SOME (Input.string "\<lambda>_. []"))])]};
in
val _ =
  (Named_Target.theory_map (Grammar_Command.grammar_cmd [] spec) \<^theory>;
   error "non-ground carrier ascription accepted")
  handle ERROR msg =>
    if String.isPrefix "Carrier of nonterminal \"S\" is not ground: the ascribed type" msg
    then () else error ("unexpected: " ^ msg)
end
\<close>


subsection \<open>Two spellings of one token value are one terminal\<close>

text \<open>Terminals are identified by their evaluated token value, not by their
  spelling: \<open>\<open>1\<close>\<close> and \<open>\<open>Suc 0\<close>\<close> are one terminal (with a warning), so two
  alternatives that differ only in that spelling are a duplicate production,
  and a grammar that keeps them apart gets its relation bridged.  Before, the
  relation had two intros for the word \<open>[1]\<close> and the \<open>parser\<close> command fell back
  to the language forms.\<close>

ML \<open>
local
  fun alt toks act =
    (map (fn s => (Grammar_Common.Tok (Input.string s), NONE)) toks,
     SOME (Input.string act));
  val spec : Grammar_Common.spec =
    {name = Binding.name "spelling_dup", tok_typ = SOME (Input.string "nat"), terminals = [],
     productions =
      [((Binding.name "S", SOME (Input.string "nat")),
        [alt ["1"] "0", alt ["Suc 0"] "1"])]};
in
val _ =
  (Named_Target.theory_map (Grammar_Command.grammar_cmd [] spec) \<^theory>;
   error "two spellings of one token accepted as distinct alternatives")
  handle ERROR msg =>
    if String.isPrefix "Duplicate production" msg then ()
    else error ("unexpected: " ^ msg)
end
\<close>

grammar (relation) spelling =
  tokens \<open>nat\<close>
  productions S :: \<open>nat\<close> = \<open>1\<close> \<Rightarrow> \<open>0\<close> | \<open>Suc 0\<close> \<open>2\<close> \<Rightarrow> \<open>1\<close>

parser spelling_parse for spelling

lemma \<open>spelling_S w x \<Longrightarrow> spelling_parse w = Some x\<close>
  by (fact spelling_parse.complete)

lemma \<open>spelling_parse [tu 0 (Suc 0) ''F'', tu 1 2 ''F''] = Some 1\<close>
  by eval


subsection \<open>Many nonterminals\<close>

text \<open>The three tree inductions (completeness, decoder totality, dec_sound)
  were quadratic in the number of nonterminals: an n-way conjunction as
  the invariant.  They are stated through a root-indexed selector now
  (\<^ML_structure>\<open>Grammar_Ptree_Induct\<close>), one body per production case.\<close>

grammar (relation) nt_chain =
  tokens \<open>abc_tok\<close>
  productions
      N1 :: \<open>nat\<close> = PA N2 \<Rightarrow> \<open>\<lambda>_ x. Suc x\<close> | PB \<Rightarrow> \<open>\<lambda>_. 0\<close>
  and N2 :: \<open>nat\<close> = PA N3 \<Rightarrow> \<open>\<lambda>_ x. Suc x\<close> | PB \<Rightarrow> \<open>\<lambda>_. 0\<close>
  and N3 :: \<open>nat\<close> = PA N4 \<Rightarrow> \<open>\<lambda>_ x. Suc x\<close> | PB \<Rightarrow> \<open>\<lambda>_. 0\<close>
  and N4 :: \<open>nat\<close> = PA N5 \<Rightarrow> \<open>\<lambda>_ x. Suc x\<close> | PB \<Rightarrow> \<open>\<lambda>_. 0\<close>
  and N5 :: \<open>nat\<close> = PA N6 \<Rightarrow> \<open>\<lambda>_ x. Suc x\<close> | PB \<Rightarrow> \<open>\<lambda>_. 0\<close>
  and N6 :: \<open>nat\<close> = PA N7 \<Rightarrow> \<open>\<lambda>_ x. Suc x\<close> | PB \<Rightarrow> \<open>\<lambda>_. 0\<close>
  and N7 :: \<open>nat\<close> = PA N8 \<Rightarrow> \<open>\<lambda>_ x. Suc x\<close> | PB \<Rightarrow> \<open>\<lambda>_. 0\<close>
  and N8 :: \<open>nat\<close> = PA \<Rightarrow> \<open>\<lambda>_. 1\<close> | PB \<Rightarrow> \<open>\<lambda>_. 0\<close>

parser nt_chain_parse for nt_chain

lemma \<open>nt_chain_N1 w x \<Longrightarrow> nt_chain_parse w = Some x\<close>
  by (fact nt_chain_parse.complete)

lemma \<open>nt_chain_parse [tu 0 PA ''F'', tu 1 PA ''F'', tu 2 PB ''F''] = Some 2\<close>
  by eval

subsection \<open>Several start symbols for one grammar\<close>

text \<open>Terms and types contain each other (\<open>lam x : Ty . Tm\<close>, \<open>{ Tm }\<close>);
  \<open>TyFile\<close>, an aligned block of declarations, is unreachable from the start
  \<open>Tm\<close> (the expected warning of \<open>grammar\<close>).  One \<open>parser\<close> command emits a
  parser per start.\<close>

datatype toy_tok = TLam | TColon | TDot | TArr | TLP | TRP | TLB | TRB | TId

datatype tm = Var nat | App tm tm | Lam nat ty tm
     and ty = TV nat | Arr ty ty | Sing tm

grammar (relation) toy =
  tokens \<open>toy_tok\<close>
  terminals
    "lam" = \<open>TLam\<close> and ":" = \<open>TColon\<close> and "." = \<open>TDot\<close> and "->" = \<open>TArr\<close> and
    "(" = \<open>TLP\<close>  and ")" = \<open>TRP\<close>    and "{" = \<open>TLB\<close>  and "}" = \<open>TRB\<close>
  productions
      Tm :: \<open>tm\<close>
        = Apps
        | "lam" TId ":" Ty "." Tm \<Rightarrow> \<open>\<lambda>x t b. Lam (s_col (span x)) t b\<close>
    and
      Apps :: \<open>tm\<close> = Atom | Apps Atom \<Rightarrow> \<open>App\<close>
    and
      Atom :: \<open>tm\<close> = TId \<Rightarrow> \<open>\<lambda>x. Var (s_col (span x))\<close> | "(" Tm ")" \<Rightarrow> \<open>\<lambda>t. t\<close>
    and
      Ty :: \<open>ty\<close> = TAtom | TAtom "->" Ty \<Rightarrow> \<open>Arr\<close>
    and
      TAtom :: \<open>ty\<close>
        = TId \<Rightarrow> \<open>\<lambda>x. TV (s_col (span x))\<close>
        | "{" Tm "}" \<Rightarrow> \<open>Sing\<close>
        | "(" Ty ")" \<Rightarrow> \<open>\<lambda>t. t\<close>
    and
      TyFile :: \<open>(nat \<times> ty) list\<close> = Decls
    and
      Decls :: \<open>(nat \<times> ty) list\<close>
        = Decl\<^sup>=         \<Rightarrow> \<open>\<lambda>d. [d]\<close>
        | Decls\<^sup>= Decl\<^sup>= \<Rightarrow> \<open>\<lambda>ds d. ds @ [d]\<close>
    and
      Decl :: \<open>nat \<times> ty\<close> = TId\<^sup>= ":"\<^sup>> Ty\<^sup>> \<Rightarrow> \<open>\<lambda>x t. (s_col (span x), t)\<close>

parser toy_parse for toy
  and toy_parse_ty for toy (Ty)
  and toy_parse_file for toy (TyFile)

text \<open>Each entry parses from its own start: \<open>x y\<close> is a term, not a type, \<open>a -> b\<close>
  a type, not a term, and the two nest through \<open>{ \<dots> }\<close> and \<open>lam\<close>.\<close>

lemma \<open>toy_parse [tu 1 TId ''x'', tu 3 TId ''y''] = Some (App (Var 1) (Var 3))\<close>
  by eval

lemma \<open>toy_parse_ty [tu 1 TId ''x'', tu 3 TId ''y''] = None\<close>
  by eval

lemma \<open>toy_parse_ty [tu 1 TId ''a'', tu 3 TArr ''->'', tu 6 TId ''b''] =
    Some (Arr (TV 1) (TV 6))\<close>
  by eval

lemma \<open>toy_parse [tu 1 TId ''a'', tu 3 TArr ''->'', tu 6 TId ''b''] = None\<close>
  by eval

lemma \<open>toy_parse_ty [tu 1 TLB ''{'', tu 2 TId ''f'', tu 4 TId ''x'', tu 5 TRB ''}'',
    tu 7 TArr ''->'', tu 10 TId ''a''] = Some (Arr (Sing (App (Var 2) (Var 4))) (TV 10))\<close>
  by eval

lemma \<open>toy_parse [tu 1 TLam ''lam'', tu 5 TId ''x'', tu 7 TColon '':'', tu 9 TLB ''{'',
    tu 10 TId ''y'', tu 11 TRB ''}'', tu 13 TDot ''.'', tu 15 TId ''x''] =
    Some (Lam 5 (Sing (Var 10)) (Var 15))\<close>
  by eval

text \<open>A \<open>TyFile\<close> is a block of aligned declarations; a misaligned line is rejected.\<close>

lemma \<open>toy_parse_file [tu 1 TId ''x'', tu 3 TColon '':'', tu 5 TId ''a'',
    tu 1 TId ''y'', tu 3 TColon '':'', tu 5 TId ''b'', tu 7 TArr ''->'', tu 10 TId ''c''] =
    Some [(1, TV 5), (1, Arr (TV 5) (TV 10))]\<close>
  by eval

lemma \<open>toy_parse_file [tu 1 TId ''x'', tu 3 TColon '':'', tu 5 TId ''a'',
    tu 2 TId ''y'', tu 4 TColon '':'', tu 6 TId ''b'', tu 8 TArr ''->'', tu 11 TId ''c''] =
    None\<close>
  by eval

lemma \<open>toy_parse_file [tu 1 TId ''x'', tu 3 TId ''y''] = None\<close>
  by eval

text \<open>The relational forms are stated against the relation of each start,
  without hypotheses.\<close>

lemma \<open>toy_parse_ty w = Some x \<Longrightarrow> toy_Ty 0 w x\<close>
  by (fact toy_parse_ty.sound)

lemma \<open>toy_Ty 0 w x \<Longrightarrow> toy_parse_ty w = Some x\<close>
  by (fact toy_parse_ty.complete)

lemma \<open>toy_parse_file w = Some x \<Longrightarrow> toy_TyFile 0 w x\<close>
  by (fact toy_parse_file.sound)

lemma \<open>toy_TyFile 0 w x \<Longrightarrow> toy_parse_file w = Some x\<close>
  by (fact toy_parse_file.complete)

lemma \<open>w \<in> ilang (toy\<lparr>istart := ''Ty''\<rparr>) \<Longrightarrow> \<exists>x. toy_parse_ty w = Some x\<close>
  by (fact toy_parse_ty.complete_lang)

text \<open>The entries share the grammar, its decoders and its relation family: an entry
  runs \<open>dparse\<close> on the grammar with another start and decodes with the grammar's
  decoder of that start, and defines nothing but its parse constant and its tables.\<close>

lemma \<open>toy_parse_ty \<equiv> \<lambda>w. Option.bind (dparse (toy\<lparr>istart := ''Ty''\<rparr>) ''!'' w) toy__dec_Ty\<close>
  by (fact toy_parse_ty_def)

lemma \<open>toy_parse_file \<equiv>
    \<lambda>w. Option.bind (dparse (toy\<lparr>istart := ''TyFile''\<rparr>) ''!'' w) toy__dec_TyFile\<close>
  by (fact toy_parse_file_def)

ML_val \<open>
  val consts = map #1 (#constants (Consts.dest (Sign.consts_of \<^theory>)));
  fun own p = filter (fn c => Long_Name.base_name c = p orelse
    String.isPrefix (p ^ "_") (Long_Name.base_name c)) consts |> map Long_Name.base_name;
  val tables = ["states", "gtab", "redtab", "i0", "xinit", "xclos"];
  val _ =
    forall (fn p => eq_set (op =) (own p, p :: map (fn t => p ^ "_" ^ t) tables))
      ["toy_parse_ty", "toy_parse_file"]
    orelse error "an entry defines more than its parse constant and its tables";
\<close>

text \<open>A start that is not a nonterminal, a name declared twice, and a second
  grammar in one command are rejected before anything is defined.\<close>
ML \<open>
local
  fun run entries =
    Named_Target.theory_map (Parser_Generators.define_cmd NONE entries) \<^theory>;
  val toy = ("toy", Position.none);
in
val _ =
  (run [(\<^binding>\<open>toy_nope\<close>, toy, SOME ("Nope", Position.none))];
   error "unknown start accepted")
  handle ERROR msg =>
    if String.isPrefix "parser \"toy_nope\": \"Nope\" is not a nonterminal of grammar \"toy\"" msg
    then () else error ("unexpected: " ^ msg)
val _ =
  (run [(\<^binding>\<open>toy_twice\<close>, toy, NONE),
        (\<^binding>\<open>toy_twice\<close>, toy, SOME ("Ty", Position.none))];
   error "a name declared twice accepted")
  handle ERROR msg =>
    if String.isPrefix "parser \"toy_twice\": declared twice in one command" msg
    then () else error ("unexpected: " ^ msg)
val _ =
  (run [(\<^binding>\<open>toy_one\<close>, toy, NONE), (\<^binding>\<open>do_two\<close>, ("do", Position.none), NONE)];
   error "two grammars in one command accepted")
  handle ERROR msg =>
    if String.isPrefix "parser \"do_two\": grammar \"do\" is not the grammar \"toy\"" msg
    then () else error ("unexpected: " ^ msg)
end
\<close>

text \<open>Naming the grammar's own start is the default entry: the same definition,
  theorems and tables as \<open>toy_parse\<close>.\<close>

parser toy_parse_tm for toy (Tm)

lemma \<open>toy_parse_tm \<equiv> \<lambda>w. Option.bind (dparse toy ''!'' w) toy__dec_Tm\<close>
  by (fact toy_parse_tm_def)

lemma \<open>toy_parse w = Some x \<Longrightarrow> toy_Tm 0 w x\<close>
  by (fact toy_parse.sound)

lemma \<open>toy_parse_tm w = Some x \<Longrightarrow> toy_Tm 0 w x\<close>
  by (fact toy_parse_tm.sound)

lemma \<open>toy_Tm 0 w x \<Longrightarrow> toy_parse w = Some x\<close>
  by (fact toy_parse.complete)

lemma \<open>toy_Tm 0 w x \<Longrightarrow> toy_parse_tm w = Some x\<close>
  by (fact toy_parse_tm.complete)

lemma \<open>toy_parse_tm w = Some x \<Longrightarrow> w \<in> ilang toy\<close>
  by (fact toy_parse_tm.sound_lang)

lemma \<open>w \<in> ilang toy \<Longrightarrow> \<exists>x. toy_parse_tm w = Some x\<close>
  by (fact toy_parse_tm.complete_lang)

lemma \<open>toy_parse_tm_states = toy_parse_states\<close>
  by eval

text \<open>The generator option applies to all entries.\<close>

parser (LR) toy_parse_ty2 for toy (Ty) and toy_parse_tm2 for toy

lemma \<open>toy_Ty 0 w x \<Longrightarrow> toy_parse_ty2 w = Some x\<close>
  by (fact toy_parse_ty2.complete)

lemma \<open>toy_Tm 0 w x \<Longrightarrow> toy_parse_tm2 w = Some x\<close>
  by (fact toy_parse_tm2.complete)

text \<open>An entry inside a locale with parameters (\<open>box\<close> above).\<close>

grammar (in box) (relation) idk2 =
  tokens do_tok productions X = Y DDo \<Rightarrow> \<open>\<lambda>y _. y\<close> and Y = DId \<Rightarrow> \<open>\<lambda>_. alive\<close>

parser (in box) idk2_parse for idk2 and idk2_parse_y for idk2 (Y)

lemma \<open>idk2_parse_y [tu 0 DId ''F''] = Some False\<close> by eval

lemma \<open>idk2_Y w x \<Longrightarrow> idk2_parse_y w = Some x\<close>
  by (fact idk2_parse_y.complete)


section \<open>Check-level grammars\<close>

text \<open>Grammar records written out by hand, to pin the static check itself:
  it must fire on the ambiguous grammars and stay empty on the deterministic
  ones.\<close>

subsection \<open>Right-recursive with an \<open>\<epsilon>\<close>-production, and LR(0)-clean\<close>

definition tg1 :: \<open>(string, string) is_cfg\<close> where
  \<open>tg1 = \<lparr> iprods = [(''S'', [(Tm ''a'', Any), (Nt ''S'', Ge)]),
                     (''S'', [])],
           istart = ''S'', istart_ind = 0 \<rparr>\<close>

definition tg2 :: \<open>(string, string) is_cfg\<close> where
  \<open>tg2 = \<lparr> iprods = [(''S'', [(Tm ''a'', Any), (Nt ''S'', Eq), (Tm ''b'', Any)]),
                     (''S'', [(Tm ''c'', Any)])],
           istart = ''S'', istart_ind = 0 \<rparr>\<close>

lemma \<open>length (pr0_states tg1 ''!'') = 5\<close>
  by eval

lemma \<open>nullables tg1 = [''S'']\<close> and \<open>nullables tg2 = []\<close>
  by eval+

lemma \<open>rlalr_conflicts tg1 ''!'' = []\<close> and \<open>rlalr_conflicts tg2 ''!'' = []\<close>
  by eval+

subsection \<open>Ambiguous: \<open>E \<rightarrow> E + E | x\<close>\<close>

definition tg3 :: \<open>(string, string) is_cfg\<close> where
  \<open>tg3 = \<lparr> iprods = [(''E'', [(Nt ''E'', Any), (Tm ''+'', Any), (Nt ''E'', Any)]),
                     (''E'', [(Tm ''x'', Any)])],
           istart = ''E'', istart_ind = 0 \<rparr>\<close>

lemma \<open>rlalr_conflicts tg3 ''!'' \<noteq> []\<close>
  by eval

subsection \<open>The NQLALR pitfall (deremer1982 section 5.1)\<close>

text \<open>\<open>S \<rightarrow> aAc | bAd | agd | bgc, A \<rightarrow> B, B \<rightarrow> g\<close> is LALR(1):
  \<open>LA(g\<^sub>0, B \<rightarrow> g) = {c}\<close> and \<open>LA(g\<^sub>1, B \<rightarrow> g) = {d}\<close>.  A state-merged
  NQLALR computation assigns \<open>{c, d}\<close> to both \<open>g\<close>-states and wrongly reports
  conflicts; the per-item cells keep the two halves apart.\<close>

definition nqg :: \<open>(string, string) is_cfg\<close> where
  \<open>nqg = \<lparr> iprods =
     [(''S'', [(Tm ''a'', Any), (Nt ''A'', Any), (Tm ''c'', Any)]),
      (''S'', [(Tm ''b'', Any), (Nt ''A'', Any), (Tm ''d'', Any)]),
      (''S'', [(Tm ''a'', Any), (Tm ''g'', Any), (Tm ''d'', Any)]),
      (''S'', [(Tm ''b'', Any), (Tm ''g'', Any), (Tm ''c'', Any)]),
      (''A'', [(Nt ''B'', Any)]),
      (''B'', [(Tm ''g'', Any)])],
    istart = ''S'', istart_ind = 0 \<rparr>\<close>

lemma \<open>lalr_conflicts nqg ''!'' = []\<close> and \<open>rlalr_conflicts nqg ''!'' = []\<close>
  by eval+

subsection \<open>Cross-anchor ambiguity\<close>

text \<open>\<open>S \<rightarrow> T\<^sup>\<star>;  T \<rightarrow> A\<^sup>= b\<^sup>= | U\<^sup>= b\<^sup>>;  U \<rightarrow> A\<^sup>=;  A \<rightarrow> a\<^sup>>\<close>.  The word
  \<open>a@2 b@1\<close> has two layout parses: \<open>T\<close> anchored at 1 (\<open>T \<rightarrow> A b\<close>) and at 0
  (\<open>T \<rightarrow> U b\<close>).  After reducing \<open>A\<close> the pooled frame carries the anchor set
  \<open>{0, 1}\<close>; the shift is live via anchor 1 and the reduce of \<open>U \<rightarrow> A\<close> via
  anchor 0.  A comparison of the two sides at one shared anchor is blind to
  this (papers/MAP.md section 7); the item-relative check is not, and its
  explanation finds the witness.\<close>

definition xag :: \<open>(string, string) is_cfg\<close> where
  \<open>xag = \<lparr> iprods =
     [(''S'', [(Nt ''T'', Any)]),
      (''T'', [(Nt ''A'', Eq), (Tm ''b'', Eq)]),
      (''T'', [(Nt ''U'', Eq), (Tm ''b'', Gt)]),
      (''U'', [(Nt ''A'', Eq)]),
      (''A'', [(Tm ''a'', Gt)])],
    istart = ''S'', istart_ind = 0 \<rparr>\<close>

lemma \<open>rlalr_conflicts xag ''!'' \<noteq> []\<close>
  by eval

lemma \<open>list_ex (\<lambda>(_, _, _, _, _, w). w \<noteq> None)
         (explain_rp xag ''!'' (rlalr_conflicts xag ''!''))\<close>
  by eval

lemma \<open>explain_rp tg2 ''!'' (rlalr_conflicts tg2 ''!'') = []\<close>
  by eval

text \<open>The cheaper levels of the explanation reach the same states: every
  reported pair of \<open>xag\<close> has a symbol path and its action pairs.\<close>

lemma \<open>list_all (\<lambda>(_, _, path, prs). path \<noteq> None \<and> prs \<noteq> [])
         (explain_rp_brief xag ''!'' (rlalr_conflicts xag ''!''))\<close>
  by eval

subsection \<open>LALR merging\<close>

text \<open>\<open>S \<rightarrow> aEa | bEb | aFb | bFa; E \<rightarrow> e; F \<rightarrow> e\<close> is LR(1) but not
  LALR(1): the merged state \<open>{E \<rightarrow> e\<sqdot>, F \<rightarrow> e\<sqdot>}\<close> pools the lookaheads of
  the \<open>a\<close>- and \<open>b\<close>-contexts, so the driver, which licenses by the merged
  cells, offers both reduces on the same lookahead: \<open>mdet\<close> fails, and the
  check, which inspects the very cells the driver licenses by, fires.\<close>

definition pol :: \<open>(string, string) is_cfg\<close> where
  \<open>pol = \<lparr> iprods =
     [(''S'', [(Tm ''a'', Any), (Nt ''E'', Any), (Tm ''a'', Any)]),
      (''S'', [(Tm ''b'', Any), (Nt ''E'', Any), (Tm ''b'', Any)]),
      (''S'', [(Tm ''a'', Any), (Nt ''F'', Any), (Tm ''b'', Any)]),
      (''S'', [(Tm ''b'', Any), (Nt ''F'', Any), (Tm ''a'', Any)]),
      (''E'', [(Tm ''e'', Any)]),
      (''F'', [(Tm ''e'', Any)])],
    istart = ''S'', istart_ind = 0 \<rparr>\<close>

lemma \<open>rlalr_conflicts pol ''!'' \<noteq> []\<close>
  by eval


subsection \<open>The same checks without the oracle\<close>

text \<open>Every \<^theory_text>\<open>by eval\<close> above is closed by \<open>holds_by_evaluation\<close>:
  the goal is compiled to ML, run, and its verdict trusted.
  \<^theory_text>\<open>code_simp\<close> rewrites with the very same code equations inside
  the kernel instead, so it produces an ordinary theorem and trusts nothing
  beyond the simplifier.  Proving the checks both ways on one small grammar is
  an oracle-free confirmation, for this development's own code, that the
  generated ML computes what the code equations say --- in particular for
  \<^const>\<open>la_fix\<close> and \<^const>\<open>acc_conflicts\<close>, whose equations bind the
  automaton once for speed and are therefore not the ones a reader would write.

  It buys that only here.  \<^const>\<open>rlalr_conflicts\<close> did not finish in 200 s on
  these same two productions, and it swallows interrupts, so a runaway cannot
  even be stopped by a timeout.  The four checks below, by contrast, cost 13 s
  by \<^theory_text>\<open>eval\<close> --- most of it the fixed ML-compilation floor --- and
  25 s by \<^theory_text>\<open>code_simp\<close>.  Keep this audit on \<open>tg1\<close>, keep
  \<^const>\<open>rlalr_conflicts\<close> out of it, and keep the whole thing under a
  minute.\<close>

lemma checks_by_eval:
  \<open>nullables tg1 = [''S'']\<close>
  \<open>length (pr0_states tg1 ''!'') = 5\<close>
  \<open>length (la_fix tg1 ''!'') = 8\<close>
  \<open>acc_conflicts tg1 ''!'' = []\<close>
  by eval+

lemma checks_by_code_simp:
  \<open>nullables tg1 = [''S'']\<close>
  \<open>length (pr0_states tg1 ''!'') = 5\<close>
  \<open>length (la_fix tg1 ''!'') = 8\<close>
  \<open>acc_conflicts tg1 ''!'' = []\<close>
  by code_simp+


section \<open>Backend plumbing\<close>

subsection \<open>Fixed terminals sharing a constructor keep their spellings\<close>

datatype kw_tok = Kw string | KNum

grammar (relation) kwg =
  tokens \<open>kw_tok\<close>
  terminals "if" = \<open>Kw ''if''\<close> and "then" = \<open>Kw ''then''\<close>
  productions
    S :: \<open>nat\<close> = "if" KNum "then" KNum \<Rightarrow> \<open>\<lambda>_ _. 0\<close>

ML_val \<open>
  val ctxt = \<^context>;
  val g = snd (Grammar_Common.check_grammar ctxt ("kwg", Position.none));
  val _ =
    LR_Backend.string_of_tm ctxt g \<^term>\<open>Kw ''then''\<close> = quote "then"
    andalso LR_Backend.string_of_tm ctxt g \<^term>\<open>Kw ''if''\<close> = quote "if"
    orelse error "fixed terminals sharing a constructor are confused in reports";
\<close>

subsection \<open>Fixed variables named like the backend's constants\<close>

context
  fixes xinit :: nat and st_find :: nat and rlalr_conflicts :: nat
begin

parser shadow_parse for term_first

lemma \<open>term_first_S w x \<Longrightarrow> shadow_parse w = Some x\<close>
  by (fact shadow_parse.complete)

end

subsection \<open>Several components\<close>

text \<open>The relation is defined by one inductive definition per strongly connected
  component of the nonterminals, lower components first: here \<open>N\<close>
  (not recursive), \<open>E\<close> and \<open>T\<close>, and \<open>S\<close>.  The soundness and the bridge
  proofs go through the components in the same order.\<close>

datatype lay_tok = LX | LNum | LPlus | LSemi | LLP | LRP

grammar (relation) lay =
  tokens \<open>lay_tok\<close>
  productions
    S :: \<open>nat list\<close> = E LSemi S \<Rightarrow> \<open>\<lambda>e _ s. e # s\<close> | E \<Rightarrow> \<open>\<lambda>e. [e]\<close>
  and
    E :: \<open>nat\<close> = E LPlus T \<Rightarrow> \<open>\<lambda>a _ b. a + b\<close> | T
  and
    T :: \<open>nat\<close> = N | LLP E LRP \<Rightarrow> \<open>\<lambda>_ e _. e\<close>
  and
    N :: \<open>nat\<close> = LX \<Rightarrow> \<open>\<lambda>_. 1\<close> | LNum \<Rightarrow> \<open>\<lambda>_. 2\<close>

ML_val \<open>
  val g = snd (Grammar_Common.check_grammar \<^context> ("lay", Position.none));
  val _ =
    Grammar_Defs.components g = [["N"], ["E", "T"], ["S"]]
    orelse error "components of lay";
\<close>

parser lay_parse for lay

lemma \<open>lay_parse [tu 1 LX ''x'', tu 2 LPlus ''+'', tu 3 LLP ''('', tu 4 LNum ''2'',
    tu 5 LRP '')'', tu 6 LSemi '';'', tu 7 LX ''x''] = Some [3, 1]\<close>
  by eval

lemma \<open>lay_S w x \<longleftrightarrow> lay_parse w = Some x\<close>
  using lay_parse.sound lay_parse.complete by blast

end
