theory Span_Tests
  imports TIGER_LR.LR_Prec_Parse Parser_Check
begin

section \<open>The span of a yield: \<open>@span\<close>\<close>

text \<open>\<open>@span\<close> in an alternative passes the action the span of the alternative's yield,
  in the place where it is written among the value symbols. It is not a grammar symbol:
  the grammar constant does not see it.\<close>

datatype s_tok = SNum | SPlus | SStar | SLP | SRP | SU

datatype ex = Num nat | Add nat nat ex ex | Mul nat nat ex ex | Par nat \<open>char list\<close> ex | Unit nat

type_synonym stoken = \<open>(s_tok, char) token\<close>

text \<open>A token at line 1, column and offset \<open>i\<close>, of the text \<open>s\<close>; consecutive tokens
  are one character apart, so the yield of a node has gaps.\<close>

fun stoks :: \<open>nat \<Rightarrow> (s_tok \<times> string) list \<Rightarrow> stoken list\<close> where
  \<open>stoks i [] = []\<close>
| \<open>stoks i ((t, s) # xs) =
    \<lparr>tok = t, span = span.make 1 i i (length s) s\<rparr> # stoks (i + length s + 1) xs\<close>

grammar spx =
  tokens \<open>stoken\<close>
  terminals "+" = \<open>SPlus\<close> and "(" = \<open>SLP\<close> and ")" = \<open>SRP\<close> and "()" = \<open>SU\<close>
  productions
    E :: \<open>ex\<close> = E "+" T @span \<Rightarrow> \<open>\<lambda>a b sp. Add (s_off sp) (s_len sp) a b\<close> | T
  and
    T :: \<open>ex\<close> = SNum \<Rightarrow> \<open>\<lambda>x. Num (s_off (span x))\<close>
      | "(" @span E ")" \<Rightarrow> \<open>\<lambda>sp e. Par (s_col sp) (s_txt sp) e\<close>
      | "()" @span \<Rightarrow> \<open>\<lambda>sp. Unit (s_len sp)\<close>

text \<open>The grammar constant has no trace of \<open>@span\<close>.\<close>

lemma \<open>spx =
  is_cfg.make
   [(''E'', [(Nt ''E'', Any), (Tm SPlus, Any), (Nt ''T'', Any)]),
    (''E'', [(Nt ''T'', Any)]),
    (''T'', [(Tm SNum, Any)]),
    (''T'', [(Tm SLP, Any), (Nt ''E'', Any), (Tm SRP, Any)]),
    (''T'', [(Tm SU, Any)])]
   ''E'' 0\<close>
  by (simp only: spx_def)

parser spx_parse for spx

text \<open>\<open>1 + (2 + ())\<close> at offsets 0, 2, 4, 6, 8, 10, 13: the whole word spans 14
  characters, the inner sum 6 (from \<open>2\<close> to the end of \<open>()\<close>).\<close>

definition w1 :: \<open>stoken list\<close> where
  \<open>w1 = stoks 0 [(SNum, ''1''), (SPlus, ''+''), (SLP, ''(''), (SNum, ''2''), (SPlus, ''+''),
    (SU, ''()''), (SRP, '')'')]\<close>

parser_check \<open>spx_parse w1 =
  Some (Add 0 14 (Num 0) (Par 4 ''(2+())'' (Add 6 6 (Num 6) (Unit 2))))\<close>

subsection \<open>With the relation: the bridge\<close>

text \<open>The relation's intro takes \<^const>\<open>word_span\<close> of the production's word, the
  decoder \<^const>\<open>yield_span\<close> of the node's children; the parser's theorems relate the
  two.\<close>

grammar (relation) spr =
  tokens \<open>stoken\<close>
  terminals "+" = \<open>SPlus\<close> and "(" = \<open>SLP\<close> and ")" = \<open>SRP\<close> and "()" = \<open>SU\<close>
  productions
    E :: \<open>ex\<close> = E "+" T @span \<Rightarrow> \<open>\<lambda>a b sp. Add (s_off sp) (s_len sp) a b\<close> | T
  and
    T :: \<open>ex\<close> = SNum \<Rightarrow> \<open>\<lambda>x. Num (s_off (span x))\<close>
      | "(" @span E ")" \<Rightarrow> \<open>\<lambda>sp e. Par (s_col sp) (s_txt sp) e\<close>
      | "()" @span \<Rightarrow> \<open>\<lambda>sp. Unit (s_len sp)\<close>

thm spr.intros

parser spr_parse for spr

parser_check \<open>spr_parse w1 =
  Some (Add 0 14 (Num 0) (Par 4 ''(2+())'' (Add 6 6 (Num 6) (Unit 2))))\<close>

lemma \<open>spr_parse w = Some x \<Longrightarrow> spr_E w x\<close>
  by (fact spr_parse.sound)

lemma \<open>spr_E w x \<Longrightarrow> spr_parse w = Some x\<close>
  by (fact spr_parse.complete)

subsection \<open>Under layout, in a template, nested\<close>

text \<open>An indentation-sensitive relation (the intros carry the column premises) and a
  template alternative with \<open>@span\<close>; \<open>S\<close>'s value is the length of each nested yield.\<close>

grammar (relation) spl =
  tokens \<open>stoken\<close>
  terminals "(" = \<open>SLP\<close> and ")" = \<open>SRP\<close>
  productions
    Wrap(X) :: \<open>nat list\<close> = "(" X\<^sup>> ")" @span \<Rightarrow> \<open>\<lambda>xs sp. s_len sp # xs\<close>
  and
    S :: \<open>nat list\<close> = SNum\<^sup>= \<Rightarrow> \<open>\<lambda>_. []\<close> | Wrap(S)

parser spl_parse for spl

parser_check \<open>spl_parse (stoks 0 [(SLP, ''(''), (SLP, ''(''), (SNum, ''42''), (SRP, '')''), (SRP, '')'')]) =
  Some [10, 6]\<close>

lemma \<open>spl_parse w = Some x \<Longrightarrow> spl_S 0 w x\<close>
  by (fact spl_parse.sound)

subsection \<open>With precedence declarations\<close>

text \<open>The parser is built from the restricted grammar; the decoders, and with them
  \<open>@span\<close>, are those of the grammar as written.\<close>

grammar spp =
  tokens \<open>stoken\<close>
  terminals "+" = \<open>SPlus\<close> and "*" = \<open>SStar\<close>
  precedence left "*" > left "+"
  productions
    E :: \<open>ex\<close>
      = E "+" E @span \<Rightarrow> \<open>\<lambda>a b sp. Add (s_off sp) (s_len sp) a b\<close>
      | E "*" @span E \<Rightarrow> \<open>\<lambda>a sp b. Mul (s_off sp) (s_len sp) a b\<close>
      | SNum \<Rightarrow> \<open>\<lambda>x. Num (s_off (span x))\<close>

parser spp_parse for spp

text \<open>\<open>1 + 2 * 3\<close> at offsets 0, 2, 4, 6, 8.\<close>

parser_check \<open>spp_parse (stoks 0 [(SNum, ''1''), (SPlus, ''+''), (SNum, ''2''), (SStar, ''*''), (SNum, ''3'')]) =
  Some (Add 0 9 (Num 0) (Mul 4 5 (Num 4) (Num 8)))\<close>

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

ML_val \<open>
  val _ = rejected "whose yield can be empty, \<open>S = @span\<close>"
    "grammar bad = tokens s_tok productions S :: nat = @span \<Rightarrow> \<open>\<lambda>sp. s_len sp\<close>";
  val _ = rejected "whose yield can be empty, \<open>S = O @span\<close>"
    "grammar bad = tokens s_tok productions S :: nat = O @span \<Rightarrow> \<open>\<lambda>_ sp. s_len sp\<close> \
    \and O :: unit = \<Rightarrow> \<open>()\<close> | SNum \<Rightarrow> \<open>\<lambda>_. ()\<close>";
  val _ = rejected "has @span twice"
    "grammar bad = tokens s_tok productions S :: nat = SNum @span @span \<Rightarrow> \<open>\<lambda>_ sp _. s_len sp\<close>";
  val _ = rejected "takes no annotation"
    "grammar bad = tokens s_tok productions S :: nat = SNum @span\<^sup>= \<Rightarrow> \<open>\<lambda>_ sp. s_len sp\<close>";
  val _ = rejected "@span inside an operator's group"
    "grammar bad = tokens s_tok productions S :: \<open>nat list\<close> = (SNum @span)+ \<Rightarrow> \<open>\<lambda>xs. map fst xs\<close>";
  val _ = rejected "@span is not a template argument"
    "grammar bad = tokens s_tok productions P(X) :: nat = SNum X \<Rightarrow> \<open>\<lambda>_ _. 0\<close> and S :: nat = P(@span)";
  val _ = rejected "(here SNum, @span)"
    "grammar bad = tokens s_tok productions S :: nat = SNum @span \<Rightarrow> \<open>\<lambda>sp. s_len sp\<close>";
\<close>

end
