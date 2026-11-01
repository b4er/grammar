theory Diag_Tests
  imports LR_Parser.LR_Parser
begin

section \<open>Diagnostics of rejected words\<close>

definition tu :: \<open>nat \<Rightarrow> 'tok \<Rightarrow> char list \<Rightarrow> ('tok, unit) token\<close> where
  \<open>tu i x u = \<lparr>tok = x, span = span.make 0 i 0 (length u) []\<rparr>\<close>

subsection \<open>The simple driver: \<open>lay\<close>\<close>

text \<open>The grammar \<open>lay\<close> of \<open>Regression_Tests\<close>, with two parsers: \<open>lay_plain\<close>
  without the option and \<open>lay_parse\<close> with it. The option adds \<open>lay_parse_diag\<close>,
  which runs a word once and returns the tree or the error, \<open>lay_parse_terminals\<close>,
  \<open>lay_parse_info\<close> and \<open>lay_parse_render\<close> for the messages (section \<^emph>\<open>Messages\<close>)
  and the fact \<open>lay_parse_diag.Inr_iff\<close>, and leaves the code equations of the
  parser and its tables as they are (checked below).\<close>

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

parser lay_plain for lay

parser (diagnostics) lay_parse for lay

ML \<open>
  (* the constants of the parser \<open>diag\<close>, defined with the option, are those of \<open>plain\<close>,
     defined without it, renamed, plus \<open>extra\<close>, and their code equations are the same *)
  fun same_code ctxt plain diag extra =
    let
      val thy = Proof_Context.theory_of ctxt;
      fun consts_of p =
        #constants (Consts.dest (Sign.consts_of thy))
        |> map #1
        |> filter (fn c => c = "Diag_Tests." ^ p orelse String.isPrefix ("Diag_Tests." ^ p ^ "_") c)
        |> sort_strings;
      fun eqns c =
        map (XML.content_of o YXML.parse_body o Pretty.unformatted_string_of)
          (Code.pretty_cert thy (Code.get_cert ctxt [] c));
      val from = raw_explode plain;
      fun go [] = []
        | go (cs as c :: rest) =
            if is_prefix (op =) from cs then diag :: go (drop (length from) cs)
            else c :: go rest;
      val rename = implode o go o raw_explode;
      val ps = consts_of plain;
      val ds = consts_of diag;
      val renamed = map rename ps;
      val extra' = subtract (op =) renamed ds;
    in
      (extra' = map (fn s => "Diag_Tests." ^ diag ^ s) extra
        orelse error ("diagnostics: unexpected constants " ^ commas_quote extra'));
      ps ~~ renamed |> List.app (fn (c, c') =>
        if map rename (eqns c) = eqns c' then ()
        else error ("diagnostics: the code equations of " ^ c' ^ " differ from " ^ c))
    end
\<close>

ML_val \<open>same_code \<^context> "lay_plain" "lay_parse" ["_diag", "_info", "_render", "_terminals"]\<close>

lemma \<open>lay_parse_diag w = Inr x \<longleftrightarrow> lay_S w x\<close>
  using lay_parse_diag.Inr_iff lay_parse.sound lay_parse.complete by blast

text \<open>An accepted word: \<open>Inr\<close> with the parser's value.\<close>

lemma \<open>lay_parse_diag [tu 1 LX ''x'', tu 2 LPlus ''+'', tu 3 LLP ''('', tu 4 LNum ''2'',
    tu 5 LRP '')'', tu 6 LSemi '';'', tu 7 LX ''x''] = Inr [3, 1]\<close>
  by eval

text \<open>A wrong token in the middle: the second \<open>+\<close>, index 2 counting from 0,
  reported with its span; an operand was expected.\<close>

lemma \<open>(case lay_parse_diag [tu 1 LX ''x'', tu 2 LPlus ''+'', tu 3 LPlus ''+'', tu 4 LX ''x''] of
    Inl e \<Rightarrow> pe_index e = 2 \<and> pe_tok e = Some (tu 3 LPlus ''+'') \<and>
      map_option (s_col \<circ> span) (pe_tok e) = Some 3 \<and> pe_kind e = NoAction \<and>
      pe_expected e = [LLP, LX, LNum] \<and> \<not> pe_expect_end e
  | Inr _ \<Rightarrow> False)\<close>
  by eval

text \<open>A closing parenthesis without an opening one: an operator, a separator or
  the end of the input was expected.\<close>

lemma \<open>(case lay_parse_diag [tu 1 LX ''x'', tu 2 LRP '')''] of
    Inl e \<Rightarrow> pe_index e = 1 \<and> pe_expected e = [LSemi, LPlus] \<and> pe_expect_end e
  | Inr _ \<Rightarrow> False)\<close>
  by eval

text \<open>A premature end of input and the empty input.\<close>

lemma \<open>(case lay_parse_diag [tu 1 LX ''x'', tu 2 LPlus ''+''] of
    Inl e \<Rightarrow> pe_index e = 2 \<and> pe_tok e = None \<and> pe_kind e = NoAction \<and>
      pe_expected e = [LLP, LX, LNum] \<and> \<not> pe_expect_end e
  | Inr _ \<Rightarrow> False)\<close>
  by eval

lemma \<open>(case lay_parse_diag [] of
    Inl e \<Rightarrow> pe_index e = 0 \<and> pe_tok e = None \<and> pe_kind e = NoAction \<and>
      pe_expected e = [LLP, LX, LNum] \<and> \<not> pe_expect_end e
  | Inr _ \<Rightarrow> False)\<close>
  by eval

text \<open>The candidates are the grammar's terminals in the order they occur in the
  productions, with their spellings; \<open>lay\<close> declares none, so a terminal is spelled
  by its name. The expected set keeps this order.\<close>

lemma \<open>lay_parse_terminals = [(LSemi, ''LSemi''), (LPlus, ''LPlus''), (LLP, ''LLP''), (LRP, ''LRP''),
    (LX, ''LX''), (LNum, ''LNum'')]\<close>
  by (simp add: lay_parse_terminals_def)

subsection \<open>The expected set against a brute-force oracle\<close>

text \<open>A design claim, checked on small grammars: a terminal \<open>t\<close> is in the expected
  set of a rejected word iff the consumed prefix extended by \<open>t\<close> and some short
  completion \<open>u\<close> is accepted; the end of the input is expected iff the prefix
  itself is accepted. The completions \<open>u\<close> range over the words up to length
  \<open>k\<close> over a few closing terminals \<open>cs\<close>, enough to complete every viable prefix
  of the grammars below within the bound. The set depends only on the
  configuration after the prefix, so each distinct report is checked once.\<close>

fun words :: \<open>'a list \<Rightarrow> nat \<Rightarrow> 'a list list\<close> where
  \<open>words xs 0 = [[]]\<close>
| \<open>words xs (Suc n) = [] # concat (map (\<lambda>x. map ((#) x) (words xs n)) xs)\<close>

definition brute_expect :: \<open>(('t, unit) token list \<Rightarrow> 'a option) \<Rightarrow> 't list \<Rightarrow> 't list \<Rightarrow> nat \<Rightarrow>
    't list \<Rightarrow> 't list \<times> bool\<close> where
  \<open>brute_expect p ts cs k pre =
     (filter (\<lambda>t. \<exists>u \<in> set (words cs k). p (map (\<lambda>x. tu 0 x []) (pre @ t # u)) \<noteq> None) ts,
      p (map (\<lambda>x. tu 0 x []) pre) \<noteq> None)\<close>

text \<open>The reports of the rejected words up to length \<open>n\<close> that disagree with the
  oracle, as (prefix, (expected set, end), (oracle's set, end)).\<close>

definition brute_mismatches :: \<open>(('t, unit) token list \<Rightarrow> 'a option) \<Rightarrow>
    (('t, unit) token list \<Rightarrow> (string, 't, unit, unit) perr + 'a) \<Rightarrow> 't list \<Rightarrow> 't list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow>
    ('t list \<times> ('t list \<times> bool) \<times> 't list \<times> bool) list\<close> where
  \<open>brute_mismatches p d ts cs n k =
     filter (\<lambda>(pre, (r, e), (b, e')). set r \<noteq> set b \<or> e \<noteq> e')
       (map (\<lambda>(pre, r). (pre, r, brute_expect p ts cs k pre))
         (remdups (List.map_filter (\<lambda>w. case d (map (\<lambda>x. tu 0 x []) w) of
              Inl e \<Rightarrow> Some (take (pe_index e) w, pe_expected e, pe_expect_end e)
            | Inr _ \<Rightarrow> None) (words ts n))))\<close>

ML \<open>
  fun check_oracle ctxt name t =
    let val r = Value_Command.value ctxt t in
      (case try HOLogic.dest_list r of
        SOME [] => writeln (name ^ ": the expected sets agree with the oracle")
      | _ => error (name ^ ": expected sets disagree with the oracle:\n" ^ Syntax.string_of_term ctxt r))
    end
\<close>

ML_val \<open>
  check_oracle \<^context> "lay"
    \<^term>\<open>brute_mismatches lay_parse lay_parse_diag [LX, LNum, LPlus, LSemi, LLP, LRP] [LX, LRP] 4 6\<close>
\<close>
subsection \<open>One pass against the rerun\<close>

text \<open>\<open>lay_parse_diag\<close> runs a word once. On every word up to length \<open>4\<close> it agrees
  with the parser followed, on a rejection, by a second run of the diagnosis.\<close>

lemma \<open>list_all (\<lambda>w. let w' = map (\<lambda>x. tu 0 x []) w in
    lay_parse_diag w' = (case lay_parse w' of Some x \<Rightarrow> Inr x
      | None \<Rightarrow> Inl (pdiagnose lay_parse_ptabs lay_parse_i0 (pnum lay_parse_ptabs)
                    (map fst lay_parse_terminals) w')))
    (words [LX, LNum, LPlus, LSemi, LLP, LRP] 4)\<close>
  by eval

subsection \<open>A unit self-loop\<close>

text \<open>A grammar with \<open>A \<Rightarrow>\<^sup>+ A\<close> is ambiguous, so its determinism check fails and the
  parser runs the set-anchored driver, with the history that stops on a repeated
  configuration (expected warning). The diagnostics run the same step, and their loop
  check fires as the parser's does.\<close>

datatype abc_tok = PA | PB | PC

grammar (relation) uloop =
  tokens \<open>abc_tok\<close>
  productions S :: \<open>nat\<close> = C \<Rightarrow> \<open>\<lambda>c. c\<close>
    and B :: \<open>nat\<close> = B \<Rightarrow> \<open>\<lambda>n. n\<close> | PB \<Rightarrow> \<open>\<lambda>_. 0\<close>
    and C :: \<open>nat\<close> = B \<Rightarrow> \<open>\<lambda>b. b\<close>

parser (diagnostics) uloop_parse for uloop

lemma \<open>(case uloop_parse_diag [tu 1 PB ''x''] of
    Inl e \<Rightarrow> pe_kind e = ReduceCycle \<and> pe_index e = 1 \<and> pe_tok e = None
  | Inr _ \<Rightarrow> False)\<close>
  by eval

lemma \<open>(case uloop_parse_diag [tu 1 PB ''x'', tu 2 PB ''y''] of
    Inl e \<Rightarrow> pe_kind e = NoAction \<and> pe_index e = 1 \<and> pe_tok e = Some (tu 2 PB ''y'')
  | Inr _ \<Rightarrow> False)\<close>
  by eval

text \<open>Without layout annotations every column is accepted, and the token is
  not misplaced.\<close>

lemma \<open>(case uloop_parse_diag [tu 1 PC ''x''] of
    Inl e \<Rightarrow> pe_kind e = NoAction \<and> pe_expected e = [PB] \<and> pe_columns e = [(PB, [(0, None)])]
  | Inr _ \<Rightarrow> False)\<close>
  by eval

text \<open>The engine on the plain tables of \<open>uloop\<close>, built as the command builds
  them for the simple driver. They keep both reduces of the conflict, and the
  step takes the first, \<open>B = B\<close>, which rebuilds the stack it popped: on \<open>PB\<close>
  the loop check fires at the end of the input and the error is
  \<^const>\<open>ReduceCycle\<close>, not \<^const>\<open>NoAction\<close>. On \<open>PB PB\<close> the second \<open>PB\<close> has no
  action.\<close>

definition ul_states where \<open>ul_states = pr0_states uloop ''!''\<close>

definition ul_ptabs where
  \<open>ul_ptabs = ptabs_of (ktabs_of (jtabs_of (mk_ltabs (pgtab uloop ul_states) ul_states
     (red_buckets uloop ''!'' (size ul_states)) (pcomps uloop ul_states) (pfins ''!'' ul_states))))\<close>

definition ul_i0 where \<open>ul_i0 = st_find ul_states (lr0_start uloop ''!'')\<close>

lemma \<open>(let e = pdiagnose ul_ptabs ul_i0 (pnum ul_ptabs) [PA, PB, PC] [tu 1 PB ''x''] in
    pe_kind e = ReduceCycle \<and> pe_index e = 1 \<and> pe_tok e = None)\<close>
  by eval

lemma \<open>(let e = pdiagnose ul_ptabs ul_i0 (pnum ul_ptabs) [PA, PB, PC] [tu 1 PB ''x'', tu 2 PB ''y''] in
    pe_kind e = NoAction \<and> pe_index e = 1 \<and> pe_tok e = Some (tu 2 PB ''y''))\<close>
  by eval

text \<open>The trials run into the same cycle: after \<open>PB\<close> the reduce \<open>B = PB\<close> is
  followed by \<open>B = B\<close> forever, whatever the lookahead, and the loop check, which
  each trial starts afresh, ends every trial. Nothing is expected, not even the
  end of the input, although \<open>[PB]\<close> is in the language: the set is what this
  parser accepts, and on \<open>uloop\<close>'s conflicting tables it accepts nothing.\<close>

lemma \<open>(let e = pdiagnose ul_ptabs ul_i0 (pnum ul_ptabs) [PA, PB, PC] [tu 1 PB ''x''] in
    pe_expected e = [] \<and> \<not> pe_expect_end e)\<close>
  by eval

subsection \<open>Merged lookaheads and spurious reductions\<close>

text \<open>The example of Pottier (2016, Sect. 4): brackets and parentheses around
  lists. The LALR state after \<open>INT\<close> merges the contexts inside \<open>(\<close> and \<open>[\<close>, so
  it reduces on \<open>)\<close> after \<open>[ INT\<close> and fails only two reductions later, in the
  state after \<open>[ list\<close>. A static reading of the first state would expect \<open>)\<close>,
  one of the second only \<open>]\<close>. The trials expect an operator, \<open>,\<close> and \<open>]\<close>,
  and the error keeps the state where it was detected.\<close>

datatype br_tok = BInt | BPlus | BComma | BLP | BRP | BLB | BRB

grammar (relation) br =
  tokens \<open>br_tok\<close>
  terminals "+" = BPlus and "," = BComma and "(" = BLP and ")" = BRP and "[" = BLB and "]" = BRB
  productions
    E :: \<open>nat\<close> = E "+" A \<Rightarrow> \<open>\<lambda>a b. a + b\<close> | A
  and
    A :: \<open>nat\<close> = "(" L ")" \<Rightarrow> \<open>\<lambda>l. l\<close> | "[" L "]" \<Rightarrow> \<open>\<lambda>l. l\<close> | BInt \<Rightarrow> \<open>\<lambda>_. 1\<close>
  and
    L :: \<open>nat\<close> = E | E "," L \<Rightarrow> \<open>\<lambda>e l. e + l\<close>

parser (diagnostics) br_parse for br

lemma \<open>(case br_parse_diag [tu 1 BLB ''['', tu 2 BInt ''1'', tu 3 BRP '')''] of
    Inl e \<Rightarrow> pe_index e = 2 \<and> pe_tok e = Some (tu 3 BRP '')'') \<and>
      set (pe_expected e) = {BPlus, BComma, BRB} \<and> \<not> pe_expect_end e
  | Inr _ \<Rightarrow> False)\<close>
  by eval

text \<open>The state where the error is detected is not the one after the last shift:
  the trials start from the latter.\<close>

lemma \<open>(case br_parse_diag [tu 1 BLB ''['', tu 2 BInt ''1'', tu 3 BRP '')''] of
    Inl e \<Rightarrow> pe_state e \<noteq> pstate (fst (case pdiag_run br_parse_ptabs br_parse_i0 br_parse_tnum
      [tu 1 BLB ''['', tu 2 BInt ''1'', tu 3 BRP '')''] of Some (DStuck _ _ sh) \<Rightarrow> sh))
  | Inr _ \<Rightarrow> False)\<close>
  by eval

ML_val \<open>
  check_oracle \<^context> "br"
    \<^term>\<open>brute_mismatches br_parse br_parse_diag [BInt, BPlus, BComma, BLP, BRP, BLB, BRB]
      [BInt, BRP, BRB] 4 6\<close>
\<close>

subsection \<open>An extended token record\<close>

text \<open>The error carries the token at the user's record type, extra fields
  included.\<close>

datatype py_tok = PWhile | PColon | PId
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

parser (diagnostics) t_ext_parse for t_ext

text \<open>Declared spellings are kept; \<open>PId\<close> has none.\<close>

lemma \<open>map snd t_ext_parse_terminals = [''while'', '':'', ''PId'']\<close>
  by (simp add: t_ext_parse_terminals_def)

lemma \<open>(case t_ext_parse_diag
      [\<lparr>tok = PColon, span = \<lparr>s_line = 0, s_col = 0, s_off = 0, s_len = 1, s_txt = []\<rparr>, trailing = []\<rparr>,
       \<lparr>tok = PColon, span = \<lparr>s_line = 0, s_col = 2, s_off = 2, s_len = 1, s_txt = []\<rparr>,
        trailing = [(Comment, \<lparr>s_line = 0, s_col = 4, s_off = 4, s_len = 3, s_txt = []\<rparr>)]\<rparr>] of
    Inl e \<Rightarrow> pe_index e = 1 \<and> pe_expected e = [PId] \<and>
      map_option trailing (pe_tok e) = Some [(Comment, \<lparr>s_line = 0, s_col = 4, s_off = 4, s_len = 3, s_txt = []\<rparr>)]
  | Inr _ \<Rightarrow> False)\<close>
  by eval

subsection \<open>The set-anchored driver: layout\<close>

text \<open>The layout grammars of \<open>Regression_Tests\<close>, with the option. Their parsers run
  the set-anchored driver. The rejected words there are rejected for a column: the
  report gives the columns at which the token would be accepted and the token it
  must be aligned with or indented from.\<close>

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

parser (diagnostics) do_parse2 for do

text \<open>\<open>y\<close> continues the inner block at column 7 or the outer one at column 4; at
  column 2 it is nearest to the outer one, opened by the inner \<open>do\<close>.\<close>

lemma \<open>(case do_parse2_diag [tu 1 DDo ''do'', tu 4 DDo ''do'', tu 7 DId ''x'', tu 2 DId ''y''] of
    Inl e \<Rightarrow> pe_index e = 3 \<and> pe_tok e = Some (tu 2 DId ''y'') \<and>
      pe_kind e = Misaligned [(4, Some 4), (7, Some 7)] \<and> pe_anchor e = Some (tu 4 DDo ''do'') \<and>
      pe_columns e = [(DId, [(4, Some 4), (7, Some 7)]), (DDo, [(4, Some 4), (7, Some 7)])] \<and>
      pe_expect_end e
  | Inr _ \<Rightarrow> False)\<close>
  by eval

text \<open>At column 9 it is nearest to the inner block, which starts with \<open>x\<close>.\<close>

lemma \<open>(case do_parse2_diag [tu 1 DDo ''do'', tu 4 DDo ''do'', tu 7 DId ''x'', tu 9 DId ''y''] of
    Inl e \<Rightarrow> pe_kind e = Misaligned [(4, Some 4), (7, Some 7)] \<and> pe_anchor e = Some (tu 7 DId ''x'')
  | Inr _ \<Rightarrow> False)\<close>
  by eval

text \<open>At the end of the input there is no token to misplace: the error is
  \<^const>\<open>NoAction\<close>, and the block may start at any column right of \<open>4\<close>.\<close>

lemma \<open>(case do_parse2_diag [tu 1 DDo ''do'', tu 4 DDo ''do''] of
    Inl e \<Rightarrow> pe_kind e = NoAction \<and> pe_tok e = None \<and> pe_anchor e = None \<and>
      pe_columns e = [(DId, [(5, None)]), (DDo, [(5, None)])] \<and> \<not> pe_expect_end e
  | Inr _ \<Rightarrow> False)\<close>
  by eval

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

parser (diagnostics) hask_case_parse2 for hask_case

lemma \<open>(case hask_case_parse2_diag [tu 1 HCase ''case'', tu 6 HId ''x'', tu 8 HOf ''of'',
      tu 3 HId ''A'', tu 4 HId ''B''] of
    Inl e \<Rightarrow> pe_index e = 4 \<and> pe_kind e = Misaligned [(3, Some 3)] \<and>
      pe_anchor e = Some (tu 3 HId ''A'') \<and>
      pe_columns e = [(HId, [(3, Some 3)]), (HSemi, [(3, None)])]
  | Inr _ \<Rightarrow> False)\<close>
  by eval

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

parser py_plain for py_suite

parser (diagnostics) py_parse2 for py_suite

text \<open>The option leaves the code equations of the set-anchored parser and its
  tables as they are.\<close>

ML_val \<open>same_code \<^context> "py_plain" "py_parse2" ["_diag", "_info", "_render", "_terminals"]\<close>

text \<open>The one pass of the vector driver agrees with the parser and a second run of
  the diagnosis on the sparse driver on every word up to length \<open>4\<close> over tokens at
  a few columns.\<close>

lemma \<open>list_all (\<lambda>w. let w' = map (\<lambda>(x, i). tu i x []) w in
    py_parse2_diag w' = (case py_parse2 w' of Some x \<Rightarrow> Inr x
      | None \<Rightarrow> Inl (sdiagnose py_parse2_stab py_parse2_sinit py_parse2_sclos py_parse2_i0
                    (map fst py_parse2_terminals) w')))
    (words [(PWhile, 1), (PId, 3), (PId, 1), (PColon, 2), (PId, 0)] 4)\<close>
  by eval

lemma \<open>(case py_parse2_diag [tu 1 PWhile ''while'', tu 7 PId ''x'', tu 8 PColon '':'',
      tu 3 PId ''y'', tu 4 PId ''z''] of
    Inl e \<Rightarrow> pe_index e = 4 \<and> pe_kind e = Misaligned [(3, Some 3)] \<and>
      pe_anchor e = Some (tu 3 PId ''y'') \<and> pe_expected e = [PId] \<and> pe_expect_end e
  | Inr _ \<Rightarrow> False)\<close>
  by eval

text \<open>The suite must be indented: right of column \<open>0\<close>, where the statement may
  start, so at least as far as \<open>while\<close>.\<close>

lemma \<open>(case py_parse2_diag [tu 1 PWhile ''while'', tu 7 PId ''x'', tu 8 PColon '':'',
      tu 0 PId ''y''] of
    Inl e \<Rightarrow> pe_kind e = Offside [(1, None)] \<and> pe_anchor e = Some (tu 1 PWhile ''while'')
  | Inr _ \<Rightarrow> False)\<close>
  by eval

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

parser (diagnostics) iswim_parse2 for iswim

text \<open>\<open>iswim\<close> keeps conflicts, and its start symbol takes every column, so most
  of its errors are not about columns. Inside a \<open>where\<close> clause, \<open>"-"\<^sup>= Expr\<^sup>=\<close>
  anchors the operand at the \<open>-\<close>, and \<open>IId\<^sup>\<ge>\<close> puts it at or right of that.\<close>

lemma \<open>(case iswim_parse2_diag [tu 1 IId ''x'', tu 3 IWhere ''where'', tu 9 IId ''y'', tu 11 IEq ''='',
      tu 2 IMinus ''-'', tu 0 IId ''z''] of
    Inl e \<Rightarrow> pe_index e = 5 \<and> pe_kind e = Offside [(2, None)] \<and>
      pe_anchor e = Some (tu 2 IMinus ''-'') \<and> set (pe_expected e) = {IId, IMinus, ILP}
  | Inr _ \<Rightarrow> False)\<close>
  by eval

subsection \<open>The representative columns against a scan of every column\<close>

text \<open>The claim behind \<^const>\<open>lreps\<close>: the trials at the representative columns
  decide every column. For each rejected word \<open>pre @ u\<close>, \<open>u\<close> up to length \<open>n\<close>
  over the terminals \<open>ts\<close> at the columns \<open>cs\<close>, every terminal is tried at every
  column below \<open>K\<close> and compared with the reported columns. The result counts the
  rejected words and those with an \<^const>\<open>Offside\<close> or \<^const>\<open>Misaligned\<close> report,
  and lists the disagreements.\<close>

definition col_check :: \<open>(unit, unit, 'p, 'n, 't) astep \<Rightarrow> (('p, 't) agconfig \<Rightarrow> bool) \<Rightarrow>
    'p aitem list \<Rightarrow> 'p aitem list \<Rightarrow> nat \<Rightarrow> 't list \<Rightarrow> ('t \<times> nat) list \<Rightarrow> nat list \<Rightarrow>
    nat \<Rightarrow> nat \<Rightarrow> nat \<times> nat \<times> (('t \<times> nat) list \<times> ('t \<times> nat) list) list\<close> where
  \<open>col_check stp fin xin xclos i\<^sub>0 ts pre cs n K =
     (let ws = map (\<lambda>u. pre @ u) (words [(t, k). t \<leftarrow> ts, k \<leftarrow> cs] n);
          rs = List.map_filter (\<lambda>w. let tw = map (\<lambda>(t, k). tu k t []) w in
                 (case ldiag_run stp fin xin xclos i\<^sub>0 tw of
                   Some (DStuck kd st sh) \<Rightarrow>
                     Some (w, ldperr stp fin ts (length tw) (Some (DStuck kd st sh)), fst sh)
                 | _ \<Rightarrow> None)) ws;
          lay = filter (\<lambda>(w, e, c). case pe_kind e of Offside _ \<Rightarrow> True | Misaligned _ \<Rightarrow> True
                                                   | _ \<Rightarrow> False) rs;
          bad = List.map_filter (\<lambda>(w, e, c).
                  let m = [(t, k). t \<leftarrow> ts, k \<leftarrow> [0..<K],
                           col_in k (case map_of (pe_columns e) t of None \<Rightarrow> [] | Some cs \<Rightarrow> cs) \<noteq>
                           ltry stp fin c (Some (t, k))]
                  in if m = [] then None else Some (w, m)) rs
      in (length rs, length lay, bad))\<close>

ML \<open>
  fun check_cols ctxt name t =
    let val r = Value_Command.value ctxt t in
      (case HOLogic.strip_tuple r of
        [n, l, bad] =>
          (case try HOLogic.dest_list bad of
            SOME [] => writeln (name ^ ": the columns agree with the scan on " ^
              Syntax.string_of_term ctxt n ^ " rejected words, " ^
              Syntax.string_of_term ctxt l ^ " of them reported Offside or Misaligned")
          | _ => error (name ^ ": columns disagree with the scan:\n" ^ Syntax.string_of_term ctxt bad))
      | _ => error "check_cols")
    end
\<close>

ML_val \<open>
  check_cols \<^context> "do"
    \<^term>\<open>col_check (sdstep_dact do_parse2_stab) (sgfinal do_parse2_stab)
      do_parse2_sinit do_parse2_sclos do_parse2_i0
      [DDo, DId] [] [0, 1, 2, 4, 6] 4 12\<close>
\<close>

ML_val \<open>
  check_cols \<^context> "do, nested"
    \<^term>\<open>col_check (sdstep_dact do_parse2_stab) (sgfinal do_parse2_stab)
      do_parse2_sinit do_parse2_sclos do_parse2_i0
      [DDo, DId] [(DDo, 1), (DDo, 4)] [1, 3, 4, 5, 7, 9] 3 14\<close>
\<close>

ML_val \<open>
  check_cols \<^context> "hask_case"
    \<^term>\<open>col_check (sdstep_dact hask_case_parse2_stab) (sgfinal hask_case_parse2_stab)
      hask_case_parse2_sinit hask_case_parse2_sclos hask_case_parse2_i0
      [HCase, HOf, HLC, HRC, HSemi, HId]
      [(HCase, 1), (HId, 6), (HOf, 8)] [2, 3, 4, 9] 3 14\<close>
\<close>

ML_val \<open>
  check_cols \<^context> "py_suite"
    \<^term>\<open>col_check (sdstep_dact py_parse2_stab) (sgfinal py_parse2_stab)
      py_parse2_sinit py_parse2_sclos py_parse2_i0
      [PWhile, PColon, PId]
      [(PWhile, 1), (PId, 7), (PColon, 8)] [0, 2, 3, 4, 6] 3 14\<close>
\<close>

ML_val \<open>
  check_cols \<^context> "iswim"
    \<^term>\<open>col_check (sdstep_dact iswim_parse2_stab) (sgfinal iswim_parse2_stab)
      iswim_parse2_sinit iswim_parse2_sclos iswim_parse2_i0
      [IWhere, IPlus, IMinus, IEq, ILP, IRP, IId]
      [] [0, 2, 4] 3 10\<close>
\<close>

ML_val \<open>
  check_cols \<^context> "iswim, where"
    \<^term>\<open>col_check (sdstep_dact iswim_parse2_stab) (sgfinal iswim_parse2_stab)
      iswim_parse2_sinit iswim_parse2_sclos iswim_parse2_i0
      [IWhere, IPlus, IMinus, IEq, ILP, IRP, IId]
      [(IId, 1), (IWhere, 3), (IId, 9), (IEq, 11)] [0, 2, 9, 11, 12] 2 16\<close>
\<close>

text \<open>The same with a conflict in the tables, where a run may restart on the sparse
  driver.\<close>

lemma \<open>list_all (\<lambda>w. let w' = map (\<lambda>(x, i). tu i x []) w in
    iswim_parse2_diag w' = (case iswim_parse2 w' of Some x \<Rightarrow> Inr x
      | None \<Rightarrow> Inl (sdiagnose iswim_parse2_stab iswim_parse2_sinit iswim_parse2_sclos
                    iswim_parse2_i0 (map fst iswim_parse2_terminals) w')))
    (words [(IId, 0), (IId, 2), (IWhere, 2), (IEq, 3), (IPlus, 4), (ILP, 1), (IRP, 1)] 4)\<close>
  by eval

text \<open>Those conflicts are between a shift and a reduction, which the vector driver
  resolves by itself. It stops only on two live reductions (expected warning), and
  there the one pass restarts on the sparse driver.\<close>

grammar (relation) rr =
  tokens \<open>abc_tok\<close>
  productions S :: \<open>nat\<close> = A PC \<Rightarrow> \<open>\<lambda>a _. a\<close> | B PC \<Rightarrow> \<open>\<lambda>b _. b\<close>
    and A :: \<open>nat\<close> = PA \<Rightarrow> \<open>\<lambda>_. 0\<close>
    and B :: \<open>nat\<close> = PA \<Rightarrow> \<open>\<lambda>_. 1\<close>

parser (diagnostics) rr_parse for rr

lemma \<open>(let w = [tu 1 PA [], tu 2 PC []]; st = ([v_av0 rr_parse_vtab], vtcols rr_parse_vtab w, w, [])
    in vdrun rr_parse_vtab st st = Some VConflict)\<close>
  by eval

lemma \<open>list_all (\<lambda>w. let w' = map (\<lambda>(x, i). tu i x []) w in
    rr_parse_diag w' = (case rr_parse w' of Some x \<Rightarrow> Inr x
      | None \<Rightarrow> Inl (sdiagnose rr_parse_stab rr_parse_sinit rr_parse_sclos
                    rr_parse_i0 (map fst rr_parse_terminals) w')))
    (words [(PA, 1), (PB, 2), (PC, 2)] 4)\<close>
  by eval

lemma \<open>(case rr_parse_diag [tu 1 PA [], tu 2 PC [], tu 3 PC []] of
    Inl e \<Rightarrow> pe_index e = 2 \<and> pe_expected e = [] \<and> pe_expect_end e
  | Inr _ \<Rightarrow> False)\<close>
  by eval

section \<open>Messages\<close>

text \<open>\<open>p_info\<close> collects what the messages need: the grammar, the LR(0)
  kernels, the spellings of the terminals and the nonterminals' names. For tokens
  over \<^typ>\<open>char\<close> or \<^typ>\<open>unit\<close>, \<open>p_render\<close> is
  \<^const>\<open>perr_render\<close> with it. The grammars below take tokens over
  \<^typ>\<open>char\<close>, so a payload token is shown by its text. The messages are checked
  line by line: \<^const>\<open>pmsg_lines\<close> of \<^const>\<open>perr_message\<close>, which
  \<^const>\<open>perr_render\<close> joins with newlines.\<close>

definition tc :: \<open>nat \<Rightarrow> nat \<Rightarrow> 'tok \<Rightarrow> string \<Rightarrow> ('tok, char) token\<close> where
  \<open>tc l c x s = \<lparr>tok = x, span = span.make l c c (length s) s\<rparr>\<close>

datatype m_tok = MX | MNum | MPlus | MSemi | MLP | MRP

grammar (relation) m_lay =
  tokens \<open>(m_tok, char) token\<close>
  terminals "+" = MPlus and ";" = MSemi and "(" = MLP and ")" = MRP
  productions
    S :: \<open>nat list\<close> = E ";" S \<Rightarrow> \<open>\<lambda>e s. e # s\<close> | E \<Rightarrow> \<open>\<lambda>e. [e]\<close>
  and
    E :: \<open>nat\<close> = E "+" T \<Rightarrow> \<open>\<lambda>a b. a + b\<close> | T
  and
    T :: \<open>nat\<close> = N | "(" E ")" \<Rightarrow> \<open>\<lambda>e. e\<close>
  and
    N :: \<open>nat\<close> = MX \<Rightarrow> \<open>\<lambda>_. 1\<close> | MNum \<Rightarrow> \<open>\<lambda>_. 2\<close>

parser (diagnostics) m_lay_parse for m_lay

lemma \<open>(case m_lay_parse_diag [tc 0 0 MX ''x'', tc 0 2 MPlus ''+'', tc 0 4 MPlus ''+''] of
    Inl e \<Rightarrow> pmsg_lines (perr_message m_lay_parse_info (\<lambda>c. [c]) e) | Inr _ \<Rightarrow> []) =
  [''0:4: syntax error at '+' (after '+')'',
   ''  expected: '(', 'MX' or '' @ squote ''MNum'',
   ''  up to here: '' @ squote ''x +'']\<close>
  by eval

text \<open>Past \<^const>\<open>pi_k\<close> expected terminals (5 in \<open>p_info\<close>) the summary takes
  over: with 1, the three here are FIRST(\<open>T\<close>), and \<open>T\<close> follows the dot in the
  kernel of the last shift.\<close>

lemma \<open>(case m_lay_parse_diag [tc 0 0 MX ''x'', tc 0 2 MPlus ''+'', tc 0 4 MPlus ''+''] of
    Inl e \<Rightarrow> pmsg_lines (perr_message (m_lay_parse_info\<lparr>pi_k := 1\<rparr>) (\<lambda>c. [c]) e) | Inr _ \<Rightarrow> []) =
  [''0:4: syntax error at '+' (after '+')'',
   ''  expected: a T'',
   ''  up to here: '' @ squote ''x +'']\<close>
  by eval

text \<open>At the end of the input the position is right after the last token, and
  the stack holds a whole \<open>E\<close>.\<close>

lemma \<open>(case m_lay_parse_diag [tc 0 0 MLP ''('', tc 0 1 MX ''x'', tc 0 3 MPlus ''+'', tc 1 0 MNum ''12''] of
    Inl e \<Rightarrow> pmsg_lines (perr_message m_lay_parse_info (\<lambda>c. [c]) e) | Inr _ \<Rightarrow> []) =
  [''1:2: syntax error at end of input (after '' @ squote ''12'' @ '')'',
   ''  expected: '' @ squote ''+'' @ '' or '' @ squote '')'',
   ''  up to here: an E was recognised: '' @ squote ''x + 12'']\<close>
  by eval

lemma \<open>(case m_lay_parse_diag [] of
    Inl e \<Rightarrow> pmsg_lines (perr_message m_lay_parse_info (\<lambda>c. [c]) e) | Inr _ \<Rightarrow> []) =
  [''0:0: syntax error at end of input'',
   ''  expected: '(', 'MX' or '' @ squote ''MNum'']\<close>
  by eval

datatype md_tok = MDo | MId

grammar (relation) m_do =
  tokens \<open>(md_tok, char) token\<close>
  terminals "do" = \<open>MDo\<close>
  productions
      Expr :: \<open>unit\<close>
        = MId\<^sup>>          \<Rightarrow> \<open>\<lambda>_. ()\<close>
        | "do"\<^sup>> BStmts\<^sup>> \<Rightarrow> \<open>\<lambda>_. ()\<close>
    and
      BStmts :: \<open>unit\<close>
        = BExpr\<^sup>=         \<Rightarrow> \<open>\<lambda>_. ()\<close>
        | BStmts\<^sup>= BExpr\<^sup>= \<Rightarrow> \<open>\<lambda>_ _. ()\<close>
    and
      BExpr :: \<open>unit\<close>
        = MId\<^sup>=          \<Rightarrow> \<open>\<lambda>_. ()\<close>
        | "do"\<^sup>= BStmts\<^sup>> \<Rightarrow> \<open>\<lambda>_. ()\<close>

parser (diagnostics) m_do_parse for m_do

text \<open>A misplaced token is reported with the columns that would accept it and the
  token it must be aligned with.\<close>

lemma \<open>(case m_do_parse_diag [tc 0 1 MDo ''do'', tc 0 4 MDo ''do'', tc 0 7 MId ''x'', tc 1 2 MId ''y''] of
    Inl e \<Rightarrow> pmsg_lines (perr_message m_do_parse_info (\<lambda>c. [c]) e) | Inr _ \<Rightarrow> []) =
  [''1:2: 'y' at column 2 must be at columns 4 or 7 (aligned with 'do' at 0:4)'',
   ''  expected: end of input'',
   ''  up to here: a BStmts was recognised: '' @ squote ''do x'']\<close>
  by eval

text \<open>For a word over \<^typ>\<open>unit\<close> tokens there is no text: a token is shown by
  the spelling of its terminal, and what was recognised by its nonterminal only.\<close>

lemma \<open>(case do_parse2_diag [tu 1 DDo ''do'', tu 4 DDo ''do'', tu 7 DId ''x'', tu 2 DId ''y''] of
    Inl e \<Rightarrow> do_parse2_render e | Inr _ \<Rightarrow> []) =
  ''0:2: 'DId' at column 2 must be at columns 4 or 7 (aligned with 'do' at 0:4)'' @ [CHR 0x0A] @
  ''  expected: end of input'' @ [CHR 0x0A] @
  ''  up to here: a BStmts was recognised''\<close>
  by eval

subsection \<open>Hand-written messages\<close>

text \<open>An \<^theory_text>\<open>errors\<close> block attaches messages to error states by example
  (Jeffery 2003, Pottier 2016). One evaluation of \<open>_probe\<close> gives each sentence its
  state; the result is the data \<open>_messages\<close>, with no theorem. The block below has
  three good sentences, one with a key on the pair of state and terminal, and
  expected warnings: a word that is accepted, a second sentence for one key, a
  hole below the stack, and a name that is no terminal. All of them leave the
  parser defined.\<close>

datatype me_tok = EInt | EPlus | EComma | ELP | ERP | ELB | ERB

grammar (relation) m_br =
  tokens \<open>(me_tok, char) token\<close>
  terminals "+" = EPlus and "," = EComma and "(" = ELP and ")" = ERP and "[" = ELB and "]" = ERB
  productions
    E :: \<open>nat\<close> = E "+" A \<Rightarrow> \<open>\<lambda>a b. a + b\<close> | A
  and
    A :: \<open>nat\<close> = "(" L ")" \<Rightarrow> \<open>\<lambda>l. l\<close> | "[" L "]" \<Rightarrow> \<open>\<lambda>l. l\<close> | EInt \<Rightarrow> \<open>\<lambda>_. 1\<close>
  and
    L :: \<open>nat\<close> = E | E "," L \<Rightarrow> \<open>\<lambda>e l. e + l\<close>

parser (diagnostics) m_br_parse for m_br
  errors
    "(" "]" \<Rightarrow> \<open>An expression must follow $0.\<close>
  | "(" EInt ")" ")" \<Rightarrow> \<open>One closing parenthesis too many.\<close>
  | "(" EInt "]" \<Rightarrow> \<open>Unclosed '(': after $0, ')' is expected.\<close>
  | "(" EInt "+" "]" (token) \<Rightarrow> \<open>']' cannot follow $0 here.\<close>
  | EInt \<Rightarrow> \<open>never reached: the word is accepted\<close>
  | "(" "+" \<Rightarrow> \<open>never used: the key of the first sentence\<close>
  | "[" EInt "]" "+" "]" \<Rightarrow> \<open>Missing an operand after $0, $7.\<close>
  | nonsense \<Rightarrow> \<open>never used: no such terminal\<close>

definition m_br_lines :: \<open>(me_tok, char) token list \<Rightarrow> string list\<close> where
  \<open>m_br_lines w = (case m_br_parse_diag w of
     Inl e \<Rightarrow> pmsg_lines (perr_message m_br_parse_info (\<lambda>c. [c]) e) | Inr _ \<Rightarrow> [])\<close>

text \<open>The hand-written text replaces the primary line, with \<open>$0\<close> the text of the
  topmost stack entry, here the whole \<open>L\<close>; the position and the notes stay.\<close>

lemma \<open>m_br_lines [tc 0 0 ELP ''('', tc 0 1 EInt ''12'', tc 0 3 EPlus ''+'', tc 0 4 EInt ''3'', tc 0 6 ERB '']''] =
  [''0:6: Unclosed '' @ squote ''('' @ '': after 12+3, '' @ squote '')'' @ '' is expected.'',
   ''  expected: '' @ squote ''+'' @ '', '' @ squote '')'' @ '' or '' @ squote '','',
   ''  up to here: a L was recognised: '' @ squote ''12+3'']\<close>
  by eval

text \<open>The key is the state, so another word reaching it gets the message; the state
  is that of an open bracket, reached here from \<open>[\<close>.\<close>

lemma \<open>hd (m_br_lines [tc 0 0 ELP ''('', tc 0 1 ELP ''('', tc 0 2 ERB '']'']) =
  ''0:2: An expression must follow (.''\<close>
  by eval

text \<open>A key on the pair goes before one on the state alone: the sentence with
  \<open>$7\<close> has the same state as the one with \<open>(token)\<close>, and answers for the other
  terminals. The hole below the stack is empty at run time.\<close>

lemma
  \<open>hd (m_br_lines [tc 0 0 ELP ''('', tc 0 1 EInt ''1'', tc 0 2 EPlus ''+'', tc 0 3 ERB '']'']) =
     ''0:3: '' @ squote '']'' @ '' cannot follow + here.''\<close>
  by eval

lemma
  \<open>hd (m_br_lines [tc 0 0 ELP ''('', tc 0 1 EInt ''1'', tc 0 2 EPlus ''+'', tc 0 3 ERP '')'']) =
     ''0:3: Missing an operand after +, .''\<close>
  by eval

text \<open>A state without a message keeps the default text.\<close>

lemma \<open>hd (m_br_lines [tc 0 0 ELB ''['', tc 0 1 EInt ''1'', tc 0 2 ERP '')'']) =
  ''0:2: syntax error at '' @ squote '')'' @ '' (after '' @ squote ''1'' @ '')''\<close>
  by eval

text \<open>A \<open>$\<close> without a digit is itself.\<close>

lemma \<open>fill_holes (\<lambda>i. if i = 1 then ''x'' else []) ''$1 costs $y$2.'' = ''x costs $y.''\<close>
  by eval

text \<open>The added constants are \<open>_messages\<close> and \<open>_probe\<close>, and the code equations stay those of the
  parser without a block.\<close>

parser m_br_plain for m_br

ML_val \<open>same_code \<^context> "m_br_plain" "m_br_parse"
  ["_diag", "_info", "_messages", "_probe", "_render", "_terminals"]\<close>

text \<open>A layout grammar, on the vector driver: \<open>@\<close> gives a token's column, and
  the other tokens follow one past the token before. Keys are the same; the
  message replaces the primary line about the column as well. With \<open>(shift)\<close> the
  key is the state after the last shift, before the reductions the offending token
  triggered.\<close>

parser (diagnostics) m_do_msg for m_do
  errors
    "do"@1 "do"@4 MId@7 MId@2 \<Rightarrow> \<open>This statement is not aligned with $0.\<close>
  | "do"@1 \<Rightarrow> \<open>A block is expected after 'do'.\<close>
  | MId@1 MId@1 (shift) \<Rightarrow> \<open>A single expression only, not $0.\<close>

lemma \<open>(case m_do_msg_diag [tc 0 1 MDo ''do'', tc 0 4 MDo ''do'', tc 0 7 MId ''x'', tc 1 2 MId ''y''] of
    Inl e \<Rightarrow> pmsg_lines (perr_message m_do_msg_info (\<lambda>c. [c]) e) | Inr _ \<Rightarrow> []) =
  [''1:2: This statement is not aligned with do x.'',
   ''  expected: end of input'',
   ''  up to here: a BStmts was recognised: '' @ squote ''do x'']\<close>
  by eval

lemma \<open>(case m_do_msg_diag [tc 0 3 MDo ''do''] of
    Inl e \<Rightarrow> hd (pmsg_lines (perr_message m_do_msg_info (\<lambda>c. [c]) e)) | Inr _ \<Rightarrow> []) =
  ''0:5: A block is expected after '' @ squote ''do'' @ ''.''\<close>
  by eval

text \<open>Over \<^typ>\<open>unit\<close> tokens a stack entry has no text and \<open>$0\<close> is its symbol.\<close>

parser (diagnostics) py_msg for py_suite
  errors
    "while"@1 PId@7 ":"@8 PId@3 PId@4 \<Rightarrow> \<open>Statements of a suite line up, after $0.\<close>

lemma \<open>(case py_msg_diag [tu 1 PWhile ''while'', tu 7 PId ''x'', tu 8 PColon '':'',
      tu 3 PId ''y'', tu 4 PId ''z''] of
    Inl e \<Rightarrow> hd (pmsg_lines (perr_message py_msg_info (\<lambda>_. []) e)) | Inr _ \<Rightarrow> []) =
  ''0:4: Statements of a suite line up, after '' @ squote ''PId'' @ ''.''\<close>
  by eval

text \<open>Tokens with further fields cannot be built from their terminals: such a
  sentence is a warning, and a word given as a term works.\<close>

parser (diagnostics) t_ext_msg for t_ext
  errors
    ":" ":" \<Rightarrow> \<open>never used: the tokens have the field trailing\<close>
  | \<open>[\<lparr>tok = PColon, span = span.make 0 0 0 1 [], trailing = []\<rparr>,
      \<lparr>tok = PColon, span = span.make 0 2 2 1 [], trailing = []\<rparr>]\<close> \<Rightarrow> \<open>An identifier follows ':'.\<close>

lemma \<open>(case t_ext_msg_diag
      [\<lparr>tok = PColon, span = span.make 0 0 0 1 [], trailing = []\<rparr>,
       \<lparr>tok = PColon, span = span.make 0 2 2 1 [], trailing = []\<rparr>] of
    Inl e \<Rightarrow> hd (pmsg_lines (perr_message t_ext_msg_info (\<lambda>_. []) e)) | Inr _ \<Rightarrow> []) =
  ''0:2: An identifier follows '' @ squote '':'' @ ''.''\<close>
  by eval

subsection \<open>An \<open>errors\<close> block cannot fail the parser\<close>

text \<open>A sentence with a free variable or without code is dropped with a warning
  (expected), and the others stay.\<close>

axiomatization m_no_code :: \<open>(me_tok, char) token list\<close>

parser (diagnostics) m_brx_parse for m_br
  errors
    "(" "]" \<Rightarrow> \<open>Kept.\<close>
  | \<open>[tc 0 0 ELP ''('', y]\<close> \<Rightarrow> \<open>never used: a free variable\<close>
  | \<open>m_no_code\<close> \<Rightarrow> \<open>never used: no code\<close>

lemma \<open>(case m_brx_parse_diag [tc 0 0 ELP ''('', tc 0 2 ERB '']''] of
    Inl e \<Rightarrow> hd (pmsg_lines (perr_message m_brx_parse_info (\<lambda>c. [c]) e)) | Inr _ \<Rightarrow> []) =
  ''0:2: Kept.''\<close>
  by eval

subsection \<open>The words of the block are not keywords\<close>

lemma errors: \<open>True\<close> by (fact TrueI)

subsection \<open>Columns\<close>

text \<open>Linear in the ends, however large the columns.\<close>

lemma \<open>col_reps [1000000, 2, 2] = [0, 1, 2, 3, 999999, 1000000, 1000001]\<close>
  by eval

subsection \<open>The state-indexed driver\<close>

text \<open>Constructors without arguments are numbered by a case distinction.\<close>

lemma \<open>map rr_parse_tnum [PA, PB, PC] = map (vnum rr_parse_vtab) [PA, PB, PC]\<close>
  by eval

text \<open>Under \<^text>\<open>parser_literal_tables\<close> its tables are literals (expected warning,
  as for \<open>rr_parse\<close>), and nothing else changes.\<close>

declare [[parser_literal_tables]]
parser (diagnostics) rr_lit_parse for rr
declare [[parser_literal_tables = false]]

lemma \<open>list_all (\<lambda>w. let w' = map (\<lambda>(x, i). tu i x []) w in
    rr_lit_parse_diag w' = rr_parse_diag w')
    (words [(PA, 1), (PB, 2), (PC, 2)] 4)\<close>
  by eval

subsection \<open>Exported code\<close>

text \<open>The parsers with their messages compile in every target.\<close>

export_code lay_parse_diag lay_parse_render do_parse2_diag do_parse2_render
  m_br_parse_diag m_br_parse_render checking SML Scala

export_code lay_parse_diag lay_parse_render do_parse2_diag do_parse2_render in Haskell

export_code lay_parse_diag lay_parse_render do_parse2_diag do_parse2_render in OCaml

end
