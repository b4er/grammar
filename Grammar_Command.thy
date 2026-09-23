theory Grammar_Command
  imports Indentation_Sensitive
  keywords "grammar" :: thy_decl
    and "tokens" "terminals" "productions"
    and "^=" "^>=" "^>" "^*"
    and "\<Rightarrow>" "=>"
    and "parser" :: thy_decl
    and "for"
begin

section \<open>Overview\<close>

text \<open>
  The package defines grammars and parsers for indentation-sensitive context-free
  grammars in the sense of Adams~\cite{adams2013}. A grammar is a value of type
  \<^typ>\<open>('n, 'tok) is_cfg\<close> (\<^file>\<open>Indentation_Sensitive.thy\<close>):
  a list of productions over non-terminals \<open>'n\<close> and token classes \<open>'tok\<close>, in
  which every right-hand-side symbol carries an indentation relation
  \<^typ>\<open>irel\<close>. Parser input is a list of token records
  \<^typ>\<open>('tok, 'ch, 'm) token_scheme\<close> (\<^file>\<open>Token.thy\<close>);
  the token class \<^const>\<open>tok\<close> and the column \<^const>\<open>s_col\<close> of the
  \<^const>\<open>span\<close> are all the parser reads, the remaining fields and any record
  extension \<open>'m\<close> pass through to the semantic actions.

  Two commands make this usable from Isar. @{command grammar} turns a
  grammar specification with semantic actions into a grammar constant and
  per non-terminal decoders, optionally also into a mutual inductive relation
  between words and values. @{command parser} emits an executable parser@{footnote
    \<open>Semantic actions must be executable if the parser is to be.\<close>
  } for such a grammar together with soundness and completeness theorems.

  The parser generator is extensible; this package provides one backend,
  \<open>LR\<close>: an LALR(1)-style parser with layout constraints, running the
  paper's exact \<open>k = 0\<close> machine under one token of lookahead propagated
  over the LR(0) automaton. Its determinism premise of completeness is
  decided by a static check (\<^theory_text>\<open>by eval\<close>).
\<close>

(*<*)
lemma lang_of_complete:
  fixes G :: \<open>('n, 'tok) is_cfg\<close>
    and P :: \<open>('m, 'ch, 'tok) tword \<Rightarrow> 'a \<Rightarrow> bool\<close>
  assumes mem: \<open>w \<in> ilang G\<close>
    and complete: \<open>\<And>pt. wf_ptree G pt \<Longrightarrow> proot pt = (Nt (istart G), istart_ind G) \<Longrightarrow> \<exists>x. P (pyield pt) x\<close>
  shows \<open>\<exists>x. P w x\<close>
proof -
  let ?A = \<open>istart G\<close> and ?i = \<open>istart_ind G\<close>
  from mem obtain pt where
    \<open>wf_ptree G pt\<close> \<open>proot pt = (Nt ?A, ?i)\<close> \<open>pyield pt = w\<close>
    by (auto simp: ilang_iff_ast ast_of_def)

  with complete show ?thesis by blast
qed

lemma wf_ptree_Tm_leaf:
  assumes \<open>fst (proot pt) = Tm t\<close> \<open>wf_ptree G pt\<close>
  shows \<open>\<exists>t'. pt = PLeaf t' \<and> tok t' = t\<close>
  using assms by (cases pt) auto

lemma erase_Nt_E2:
  assumes \<open>proot pt = (Nt A, i)\<close>
  obtains ts where \<open>erase pt = Node A ts\<close>
  using assms by (cases pt) auto

text \<open>The two rules behind the linear decoder proofs (\<^file>\<open>parser_dec_total.ML\<close>,
  \<^file>\<open>parser_rel_bridge.ML\<close>):\<close>

lemma proot_Tm_E:
  assumes \<open>fst (proot pt) = Tm t\<close>
  obtains sp m where \<open>erase pt = Leaf \<lparr>tok = t, span = sp, \<dots> = m\<rparr>\<close>
    and \<open>pyield pt = [\<lparr>tok = t, span = sp, \<dots> = m\<rparr>]\<close> and \<open>snd (proot pt) = s_col sp\<close>
proof -
  from assms have \<open>\<exists>sp m. pt = PLeaf \<lparr>tok = t, span = sp, \<dots> = m\<rparr>\<close>
  proof (cases pt)
    case (PLeaf r)
    then have \<open>pt = PLeaf \<lparr>tok = t, span = span r, \<dots> = token.more r\<rparr>\<close>
      using assms by (cases r) auto
    then show ?thesis by blast
  qed (use assms in simp)

  then obtain sp m
    where \<open>pt = PLeaf \<lparr>tok = t, span = sp, \<dots> = m\<rparr>\<close> by blast
  then show thesis by (intro that[of sp m]) simp_all
qed

lemma case_ast_Nt_None:
  \<open>asym a = Nt B \<Longrightarrow> (case a of Leaf x \<Rightarrow> f x | Node n xs \<Rightarrow> None) = None\<close>
  by (cases a) auto

text \<open>The decoders of a grammar are defined through this recursion combinator,
  which restricts the recursive calls to the children of a node: the functional
  of a grammar is then an ordinary definition.\<close>

function ast_rec ::
  \<open>(('i \<Rightarrow> ('m, 'ch, 'n, 'tok) ast \<Rightarrow> 'r) \<Rightarrow> 'i \<Rightarrow> 'n \<Rightarrow> ('m, 'ch, 'n, 'tok) ast list \<Rightarrow> 'r) \<Rightarrow>
    'r \<Rightarrow> 'i \<Rightarrow> ('m, 'ch, 'n, 'tok) ast \<Rightarrow> 'r\<close> where
  \<open>ast_rec F d i (Node n xs) = F (\<lambda>j c. if c \<in> set xs then ast_rec F d j c else d) i n xs\<close>
| \<open>ast_rec F d i (Leaf w) = d\<close>
  by pat_completeness auto
termination
  by (relation \<open>measure (\<lambda>(F, d, i, t). size t)\<close>)
    (auto intro: le_imp_less_Suc size_list_estimation')

declare ast_rec.simps [simp del, code del]

ML_file \<open>grammar_common.ML\<close>
ML_file \<open>grammar_ptree_induct.ML\<close>
ML_file \<open>grammar_defs.ML\<close>
ML_file \<open>grammar.ML\<close>

ML_file \<open>parser_dec_total.ML\<close>
ML_file \<open>parser_rel_bridge.ML\<close>
ML_file \<open>parser_generators.ML\<close>

hide_fact
  lang_of_complete
  wf_ptree_Tm_leaf
  erase_Nt_E2
  proot_Tm_E
  case_ast_Nt_None
(*>*)

section \<open>Grammar specifications\<close>

text \<open>
  \begin{matharray}{rcl}
    @{command grammar} & : & \<open>local_theory \<rightarrow> local_theory\<close> \\
  \end{matharray}

  \<^rail>\<open>
    @@{command grammar} ('(' 'relation' ')')? name '=' \<newline>
      (@'tokens' type)? \<newline>
      (@'terminals' (terminal + @'and'))? \<newline>
      @'productions' (production + @'and')
    ;
    non_terminal: name
    ;
    terminal: string '=' term | name
    ;
    production: non_terminal ('::' type)? '=' (alternative + '|')
    ;
    alternative: (symbol +) semantic_action? | semantic_action
    ;
    symbol: (string | non_terminal | cartouche) ('\<^sup>=' | '\<^sup>\<ge>' | '\<^sup>>' | '\<^sup>*')?
    ;
    semantic_action: ('\<Rightarrow>' | '=>') term
  \<close>

  The categories \<open>name\<close>, \<open>string\<close>, \<open>type\<close>, \<open>term\<close> and \<open>cartouche\<close> are those
  of the Isar reference manual. The annotations may also be written in ASCII:
  \<^verbatim>\<open>^=\<close>, \<^verbatim>\<open>^>=\<close>, \<^verbatim>\<open>^>\<close> and \<^verbatim>\<open>^*\<close>.

  \<^descr> \<^theory_text>\<open>grammar G = \<dots>\<close> checks the specification and defines the
  grammar constant \<open>G\<close> (\<^theory_text>\<open>grammar (relation) G = \<dots>\<close> also defines the
  relation family, see below).

  The first non-terminal is the start symbol.

  \<^descr> \<^theory_text>\<open>tokens T\<close> fixes the token record type. \<open>T\<close> is a ground
  instance of \<^typ>\<open>('tok, 'ch, 'm) token_scheme\<close>: the plain record
  \<^typ>\<open>('tok, 'ch) token\<close>, or a client extension
  \<^theory_text>\<open>record my_token = (my_tok, char) token + \<dots>\<close> (see below).

  A type that is not a token record abbreviates \<open>(T, unit) token\<close>; without
  a \<^theory_text>\<open>tokens\<close> clause the token type is \<^typ>\<open>string\<close>.

  \<^descr> \<^theory_text>\<open>terminals\<close> declares the terminal symbols. A \<^emph>\<open>fixed spelling\<close>
  \<open>"s" = t\<close> lets the quoted spelling \<open>"s"\<close> stand for the token
  \<open>t :: 'tok\<close> in the productions without binding it in semantic actions;
  a bare name declares a \<^emph>\<open>token class\<close>, used by its name in the
  productions with the whole token record as its value. A bare name that
  is neither a non-terminal nor declared is read as a term of type \<open>'tok\<close>
  (for the \<^typ>\<open>string\<close> token type: the string itself).

  \<^descr> \<^theory_text>\<open>productions\<close> lists the non-terminals. A group \<open>A :: \<tau> = alt\<^sub>1 | \<dots> | alt\<^sub>n\<close>
  declares the non-terminal \<open>A\<close> with \<^emph>\<open>carrier\<close> \<open>\<tau>\<close> (the type of its semantic
  values and its alternatives). The ascription can be omitted when the
  carrier follows from the actions.

  \<^descr> An alternative is a sequence of symbols, each with an optional
  annotation, followed by an optional semantic action. A symbol is a
  non-terminal, a fixed terminal, or an inline token \<open>\<open>t\<close>\<close> with
  \<open>t :: 'tok\<close>.

  A non-terminal \<open>B\<close> contributes its value of type \<open>\<tau>\<^sub>B\<close>, and a token the
  complete token record.

  \<^descr> The semantic action \<open>\<Rightarrow> f\<close> computes the value of the alternative from the
  values of its value binding symbols, in order: \<open>\<tau>\<^sub>1 \<Rightarrow> \<dots> \<Rightarrow> \<tau>\<^sub>k \<Rightarrow> \<tau>\<^sub>A\<close>.

  An alternative without action must have exactly one value symbol, whose
  value is passed on.

  \<^descr> The annotation of a symbol is its indentation relation: \<open>\<^sup>=\<close> for
  \<^const>\<open>Eq\<close>, \<open>\<^sup>\<ge>\<close> for \<^const>\<open>Ge\<close>, \<open>\<^sup>>\<close> for \<^const>\<open>Gt\<close> and \<open>\<^sup>*\<close> for
  \<^const>\<open>Any\<close>, the default.
\<close>


subsection \<open>Meaning of the annotations\<close>

text \<open>
  The indentation of a terminal is the column of its token, a nonterminal has
  no token of its own and its indentation is a free choice restricted only
  by the annotations.

  A sentential form annotates every symbol with an indentation (column).
  Expanding \<open>(A, i)\<close> by a production \<open>A = X\<^sub>1\<^sup>r\<^sup>1 \<dots> X\<^sub>n\<^sup>r\<^sup>n\<close> chooses for each
  symbol an indentation \<open>j\<^sub>k\<close> with \<open>irel_sat r\<^sub>k j\<^sub>k i\<close>:

  \begin{center}
  @{thm [mode = iff] irel_sat.simps(1) [no_vars]} \\
  @{thm [mode = iff] irel_sat.simps(2) [no_vars]} \\
  @{thm [mode = iff] irel_sat.simps(3) [no_vars]} \\
  @{thm [mode = iff] irel_sat.simps(4) [no_vars]}
  \end{center}

  So \<open>\<^sup>=\<close> aligns a symbol with the nonterminal being expanded, \<open>\<^sup>>\<close> indents it
  further, \<open>\<^sup>\<ge>\<close> allows both, and \<open>\<^sup>*\<close> places no constraint. A block whose
  members are aligned is written \<open>Block = Stmt\<^sup>= | Block\<^sup>= Stmt\<^sup>=\<close>: all
  statements share the indentation of the block. A grammar in which every
  annotation is \<open>\<^sup>*\<close> is an ordinary context-free grammar.

  \<^term>\<open>ilang G\<close> is the set of token words derivable in this way.
\<close>


subsection \<open>What is defined\<close>

text \<open>
  For \<^theory_text>\<open>grammar G\<close> with non-terminals \<open>A\<close> of carrier \<open>\<tau>\<^sub>A\<close> and start
  symbol \<open>S\<close>:

  \<^descr> The grammar constant \<open>G :: (string, 'tok) is_cfg\<close> with its equation \<open>G_def\<close>.
  Nonterminals are represented by their names, the start symbol has
  indentation \<open>0\<close>.

  \<^descr> One decoder \<open>G__dec_A :: ('m, 'ch, string, 'tok) ast \<Rightarrow> \<tau>\<^sub>A option\<close> per
  nonterminal, defined by \<^theory_text>\<open>fun\<close>. It evaluates the actions over a parse
  tree, matching each node against the productions of \<open>A\<close>.

  \<^descr> With \<open>(relation)\<close>: the mutual \<^theory_text>\<open>inductive\<close> family
  \<open>G_A :: nat \<Rightarrow> word \<Rightarrow> \<tau>\<^sub>A \<Rightarrow> bool\<close>, where \<open>G_A i w x\<close> holds if the word
  \<open>w\<close> derives from \<open>(A, i)\<close> with value \<open>x\<close>, there is one introduction rule
  per alternative. The facts are \<open>G.intros\<close>, \<open>G.inducts\<close> and
  \<open>G.lang: (\<exists>x. G_S 0 w x) \<longleftrightarrow> w \<in> ilang G\<close>.

  For a grammar without annotations the indentation argument is dropped:
  \<open>G_A :: word \<Rightarrow> \<tau>\<^sub>A \<Rightarrow> bool\<close> and \<open>G.lang: (\<exists>x. G_S w x) \<longleftrightarrow> w \<in> ilang G\<close>.
\<close>


section \<open>Parser generation\<close>

text \<open>
  \begin{matharray}{rcl}
    @{command parser} & : & \<open>local_theory \<rightarrow> local_theory\<close> \\
  \end{matharray}

  \<^rail>\<open>
    @@{command parser} ('(' name ')')? name @'for'? name
  \<close>

  \<^descr> \<^theory_text>\<open>parser p for G\<close> defines \<open>p :: word \<Rightarrow> \<tau>\<^sub>S option\<close> for the start
  symbol \<open>S\<close> of \<open>G\<close>, together with soundness and completeness theorems.
  The optional first name selects the parser generator (by default \<open>LR\<close>).
\<close>

text \<open>
  The only generator at present is \<open>LR\<close> (\<^file>\<open>lr/lr.ML\<close>), described next.
\<close>

section \<open>LR parser\<close>

text \<open>
  \<^descr> The definition is \<open>p w = Option.bind (dparse G Shn w) G__dec_S\<close>:
  \<^text>\<open>dparse\<close> is the verified driver of \<^file>\<open>lr/LR_Driver.thy\<close>, an
  LALR(1)-style parser over the LR(0) automaton whose lookahead cells carry
  the layout constraints, \<open>Shn\<close> a
  fresh name for the augmented start symbol, and \<open>G__dec_S\<close> the decoder of
  the start symbol. For code generation the LR tables are computed once at
  definition time and stored as constants \<open>p_states\<close>, \<open>p_gtab\<close>, \<open>p_redtab\<close>,
  \<open>p_xinit\<close>, \<open>p_xclos\<close> and \<open>p_i0\<close>. The code equation of \<open>p\<close> refers to those
  tables, so neither \<^theory_text>\<open>eval\<close> nor exported code needs to rebuild the
  automaton.

  \<^descr> The facts \<open>p.sound\<close> and \<open>p.complete\<close> relate the parser to the
  language:
  \begin{center}
    \<open>p.sound: p w = Some x \<Longrightarrow> w \<in> ilang G\<close> \\
    \<open>p.complete: w \<in> ilang G \<Longrightarrow> \<exists>x. p w = Some x\<close>
  \end{center}
  For a grammar declared with \<open>(relation)\<close>, \<open>p.sound\<close> and \<open>p.complete\<close>
  relate it to the relation of the start symbol:
  \begin{center}
    \<open>p.sound: p w = Some x \<Longrightarrow> G_S 0 w x\<close> \\
    \<open>p.complete: G_S 0 w x \<Longrightarrow> p w = Some x\<close>
  \end{center}
  The language forms are then available as \<open>p.sound_lang\<close> and
  \<open>p.complete_lang\<close>; should the bridge to the relation fail, the command
  warns and keeps the language forms under the plain names.
\<close>

text \<open>
  The generic theorems behind these facts carry premises that the command
  discharges when \<open>p\<close> is defined. Soundness needs only \<^const>\<open>fresh_name\<close>,
  proved by simplification, and is therefore always unconditional.

  Completeness needs in addition:

  \<^descr> \<open>mdet G Shn\<close>, determinism of the driver on the grammar. The
  command evaluates the static report \<open>rlalr_conflicts G Shn\<close>, the
  LALR conflict analysis extended with the layout constraints. If it is
  empty, \<^text>\<open>mdet\<close> follows by \<^text>\<open>rlalr_sufficient\<close> and the command
  says so; otherwise it warns, lists the conflicting states, and keeps
  \<^text>\<open>mdet\<close> as a premise of \<open>p.complete\<close>. The check is sufficient,
  not necessary: an ambiguous grammar always fails it, a deterministic one
  may fail it too.  The parser is emitted either way; a run of it that
  revisits a configuration without consuming input (a unit self-loop whose
  reduce is licensed at the end of the input, say) ends with \<open>None\<close>.

  \<^descr> Totality of the decoders on the parse trees of \<open>G\<close>.

  \<^descr> For the relational forms, \<open>acc_conflicts G Shn = []\<close> (again by
  evaluation).

  Premises that cannot be discharged stay on the theorem as assumptions, so
  \<^theory_text>\<open>thm p.complete\<close> shows what has been established.
\<close>

section \<open>Example\<close>

text \<open>
  A statement is an identifier or a \<open>while\<close> header followed by a block
  indented further than the header, all statements of a block aligned.
  Values count statements:

  @{theory_text [display, indent = 2]
    \<open>datatype tok = While | Colon | Id

grammar (relation) py =
  tokens \<open>tok\<close>
  terminals "while" = \<open>While\<close> and ":" = \<open>Colon\<close>
  productions
      Prog :: \<open>nat\<close> = Block\<^sup>*
    and
      Block :: \<open>nat\<close>
        = Stmt\<^sup>=
        | Block\<^sup>= Stmt\<^sup>=  \<Rightarrow> \<open>(+)\<close>
    and
      Stmt :: \<open>nat\<close>
        = Id\<^sup>=                      \<Rightarrow> \<open>\<lambda>_. 1\<close>
        | "while"\<^sup>= Id\<^sup>> ":"\<^sup>> Block\<^sup>>  \<Rightarrow> \<open>\<lambda>_ n. n + 1\<close>

parser py_parse for py\<close>}

  The token class \<open>Id\<close> is a value symbol, so the first action of \<open>Stmt\<close> takes
  the token record and ignores it. \<open>Block\<^sup>*\<close> leaves the column of the outermost
  block open, \<open>Block\<^sup>>\<close> after a header demands a deeper one, and \<open>Block\<^sup>= Stmt\<^sup>=\<close>
  aligns the members.

  The key theorem generated is
  \begin{center}
    \<open>py.lang: (\<exists>x. py_Prog 0 w x) = (w \<in> ilang py)\<close>
  \end{center}
  where \<open>py_Prog\<close> is the mutual \<^theory_text>\<open>inductive\<close> relation defined. For sake of
  brevity we omit the full \<open>py.inducts\<close>/\<open>py.intros\<close> and only show the intros
  for \<open>py_Stmt\<close>, writing
  \<open>\<langle>t; sp\<rangle>\<close> for the token record \<open>\<lparr>tok = t, span = sp\<rparr>\<close> (extension fields elided):

  \begin{mathpar}
  \inferrule
    {\mbox{\<open>s_col sp = i\<close>}}
    {\mbox{\<open>py_Stmt i [\<langle>Id; sp\<rangle>] 1\<close>}}
  \and
  \inferrule
    {\mbox{\<open>py_Block j w v\<close>} \\
     \mbox{\<open>s_col sp\<^sub>1 = i\<close>} \\
     \mbox{\<open>i < s_col sp\<^sub>2\<close>} \\
     \mbox{\<open>i < s_col sp\<^sub>3\<close>} \\
     \mbox{\<open>i < j\<close>}}
    {\mbox{\<open>py_Stmt i (\<langle>While; sp\<^sub>1\<rangle> # \<langle>Id; sp\<^sub>2\<rangle> # \<langle>Colon; sp\<^sub>3\<rangle> # w) (v + 1)\<close>}}
  \end{mathpar}

  The static check is empty for \<open>py\<close>, so completeness is unconditional:
  \begin{center}
  \<open>py_parse.complete: py_Prog 0 w x \<Longrightarrow> py_parse w = Some x\<close>
  \end{center}

  With \<open>tu c t\<close> a token of class \<open>t\<close> at column \<open>c\<close>, the word
  \<open>while x:\<close> at column 1, \<open>y\<close> and \<open>z\<close> at column 3 and \<open>w\<close> at column 1 parses
  to \<open>Some 4\<close>, while moving \<open>z\<close> to column 4 gives \<open>None\<close>:

  @{theory_text [display, indent = 2]
    \<open>lemma \<open>py_parse [tu 1 While, tu 7 Id, tu 8 Colon, tu 3 Id, tu 3 Id, tu 1 Id] = Some 4\<close>
  by eval

lemma \<open>py_parse [tu 1 While, tu 7 Id, tu 8 Colon, tu 3 Id, tu 4 Id] = None\<close>
  by eval\<close>}

  Further examples can be found in \<^file>\<open>tests/Regression_Tests.thy\<close>.
\<close>

end
