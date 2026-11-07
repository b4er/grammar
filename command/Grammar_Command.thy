theory Grammar_Command
  imports Grammar_Model.Grammar_Base
  keywords "grammar" :: thy_decl
    and "tokens" "terminals" "productions"
    and "^=" "^>=" "^>" "*"
    and "\<Rightarrow>" "=>"
    and "parser" :: thy_decl
    and "for"
begin

section \<open>Overview\<close>

text \<open>
  The package defines grammars and parsers for indentation-sensitive context-free
  grammars in the sense of Adams~\cite{adams2013}. A grammar is a value of type
  \<^typ>\<open>('n, 'tok) is_cfg\<close> (\<^file>\<open>../Indentation_Sensitive.thy\<close>):
  a list of productions over non-terminals \<open>'n\<close> and token classes \<open>'tok\<close>, in
  which every right-hand-side symbol carries an indentation relation
  \<^typ>\<open>irel\<close>. Parser input is a list of token records
  \<^typ>\<open>('tok, 'ch, 'm) token_scheme\<close> (\<^file>\<open>../Token.thy\<close>);
  the token class \<^const>\<open>tok\<close> and the column \<^const>\<open>s_col\<close> of the
  \<^const>\<open>span\<close> are all the parser reads, the remaining fields and any record
  extension \<open>'m\<close> pass through to the semantic actions.

  Two commands make this usable from Isar. @{command grammar} turns a
  grammar specification with semantic actions into a grammar constant and
  per non-terminal decoders, optionally also into an inductive relation
  between words and values. @{command parser} emits an executable parser@{footnote
    \<open>Semantic actions must be executable if the parser is to be.\<close>
  } for such a grammar together with soundness and completeness theorems.

  A grammar may use the nonterminals of an earlier grammar, as \<open>a.X\<close>, and parametric
  nonterminals (templates) such as \<open>Sep1(X, S)\<close>, with the postfix operators \<open>* + ?\<close>
  for lists and options. Both are expanded before anything is defined, so the result
  is an ordinary closed grammar. A rejected word gets a located error report, with
  hand-written messages if given, and can be recovered into a tree; that side is
  unverified and cannot change what the parser accepts.

  The parser generator is extensible; this package provides one backend,
  \<open>LR\<close>: an LALR(1)-style parser with layout constraints, running the
  paper's exact \<open>k = 0\<close> machine under one token of lookahead propagated
  over the LR(0) automaton. Its determinism premise of completeness is
  decided by a static check (\<^theory_text>\<open>by eval\<close>).
\<close>

section \<open>The span of a yield\label{sec:span}\<close>

text \<open>An alternative that writes \<open>@span\<close> passes its action the span of its yield,
  from the first token to the last (\<open>word_span\<close>): line, column and offset of
  the first token, the length up to the end of the last, and the concatenated texts of
  the tokens. The decoders compute it on the children of a node
  (\<open>yield_span\<close>), the relation on the word; \<open>ast_yield_erase\<close> makes the two
  agree.\<close>

fun ast_yield :: \<open>('m, 'ch, 'n, 'tok) ast \<Rightarrow> ('m, 'ch, 'tok) tword\<close> where
  \<open>ast_yield (Leaf t) = [t]\<close>
| \<open>ast_yield (Node n ts) = concat (map ast_yield ts)\<close>

definition word_span :: \<open>('m, 'ch, 'tok) tword \<Rightarrow> 'ch span\<close> where
  \<open>word_span w =
    (case w of
      [] \<Rightarrow> \<lparr>s_line = 0, s_col = 0, s_off = 0, s_len = 0, s_txt = []\<rparr>
    | t # _ \<Rightarrow>
        \<lparr>s_line = s_line (span t), s_col = s_col (span t), s_off = s_off (span t),
         s_len = s_off (span (last w)) + s_len (span (last w)) - s_off (span t),
         s_txt = concat (map (s_txt \<circ> span) w)\<rparr>)\<close>

definition yield_span :: \<open>('m, 'ch, 'n, 'tok) ast list \<Rightarrow> 'ch span\<close> where
  \<open>yield_span xs = word_span (concat (map ast_yield xs))\<close>

lemma ast_yield_erase [simp]: \<open>ast_yield (erase pt) = pyield pt\<close>
  by (induction pt) (simp_all cong: map_cong)

(*<*)
fun ast_first :: \<open>('m, 'ch, 'n, 'tok) ast list \<Rightarrow> ('tok, 'ch, 'm) token_scheme option\<close> where
  \<open>ast_first [] = None\<close>
| \<open>ast_first (Leaf t # _) = Some t\<close>
| \<open>ast_first (Node _ ts # xs) = (case ast_first ts of None \<Rightarrow> ast_first xs | r \<Rightarrow> r)\<close>

fun ast_last :: \<open>('m, 'ch, 'n, 'tok) ast list \<Rightarrow> ('tok, 'ch, 'm) token_scheme option\<close> where
  \<open>ast_last [] = None\<close>
| \<open>ast_last (x # xs) =
    (case ast_last xs of
      None \<Rightarrow> (case x of Leaf t \<Rightarrow> Some t | Node _ ts \<Rightarrow> ast_last ts)
    | r \<Rightarrow> r)\<close>

fun hd_opt :: \<open>'a list \<Rightarrow> 'a option\<close> where
  \<open>hd_opt [] = None\<close>
| \<open>hd_opt (x # _) = Some x\<close>

lemma hd_opt_append: \<open>hd_opt (a @ b) = (case hd_opt a of None \<Rightarrow> hd_opt b | r \<Rightarrow> r)\<close>
  by (cases a) auto

lemma hd_opt_rev: \<open>hd_opt (rev c) = (if c = [] then None else Some (last c))\<close>
  by (induction c) (auto simp: hd_opt_append split: option.split)

lemma ast_first_yield: \<open>ast_first xs = hd_opt (concat (map ast_yield xs))\<close>
  by (induction xs rule: ast_first.induct) (auto simp: hd_opt_append split: option.split)

lemma ast_last_yield: \<open>ast_last xs = hd_opt (rev (concat (map ast_yield xs)))\<close>
  by (induction xs rule: ast_last.induct) (auto simp: hd_opt_append split: option.split ast.split)

text \<open>The texts by an accumulator: on a left-recursive spine, \<open>concat (map ast_yield xs)\<close>
  would rebuild the left-nested appends at every node.\<close>

fun ast_txts :: \<open>('m, 'ch, 'n, 'tok) ast list \<Rightarrow> 'ch list \<Rightarrow> 'ch list\<close> where
  \<open>ast_txts [] acc = acc\<close>
| \<open>ast_txts (Leaf t # xs) acc = s_txt (span t) @ ast_txts xs acc\<close>
| \<open>ast_txts (Node _ ts # xs) acc = ast_txts ts (ast_txts xs acc)\<close>

lemma ast_txts_yield:
  \<open>ast_txts xs acc = concat (map (s_txt \<circ> span) (concat (map ast_yield xs))) @ acc\<close>
  by (induction xs acc rule: ast_txts.induct) simp_all

lemma yield_span_code [code]:
  \<open>yield_span xs =
    (case ast_first xs of
      None \<Rightarrow> \<lparr>s_line = 0, s_col = 0, s_off = 0, s_len = 0, s_txt = []\<rparr>
    | Some t \<Rightarrow>
        (case ast_last xs of
          None \<Rightarrow> undefined
        | Some z \<Rightarrow>
            \<lparr>s_line = s_line (span t), s_col = s_col (span t), s_off = s_off (span t),
             s_len = s_off (span z) + s_len (span z) - s_off (span t),
             s_txt = ast_txts xs []\<rparr>))\<close>
proof -
  obtain c where c: \<open>concat (map ast_yield xs) = c\<close> by blast
  show ?thesis
    unfolding yield_span_def word_span_def ast_first_yield ast_last_yield ast_txts_yield c
    by (cases c) (simp_all add: hd_opt_rev del: rev.simps)
qed
(*>*)

(*<*)
ML_file \<open>grammar_common.ML\<close>
ML_file \<open>grammar_ptree_induct.ML\<close>
ML_file \<open>grammar_defs.ML\<close>
ML_file \<open>grammar_rel.ML\<close>
ML_file \<open>grammar_expand.ML\<close>
ML_file \<open>grammar_elab.ML\<close>
ML_file \<open>grammar_syntax.ML\<close>

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
    @@{command grammar} ('(' 'relation' ')')? name '=' ('open' (name +))? \<newline>
      (@'tokens' type)? \<newline>
      (@'terminals' (terminal + @'and'))? \<newline>
      ((@'precedence' levels | @'forbid' forbid) *) \<newline>
      @'productions' (production + @'and')
    ;
    levels: (level + '>')
    ;
    level: ('left' | 'right' | 'nonassoc' | 'open' | 'list') ((prec_name '!'?) +)
    ;
    forbid: prec_name '@' nat ('direct' | 'left' | 'right') (prec_name +)
    ;
    prec_name: string | name
    ;
    non_terminal: name
    ;
    terminal: string '=' term | name
    ;
    production: non_terminal parameters? ('::' type)? '=' (alternative + '|')
    ;
    parameters: '(' (name + ',') ')'
    ;
    alternative: (symbol +) mark? semantic_action? | mark? semantic_action
    ;
    mark: '(' 'prec' prec_name ')'
    ;
    symbol: item ('\<^sup>=' | '\<^sup>\<ge>' | '\<^sup>>')? | '@span'
    ;
    item: (string | non_terminal | reference | cartouche | instance | '(' (symbol +) ')')
      ('*' | '+' | '?') *
    ;
    instance: name '(' (item + ',') ')'
    ;
    reference: name '.' non_terminal
    ;
    semantic_action: ('\<Rightarrow>' | '=>') term
  \<close>

  The categories \<open>name\<close>, \<open>string\<close>, \<open>type\<close>, \<open>term\<close> and \<open>cartouche\<close> are those
  of the Isar reference manual. The annotations may also be written in ASCII:
  \<^verbatim>\<open>^=\<close>, \<^verbatim>\<open>^>=\<close> and \<^verbatim>\<open>^>\<close>. Templates, instances and the
  operators are described below.

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

  \<^descr> \<open>@span\<close> is a value of type \<^typ>\<open>'ch span\<close>, in the place where it is written
  among the value symbols: the span of the alternative's yield, from its first token to
  its last (\<^const>\<open>word_span\<close>, section~\ref{sec:span}). It is not a grammar symbol;
  the grammar constant, the tables and the diagnostics do not see it.

  An alternative with \<open>@span\<close> needs a symbol that derives no empty word, or it has no
  first token. \<open>@span\<close> takes no annotation, is written once per alternative, and stands
  at the top level of an alternative, not inside an operator's group or as a template
  argument (a template alternative may have it).

  \<^descr> The annotation of a symbol is its indentation relation: \<open>\<^sup>=\<close> for
  \<^const>\<open>Eq\<close>, \<open>\<^sup>\<ge>\<close> for \<^const>\<open>Ge\<close>, \<open>\<^sup>>\<close> for \<^const>\<open>Gt\<close>; without
  annotation it is \<^const>\<open>Any\<close>.
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
  further, \<open>\<^sup>\<ge>\<close> allows both, and no annotation places no constraint. A block whose
  members are aligned is written \<open>Block = Stmt\<^sup>= | Block\<^sup>= Stmt\<^sup>=\<close>: all
  statements share the indentation of the block. A grammar without
  annotations is an ordinary context-free grammar.

  \<^term>\<open>ilang G\<close> is the set of token words derivable in this way.
\<close>


subsection \<open>Precedence\<close>

text \<open>
  \<^theory_text>\<open>precedence right "^" > left "*" "/" > left "+" "-" > nonassoc "=="\<close> declares
  levels, \<open>>\<close> binding tighter. A production goes by its \<^theory_text>\<open>(prec NAME)\<close>, else by its
  last terminal, written as its spelling or its constructor name; a level's name need
  not be a terminal, as in \<^theory_text>\<open>"-" E (prec UMINUS)\<close>. Several lines merge: a name in two
  lines is one level, with one associativity, and the order is the transitive closure of
  the lines. A cycle is an error. Two levels no line relates stay ambiguous, and the
  parser reports the conflict.

  \<open>left\<close>, \<open>right\<close> and \<open>nonassoc\<close> are the usual readings. \<open>open\<close> leaves the
  left operand of its productions unconstrained, for forms that end in an open
  construct. \<open>list\<close> does not constrain the productions of the level against each other
  on one nonterminal, for flat chains. A prefix form on the right of a tighter operator
  is normally allowed, as in \<open>a * - b\<close>; \<open>!\<close> on an item forbids that. \<^theory_text>\<open>forbid p @ k
  right c\<close> says what no level says: \<open>c\<close> is not on the right spine of child \<open>k\<close> of
  \<open>p\<close> (\<open>left\<close>: the left spine, \<open>direct\<close>: the child itself).

  The declarations belong to the grammar, the restriction to the parser: each parser
  of a declaring grammar defines \<open>p_prec\<close> and \<open>p_gram = restricted G p_prec\<close> and is built
  from \<open>p_gram\<close>, from its own start; a grammar without declarations is not touched.
  Such a theory imports \<^verbatim>\<open>LR_Parser.LR_Prec_Parse\<close>. \<open>p.sound\<close> and \<open>p.complete\<close> are
  stated against \<open>G\<close> and \<open>prec_ok\<close>, on trees of \<open>G\<close>; \<open>p.sound_lang\<close> and
  \<open>p.complete_lang\<close> against \<open>prec_lang\<close>. With \<^theory_text>\<open>grammar (relation)\<close> the relation
  family is defined as usual but does not read the declarations, so no theorem is
  stated against it, and \<^theory_text>\<open>parser\<close> says so.
\<close>


subsection \<open>Composition by reference\<close>

text \<open>
  A symbol \<open>a.X\<close>, with \<open>a\<close> an earlier grammar and \<open>X\<close> one of its nonterminals,
  uses \<open>X\<close> in another grammar \<open>b\<close>. The productions of \<open>a\<close> reachable from \<open>X\<close> are
  copied into \<open>b\<close>, after \<open>b\<close>'s own, renaming each nonterminal \<open>Y\<close> of \<open>a\<close> to \<open>a.Y\<close>;
  a nonterminal that \<open>a\<close> copied itself, \<open>c.Z\<close>, keeps its name, so one reached along
  two paths is copied once. \<open>b\<close> is then a closed grammar like any other, and \<open>a.X\<close> is
  one of its nonterminals, also as the start of a \<^theory_text>\<open>parser\<close> entry. In constant and fact
  names the dot is an underscore: \<open>b__dec_a_X\<close>, \<open>b_a_X\<close>.

  The token types of \<open>a\<close> and \<open>b\<close> must be the same. The fixed spellings of the copied
  productions' terminals come with them and may be used in \<open>b\<close>; a spelling that
  stands for two different tokens is an error. The precedence declarations of \<open>a\<close>
  apply to the copied productions. A defined nonterminal has a plain name, and two
  nonterminals with one name in the constants (\<open>a_X\<close> and \<open>a.X\<close>) are an error.

  If \<open>a\<close> and \<open>b\<close> both have a relation (\<^theory_text>\<open>grammar (relation)\<close>) and agree in being
  indentation-sensitive or not, \<open>b.a_X_iff: b_a_X i w x \<longleftrightarrow> a_X i w x\<close> links the two
  for each \<open>a.X\<close> that \<open>b\<close> names, so what a parser of \<open>b\<close> proves about \<open>a.X\<close> is a fact
  about \<open>a\<close>. The decoders are defined anew for the copy.

  \<^theory_text>\<open>grammar b = open a\<close> lets \<open>b\<close> write a nonterminal \<open>X\<close> of \<open>a\<close> without the
  qualifier: a bare name that is not a nonterminal or terminal class of \<open>b\<close> itself, nor
  a template parameter, is \<open>a.X\<close> if \<open>a\<close> defines \<open>X\<close>. So \<open>b\<close>'s own names come first,
  a name that two opened grammars define must be qualified, and a name no opened grammar
  defines is read as before (a token, under a token type other than \<^typ>\<open>string\<close>). A
  template \<open>P\<close> of an opened grammar comes before one of the same name elsewhere. Only
  the names change: \<open>X\<close> under \<open>open a\<close> is the copy \<open>a.X\<close>, with the same constants.

  Messages name a copy without the qualifier (\<open>a.Atom\<close> as \<open>Atom\<close>, \<open>a.Block(Bind)\<close> as
  \<open>Block(Bind)\<close>), except where two nonterminals would then read alike.

  Under \<^theory_text>\<open>declare [[grammar_nat_labels]]\<close> a grammar's nonterminals are
  numbers in HOL, \<^typ>\<open>(nat, 'tok) is_cfg\<close>, instead of their names: \<open>0\<close> for the first,
  then \<open>2, 3, \<dots>\<close> in the order of declaration, the copies after the grammar's own (\<open>1\<close>
  is skipped, as the simplifier rewrites it to \<open>Suc 0\<close>). The constants, relations,
  decoders and parsers are the same otherwise, and messages still show the names. The
  generated proofs then compare numerals instead of strings, which pays for long
  qualified names such as \<open>caraml_exprs.Atom\<close>. A grammar with \<open>precedence\<close> of its own,
  or that copies nonterminals of one with \<open>precedence\<close>, keeps its names, since the
  restriction of \<^file>\<open>../lr/LR_Restrict.thy\<close> works on strings.
\<close>


subsection \<open>Templates and operators\<close>

text \<open>
  A production group with parameters, \<open>P(X\<^sub>1, \<dots>, X\<^sub>n) :: \<tau> = \<dots>\<close>, is a \<^emph>\<open>template\<close>.
  It defines nothing by itself. Each use \<open>P(a\<^sub>1, \<dots>, a\<^sub>n)\<close>, with the parenthesis
  written directly after the name, is an \<^emph>\<open>instance\<close>: the group with every \<open>X\<^sub>i\<close>
  replaced by \<open>a\<^sub>i\<close>, an ordinary nonterminal named \<open>P(a\<^sub>1, \<dots>, a\<^sub>n)\<close>, made once per
  distinct argument list. An argument is a symbol (a nonterminal, a terminal, an
  instance, a reference \<open>a.X\<close>), a symbol with an operator, or a group of symbols, which
  then stands in place of the parameter as a sequence. The actions of the template see
  the right-hand side after the replacement: a parameter bound to a fixed terminal binds
  nothing. Type variables in the ascription of a template are inferred per instance.
  A template of an earlier grammar \<open>g\<close> is used as \<open>g.P(\<dots>)\<close> or, when no other
  template has the name, \<open>P(\<dots>)\<close>; its nonterminals then come in as \<open>g.Y\<close>, its
  spellings with them. A grammar of templates only defines nothing.

  The postfix operators over a symbol or a group \<open>(s\<^sub>1 \<dots> s\<^sub>n)\<close> generate a
  nonterminal: \<open>s*\<close> and \<open>s+\<close> are left-recursive lists of carrier \<open>'x list\<close>,
  \<open>L = \<epsilon> | L s\<^sub>1 \<dots> s\<^sub>n\<close> (and \<open>L = s\<^sub>1 \<dots> s\<^sub>n | \<dots>\<close>) with \<open>xs @ [x]\<close>, and
  \<open>s?\<close> is an option, \<open>None\<close> or \<open>Some x\<close>. The element \<open>x\<close> is the value of the one value
  symbol of the group, or the tuple of several. A group without value symbol, as in
  \<open>";"?\<close>, generates a nonterminal that binds nothing at its use. The recursive occurrence
  \<open>L\<close> carries the annotation of the group's first symbol, so \<open>(Stmt\<^sup>=)+\<close> is
  \<open>L = Stmt\<^sup>= | L\<^sup>= Stmt\<^sup>=\<close>, and a grammar without annotations stays one. An
  annotation after the operator, \<open>(";" X)*\<^sup>=\<close>, is that of the generated nonterminal at
  its use. A group without operator is inlined and takes no annotation.

  Generated nonterminals are named as written, \<open>Block(Decl)\<close>, \<open>(; Decl)*\<close> (a
  spelling without its quotes, which a HOL string cannot hold); in constant names they are identifiers: \<open>Block_Decl\<close>,
  \<open>Decl_list\<close>, \<open>Decl_list1\<close>, \<open>Decl_opt\<close> for an operator over one nonterminal, and
  \<open>A_1, A_2, \<dots>\<close> for the groups of the alternatives of \<open>A\<close>. Messages show a list or option
  by its element: \<open>Decl+\<close>, \<open>Decl*\<close>, \<open>Decl?\<close> and the prelude's \<open>List1(Decl)\<close> or
  \<open>Sep1(Decl, ;)\<close> as \<open>a Decl\<close>, a group as its first symbol (\<open>(; Decl)*\<close> as \<open>';'\<close>); other
  instances, as \<open>Block(Decl)\<close>, keep their names.

  @{command grammar} \<open>Grammar_Prelude\<close> below provides the generic templates.
\<close>

grammar Grammar_Prelude =
  productions
    List(X) :: \<open>'x list\<close> = \<Rightarrow> \<open>[]\<close> | List(X) X \<Rightarrow> \<open>\<lambda>xs x. xs @ [x]\<close>
  and
    List1(X) :: \<open>'x list\<close> = X \<Rightarrow> \<open>\<lambda>x. [x]\<close> | List1(X) X \<Rightarrow> \<open>\<lambda>xs x. xs @ [x]\<close>
  and
    Opt(X) :: \<open>'x option\<close> = \<Rightarrow> \<open>None\<close> | X \<Rightarrow> \<open>Some\<close>
  and
    Sep1(X, S) :: \<open>'x list\<close> = X \<Rightarrow> \<open>\<lambda>x. [x]\<close> | Sep1(X, S) S X \<Rightarrow> \<open>\<lambda>xs x. xs @ [x]\<close>
  and
    Sep(X, S) :: \<open>'x list\<close> = \<Rightarrow> \<open>[]\<close> | Sep1(X, S)


section \<open>Parsers\<close>

text \<open>
  \begin{matharray}{rcl}
    @{command parser} & : & \<open>local_theory \<rightarrow> local_theory\<close> \\
  \end{matharray}

  \<^rail>\<open>
    @@{command parser} ('(' name ')')? (entry + @'and')
    ;
    entry: name @'for'? name ('(' name ')')? (@'recover' name)? repair?
      (@'on_error_reduce' (name +))? (@'token_info' term)? (@'errors' (message + '|'))?
    ;
    repair: @'repair' (@'token' term)? (@'avoid' (name+))?
    ;
    message: (sentence | cartouche) ('(' ('token' | 'shift') ')')? ('\<Rightarrow>' | '=>') text
    ;
    sentence: (name (@'@' nat)?)+
  \<close>

  \<^descr> \<^theory_text>\<open>parser p for G\<close> defines \<open>p :: word \<Rightarrow> \<tau>\<^sub>S option\<close> for the start
  symbol \<open>S\<close> of \<open>G\<close>, together with soundness and completeness theorems.
  The optional first name selects the parser generator (by default \<open>LR\<close>) for
  all entries of the command.

  \<^descr> \<^theory_text>\<open>parser p for G (A)\<close> parses from the nonterminal \<open>A\<close> of \<open>G\<close>
  instead: \<open>p :: word \<Rightarrow> \<tau>\<^sub>A option\<close>, built from \<open>G\<lparr>istart := ''A''\<rparr>\<close>, the
  grammar with the same productions and start \<open>A\<close>. Its theorems are those
  of the start symbol with \<open>A\<close> for \<open>S\<close>: the relational forms are about
  \<open>G_A 0 w x\<close> and the language forms about \<open>ilang (G\<lparr>istart := ''A''\<rparr>)\<close>, the
  language of \<open>A\<close>. \<^theory_text>\<open>(S)\<close> with \<open>S\<close> the start symbol is the plain
  form.

  \<^descr> \<^theory_text>\<open>parser (ast) p for G\<close> defines \<open>p :: word \<Rightarrow> ('m, 'ch, string, 'tok) ast option\<close>,
  which returns the tree of the word and evaluates no action: the decoder is \<^const>\<open>Some\<close>.
  For an outline or folding in an editor, or a grammar whose actions are not written yet
  (they are still checked by \<^theory_text>\<open>grammar\<close>). The theorems speak of the tree,
  see below; the option combines with the others, with entries and with the diagnostics,
  whose \<open>p_diag\<close> and \<open>p_recover\<close> then return trees as well.

  \<^descr> \<^theory_text>\<open>parser p for G and q for G (A)\<close> declares several parsers
  for one grammar, one after the other (parsers for another grammar need a
  command of their own). The entries share the grammar's decoders, its relation
  and the decoder and relation lemmas the theorems are discharged with, proved
  once for the command; each entry has its own tables, from its own start.

  The clauses after the start symbol, and the option \<open>(no_diagnostics)\<close>, are about
  rejected words; they are described with the diagnostics below.
\<close>


section \<open>What is defined\<close>

subsection \<open>Constants and facts of a grammar\<close>

text \<open>
  For \<^theory_text>\<open>grammar G\<close> with non-terminals \<open>A\<close> of carrier \<open>\<tau>\<^sub>A\<close> and start
  symbol \<open>S\<close>:

  \<^descr> The grammar constant \<open>G :: (string, 'tok) is_cfg\<close> with its equation \<open>G_def\<close>.
  Nonterminals are represented by their names, the start symbol has
  indentation \<open>0\<close>.

  \<^descr> One decoder \<open>G__dec_A :: ('m, 'ch, string, 'tok) ast \<Rightarrow> \<tau>\<^sub>A option\<close> per
  nonterminal, with the equations \<open>G__dec_A.simps\<close>. It evaluates the actions
  over a parse tree, matching each node against the productions of \<open>A\<close>.
  The decoders are defined together through \<^const>\<open>ast_rec\<close>.

  \<^descr> With \<open>(relation)\<close>: the \<^theory_text>\<open>inductive\<close> family
  \<open>G_A :: nat \<Rightarrow> word \<Rightarrow> \<tau>\<^sub>A \<Rightarrow> bool\<close>, where \<open>G_A i w x\<close> holds if the word
  \<open>w\<close> derives from \<open>(A, i)\<close> with value \<open>x\<close>, there is one introduction rule
  per alternative. The predicates are defined by one (mutual) inductive
  definition per strongly connected component of the nonterminals, lower
  components first. The facts are \<open>G.intros\<close>, \<open>G.inducts\<close> (the induction
  rule of each predicate, over its component) and
  \<open>G.lang: (\<exists>x. G_S 0 w x) \<longleftrightarrow> w \<in> ilang G\<close>.

  For a grammar without annotations the indentation argument is dropped:
  \<open>G_A :: word \<Rightarrow> \<tau>\<^sub>A \<Rightarrow> bool\<close> and \<open>G.lang: (\<exists>x. G_S w x) \<longleftrightarrow> w \<in> ilang G\<close>.

  A copied nonterminal \<open>a.X\<close> of a composed grammar \<open>b\<close> gets the decoder
  \<open>b__dec_a_X\<close> and, with \<open>(relation)\<close>, the predicate \<open>b_a_X\<close> like any other; a
  template defines nothing, its instances are ordinary nonterminals.
\<close>

subsection \<open>Constants of a parser\<close>

text \<open>
  The definition of \<open>p\<close> is \<open>p w = Option.bind (dparse G Shn w) G__dec_S\<close>
  (for an entry \<open>(A)\<close>, \<open>dparse (G\<lparr>istart := ''A''\<rparr>) Shn w\<close> and \<open>G__dec_A\<close>):
  \<^text>\<open>dparse\<close> is the verified driver of \<^file>\<open>../lr/LR_Driver.thy\<close>, an
  LALR(1)-style parser over the LR(0) automaton whose lookahead cells carry
  the layout constraints, \<open>Shn\<close> a
  fresh name for the augmented start symbol, and \<open>G__dec_S\<close> the decoder of
  the start symbol.

  A parser of a grammar with \<^theory_text>\<open>precedence\<close> declarations also defines \<open>p_prec\<close>
  and \<open>p_gram\<close> and is built from \<open>p_gram\<close>, see the precedence subsection above. The
  constants of the diagnostics (\<open>p_diag\<close>, \<open>p_messages\<close>, \<open>p_recover\<close>,
  \<open>p_coverage\<close> and the others) are described with them below, the tables of the code with
  the backend.
\<close>


section \<open>Theorems\<close>

text \<open>
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

  With \<open>(ast)\<close>, \<open>p.sound\<close> and \<open>p.complete\<close> are stated against the parse trees of
  \<open>G\<close>, with or without a relation:
  \begin{center}
    \<open>p.sound: p w = Some t \<Longrightarrow> ast_of G (Nt (istart G)) (istart_ind G) t w\<close> \\
    \<open>p.complete: wf_ptree G pt \<Longrightarrow> proot pt = (Nt (istart G), istart_ind G) \<Longrightarrow>
      p (pyield pt) = Some (erase pt)\<close>
  \end{center}
  that is, \<open>t\<close> is the erasure of a parse tree of \<open>w\<close>, and every parse tree of a word
  erases to the tree \<open>p\<close> returns, which is therefore unique; \<open>p.sound_lang\<close> and
  \<open>p.complete_lang\<close> are the language forms, with no premise on a decoder.
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

  For a grammar with precedence declarations the theorems are stated against
  \<open>prec_ok\<close>, and a composed grammar adds the link theorems \<open>b.a_X_iff\<close>; both
  are described with the grammar specifications above.
\<close>


section \<open>Diagnostics\<close>

text \<open>
  The parser \<open>p\<close> says only \<open>None\<close> on a rejected word. Each parser also has a
  diagnostics side, unless \<^theory_text>\<open>parser (no_diagnostics)\<close> turns it off (the
  option \<open>diagnostics\<close> states the default; \<open>p\<close> and its tables are the same either way):
  \<open>p_diag w\<close> is \<open>Inr x\<close> exactly when \<open>p w = Some x\<close>, and otherwise \<open>Inl e\<close> with
  \<open>e\<close> a record \<open>perr\<close> (\<^file>\<open>../lr/LR_Diag.thy\<close>): the index and token at which the
  word failed (\<open>None\<close> at the end of the input), the state, the kind (no action, a
  cycle of reductions, a token offside or misaligned), the expected terminals and,
  under layout, their columns, the anchor, the stack with its spans, and any
  repair. \<open>perr_message\<close> turns it into text, and the \<open>errors\<close> block overrides that
  text state by state. Two things in that text come from the grammar. A pair of terminals
  that balance in every production and of which the second ends one (\<open>brackets\<close>) is a
  bracket: when the innermost one on the stack is the error, the message says
  ``\<open>'(' at 2:24 is not closed\<close>'' and the generic text becomes a note. And a long
  \<open>expected:\<close> list is shortened to the nonterminals that may start there, by the name
  they have in the grammar (a generated list by its element, see above), so a
  nonterminal's name is part of the messages.
\<close>

text \<open>
  \<^descr> \<^theory_text>\<open>parser (diagnostics) p for G errors s \<Rightarrow> \<open>m\<close> | \<dots>\<close> attaches hand-written
  messages to the error states of \<open>p\<close>, by example (Jeffery 2003, Pottier 2016). The
  word \<open>s\<close> is written with the terminals' spellings or constructor names, each
  with an optional column after \<open>@\<close>; a token without one follows the previous token.
  For tokens with further fields, or to use a lexer, \<open>s\<close> is a cartouche with a
  term of the word type. The last token of \<open>s\<close>, or the end of \<open>s\<close>, is where it fails.

  The command evaluates \<open>p_probe\<close>, the error state of a word without its decoder
  and expected set, once on all the sentences, with no theorem, which gives the
  constant \<open>p_messages\<close>, plain data that \<open>p_render\<close> consults: the text
  replaces the primary line of the default message, \<open>$0\<close> to \<open>$9\<close> standing for the
  text of the stack entries from the top. The key is the state where the error is
  detected, with \<open>(token)\<close> that state and the offending terminal, which goes first,
  and with \<open>(shift)\<close> the state after the last shift. A word that is accepted, a key
  taken by an earlier sentence, a terminal that does not exist, and a sentence that
  cannot be evaluated are warnings, and the sentence is ignored; a word rejected
  before its last token and a hole below the stack are warnings only. Since keys
  are computed at each elaboration, a grammar edit that renumbers the states
  needs no change of the block.

  \<^descr> \<^theory_text>\<open>parser (diagnostics) p for G recover e\<close> adds \<open>p_recover\<close>, for a
  grammar where the terminal \<open>e\<close> (a spelling or a constructor) stands for broken
  input: an ordinary terminal with ordinary productions such as
  \<open>Expr = \<dots> | ERR \<Rightarrow> \<open>EErr\<close>\<close>, which builds an error node. It is checked like any
  other terminal, so a conflict it takes part in is reported, and it is left out of
  the expected sets of the reports. \<open>p_recover w\<close> is \<open>(errs, p w')\<close>: \<open>w' = w\<close> and
  \<open>errs = []\<close> when \<open>p\<close> accepts \<open>w\<close>; otherwise \<open>p_repair\<close>, which is not verified,
  gives \<open>w'\<close>, and \<open>errs\<close> are the reports at each stop, never empty, with
  \<open>pe_index\<close> into \<open>w\<close>. At a stop the stack is popped to a state that can shift
  \<open>e\<close>, the tokens are skipped up to one that continues, and the whole span becomes
  one \<open>e\<close> carrying the source span of what it replaces (Menhir's \<open>error\<close>, Bison's
  three tokens of quiet between reports); under layout it takes a column the state
  accepts. A word with no place for \<open>e\<close> gives \<open>None\<close> with its reports. The word
  \<open>w'\<close> is parsed by \<open>p\<close> itself, so \<open>p_recover\<close> costs nothing on good input and
  all the theorems of \<open>p\<close> apply to the tree. Two facts come with it:
  \<open>p_recover.clean\<close>, that no reports means the tree is the one of \<open>p w\<close>, and
  \<open>p_recover.no_error\<close>, that the tree of a word without \<open>e\<close> has no \<open>e\<close> in its
  yield. Nothing is proved about \<open>p_repair\<close>. Without \<open>diagnostics\<close>, or with a name
  that is not a terminal of \<open>G\<close>, \<open>recover\<close> is a warning and is ignored.

  \<^descr> \<^theory_text>\<open>parser (diagnostics) p for G repair\<close> adds \<open>p_recover\<close> as well, for
  any grammar: at a stop, before \<open>e\<close> if there is a \<^theory_text>\<open>recover\<close>, it
  searches for a repair sequence as in CPCT+ (Diekmann and Tratt 2020): tokens
  inserted and deleted at the least cost, then kept, ranked by how far parsing goes
  on. The repair is in \<open>pe_repair\<close> of the report and in its message. A budget of
  nodes for the whole word bounds the search, as HOL has no clock (\<open>rnodes\<close>, in
  \<^file>\<open>../lr/LR_Recover.thy\<close>), and compatible nodes are merged; past it, the search gives
  up, \<open>e\<close> is tried, and otherwise the report stands.
  An inserted terminal is a neighbour token with its terminal and an empty span. For
  tokens whose text a decoder reads, \<^theory_text>\<open>repair token f\<close> supplies them, with
  \<open>f :: 't \<Rightarrow> span \<Rightarrow> token\<close>. \<^theory_text>\<open>repair avoid A B\<close> ranks repairs that insert \<open>A\<close>
  or \<open>B\<close> lower among those that parse equally far (\<open>%avoid_insert\<close>). Under layout
  the terminal takes the column of the next token if it fits, otherwise the nearest
  that does.

  \<^descr> \<^theory_text>\<open>parser (diagnostics)\<close> also defines \<open>p_coverage\<close>, the tables and the
  driver as numbers. An \<open>errors\<close> block is checked for coverage with the method of
  Pottier (Reachability and error diagnosis in LR(1) parsers, CC 2016): every pair of a
  state and a terminal that has no action and that some word reaches, each with a
  shortest word. A pair is covered by a key \<open>PState\<close> of its state or \<open>PToken\<close> of the
  pair; \<open>(shift)\<close> keys do not count. The states left over come as a warning, with a
  skeleton of an \<open>errors\<close> block that can be pasted. \<^theory_text>\<open>parser_error_states p\<close> lists
  all pairs and the skeleton, and \<^theory_text>\<open>parser_error_states (token) p\<close> keys it by
  pair. With \<open>recover e\<close> no word contains \<open>e\<close>. Each sentence is run on the driver.

  On a grammar with columns the automaton without them gives an upper bound, and a pair
  is listed when a run reaches it, in the default layout (one token after the other)
  or in another order of the columns. Candidates no run reaches are named, and the list
  is then not known to be complete; the sentences are shortest for the automaton only.
  None of this is proved. \<open>[[parser_errors_budget = n]]\<close> bounds it to \<open>n\<close> seconds
  (default \<open>0\<close>, which turns it off; a block is still evaluated for its keys).
  A coverage pass is a deliberate step, e.g. \<open>[[parser_errors_budget = 600]]\<close>.

  \<^descr> \<open>on_error_reduce A B\<close> (Pottier, Sect. 4) changes what \<open>p_diag\<close> reports: on a
  rejected word a second run reduces a production of \<open>A\<close> or \<open>B\<close> in any state that has
  no action on the next terminal, so the error is met in the state after them, which
  is the one the keys of a block and the listing mean. The parser and its tables are
  untouched, and \<open>p_diag.Inr_iff\<close> still holds. \<open>p_repair\<close> plans on the parser's own
  tables and takes its reports from the second run. A state with two such productions
  takes the lowest one, with a warning; on the simple driver \<open>on_error_reduce\<close> is a
  warning and is ignored. The second run costs tables of its own in \<open>p_diag\<close>, built
  when an exported parser is loaded.

  \<^descr> \<open>token_info f\<close>, for tokens with further record fields: \<open>f t\<close> is the value of the
  extension (\<open>r.fields \<dots>\<close> for a record \<open>r\<close>) for a token of class \<open>t\<close>. Sentences of symbols and the runs of coverage need it;
  without it the sentences of coverage are not run, and pairs that depend on columns
  are left out with a warning.
\<close>

text \<open>
  No theorem is about the \<open>Inl\<close> side, by design: \<open>Inl _\<close> means failure, and only
  accepted trees matter. \<open>p_diag.Inr_iff\<close> is what makes this safe. Whatever the error
  code does, it decides nothing, so a report can be wrong but no word changes
  its status. Recovery is built the same way: it rewrites the word, unverified,
  and the verified \<open>p\<close> parses the result. Coverage, \<open>on_error_reduce\<close>,
  \<open>recover\<close> and \<open>repair\<close> are described above; none of them changes \<open>p\<close> or its
  tables, and all of them run only after a failure, so \<open>p\<close> costs the same.
\<close>


section \<open>Backend: the LR parser\<close>

text \<open>
  The only generator at present is \<open>LR\<close> (\<^file>\<open>lr.ML\<close>). The definition of \<open>p\<close>
  runs \<^text>\<open>dparse\<close> on the grammar; its code equations do not.

  For code generation the LR tables are constants \<open>p_states\<close>,
  \<open>p_gtab\<close>, \<open>p_redtab\<close>, \<open>p_i0\<close> and, for the driver, \<open>p_stab\<close>,
  \<open>p_vtab\<close>, \<open>p_vktab\<close>, \<open>p_sinit\<close> and \<open>p_sclos\<close> (the state-indexed tables of
  \<^file>\<open>../lr/LR_Vec.thy\<close>, the sparse closures of \<^file>\<open>../lr/LR_Sparse.thy\<close>; \<open>p_xinit\<close> and \<open>p_xclos\<close> for a grammar with an
  \<open>\<epsilon>\<close>-cycle), each defined by its term over the ones before it
  (\<open>p_gtab = la_gtab G p_states\<close>); generated code computes each once when it
  loads. The code equation of \<open>p\<close> refers to those constants, so neither
  \<^theory_text>\<open>eval\<close> nor exported code rebuilds the automaton per call. With
  \<^theory_text>\<open>declare [[parser_literal_tables]]\<close> the six constants are instead
  the evaluated tables, for exported code that must not compute them at startup;
  the command then evaluates the tables as well as its checks, including, for
  the state-indexed driver, \<open>p_stab\<close>, \<open>p_vtab\<close>, \<open>p_vktab\<close>, \<open>p_sinit\<close> and
  \<open>p_sclos\<close>. If the grammar
  has no layout annotations, the static determinism check is empty and no
  lookahead cell of a reduce constrains the width of its token, the code
  equation instead runs the
  simple driver of \<^file>\<open>../lr/LR_Simple.thy\<close>, using the precise LR(0)
  automaton as well (tables \<open>p_psts\<close>, \<open>p_pgt\<close>, \<open>p_pcomps\<close>, \<open>p_pfins\<close>,
  \<open>p_p0\<close>). It keeps a stack of state indices and computes no closures at run
  time; \<^text>\<open>dparse_eq_sparse\<close> proves that it computes the same result as
  \<^text>\<open>dparse\<close>. Its code equation runs on indexed tables, computed from
  \<open>p_ltabs\<close>: productions and nonterminals are numbered, goto rows are keyed
  by terminal or by nonterminal number, and the reduces licensed at a state
  are tabulated by lookahead (\<^text>\<open>isctl_eq\<close>). These tables are then stored
  as binary tries keyed by the bits of the index (\<^file>\<open>../lr/LR_Trie.thy\<close>,
  \<^text>\<open>jctl_eq\<close>): they are static data, and with binary naturals a lookup
  involves no arithmetic, once the code equations \<^text>\<open>tlookup_binary\<close> are
  declared next to \<^verbatim>\<open>Code_Binary_Nat\<close>. The input word is numbered once,
  pairing each token with its number in the tables (\<^file>\<open>../lr/LR_Tok.thy\<close>,
  \<^text>\<open>xrun_jctl2\<close>). Finally, the reachable pairs of states of the two
  automata are numbered, \<open>p_kpairs\<close>, and the tables of the code, \<open>p_ktabs\<close>,
  are those of this product automaton, with one number per stack entry and
  the candidate reduces tabulated by lookahead (\<^file>\<open>../lr/LR_Prod.thy\<close>,
  \<^text>\<open>xrun_kctl\<close>); the closure of \<open>p_kpairs\<close> under shifts and gotos is
  checked by evaluation (\<^text>\<open>kok\<close>). If the check fails, the code runs on
  the tries \<open>p_jtabs\<close>. On the product automaton the run detects loops of
  reductions by comparing with one saved stack instead of all stacks since the
  last shift (\<^file>\<open>../lr/LR_Loop.thy\<close>, \<^text>\<open>xrun_hist_brun\<close>), and a
  step looks up one action table, \<open>p_ptabs\<close>, by pair number and
  lookahead: the shift target, or else the reduces with their productions
  (\<^file>\<open>../lr/LR_Plain.thy\<close>, \<^text>\<open>pctl_eq\<close>). If the token type is a
  datatype whose constructors have no arguments, the number of a token is
  computed by a case distinction, \<open>p_tnum\<close>, instead of a search in the list
  of terminals; \<open>pnum p_ptabs = p_tnum\<close> is proved constructor by
  constructor. With
  \<^theory_text>\<open>declare [[parser_int_tables]]\<close> the tables are instead arrays with
  integer indices, \<open>p_ztabs\<close>, computed when the code is loaded
  (\<^file>\<open>../lr/LR_Int.thy\<close>, \<^text>\<open>zrun_eq\<close>). For OCaml,
  \<^file>\<open>../lr/LR_Simple.thy\<close> implements immutable arrays (\<^verbatim>\<open>iarray\<close>) by
  OCaml arrays.
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
      Prog :: \<open>nat\<close> = Block
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
  the token record and ignores it. \<open>Block\<close> without annotation leaves the column of the outermost
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

  Further examples can be found in \<^file>\<open>../tests/Regression_Tests.thy\<close>.
\<close>

end
