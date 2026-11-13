(* Author: Basil Fürer *)

theory TIGER
  imports TIGER_Grammar.LR_Prec_Parse TIGER_Lexer.Lexer_Check
begin

section \<open>Overview\<close>

text \<open>
  TIGER (Tokenization, Indentation-sensitive Grammars and Executable Recognizers)
  provides Isabelle/HOL commands that turn a specification of syntax into
  executable recognizers. They work like the lexer and parser generators
  \<^verbatim>\<open>flex\<close> \<^cite>\<open>"paxson2026-flex-manual"\<close>, ocamlyacc
  \<^cite>\<open>"leroy2026-ocaml-manual"\<close> and Menhir \<^cite>\<open>"pottier2026-menhir-manual"\<close>.
  Unlike Isabelle's mixfix annotations
  \<^cite>\<open>\<open>Sect.~9.2\<close> in "wenzel2026-isabelle-isar-reference"\<close>
  or \<^verbatim>\<open>Isabelle_Lex-Yacc\<close> \<^cite>\<open>"brucker2026-isabelle-lex-yacc"\<close> they also prove that what they generate meets the
  specification: a lexing judgment after Verbatim
  \<^cite>\<open>"egolf2021-verbatim-verified-lexer"\<close>, and a grammar with layout constraints
  after Adams \<^cite>\<open>"adams2013"\<close>.

  The TIGER entry provides three main commands:

  \<^item> @{command lexer} (Section~\ref{sec:lexer}) defines a lexer specification with
  modes and rules, its lexing judgment, and an executable lexer on DFA tables that
  computes the judgment.

  \<^item> @{command grammar} (Section~\ref{sec:grammar}) defines a grammar with semantic
  actions, decoders from parse trees to values and, on request, an inductive relation
  between words and values.

  \<^item> @{command parser} (Section~\ref{sec:parser}) emits an executable LR parser for grammars, proven sound for
  the particular grammar. Completeness is proven by evaluation when it has no LALR conflicts.
\<close>

section \<open>Lexers\label{sec:lexer}\<close>

text \<open>
  A lexer specification gives each \<^emph>\<open>mode\<close> a list of \<^emph>\<open>rules\<close>, each a regular
  expression with an action. Lexing follows flex \<^cite>\<open>"paxson2026-flex-manual"\<close>: in
  the mode on top of a stack of modes, the longest prefix of the input that a rule
  matches is the next lexeme, and of the rules that match it the first one wins. Its
  action gives the token class of the lexeme (or \<^term>\<open>None\<close> for trivia such as blanks and
  comments), and the new stack. Trivia go with the token before them, so the source is
  the concatenation of its tokens and trivia, and each token carries its span: line,
  column, offset, length and text.

  This meaning is an inductive judgment over the specification, not a program
  (Section~\ref{sec:lexer-defined}), and the command proves that the lexer it generates
  computes it. The lexer runs on DFA tables, one per mode. Their states are sets of
  partial derivatives of the rules' regular expressions, each tagged with its rule: the
  subset construction over partial derivatives
  \<^cite>\<open>\<open>Prop.~4.3\<close> in "antimirov1996-partial-derivatives"\<close> rather than the
  derivative automata of \<^cite>\<open>"brzozowski1964-derivatives-regular-expressions" and
    "owens2009-regex-derivatives-reexamined"\<close>. The expressions are kept
  symbolic \<^cite>\<open>"keil2014-symbolic-regex-inequalities"\<close>: their atoms are classes of
  characters, intervals of codepoints, not single characters, and a transition goes by a
  minterm of the atoms \<^cite>\<open>\<open>Sect.~4, Fig.~2\<close> in "dantoni2014-minimization-symbolic-automata"\<close>.
\<close>

subsection \<open>Specifications\<close>

text \<open>
  The categories \<open>name\<close>, \<open>string\<close>, \<open>type\<close>, \<open>term\<close> and \<open>cartouche\<close> in the
  syntax diagrams are those of the Isar reference manual
  \<^cite>\<open>\<open>Sects.~4.2--4.3\<close> in "wenzel2026-isabelle-isar-reference"\<close>.

  \<^rail>\<open>
    @@{command lexer} ('(' (option + ',') ')')? name '::' type \<newline>
      (clause *) definitions? rules
  \<close>

  \<^descr> \descform{\<^theory_text>\<open>lexer L :: \<open>\<tau>\<close> \<dots>\<close>} defines the lexer \<open>L\<close> with token
  classes of type \<open>\<tau>\<close>. Each clause is given at most once.
\<close>

text \<open>
  \<^rail>\<open>
    option: 'sketch' | 'codepoints' | 'char' | 'no_check'
  \<close>

  \<^descr> \descform{\<^verbatim>\<open>sketch\<close>} stops after the specification: generates no tables
  and no lexer. The other options are ignored.

  \<^descr> \descform{\<^verbatim>\<open>codepoints\<close>} (default) builds a lexer on codepoints,
  natural numbers: \<^const>\<open>cp_lexer\<close> on the tables of \<open>L.spec\<close>.

  \<^descr> \descform{\<^verbatim>\<open>char\<close>} builds a lexer on bytes, of type \<^typ>\<open>char\<close>:
  \<^const>\<open>char_lexer\<close> on the tables of \<^const>\<open>char_spec\<close> \<open>L.spec\<close>, where a class
  means its part below \<open>0x100\<close>. A class that reaches above \<open>0xFF\<close> is then an error,
  unless it reaches the last codepoint: \<^verbatim>\<open>_\<close> and \<open>[^\<dots>]\<close> mean the remaining
  bytes.

  \<^descr> \descform{\<^verbatim>\<open>no_check\<close>} drops the warning at rules that can never match
  (Section~\ref{sec:lexer-defined}).
\<close>

text \<open>
  \<^rail>\<open>
    clause: @'modes' (cartouche | (name +)) | (@'start' | @'after') term |
      (@'exclusive' | @'final') (term +) | @'newline' name
  \<close>

  \<^descr> \descform{\<^theory_text>\<open>modes A B \<dots>\<close>} names the modes, which become a datatype
  \<open>L_mode\<close>; \<^theory_text>\<open>modes \<open>\<mu>\<close>\<close> takes an existing datatype \<open>\<mu>\<close>, whose values the
  command enumerates. Without the clause there is one mode, of type \<^typ>\<open>unit\<close>.

  \<^descr> \descform{\<^theory_text>\<open>start m\<close>} is the start mode, by default the first.

  \<^descr> \descform{\<^theory_text>\<open>exclusive m\<^sub>1 \<dots> m\<^sub>n\<close>} lists modes in which only the rules
  tagged for them are active (flex's \<open>%x\<close> \<^cite>\<open>\<open>Sect.~10\<close> in "paxson2026-flex-manual"\<close>).

  \<^descr> \descform{\<^theory_text>\<open>final m\<^sub>1 \<dots> m\<^sub>n\<close>} lists the modes in which the input may end,
  by default those that are not exclusive: an input that ends in a comment mode is an
  unterminated comment.

  \<^descr> \descform{\<^theory_text>\<open>after h\<close>} is a hook \<open>h :: \<tau> option \<Rightarrow> \<mu> \<Rightarrow> \<mu>\<close> that computes
  the new top of the stack from the token class of a lexeme, when its rule names no
  mode (by default the identity). It is lex's user flag
  \<^cite>\<open>\<open>Sect.~10\<close> in "lesk1975-lex"\<close> made pure: a flag set in every action is a
  function of the token.

  \<^descr> \descform{\<^theory_text>\<open>newline c\<close>} names the class of characters that end a line,
  by default \<open>[\n]\<close>.
\<close>

text \<open>
  \<^rail>\<open>
    definitions: @'where' (definition + '|')
    ;
    definition: name ('(' (name + ',') ')')? '=' cartouche
  \<close>

  \<^descr> \descform{\<^theory_text>\<open>where c = \<open>p\<close> | \<dots>\<close>} names patterns (lex's definitions
  \<^cite>\<open>\<open>Sect.~6\<close> in "lesk1975-lex"\<close>); each becomes a constant \<open>L.c\<close>. A
  definition with parameters is a template, for example \<open>p+\<close> may be redefined
  as \<open>many(p) = \<open>p p*\<close>\<close>. Templates are substituted where they are used.
\<close>

text \<open>
  \<^rail>\<open>
    rules: @'rules' (item + '|')
    ;
    item: tag? (rule | '(' (item + '|') ')')
    ;
    tag: '<' (term + ',') '>'
  \<close>

  \<^descr> \descform{\<^theory_text>\<open>rules r\<^sub>1 | \<dots> | r\<^sub>n\<close>} lists the rules. Each mode has its
  active rules in the order of the source, so priority is the order of the file.
  A rule is active in the modes its tag matches, or, without a tag, in every mode
  that is not exclusive. The terms of a tag are HOL patterns over the mode type,
  with \<^verbatim>\<open>_\<close> for any part. A scope \<open><p> (r\<^sub>1 | \<dots> | r\<^sub>n)\<close> tags each rule in it; it is
  written with parentheses where flex has braces, as \<open>{\<close> opens a proof block in Isar.
\<close>

text \<open>
  \<^rail>\<open>
    rule: pattern '\<Rightarrow>' action (@'when' term)? (',' mode_op)?
    ;
    pattern: cartouche | string
  \<close>

  \<^descr> \descform{\<^theory_text>\<open>p \<Rightarrow> a when P, m\<close>} lexes a match of the pattern \<open>p\<close>
  with the action \<open>a\<close> and then applies the mode operation \<open>m\<close>. The pattern is a
  cartouche in the syntax of Section~\ref{sec:patterns}, or a string for the literal
  text. The guard \<^theory_text>\<open>when P\<close> makes a lexeme \<open>u\<close> with \<open>\<not> P u\<close> an error.
  \<open>\<Rightarrow>\<close> may be written \<^verbatim>\<open>=>\<close>.
\<close>

text \<open>
  \<^rail>\<open>
    action: @'skip' | @'error' | term
  \<close>

  \<^descr> \descform{\<^theory_text>\<open>skip\<close> | \<^theory_text>\<open>error\<close> | \<open>t\<close>} is
  \<^theory_text>\<open>skip\<close> for trivia, \<^theory_text>\<open>error\<close> to stop, or a term: a token class, a
  function from the lexeme to a token class, or a complete action of type
  \<^typ>\<open>'ch list \<Rightarrow> 'm list \<Rightarrow> 'k option \<times> 'm list\<close>.
\<close>

text \<open>
  \<^rail>\<open>
    mode_op: @'begin' term | @'push' term | @'pop' | cartouche
  \<close>

  \<^descr> \descform{\<^theory_text>\<open>begin m\<close> | \<^theory_text>\<open>push m\<close> | \<^theory_text>\<open>pop\<close> | \<open>\<open>f\<close>\<close>} change
  the stack as flex does \<^cite>\<open>\<open>Sect.~10\<close> in "paxson2026-flex-manual"\<close>:
  \<^theory_text>\<open>begin m\<close> replaces the top, \<^theory_text>\<open>push m\<close> pushes \<open>m\<close>,
  \<^theory_text>\<open>pop\<close> pops, and a cartouche is a function on the stack. Without a mode
  operation the stack stays as it is, up to the hook. A pop of the last mode is the
  empty stack, where lexing stops (flex aborts there).
\<close>

subsection \<open>Patterns\label{sec:patterns}\<close>

text \<open>
  A pattern elaborates to a class of codepoints, of type \<^typ>\<open>nat cls\<close>, or a regular
  expression over classes, of type \<^typ>\<open>nat cls rexp\<close>. Its syntax follows flex \<^cite>\<open>\<open>Sect.~6\<close> in "paxson2026-flex-manual"\<close> and
  ocamllex \<^cite>\<open>\<open>Sect.~17.2.4\<close> in "leroy2026-ocaml-manual"\<close>, with the usual precedence: postfix operators bind tightest, then
  concatenation, then the difference \<open>#\<close>, then the union \<open>|\<close>.

  \<^descr> \<open>"text"\<close> is the literal text, with the escapes \<open>\n\<close>, \<open>\t\<close>, \<open>\r\<close>, \<open>\\\<close>,
  \<open>\"\<close> and \<open>\u{h}\<close> for the codepoint with hexadecimal number \<open>h\<close>.

  \<^descr> \<open>[a-z\<alpha>-\<omega>0-9]\<close> is a class of characters and ranges, a dash at
  either end for itself, and a backslash before any character for that character. As
  in flex, a blank in a class is a member: \<open>[a-z A-Z]\<close> holds the space, an escaped
  blank is an error, and a newline is written \<open>\n\<close>.
  \<open>[^\<dots>]\<close> is its complement, and \<^verbatim>\<open>_\<close> is any codepoint.

  \<^descr> A character is a codepoint: an ASCII or UTF-8 character, or a named symbol such
  as \<open>\<alpha>\<close>, read through the \<open>code\<close> column of Isabelle's symbol table.

  \<^descr> \<open>p*\<close>, \<open>p+\<close> and \<open>p?\<close> repeat, \<open>p q\<close> concatenates, \<open>p | q\<close> is the union, \<open>p # q\<close>
  the difference of two classes, and \<open>(p)\<close> groups.

  \<^descr> A name refers to a definition of the specification, \<open>name(p\<^sub>1, \<dots>, p\<^sub>n)\<close> instantiates a
  template, and any other name is a HOL constant of one of the two types.
\<close>

text \<open>
  Classes and regular expressions share one namespace, and the elaborator infers the
  kind of each pattern: a union, difference or complement of classes is a class,
  everything else a regular expression.

  \<^theory_text>\<open>pattern \<open>p\<close> where \<dots>\<close> prints the elaboration of a pattern and its kind,
  in an optional environment of definitions. In a term, \<open>PAT\<open>p\<close>\<close> is the elaboration
  of the pattern \<open>p\<close>, whose names are HOL constants: \<^term>\<open>PAT\<open>[a-z]+ | "_"\<close>\<close>.
\<close>

subsection \<open>What is defined\label{sec:lexer-defined}\<close>

text \<open>
  Lexing is defined once, for every alphabet, in the locale \<^locale>\<open>symbolic\<close>. It
  fixes nothing but the reading \<open>sem :: 'p \<Rightarrow> 'ch \<Rightarrow> bool\<close> of the atoms: \<^term>\<open>Pred p\<close>
  matches the characters \<open>c\<close> with \<open>sem p c\<close>, and \<^const>\<open>symbolic.lang\<close> is the
  language of a regular expression over atoms. There is no type class on \<open>'ch\<close> and no
  finite alphabet, so codepoints and bytes are instances, not assumptions.

  A specification \<open>sp\<close> gives each mode its list of rules. One step of lexing follows
  the judgments \<open>MaxPref\<close> and \<open>FirstToken\<close> of Verbatim
  \<^cite>\<open>\<open>Figs.~3--4\<close> in "egolf2021-verbatim-verified-lexer"\<close>: the lexeme is the
  longest nonempty prefix of the input that a rule of the mode on top of the stack
  matches, and the winning rule is the first that matches it. Its action, which Verbatim
  does not have, gives the token class and the new stack.

  The judgment \<open>lexes sp is_newline st q s l r st\<^sub>f\<close> chains steps from the stack \<open>st\<close> and
  the position \<open>q\<close>, and relates the input \<open>s\<close> to its tokens with their spans and trivia
  \<open>l\<close>, the residue \<open>r\<close> where no step applies, and the stack \<open>st\<^sub>f\<close> it stops in. A lexical
  error is not a failure but a nonempty residue, and an unterminated comment is an empty
  residue in a mode that is not final. Each step consumes a nonempty lexeme, so whatever
  the actions do to the stack, lexing ends:
  @{thm [display, margin = 80] symbolic.lexes_total [no_vars]}
  and with @{thm [source] symbolic.lexes_deterministic} the judgment is a function.
  Totality is the argument Verbatim gives for the termination of its lexer, whose
  recursive calls are on proper suffixes of the input
  \<^cite>\<open>\<open>Sect.~IV\<close> in "egolf2021-verbatim-verified-lexer"\<close>. Determinism is its
  Uniqueness lemma \<^cite>\<open>\<open>Sect.~V-B\<close> in "egolf2021-verbatim-verified-lexer"\<close>, here
  for a judgment that also carries the stack.

  The command takes the codepoints, natural numbers, as the alphabet, and classes of
  type \<^typ>\<open>nat cls\<close>, read by \<^const>\<open>in_cls\<close>, as the atoms. For a lexer \<open>L\<close> it
  defines:

  \<^descr> The specification \<open>L.spec :: \<mu> \<Rightarrow> \<dots> rule list\<close>, by cases on the mode \<open>\<mu>\<close>, with
  the equations \<open>L.spec.simps\<close>. A rule pairs a regular expression \<^const>\<open>match\<close>
  with an action \<^const>\<open>act\<close>, built by \<^const>\<open>mk_act\<close> from the token class, the
  guard, the effect on the stack and the hook. The constants \<open>L.c\<close> of the definitions,
  the start mode \<open>L.start\<close>, the final modes \<open>L.final\<close> and the line ends
  \<open>L.is_newline\<close> come with it.

  \<^descr> The lexer \<open>L_lex\<close>, which runs \<^const>\<open>cp_lexer\<close> on the DFA tables of
  \<open>L.spec\<close> from the stack \<open>[L.start]\<close> and the first position \<open>q\<^sub>0\<close>. The command
  evaluates the tables once for each distinct list of active rules, as constants
  \<open>L_lex.tables_k\<close> whose code equations are the evaluated tables, so modes with the
  same rules share them; \<open>L_lex.index\<close> maps each mode to its tables. The code
  equations are proved by evaluation, and only the generated code depends on them. \<open>L_lex.ok w\<close>
  holds if \<open>L_lex\<close> consumes all of \<open>w\<close> and stops in a final mode.

  \<^descr> \<open>L_lex.correct\<close>: on an input of codepoints, \<open>L_lex\<close> computes the judgment,
  @{text [display] \<open>(\<forall>c \<in> set w. c \<le> 0x10FFFF) \<Longrightarrow>
  L_lex w = (l, r, st\<^sub>f) \<longleftrightarrow>
    symbolic.lexes in_cls L.spec L.is_newline [L.start] q\<^sub>0 w l r st\<^sub>f\<close>}
  the instance of @{thm [source] cp_lexer_iff_lexes_in_range} for \<open>L.spec\<close>. With the
  option \<open>(\<^verbatim>\<open>char\<close>)\<close> it is @{thm [source] char_lexer_iff_lexes}, the judgment of
  \<^const>\<open>char_spec\<close> \<open>L.spec\<close> on bytes, with no condition on the input.
\<close>

text \<open>
  The command reports each table with its modes, its size and the time of its
  evaluation. It warns at a rule that wins in no state of a mode's tables, as
  rules of higher priority match all its lexemes; \<open>(\<^verbatim>\<open>no_check\<close>)\<close> drops the warning.
\<close>

subsection \<open>Example\<close>

text \<open>
  Words and numbers, with nested comments in an exclusive mode:

  @{theory_text [display, indent = 2]
\<open>datatype ctok = Word | Num

lexer cmt :: \<open>ctok\<close>
  modes Code Comment
  exclusive Comment
  where letter = \<open>[a-z]\<close>
  rules
    \<open>letter+\<close> \<Rightarrow> Word
  | \<open>[0-9]+\<close> \<Rightarrow> Num
  | \<open>[ \n]+\<close> \<Rightarrow> skip
  | "(*" \<Rightarrow> skip, push Comment
  | <Comment> (
      "(*" \<Rightarrow> skip, push Comment
    | "*)" \<Rightarrow> skip, pop
    | \<open>[^*(]+ | [*(]\<close> \<Rightarrow> skip
  )\<close>}

  The comment rules are active only in \<open>Comment\<close>, and the stack counts the depth of
  nesting. \<open>cmt.final\<close> holds of \<open>Code\<close> only, so a text that ends inside a comment is
  not \<open>cmt_lex.ok\<close>.

  A hook tells a negation from a subtraction by the token before it:

  @{theory_text [display, indent = 2]
\<open>datatype otok = Id | Minus | Neg | LParen | RParen
datatype omode = Start | AfterOperand

fun after_tok :: \<open>otok option \<Rightarrow> omode \<Rightarrow> omode\<close> where
  \<open>after_tok (Some Id) _ = AfterOperand\<close>
| \<open>after_tok (Some RParen) _ = AfterOperand\<close>
| \<open>after_tok _ _ = Start\<close>

lexer ops :: \<open>otok\<close>
  modes \<open>omode\<close>
  after after_tok
  rules
    \<open>[a-z]+\<close> \<Rightarrow> Id | "(" \<Rightarrow> LParen | ")" \<Rightarrow> RParen | \<open>[ ]+\<close> \<Rightarrow> skip
  | <Start> "-" \<Rightarrow> Neg
  | <AfterOperand> "-" \<Rightarrow> Minus\<close>}

  Both examples can be found in \<^file>\<open>lexer/tests/Lexer_Command_Tests.thy\<close>.
\<close>

section \<open>Grammars and parsers\label{sec:grammar}\<close>

text \<open>
  A grammar is a value of type \<^typ>\<open>('n, 'tok) is_cfg\<close>: a list of productions over
  nonterminals \<open>'n\<close> and token classes \<open>'tok\<close> with a start symbol, in which every
  symbol on a right-hand side carries an indentation relation \<^typ>\<open>irel\<close>
  (\<^file>\<open>grammar/model/Indentation_Sensitive.thy\<close>, after Adams
  \<^cite>\<open>"adams2013"\<close>). Its language \<^term>\<open>ilang G\<close> is a set of token words, lists of
  records \<^typ>\<open>('tok, 'ch, 'm) token_scheme\<close>, of which a parser reads the class
  \<^const>\<open>tok\<close> and the column \<^const>\<open>s_col\<close> of the \<^const>\<open>span\<close>; the other fields
  and any extension \<open>'m\<close> of the record pass through to the semantic actions. A
  grammar may use the nonterminals of an earlier one and parametric nonterminals such as
  \<open>Sep1(X, S)\<close>, with the postfix operators \<open>* + ?\<close> for lists and options; both are
  expanded before anything is defined, so the result is an ordinary closed grammar.

  This meaning is a set of derivations, not a program
  (Section~\ref{sec:grammar-defined}), and the command proves the parser it generates
  sound for it. The parser runs the LR automaton of the grammar under one token of
  lookahead with layout constraints in its lookahead. This static check of the tables
  is evaluated when the parser is defined and its result is used to discharge the
  determinism premise for completeness. Thus parsers for LALR(1) grammars are
  automatically proven correct.
\<close>

subsection \<open>Specifications\<close>

text \<open>
  \<^rail>\<open>
    @@{command grammar} ('(' 'relation' ')')? name '=' \<newline>
      (@'open' (name +))? (@'tokens' type)? \<newline>
      terminals? (prec_decl *) \<newline>
      productions
  \<close>

  \<^descr> \descform{\<^theory_text>\<open>grammar G = \<dots>\<close>} checks the specification and defines the
  grammar constant \<open>G\<close>; \<^theory_text>\<open>grammar (relation) G = \<dots>\<close> also defines the
  relation. The first nonterminal is the start symbol. \<^theory_text>\<open>open a\<^sub>1 \<dots> a\<^sub>n\<close> lets
  the productions refer to the nonterminals of earlier grammars without qualifier
  (Section~\ref{sec:composition}), and the declarations \<open>prec_decl\<close> restrict the
  trees of an ambiguous grammar (Section~\ref{sec:precedence}).

  \<^descr> \descform{\<^theory_text>\<open>tokens T\<close>} fixes the token type. \<open>T\<close> is a ground instance
  of \<^typ>\<open>('tok, 'ch, 'm) token_scheme\<close>: the plain record \<^typ>\<open>('tok, 'ch) token\<close>,
  or an extension \<^theory_text>\<open>record my_token = \<open>(my_tok, char) token\<close> + \<dots>\<close>. Another
  type \<open>T\<close> abbreviates \<open>(T, unit) token\<close>, and without the clause the token classes
  are strings.
\<close>

text \<open>
  \<^rail>\<open>
    terminals: @'terminals' ((string '=' term | name) + @'and')
  \<close>

  \<^descr> \descform{\<^theory_text>\<open>terminals "s" = t and c \<dots>\<close>} declares the terminals. A
  \<^emph>\<open>fixed spelling\<close> \<open>"s" = t\<close> lets \<open>"s"\<close> stand for the token class \<open>t\<close> in the
  productions, and binds no value. A bare name \<open>c\<close> declares a \<^emph>\<open>token class\<close>,
  written by its name in the productions, whose value is the whole token record. A name
  used in a production that is neither a nonterminal nor declared is read as a term of
  the token class type.
\<close>

text \<open>
  \<^rail>\<open>
    productions: @'productions' (production + @'and')
    ;
    production: name ('(' (name + ',') ')')? ('::' type)? '=' \<newline>
    (alternative + '|')
  \<close>

  \<^descr> \descform{\<^theory_text>\<open>A :: \<open>\<tau>\<close> = alt\<^sub>1 | \<dots> | alt\<^sub>n\<close>} declares the nonterminal
  \<open>A\<close> with \<^emph>\<open>carrier\<close> \<open>\<tau>\<close>, the type of its values. The ascription can be omitted
  when the actions determine it. A production with parameters is a template
  (Section~\ref{sec:templates}).
\<close>

text \<open>
  \<^rail>\<open>
    alternative: (symbol *) mark? ('\<Rightarrow>' term)?
    ;
    mark: '(' 'prec' (string | name) ')'
  \<close>

  \<^descr> \descform{\<^theory_text>\<open>X\<^sub>1 \<dots> X\<^sub>k (prec q) \<Rightarrow> f\<close>} is an alternative: a sequence of
  symbols, an optional mark and an optional action. The action \<open>f\<close> computes the value
  of the alternative from the values of its symbols, in order:
  \<open>f :: \<tau>\<^sub>1 \<Rightarrow> \<dots> \<Rightarrow> \<tau>\<^sub>k \<Rightarrow> \<tau>\<^sub>A\<close>. An alternative without action has exactly one
  symbol with a value, which it passes on; one without symbols needs an action. The
  mark gives the alternative a precedence level (Section~\ref{sec:precedence}).
  \<open>\<Rightarrow>\<close> may be written \<^verbatim>\<open>=>\<close>.
\<close>

text \<open>
  \<^rail>\<open>
    symbol: item ('\<^sup>=' | '\<^sup>\<ge>' | '\<^sup>>')? | @'@span'
    ;
    item: (atom | '(' (symbol +) ')') (('*' | '+' | '?') *)
    ;
    atom: string | cartouche | name ('.' name | '(' (item + ',') ')')?
  \<close>

  \<^descr> \descform{\<open>X\<close>, \<open>X\<^sup>=\<close>, \<open>X\<^sup>\<ge>\<close>, \<open>X\<^sup>>\<close>} is a symbol \<open>X\<close> with its
  annotation. \<open>X\<close> is a nonterminal, a
  fixed spelling, a token class, an inline token class \<open>\<open>t\<close>\<close>, a nonterminal \<open>a.X\<close>
  of an earlier grammar \<open>a\<close> (Section~\ref{sec:composition}), an instance of a template,
  or a group with an operator. A nonterminal contributes its value, a token class the
  token record. The annotation of a symbol is its indentation relation: \<open>\<^sup>=\<close> for
  \<^const>\<open>Eq\<close>, \<open>\<^sup>\<ge>\<close> for \<^const>\<open>Ge\<close> and \<open>\<^sup>>\<close> for \<^const>\<open>Gt\<close>, written
  \<^verbatim>\<open>^=\<close>, \<^verbatim>\<open>^>=\<close> and \<^verbatim>\<open>^>\<close> in ASCII; without annotation it is
  \<^const>\<open>Any\<close>. This departs from the convention of
  \<^cite>\<open>\<open>Sect.~3.4\<close> in "adams2013"\<close>, where an unannotated nonterminal defaults to \<open>=\<close>
  and an unannotated terminal to \<open>>\<close>.

  \<^descr> \descform{\<^theory_text>\<open>@span\<close>} is not a grammar symbol but a value of type
  \<^typ>\<open>'ch span\<close> among those of the symbols, where it is written: the span of the
  alternative's yield, from the line, column and offset of its first token to the end
  of its last, with their concatenated texts (\<^const>\<open>word_span\<close>). It needs a symbol
  that derives no empty word, is written once per alternative, takes no annotation and
  stands at the top level of the alternative.
\<close>

subsection \<open>Precedence\label{sec:precedence}\<close>

text \<open>
  \<^rail>\<open>
    prec_decl: @'precedence' levels | @'forbid' forbid
    ;
    levels: (level + '>')
    ;
    level: ('left' | 'right' | 'nonassoc' | 'open' | 'list') ((prec '!'?) +)
    ;
    forbid: prec '@' nat ('direct' | 'left' | 'right') (prec +)
    ;
    prec: string | name
  \<close>

  \<^theory_text>\<open>precedence right "^" > left "*" "/" > left "+" "-" > nonassoc "=="\<close>
  declares levels, \<open>>\<close> binding tighter. A production has the level of its mark
  \<^theory_text>\<open>(prec NAME)\<close>, else that of its last terminal, written as its spelling or
  its name; the name of a level need not be a terminal, as in
  \<^theory_text>\<open>"-" E (prec UMINUS)\<close>. This is the convention of yacc's \<open>%left\<close> and
  \<open>%prec\<close> in ocamlyacc \<^cite>\<open>"leroy2026-ocaml-manual"\<close> and Menhir
  \<^cite>\<open>"pottier2026-menhir-manual"\<close>. Several declarations merge: a name in two of them is
  one level, the order is their transitive closure, and a cycle is an error, as for the
  priority chains of \<^cite>\<open>\<open>Sect.~3.3, Def.~2\<close> in "afroozeh2013-operator-precedence"\<close>. Two
  levels that no declaration orders stay ambiguous, and the parser reports the conflict.

  \<open>left\<close>, \<open>right\<close> and \<open>nonassoc\<close> have the usual readings. \<open>open\<close> leaves the left
  operand of its productions unconstrained, for forms that end in an open construct,
  and \<open>list\<close> does not order the productions of the level against each other, for
  flat chains. A prefix form is allowed on the right of a tighter operator, as in
  \<open>a * - b\<close>; \<open>!\<close> on a name forbids that. \<open>left\<close> and \<open>right\<close> are the
  associativity relations of \<^cite>\<open>\<open>Def.~4\<close> in "afroozeh2013-operator-precedence"\<close>, and the
  levels become patterns after \<^cite>\<open>\<open>Tables~1--2\<close> in "afroozeh2013-operator-precedence"\<close>;
  \<open>open\<close>, \<open>list\<close> and \<open>!\<close> are not in the paper. \<^theory_text>\<open>forbid p @ k right c\<close> says what no
  level says: \<open>c\<close> is not on the right spine of child \<open>k\<close> of \<open>p\<close> (\<open>left\<close>: the left
  spine, \<open>direct\<close>: the child itself). \<open>direct\<close> is a pattern
  \<^cite>\<open>\<open>Def.~5\<close> in "afroozeh2013-operator-precedence"\<close>; the spine forms exclude
  operators at any depth, which one-level patterns cannot
  \<^cite>\<open>\<open>Sect.~2.2, Fig.~2\<close> in "afroozeh2013-operator-precedence"\<close>.

  These declarations restrict the trees, not the grammar: they are a filter on the parse
  trees of \<open>G\<close> \<^cite>\<open>\<open>Defs.~4.1, 4.8\<close> in "klint1994-disambiguation-filters"\<close>, given
  as a tree automaton \<^cite>\<open>\<open>Sects.~1, 3.1\<close> in "adams2017-tree-automata"\<close>. A parser of \<open>G\<close> is built from
  \<open>p_gram = restricted G p_prec\<close>, and its theorems are stated against \<open>G\<close> and the
  trees that satisfy \<open>prec_ok\<close>, or against the language \<open>prec_lang\<close>. Such a theory
  imports \<^verbatim>\<open>TIGER_Grammar.LR_Prec_Parse\<close>. The relation of
  \<^theory_text>\<open>grammar (relation)\<close> does not read the declarations, so no theorem is
  stated against it.
\<close>

subsection \<open>Composition\label{sec:composition}\<close>

text \<open>
  A symbol \<open>a.X\<close>, with \<open>a\<close> an earlier grammar and \<open>X\<close> one of its nonterminals, uses
  \<open>X\<close> in another grammar \<open>b\<close>. The productions of \<open>a\<close> reachable from \<open>X\<close> are copied
  into \<open>b\<close>, renaming each nonterminal \<open>Y\<close> of \<open>a\<close> to \<open>a.Y\<close>; a copy \<open>c.Z\<close> that \<open>a\<close>
  made itself keeps its name, so it is copied once however it is reached.

  \<open>b\<close> is then a closed grammar, and \<open>a.X\<close> one of its nonterminals. In the names of
  constants and facts the dot is replaced with an underscore, for example
  \<open>b__dec_a_X\<close>, or \<open>b_a_X\<close>.

  If \<open>a\<close> and \<open>b\<close> both have a relation, \<open>b.a_X_iff: b_a_X i w x \<longleftrightarrow> a_X i w x\<close> links them,
  so what a parser of \<open>b\<close> proves about \<open>a.X\<close> is a fact about \<open>a\<close>.

  \<^theory_text>\<open>grammar b = open a\<close> lets \<open>b\<close> write \<open>X\<close> for \<open>a.X\<close>: a bare name that is not a
  nonterminal, terminal or template parameter of \<open>b\<close> itself is \<open>a.X\<close> if \<open>a\<close> defines \<open>X\<close>.
\<close>

subsection \<open>Templates and operators\label{sec:templates}\<close>

text \<open>
  A production with parameters, \<open>P(X\<^sub>1, \<dots>, X\<^sub>n) :: \<tau> = \<dots>\<close>, is a \<^emph>\<open>template\<close> and
  defines nothing by itself. A use \<open>P(a\<^sub>1, \<dots>, a\<^sub>n)\<close>, with the parenthesis directly
  after the name, is an \<^emph>\<open>instance\<close>: the production with each \<open>X\<^sub>i\<close> replaced by
  \<open>a\<^sub>i\<close>, an ordinary nonterminal made once for each distinct list of arguments. An
  argument is a symbol, a symbol with an operator or a group of symbols. The actions of
  the template see the right-hand side after the replacement, so a parameter bound to
  a fixed spelling binds no value, and the type variables of the carrier are inferred
  per instance. A template of an earlier grammar \<open>g\<close> is used as \<open>g.P(\<dots>)\<close>, or as
  \<open>P(\<dots>)\<close> if no other template has that name.
\<close>

subsection \<open>Parsers\label{sec:parser}\<close>

text \<open>
  \<^rail>\<open>
    @@{command parser} ('(' (option + ',') ')')? (entry + @'and')
    ;
    entry: name @'for' name ('(' name ')')? error_clauses
  \<close>

  \<^descr> \descform{\<^theory_text>\<open>parser p for G\<close>} defines \<open>p :: word \<Rightarrow> \<tau>\<^sub>S option\<close> for the start
  symbol \<open>S\<close> of \<open>G\<close>, with soundness and completeness theorems
  (Section~\ref{sec:grammar-defined}).

  \<^descr> \descform{\<^theory_text>\<open>parser p for G (A)\<close>} parses from the nonterminal \<open>A\<close> instead:
  \<open>p :: word \<Rightarrow> \<tau>\<^sub>A option\<close>, for the grammar \<open>G\<lparr>istart := ''A''\<rparr>\<close> with the same
  productions and the start \<open>A\<close>. Its theorems are those of the start symbol with
  \<open>A\<close> for \<open>S\<close>.

  \<^descr> \descform{\<^theory_text>\<open>parser p for G and q for G (A)\<close>} defines several parsers for one
  grammar. They share its decoders, its relation and the lemmas their theorems are
  proved with; each has its own tables. The clauses \<open>error_clauses\<close> are about
  rejected words (Section~\ref{sec:diagnostics}).
\<close>

text \<open>
  \<^rail>\<open>
    option: 'ast' | 'diagnostics' | 'no_diagnostics' | name
  \<close>

  \<^descr> \descform{\<^verbatim>\<open>ast\<close>} defines \<open>p :: word \<Rightarrow> (\<dots>) ast option\<close>, which
  returns the raw parse tree and evaluates no semantic action.

  \<^descr> \descform{\<^verbatim>\<open>diagnostics\<close> | \<^verbatim>\<open>no_diagnostics\<close>} turns the
  report of a rejected word, \<open>p_diag\<close>, on (default) or off
  (Section~\ref{sec:diagnostics}).

  \<^descr> \descform{\<open>name\<close>} selects the parser generator, by default the
  most recently declared one (i.e. \<open>LR\<close>).
\<close>

subsection \<open>What is defined\label{sec:grammar-defined}\<close>

text \<open>
  The language of a grammar is defined by derivations in which every symbol has an
  indentation. The indentation of a terminal is the column of its token. A nonterminal
  has no token of its own; its indentation is free up to the annotations. Expanding a
  nonterminal at indentation \<open>i\<close> by a production \<open>A = X\<^sub>1\<^sup>r\<^sup>1 \<dots> X\<^sub>n\<^sup>r\<^sup>n\<close> chooses for
  each symbol an indentation \<open>j\<^sub>k\<close> with \<open>irel_sat r\<^sub>k j\<^sub>k i\<close>:
  \begin{center}
  @{thm [mode = iff] irel_sat.simps(1) [no_vars]} \qquad
  @{thm [mode = iff] irel_sat.simps(2) [no_vars]} \\
  @{thm [mode = iff] irel_sat.simps(3) [no_vars]} \qquad
  @{thm [mode = iff] irel_sat.simps(4) [no_vars]}
  \end{center}
  So \<open>\<^sup>=\<close> aligns a symbol with the nonterminal being expanded, \<open>\<^sup>>\<close> indents it
  further, \<open>\<^sup>\<ge>\<close> allows both, and no annotation places no constraint. A block of aligned
  statements is \<open>Block = Stmt\<^sup>= | Block\<^sup>= Stmt\<^sup>=\<close>. A grammar without annotations is an
  ordinary context-free grammar, and \<^term>\<open>ilang G\<close> is the set of words derived in this
  way from the start symbol at indentation \<open>0\<close>. This is the rewrite relation of
  Adams \<^cite>\<open>\<open>Sect.~4\<close> in "adams2013"\<close>, with his four relations
  \<open>=\<close>, \<open>>\<close>, \<open>\<ge>\<close> and \<open>\<star>\<close>, the last written as no annotation.
\<close>

text \<open>
  For \<^theory_text>\<open>grammar G\<close> with nonterminals \<open>A\<close> of carrier \<open>\<tau>\<^sub>A\<close> and start
  symbol \<open>S\<close> the command defines:

  \<^descr> The grammar \<open>G :: (string, 'tok) is_cfg\<close> with its definition \<open>G_def\<close>. The
  nonterminals are represented by their names.

  \<^descr> A decoder \<open>G__dec_A :: (\<dots>) ast \<Rightarrow> \<tau>\<^sub>A option\<close> for each nonterminal, with the
  equations \<open>G__dec_A.simps\<close>, which evaluates the actions over a parse tree.

  \<^descr> With \<open>(relation)\<close>, an inductive predicate \<open>G_A :: nat \<Rightarrow> word \<Rightarrow> \<tau>\<^sub>A \<Rightarrow> bool\<close>
  for each nonterminal, with one introduction rule per alternative: \<open>G_A i w x\<close> holds
  if \<open>w\<close> derives from \<open>A\<close> at indentation \<open>i\<close> with the value \<open>x\<close>. The facts are
  \<open>G.intros\<close>, \<open>G.inducts\<close> and \<open>G.lang: (\<exists>x. G_S 0 w x) \<longleftrightarrow> w \<in> ilang G\<close>. For a
  grammar without annotations the indentation argument is dropped.
\<close>

text \<open>
  For \<^theory_text>\<open>parser p for G\<close> it defines:

  \<^descr> The parser \<open>p w = Option.bind (dparse G Shn w) G__dec_S\<close>, where \<open>dparse\<close> is
  the verified driver of \<^file>\<open>grammar/lr/LR_Driver.thy\<close> and \<open>Shn\<close> a fresh start symbol.
  The code equation of \<open>p\<close> runs on tables that are computed once, when the code is
  loaded, by a faster driver proved equal to \<open>dparse\<close>; for a grammar without
  annotations this is a table-driven LR driver on a stack of state numbers. With
  \<^theory_text>\<open>declare [[parser_literal_tables]]\<close> the tables are evaluated when the
  parser is defined instead.

  \<^descr> \<open>p.sound\<close> and \<open>p.complete\<close> relate the parser to the language:
  \begin{center}
    \<open>p.sound: p w = Some x \<Longrightarrow> w \<in> ilang G\<close> \\
    \<open>p.complete: w \<in> ilang G \<Longrightarrow> \<exists>x. p w = Some x\<close>
  \end{center}
  For a grammar with a relation, to the relation of the start symbol:
  \begin{center}
    \<open>p.sound: p w = Some x \<Longrightarrow> G_S 0 w x\<close> \\
    \<open>p.complete: G_S 0 w x \<Longrightarrow> p w = Some x\<close>
  \end{center}
  and the language forms are \<open>p.sound_lang\<close> and \<open>p.complete_lang\<close>. With \<open>(ast)\<close>
  they are about the parse trees of \<open>G\<close>:
  \begin{center}
    \<open>p.sound: p w = Some t \<Longrightarrow> ast_of G (Nt (istart G)) (istart_ind G) t w\<close> \\
    \<open>p.complete: wf_ptree G pt \<Longrightarrow> proot pt = (Nt (istart G), istart_ind G) \<Longrightarrow>
      p (pyield pt) = Some (erase pt)\<close>
  \end{center}
  that is, \<open>t\<close> is (the erasure of) a parse tree of \<open>w\<close>, and every parse tree of a
  word is the one \<open>p\<close> returns, which is therefore unique.
\<close>

text \<open>
  Soundness holds outright. Completeness needs the determinism of the driver on the
  grammar, \<open>mdet G Shn\<close>, and the totality of the decoders. For determinism the
  command evaluates \<open>rlalr_conflicts G Shn\<close>, the LALR(1) conflict analysis extended with
  the layout constraints. If there are no conflicts, \<open>mdet\<close> follows; otherwise the
  command lists the conflicting states and keeps \<open>mdet\<close> as a premise of
  \<open>p.complete\<close>. The check is sufficient but not necessary: an ambiguous grammar
  always fails it, a deterministic one may fail it too. The parser is defined either
  way, and \<^theory_text>\<open>thm p.complete\<close> shows what has been established.

  The checks are proved by evaluation (\<open>Code_Runtime.dynamic_holds_conv\<close>), so an
  unconditional \<open>p.complete\<close> trusts the code generator; \<open>p.sound\<close> does not
  depend on evaluation. The code equation of \<open>p\<close> does: the checks that let the
  faster driver stand for \<open>dparse\<close> are evaluated too. Jourdan, Pottier and Leroy
  also check their automaton by computation, running their validator with Coq's
  virtual machine \<^cite>\<open>\<open>Sect.~5\<close> in "jourdan2012-validating-lr1"\<close>.
\<close>

subsection \<open>Diagnostics and recovery\label{sec:diagnostics}\<close>

text \<open>
  \<open>p\<close> says only \<open>None\<close> on a rejected word. Unless \<^theory_text>\<open>parser (no_diagnostics)\<close>
  turns it off, each parser also defines \<open>p_diag\<close>, with \<open>p_diag w = Inr x\<close> exactly
  when \<open>p w = Some x\<close> (\<open>p_diag.Inr_iff\<close>) and otherwise \<open>Inl e\<close>, a report: the token
  where the word failed, the expected terminals with their columns, the stack with its
  spans and any repair. \<open>perr_message\<close> renders it. A bracket that is not closed is
  named as such, and a long list of expected terminals is shortened to the
  nonterminals that may start there.

  No theorem is about the \<open>Inl\<close> side, by design: a report can be wrong, but no word
  changes its status. Recovery is built the same way. It rewrites the word, unverified,
  and the verified \<open>p\<close> parses the result, so all its theorems apply to the tree. None
  of this changes \<open>p\<close> or its tables, and all of it runs only after a failure.
\<close>

text \<open>
  \<^rail>\<open>
    error_clauses: (@'recover' name)? repair? \<newline>
      (@'on_error_reduce' (name +))? (@'token_info' term)? \<newline>
      (@'errors' (message + '|'))?
  \<close>

  \<^descr> \descform{\<^theory_text>\<open>recover e\<close>} adds \<open>p_recover\<close> for a grammar in which the terminal \<open>e\<close>
  stands for broken input, with ordinary productions such as \<open>Expr = \<dots> | ERR \<Rightarrow> EErr\<close>.
  \<open>p_recover w = (errs, p w')\<close>: where \<open>w\<close> fails, the stack is popped to a state that
  can shift \<open>e\<close>, tokens are skipped up to one that continues, and the stretch becomes
  one \<open>e\<close>, as with the \<open>error\<close> token of ocamlyacc
  \<^cite>\<open>\<open>Sect.~17.4.4\<close> in "leroy2026-ocaml-manual"\<close>, which skips to three tokens
  that continue.

  \<^descr> \descform{\<^theory_text>\<open>on_error_reduce A B\<close>} lets the report of a rejected word come after
  reducing productions of \<open>A\<close> or \<open>B\<close> \<^cite>\<open>\<open>Sect.~4\<close> in "pottier2016-lr1-reachability"\<close>, so it names the
  construct that was complete.

  \<^descr> \descform{\<^theory_text>\<open>token_info f\<close>} gives the record extension for a token
  class, for the sentences of \<^theory_text>\<open>errors\<close> with extended token records.
\<close>

text \<open>
  \<^rail>\<open>
    repair: @'repair' ('token' term)? ('avoid' (name +))?
  \<close>

  \<^descr> \descform{\<^theory_text>\<open>repair\<close>} adds \<open>p_recover\<close> for any grammar: at an error it searches for
  a least-cost sequence of inserted and deleted tokens, ranked by how far parsing goes
  on, as in CPCT+ \<^cite>\<open>"diekmann2020-dont-panic"\<close>. A budget of search nodes bounds it.
  \<^theory_text>\<open>repair token f\<close> supplies inserted tokens whose text an action reads, and
  \<^theory_text>\<open>repair avoid A B\<close> ranks repairs that insert \<open>A\<close> or \<open>B\<close> lower.
\<close>

text \<open>
  \<^rail>\<open>
    message: (sentence | cartouche) ('(' ('token' | 'shift') ')')? '\<Rightarrow>' text
    ;
    sentence: ((name ('@' nat)?) +)
  \<close>

  \<^descr> \descform{\<^theory_text>\<open>errors s \<Rightarrow> \<open>m\<close> | \<dots>\<close>} attaches messages to error states by example
  \<^cite>\<open>"jeffery2003-lr-error-messages" and "pottier2016-lr1-reachability"\<close>. The sentence \<open>s\<close> is written with the spellings or
  names of terminals, each with an optional column after \<open>@\<close>, or as a cartouche with a
  term of the word type. It fails at its last token, or at its end. The message
  replaces the first line of the report of every word that fails in the same state, or
  with \<open>(token)\<close> in the same state at the same terminal; \<open>$0\<close> to \<open>$9\<close> stand for the
  text of the stack entries from the top. The keys are computed from the sentences,
  so an edit of the grammar that renumbers the states needs no change of the block.
\<close>

subsection \<open>Example\<close>

text \<open>
  A statement is an identifier or a \<open>while\<close> header followed by a block indented
  further than the header, the statements of a block aligned. The value is the number
  of statements:

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

  \<open>Id\<close> is a token class, so the first action of \<open>Stmt\<close> takes its token record and
  ignores it. \<open>Block\<close> without annotation leaves the column of the outermost block free,
  \<open>Block\<^sup>>\<close> after a header demands a deeper one, and \<open>Block\<^sup>= Stmt\<^sup>=\<close> aligns the
  members. The introduction rules of \<open>py_Stmt\<close>, writing \<open>\<langle>t; sp\<rangle>\<close> for the token
  \<open>\<lparr>tok = t, span = sp\<rparr>\<close>, are
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
  The grammar has no conflicts, so completeness is unconditional:
  \begin{center}
  \<open>py_parse.complete: py_Prog 0 w x \<Longrightarrow> py_parse w = Some x\<close>
  \end{center}
  With \<open>tu c t\<close> a token of class \<open>t\<close> at column \<open>c\<close>:

  @{theory_text [display, indent = 2]
\<open>lemma \<open>py_parse [tu 1 While, tu 7 Id, tu 8 Colon, tu 3 Id, tu 3 Id, tu 1 Id] = Some 4\<close>
  by eval

lemma \<open>py_parse [tu 1 While, tu 7 Id, tu 8 Colon, tu 3 Id, tu 4 Id] = None\<close>
  by eval\<close>}

  More examples are in \<^file>\<open>grammar/tests/Regression_Tests.thy\<close>.
\<close>

(* Citations in the theories that this document does not make, as \<^cite> forms to paste
   into a text block.

  LR construction:
    the state sets \<^cite>\<open>\<open>Sect.~II, step 3\<close> in "knuth1965-lr-translation"\<close>,
    the LR(k) condition \<^cite>\<open>\<open>Sect.~I\<close> in "knuth1965-lr-translation"\<close>;
    the LR(0) automaton \<^cite>\<open>\<open>Sect.~2.2\<close> in "deremer1982-lalr-lookahead"\<close>,
    per-item lookahead \<^cite>\<open>\<open>Sect.~3\<close> in "deremer1982-lalr-lookahead"\<close>,
    the NQLALR pitfall \<^cite>\<open>\<open>Sect.~5.1\<close> in "deremer1982-lalr-lookahead"\<close>;
    the worklist \<open>visit\<close> \<^cite>\<open>\<open>Sect.~5.3, Def.~5.5.4\<close> in "barthwal2010-thesis-cfl-hol4"\<close>,
    conflict freedom on reachable states \<^cite>\<open>\<open>Def.~5.3.7, Thm.~5.4.4\<close> in "barthwal2010-thesis-cfl-hol4"\<close>;
    the completeness validator \<^cite>\<open>\<open>Sect.~3.3, Thm.~3\<close> in "jourdan2012-validating-lr1"\<close>,
    unambiguity \<^cite>\<open>\<open>Thm.~4\<close> in "jourdan2012-validating-lr1"\<close>.

  Regexes and lexer tables:
    partial derivatives \<^cite>\<open>\<open>Def.~2.8, Prop.~2.10\<close> in "antimirov1996-partial-derivatives"\<close>,
    finitely many \<^cite>\<open>\<open>Thm.~3.4\<close> in "antimirov1996-partial-derivatives"\<close>;
    effective Boolean algebras \<^cite>\<open>\<open>Sect.~2\<close> in "dantoni2014-minimization-symbolic-automata"\<close>,
    minterms \<^cite>\<open>\<open>Sect.~4, Fig.~2\<close> in "dantoni2014-minimization-symbolic-automata"\<close>,
    a transition by a minterm \<^cite>\<open>\<open>Prop.~1\<close> in "dantoni2014-minimization-symbolic-automata"\<close>;
    character classes of a regex \<^cite>\<open>\<open>Thm.~4.2\<close> in "owens2009-regex-derivatives-reexamined"\<close>;
    backing up to the last accepting position \<^cite>\<open>\<open>Sect.~2, Fig.~1(a)\<close> in "reps1998-maximal-munch-linear"\<close>,
    the quadratic example \<^cite>\<open>\<open>Sect.~1\<close> in "reps1998-maximal-munch-linear"\<close>,
    linear-time tokenization \<^cite>\<open>\<open>Sect.~3\<close> in "reps1998-maximal-munch-linear"\<close>;
    JFlex's \<open>%8bit\<close> \<^cite>\<open>\<open>``Input Character sets''\<close> in "klein2023-jflex-manual"\<close>;
    Unicode scalar values \<^cite>\<open>\<open>Sect.~3.9, D76\<close> in "unicode2025-standard"\<close>.
*)

end
