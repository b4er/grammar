(* Author: Basil Fürer *)

theory Lexer_Check
  imports Lexer_Command
  keywords "lexer_check" :: thy_decl and "lex" :: diag
begin

section \<open>Edit-time tools: a test command and a lexing diagnostic\<close>

text \<open>\<^theory_text>\<open>lexer_check \<open>t\<^sub>1\<close> \<dots> \<open>t\<^sub>n\<close>\<close> (also separated by \<^theory_text>\<open>and\<close>) evaluates
  each closed boolean term \<open>t\<^sub>i\<close> in the ML compiler, as \<open>by eval\<close> would, and fails at
  the first that is not \<open>True\<close>. For an equation it shows the value of the left-hand
  side. It proves nothing: it replaces \<^theory_text>\<open>lemma \<dots> by eval\<close> where the lemma is not
  used afterwards.

  The first check that mentions a constant compiles the constant's whole program into an
  ML structure of the theory and registers its datatypes for the evaluation target, as
  \<^theory_text>\<open>code_reflect\<close> does. A check takes the compiled constants out of its term as
  arguments, generates code only for what is left, and applies it to the compiled values.
  So the table literals of a lexer are compiled once per theory chain, not once per check.
  A constant with sort constraints is not compiled (its code takes dictionaries). The
  command is the test command \<open>parser_check\<close> of the LR parser generator \<open>grammar\<close>
  (\<open>tests/parser_check.ML\<close>), renamed.

  \<^theory_text>\<open>lex L_lex \<open>text\<close>\<close> lexes the text with a lexer of @{command lexer} (on
  codepoints, or on the UTF-8 bytes of the text for a lexer on bytes) and prints a line per
  token: its kind, line and column (from 0), lexeme and trailing trivia. Then it prints the
  residue and the final stack, with whether its top is final in \<open>L\<close>. Each lexeme of the
  text shows its kind on hover. A lexer compiled by an earlier @{command lexer_check} is
  not compiled again.\<close>

text \<open>What \<^theory_text>\<open>lex\<close> prints of a result: the length of the leading trivia, per token
  its kind, line, column, offset, length and length of trivia, the length of the residue,
  the final stack and whether its top satisfies \<open>fin\<close>:\<close>

definition lex_summary ::
  \<open>('k, 'ch) lexed \<times> 'ch list \<times> 'm list \<Rightarrow> ('m \<Rightarrow> bool) \<Rightarrow>
    nat \<times> ('k \<times> nat \<times> nat \<times> nat \<times> nat \<times> nat) list \<times> nat \<times> 'm list \<times> bool\<close>
where
  \<open>lex_summary x fin = (case x of (l, r, st) \<Rightarrow>
    (length (header l),
     map (\<lambda>t. (tok t, s_line (span t), s_col (span t), s_off (span t), s_len (span t),
       length (trivia t))) (toks l),
     length r, st, st \<noteq> [] \<and> fin (hd st)))\<close>

ML_file \<open>lexer_check.ML\<close>

end
