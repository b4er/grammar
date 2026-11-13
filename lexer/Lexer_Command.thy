(* Author: Basil Fürer, Claude *)

theory Lexer_Command
  imports TIGER_Pattern TIGER_Rules
  keywords "lexer" :: thy_decl
    and "modes" "start" "exclusive" "final" "after" "newline" "rules"
    and "skip" "error" "push" "pop" "\<Rightarrow>"
begin

section \<open>The lexer command\<close>

text \<open>The command @{command lexer} defines a lexer spec from a flex-like source
  \<^cite>\<open>"paxson2026-flex-manual"\<close>: the token type, the modes, named classes and regexes
  after \<open>where\<close> (lex's definitions \<^cite>\<open>\<open>Sect.~6\<close> in "lesk1975-lex"\<close>) and the rules.
  The spec is not evaluated. Each entry \<open>c\<close> of \<open>where\<close> becomes a constant \<open>L.c\<close>, and a
  template \<open>c(x, \<dots>)\<close> is substituted where it is used.

  The modes are names, which become a datatype \<open>L_mode\<close>, or a datatype whose values the
  command enumerates. A rule is active in the modes its tags match (HOL patterns over the
  mode type, \<open>_\<close> for any part) or, untagged, in every mode that is not exclusive (flex's
  \<open>%x\<close> \<^cite>\<open>\<open>Sect.~10\<close> in "paxson2026-flex-manual"\<close>). A scope \<open><p> (r | \<dots>)\<close> tags each rule in it. Each mode has its active rules in
  the order of the source, so priority is the file order (flex \<^cite>\<open>\<open>Sect.~7\<close> in
  "paxson2026-flex-manual"\<close>). We write a scope with parentheses where flex has braces
  (\<open>{\<close> starts a proof block in Isar).

  An action is \<open>skip\<close> (trivia), \<open>error\<close>, a token, a function from the lexeme to a token,
  or a complete action of the type of \<^const>\<open>act\<close>. A guard \<open>when P\<close> and a mode
  operation \<open>begin m\<close>, \<open>push m\<close>, \<open>pop\<close> or a stack function follow. The command builds
  the action with \<^const>\<open>mk_act\<close>, whose hook is the function of \<open>after\<close> (the identity
  by default).

  The command defines \<open>L.spec\<close> by cases on the mode, with the equations \<open>L.spec.simps\<close>,
  the start mode \<open>L.start\<close>, the final modes \<open>L.final\<close> (by default those that are not
  exclusive) and \<open>L.is_newline\<close> from the class of \<open>newline\<close> (by default \<open>[\n]\<close>).

  The command also builds the lexer \<open>L_lex\<close> of the spec. It evaluates the tables of
  \<open>L\<close> once per distinct rule list into constants \<open>L_lex.tables_k\<close>, whose code
  equations \<open>L_lex.tables_k_code\<close> are the evaluated tables, so modes with the same
  active rules share them. \<open>L_lex.tables\<close> is the array of these tables and
  \<open>L_lex.index\<close> maps each mode to its entry. \<open>L_lex\<close> is \<^const>\<open>cp_lexer\<close> on
  them from the stack of \<open>L.start\<close> and the first position. \<open>L_lex.ok\<close> holds of an
  input that \<open>L_lex\<close> consumes up to a final mode, and \<open>L_lex.correct\<close> is
  @{thm [source] cp_lexer_iff_lexes_in_range} for \<open>L.spec\<close> (from
  \<open>L_lex.index_tables\<close>, which says that the index of each mode holds its tables).
  The option \<open>(sketch)\<close> stops after the spec.

  The command reports each table with the modes that share it, its sizes and the time of
  its evaluation, and the time of all tables. It warns at a rule that wins in no state of
  the tables of a mode, naming the modes. Such a rule cannot be matched there (flex's
  warning of that name \<^cite>\<open>\<open>Sect.~23\<close> in "paxson2026-flex-manual"\<close>), as a rule of higher priority matches each of its lexemes. The
  option \<open>(no_check)\<close> drops the warning.

  The option \<open>(char)\<close> builds the lexer on bytes, \<^const>\<open>char_lexer\<close> on the tables
  of \<^const>\<open>char_spec\<close> \<open>L.spec\<close>, with \<open>L_lex.correct\<close> from
  @{thm [source] char_lexer_iff_lexes}. A class of \<open>L\<close> that reaches above \<open>0xFF\<close> is
  an error there (the byte instance of JFlex's \<open>%8bit\<close> \<^cite>\<open>\<open>``Input Character sets\<close> in "klein2023-jflex-manual"\<close>), unless it reaches the end of the
  codepoints: such a class is a complement such as \<open>_\<close> or \<open>[^\<dots>]\<close>, and on bytes it is
  its part below \<open>0x100\<close>.\<close>

ML_file \<open>lexer_command.ML\<close>
ML_file \<open>lexer_tables.ML\<close>
ML_file \<open>lexer_syntax.ML\<close>

end
