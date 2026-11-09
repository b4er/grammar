theory Lexer_Command
  imports Pattern Rules
  keywords "lexer" :: thy_decl and "\<Rightarrow>"
begin

section \<open>The lexer command\<close>

text \<open>The command @{command lexer} defines a lexer spec from a flex-like source
  \<^cite>\<open>"paxson2026-flex-manual"\<close>: the token type, the modes, named classes and regexes
  after \<open>where\<close> (lex's definitions \<^cite>\<open>\<open>Sect. 12\<close> in "lesk1975-lex"\<close>) and the rules.
  Nothing is evaluated. Each entry \<open>c\<close> of \<open>where\<close> becomes a constant \<open>L.c\<close>, and a
  template \<open>c(x, \<dots>)\<close> is substituted where it is used.

  The modes are names, which become a datatype \<open>L_mode\<close>, or a datatype whose values the
  command enumerates. A rule is active in the modes its tags match (HOL patterns over the
  mode type, \<open>_\<close> for any part) or, untagged, in every mode that is not exclusive (flex's
  \<open>%x\<close>). A scope \<open><p> (r | \<dots>)\<close> tags each rule in it. Each mode has its active rules in
  the order of the source, so priority is the file order (flex \<^cite>\<open>\<open>Sect. 8\<close> in
  "paxson2026-flex-manual"\<close>). We write a scope with parentheses where flex has braces
  (\<open>{\<close> starts a proof block in Isar).

  An action is \<open>skip\<close> (trivia), \<open>error\<close>, a token, a function from the lexeme to a token,
  or a complete action of the type of \<^const>\<open>act\<close>. A guard \<open>when P\<close> and a mode
  operation \<open>begin m\<close>, \<open>push m\<close>, \<open>pop\<close> or a stack function follow. The command builds
  the action with \<^const>\<open>mk_act\<close>, whose hook is the function of \<open>after\<close> (the identity
  by default).

  The command defines \<open>L.spec\<close> by cases on the mode, with the equations \<open>L.spec.simps\<close>,
  the start mode \<open>L.start\<close>, the final modes \<open>L.final\<close> (by default those that are not
  exclusive) and \<open>L.is_newline\<close> from the class of \<open>newline\<close> (by default \<open>[\n]\<close>).\<close>

ML_file \<open>lexer_command.ML\<close>
ML_file \<open>lexer_syntax.ML\<close>

end
