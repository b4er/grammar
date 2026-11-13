(* Author: Basil Fürer *)

theory TIGER_Pattern
  imports TIGER_Lexer.TIGER_Codepoints
  keywords "pattern" :: diag
begin

section \<open>Patterns\<close>

text \<open>A pattern is the text of a cartouche in a regex syntax after flex and ocamllex
  \<^cite>\<open>\<open>Sect.~6\<close> in "paxson2026-flex-manual"\<close> \<^cite>\<open>\<open>Sect.~17.2.4\<close> in "leroy2026-ocaml-manual"\<close>. It elaborates to a codepoint class
  (\<^typ>\<open>nat cls\<close>) or a regex over classes (\<^typ>\<open>nat cls rexp\<close>). A class in
  brackets is a literal interval list in sorted normal form, and the class operators
  become \<^const>\<open>cp_disj\<close>, \<^const>\<open>cp_conj\<close> and \<^const>\<open>cp_neg\<close>. A class used as
  a regex is wrapped in \<^const>\<open>Pred\<close>.

  The elaborator infers the kind of every pattern (there is one namespace for classes
  and regexes, as in ocamllex \<^cite>\<open>\<open>Sect.~17.2.2\<close> in "leroy2026-ocaml-manual"\<close>). Union, difference \<open>#\<close> and complement \<open>[^\<dots>]\<close> of classes
  are classes, everything else is a regex. A character is a codepoint: an ASCII or
  UTF-8 symbol, or a named symbol such as \<open>\<alpha>\<close> read through the \<open>code\<close> column of
  Isabelle's symbol table.

  The command @{command pattern} prints the elaboration of a pattern, optionally in an
  environment of definitions after \<open>where\<close>. A term \<open>PAT\<open>\<dots>\<close>\<close> is the elaboration of
  a pattern whose names are constants of these types.\<close>

ML_file \<open>pattern.ML\<close>

syntax "_lexer_pattern" :: \<open>cartouche_position \<Rightarrow> 'a\<close>  (\<open>PAT_\<close>)

parse_translation \<open>[(\<^syntax_const>\<open>_lexer_pattern\<close>, Pattern.pattern_tr)]\<close>

end
