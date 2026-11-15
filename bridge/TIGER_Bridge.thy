(* Author: Basil Fürer *)

theory TIGER_Bridge
  imports TIGER_Grammar.LR_Prec_Parse TIGER_Lexer.Lexer_Check
begin

section \<open>Lexers as terminal providers\<close>

text \<open>From here on each @{command lexer} \<open>L\<close> is a terminal provider of the grammar
  command: \<^theory_text>\<open>grammar G = tokens of L\<close> takes the type of the tokens
  that \<open>L_lex\<close> produces, and the token of each fixed spelling from the literal rules
  \<open>"s" \<Rightarrow> t\<close> of \<open>L\<close> (without guard, whose action is a token; the first rule of a
  spelling counts). Neither the grammar nor the lexer session imports the other; the
  hook that the lexer command runs is empty until this theory adds the registration.\<close>

setup \<open>
  Lexer_Command.add_hook (fn {name, tokenT, spellings} =>
    Terminal_Provider.register name {tokenT = tokenT, spellings = spellings})
\<close>

end
