theory Parser_Check
  imports Main
  keywords "parser_check" :: thy_decl
begin

section \<open>A test command: evaluation with cached code\<close>

text \<open>\<^theory_text>\<open>parser_check \<open>t\<^sub>1\<close> \<dots> \<open>t\<^sub>n\<close>\<close> (also separated by \<^theory_text>\<open>and\<close>) evaluates
  each closed boolean term \<open>t\<^sub>i\<close> in the ML compiler, as \<open>by eval\<close> would, and fails
  at the first that is not \<open>True\<close>; for an equation it shows the value of the
  left-hand side. It proves nothing: it replaces \<^theory_text>\<open>lemma \<dots> by eval\<close> where the
  lemma is not used afterwards.

  The first check that mentions a constant compiles the constant's whole program
  into an ML structure of the theory and registers its datatypes for the
  evaluation target, as \<^theory_text>\<open>code_reflect\<close> does. A check takes the compiled
  constants out of its term as arguments, generates code only for what is left,
  and applies it to the compiled values. So the tables of a parser are computed
  once per theory chain, not once per check, and the code preprocessor sees only
  the small term. A constant with sort constraints is not compiled (its code
  takes dictionaries) and costs what it costs under \<open>by eval\<close>.\<close>

ML_file \<open>parser_check.ML\<close>

end
