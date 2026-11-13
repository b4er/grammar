(* Author: Basil Fürer *)

theory TIGER_Rules
  imports TIGER_Lexer.TIGER_Spec
begin

section \<open>Rule actions from mode operations\<close>

text \<open>Rule actions built from three parts: the token kind of the lexeme, a guard on the
  lexeme and an effect on the mode stack. The
  effects are flex's: keep the stack, replace the top (\<open>BEGIN\<close>), push or pop
  \<^cite>\<open>\<open>Sect.~10\<close> in "paxson2026-flex-manual"\<close>, or any function on the stack.

  A hook of type \<^typ>\<open>'k option \<Rightarrow> 'm \<Rightarrow> 'm\<close> computes the new top from the kind of
  the lexeme when the rule names no mode. It is lex's user flag
  \<^cite>\<open>\<open>Sect.~10\<close> in "lesk1975-lex"\<close> made pure: a flag set in every action is a
  function of the token.\<close>

datatype 'm effect = Keep | Begin 'm | Push 'm | Pop | Stack \<open>'m list \<Rightarrow> 'm list\<close>

fun apply_effect ::
  \<open>('k option \<Rightarrow> 'm \<Rightarrow> 'm) \<Rightarrow> 'm effect \<Rightarrow> 'k option \<Rightarrow> 'm list \<Rightarrow> 'm list\<close>
where
  apply_effect_Keep: \<open>apply_effect h Keep k (m # st) = h k m # st\<close>
| apply_effect_Begin: \<open>apply_effect h (Begin m') k (m # st) = m' # st\<close>
| apply_effect_Push: \<open>apply_effect h (Push m') k st = m' # st\<close>
| apply_effect_Pop: \<open>apply_effect h Pop k (m # m' # st) = h k m' # st\<close>
| apply_effect_Stack: \<open>apply_effect h (Stack f) k st = f st\<close>
| apply_effect_Pop_last: \<open>apply_effect h Pop k [m] = []\<close>
| apply_effect_Nil: \<open>apply_effect h e k [] = []\<close>

text \<open>The stack after an effect. The hook gives the top after \<^const>\<open>Keep\<close> and
  \<^const>\<open>Pop\<close>, a named mode is taken as it is. A pop of the last mode is the empty
  stack, which the driver rejects (flex aborts on an empty start condition stack \<^cite>\<open>\<open>Sect.~10\<close> in "paxson2026-flex-manual"\<close>).\<close>

definition mk_act ::
  \<open>('k option \<Rightarrow> 'm \<Rightarrow> 'm) \<Rightarrow> ('ch list \<Rightarrow> 'k option) \<Rightarrow> ('ch list \<Rightarrow> bool) \<Rightarrow>
    'm effect \<Rightarrow> 'ch list \<Rightarrow> 'm list \<Rightarrow> 'k option \<times> 'm list\<close>
where
  \<open>mk_act h kind guard e u st =
    (if guard u then (kind u, apply_effect h e (kind u) st) else (None, []))\<close>

text \<open>The action of a rule with kind \<open>kind\<close>, guard \<open>guard\<close> and effect \<open>e\<close>. A lexeme that
  fails the guard gives the empty stack, so the driver stops there. The guard cannot fall
  back to another rule, as flex's \<open>yyreject()\<close> (formerly \<open>REJECT\<close>) does
  \<^cite>\<open>\<open>Sect.~8\<close> in "paxson2026-flex-manual"\<close>. A failed guard plays the part of a
  Verbatim++ semantic action that returns \<open>None\<close> on an ill-formed lexeme
  \<^cite>\<open>\<open>Sect.~6\<close> in "egolf2022-verbatim-plus-plus"\<close>. Both fail safely, but Verbatim++ then
  rejects the whole input, while here lexing stops at the lexeme and leaves a residue.\<close>

end
