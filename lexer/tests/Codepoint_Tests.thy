(* Author: Basil Fürer, Claude *)

theory Codepoint_Tests
  imports TIGER_Lexer.TIGER_Codepoints
begin

section \<open>Tests of the codepoint instance\<close>

text \<open>Identifiers over ASCII and Greek letters: a lower
  case letter starts a value identifier, an upper case letter a constructor, and both
  continue with letters, digits, \<open>_\<close> and \<open>'\<close>. \<open>\<lambda>\<close> (\<open>U+03BB\<close>) is no letter, and
  \<open>U+03A2\<close> is unassigned. Operators are runs of \<open>U+2190 .. U+22FF\<close> (arrows and
  mathematical operators).\<close>

datatype tok = LIDENT | UIDENT | OP

definition lower :: \<open>nat cls\<close> where \<open>lower = [(0x61, 0x7A), (0x3B1, 0x3BA), (0x3BC, 0x3C9)]\<close>
definition upper :: \<open>nat cls\<close> where \<open>upper = [(0x41, 0x5A), (0x391, 0x3A1), (0x3A3, 0x3A9)]\<close>
definition \<open>idchar = lower @ upper @ [(0x30, 0x39), (0x5F, 0x5F), (0x27, 0x27)]\<close>
definition opchar :: \<open>nat cls\<close> where \<open>opchar = [(0x2190, 0x22FF)]\<close>
definition space :: \<open>nat cls\<close> where \<open>space = [(0x20, 0x20), (0x0A, 0x0A)]\<close>

definition \<open>many p = Times (Pred p) (Star (Pred p))\<close>

definition cp_rules :: \<open>(tok, nat cls, nat, nat) rule list list\<close> where
  \<open>cp_rules = [[
    \<lparr>match = Times (Pred lower) (Star (Pred idchar)), act = \<lambda>_ st. (Some LIDENT, st)\<rparr>,
    \<lparr>match = Times (Pred upper) (Star (Pred idchar)), act = \<lambda>_ st. (Some UIDENT, st)\<rparr>,
    \<lparr>match = many opchar, act = \<lambda>_ st. (Some OP, st)\<rparr>,
    \<lparr>match = many space, act = \<lambda>_ st. (None, st)\<rparr>]]\<close>

definition \<open>cp_tables_test = cp_lexer_tables cp_rules\<close>

local_setup \<open>eval_table (\<^binding>\<open>cp_tables_test_code\<close>, \<^term>\<open>cp_tables_test\<close>)\<close>

declare cp_tables_test_code[code]

definition \<open>is_lf c \<longleftrightarrow> c = (0x0A :: nat)\<close>

definition \<open>start = \<lparr>line = 0, col = 0, off = 0\<rparr>\<close>

definition \<open>cp_lex s = cp_lexer cp_tables_test id (list_spec cp_rules) is_lf [0] start s\<close>

text \<open>On an input in range the lexer is the driver of the spec with the plain reading of
  classes:\<close>

theorem cp_lex_iff_lexes:
  \<open>\<forall>c \<in> set s. c \<le> 0x10FFFF \<Longrightarrow>
    cp_lex s = (l, r, st\<^sub>f) \<longleftrightarrow>
      symbolic.lexes in_cls (list_spec cp_rules) is_lf [0] start s l r st\<^sub>f\<close>
  by (simp add: cp_lex_def cp_tables_test_def cp_lexer_list_iff_lexes_in_range)

text \<open>\<open>\<alpha>\<beta> \<rightarrow>\<Rightarrow> \<Lambda>'\<close>, then a newline and \<open>x1\<close>. Columns count codepoints:\<close>

lemma \<open>cp_lex [0x3B1, 0x3B2, 0x20, 0x2192, 0x21D2, 0x20, 0x39B, 0x27, 0x0A, 0x78, 0x31] =
  (Lexed []
    [\<lparr>tok = LIDENT, span = \<lparr>s_line = 0, s_col = 0, s_off = 0, s_len = 2, s_txt = [0x3B1, 0x3B2]\<rparr>,
      trivia = [0x20]\<rparr>,
     \<lparr>tok = OP, span = \<lparr>s_line = 0, s_col = 3, s_off = 3, s_len = 2, s_txt = [0x2192, 0x21D2]\<rparr>,
      trivia = [0x20]\<rparr>,
     \<lparr>tok = UIDENT, span = \<lparr>s_line = 0, s_col = 6, s_off = 6, s_len = 2, s_txt = [0x39B, 0x27]\<rparr>,
      trivia = [0x0A]\<rparr>,
     \<lparr>tok = LIDENT, span = \<lparr>s_line = 1, s_col = 0, s_off = 9, s_len = 2, s_txt = [0x78, 0x31]\<rparr>,
      trivia = []\<rparr>],
   [], [0])\<close>
  by eval

text \<open>\<open>\<lambda>x\<close> stops at \<open>\<lambda>\<close>, and a surrogate stops too:\<close>

lemma \<open>cp_lex [0x3BB, 0x78] = (Lexed [] [], [0x3BB, 0x78], [0])\<close>
  by eval

lemma \<open>cp_lex [0x61, 0x20, 0xD800] =
  (Lexed []
    [\<lparr>tok = LIDENT, span = \<lparr>s_line = 0, s_col = 0, s_off = 0, s_len = 1, s_txt = [0x61]\<rparr>,
      trivia = [0x20]\<rparr>],
   [0xD800], [0])\<close>
  by eval

text \<open>A number above the range lexes as \<open>U+10FFFF\<close>. No class of \<open>cp_rules\<close> holds
  of it, and a class reaching \<open>U+10FFFF\<close> does:\<close>

lemma \<open>cp_lex [0x61, 0x110000] =
  (Lexed []
    [\<lparr>tok = LIDENT, span = \<lparr>s_line = 0, s_col = 0, s_off = 0, s_len = 1, s_txt = [0x61]\<rparr>,
      trivia = []\<rparr>],
   [0x110000], [0])\<close>
  by eval

definition wide_rules :: \<open>(tok, nat cls, nat, nat) rule list list\<close> where
  \<open>wide_rules = [[\<lparr>match = many [(0x80, 0x10FFFF)], act = \<lambda>_ st. (Some OP, st)\<rparr>]]\<close>

definition \<open>wide_tables = cp_lexer_tables wide_rules\<close>

local_setup \<open>eval_table (\<^binding>\<open>wide_tables_code\<close>, \<^term>\<open>wide_tables\<close>)\<close>

declare wide_tables_code[code]

lemma \<open>cp_lexer wide_tables id (list_spec wide_rules) is_lf [0] start [0x10FFFF, 0x110000, 0x61] =
  (Lexed []
    [\<lparr>tok = OP, span = \<lparr>s_line = 0, s_col = 0, s_off = 0, s_len = 2, s_txt = [0x10FFFF, 0x110000]\<rparr>,
      trivia = []\<rparr>],
   [0x61], [0])\<close>
  by eval

end
