(* Author: Basil Fürer, Claude *)

theory Driver_Tests
  imports TIGER_Lexer.TIGER_Tables
begin

section \<open>Tests of the driver\<close>

text \<open>A two-mode spec on bytes with nested comments. Mode \<open>0\<close> lexes identifiers and
  skips whitespace, and \<open>(*\<close> pushes mode \<open>1\<close>. In mode \<open>1\<close>, \<open>(*\<close> pushes mode \<open>1\<close> again,
  \<open>*)\<close> pops it, and every other character is trivia (a single \<open>(\<close> or \<open>*\<close> loses to
  \<open>(*\<close> and \<open>*)\<close> by length). The theorem about the lexer is an instance of
  @{thm [source] char_lexer_list_iff_lexes}.\<close>

datatype tok = IDENT

definition \<open>chr c = Pred [(c, c)]\<close>
definition \<open>letter = [(CHR ''a'', CHR ''z'')]\<close>
definition \<open>space = [(CHR '' '', CHR '' ''), (CHR 0x0A, CHR 0x0A)]\<close>

text \<open>Every byte but \<open>(\<close> (\<open>0x28\<close>) and \<open>*\<close> (\<open>0x2A\<close>):\<close>

definition \<open>other = [(CHR 0x00, CHR 0x27), (CHR 0x29, CHR 0x29), (CHR 0x2B, CHR 0xFF)]\<close>

definition \<open>open_comment = Times (chr CHR ''('') (chr CHR ''*'')\<close>
definition \<open>close_comment = Times (chr CHR ''*'') (chr CHR '')'')\<close>

definition comment_rules :: \<open>(tok, char cls, char, nat) rule list list\<close> where
  \<open>comment_rules = [
    [\<lparr>match = open_comment, act = \<lambda>_ st. (None, 1 # st)\<rparr>,
     \<lparr>match = Times (Pred letter) (Star (Pred letter)), act = \<lambda>_ st. (Some IDENT, st)\<rparr>,
     \<lparr>match = Times (Pred space) (Star (Pred space)), act = \<lambda>_ st. (None, st)\<rparr>],
    [\<lparr>match = open_comment, act = \<lambda>_ st. (None, 1 # st)\<rparr>,
     \<lparr>match = close_comment, act = \<lambda>_ st. (None, tl st)\<rparr>,
     \<lparr>match = Pred other, act = \<lambda>_ st. (None, st)\<rparr>,
     \<lparr>match = chr CHR ''('', act = \<lambda>_ st. (None, st)\<rparr>,
     \<lparr>match = chr CHR ''*'', act = \<lambda>_ st. (None, st)\<rparr>]]\<close>

definition \<open>comment_tables = char_lexer_tables comment_rules\<close>

(* ~5s *)
local_setup \<open>eval_table (\<^binding>\<open>comment_tables_code\<close>, \<^term>\<open>comment_tables\<close>)\<close>

declare comment_tables_code[code]

definition \<open>is_lf c \<longleftrightarrow> c = CHR 0x0A\<close>

definition \<open>start = \<lparr>line = 0, col = 0, off = 0\<rparr>\<close>

definition \<open>comment_lex st = char_lexer comment_tables id (list_spec comment_rules) is_lf st start\<close>

text \<open>The lexer on the tables is the driver of the spec:\<close>

theorem comment_lex_iff_lexes:
  \<open>comment_lex st s = (l, r, st\<^sub>f) \<longleftrightarrow>
    char_cls.lexes (list_spec comment_rules) is_lf st start s l r st\<^sub>f\<close>
  by (simp add: comment_lex_def comment_tables_def char_lexer_list_iff_lexes)

text \<open>A nested comment across a newline is the trailing trivia of \<open>ab\<close>. The span of
  \<open>xy\<close> is on line \<open>1\<close>, column \<open>4\<close>, offset \<open>22\<close>:\<close>

definition \<open>nested = ''ab (* c (* d *) e'' @ [CHR 0x0A] @ '' *) xy''\<close>

value \<open>comment_lex [0] nested\<close>

lemma \<open>comment_lex [0] nested =
  (Lexed []
    [\<lparr>tok = IDENT, span = \<lparr>s_line = 0, s_col = 0, s_off = 0, s_len = 2, s_txt = ''ab''\<rparr>,
      trivia = '' (* c (* d *) e'' @ [CHR 0x0A] @ '' *) ''\<rparr>,
     \<lparr>tok = IDENT, span = \<lparr>s_line = 1, s_col = 4, s_off = 22, s_len = 2, s_txt = ''xy''\<rparr>,
      trivia = []\<rparr>],
   [], [0])\<close>
  by eval

text \<open>Leading trivia go into the header:\<close>

lemma \<open>comment_lex [0] '' (*c*) ab'' =
  (Lexed '' (*c*) ''
    [\<lparr>tok = IDENT, span = \<lparr>s_line = 0, s_col = 7, s_off = 7, s_len = 2, s_txt = ''ab''\<rparr>,
      trivia = []\<rparr>],
   [], [0])\<close>
  by eval

text \<open>An unmatched character stops the lexer with the residue:\<close>

lemma \<open>comment_lex [0] ''ab $ cd'' =
  (Lexed []
    [\<lparr>tok = IDENT, span = \<lparr>s_line = 0, s_col = 0, s_off = 0, s_len = 2, s_txt = ''ab''\<rparr>,
      trivia = '' ''\<rparr>],
   ''$ cd'', [0])\<close>
  by eval

text \<open>Popping the last mode is no step either: from the stack \<open>[1]\<close>, \<open>*)\<close> stays
  unread:\<close>

lemma \<open>comment_lex [1] ''c *) ab'' = (Lexed ''c '' [], ''*) ab'', [1])\<close>
  by eval

text \<open>An unterminated comment consumes the input. The residue is empty, and the final
  stack, one entry per open comment, says that the input ended in mode \<open>1\<close>:\<close>

lemma \<open>comment_lex [0] ''ab (* c'' =
  (Lexed []
    [\<lparr>tok = IDENT, span = \<lparr>s_line = 0, s_col = 0, s_off = 0, s_len = 2, s_txt = ''ab''\<rparr>,
      trivia = '' (* c''\<rparr>],
   [], [1, 0])\<close>
  by eval

lemma \<open>comment_lex [0] ''(* a (* b *)'' = (Lexed ''(* a (* b *)'' [], [], [1, 0])\<close>
  by eval

end
