(* Author: Basil Fürer *)

theory TIGER_Lexed
  imports TIGER_Token.TIGER_Token
begin

text \<open>What the lexer adds to the token interface of \<^theory>\<open>TIGER_Token.TIGER_Token\<close>:
  positions, from which the lexer computes the spans, and its output, tokens with their
  trailing trivia. The parser needs neither.\<close>

section \<open>Positions\<close>

text \<open>A position is a line, a column and a character offset, all counted from \<open>0\<close>. The
  spans store the start position and the text, so the stop position of a span is
  derived from its text by \<open>advance_list\<close> (half-open: the stop position is the
  first one past the span).\<close>

record pos =
  line :: nat
  col :: nat
  off :: nat

definition advance :: \<open>('ch \<Rightarrow> bool) \<Rightarrow> 'ch \<Rightarrow> pos \<Rightarrow> pos\<close> where
  \<open>advance is_newline c p = (if is_newline c
     then \<lparr>line = Suc (line p), col = 0, off = Suc (off p)\<rparr>
     else p\<lparr>col := Suc (col p), off := Suc (off p)\<rparr>)\<close>

text \<open>\<^const>\<open>advance\<close> moves past one character. The newline test is a parameter
  (the character type is arbitrary).\<close>

primrec advance_list :: \<open>('ch \<Rightarrow> bool) \<Rightarrow> 'ch list \<Rightarrow> pos \<Rightarrow> pos\<close> where
  \<open>advance_list is_newline [] p = p\<close>
| \<open>advance_list is_newline (c # w) p = advance_list is_newline w (advance is_newline c p)\<close>

lemma off_advance[simp]: \<open>off (advance is_newline c p) = Suc (off p)\<close>
  by (simp add: advance_def)

lemma off_advance_list[simp]: \<open>off (advance_list is_newline w p) = off p + length w\<close>
  by (induct w arbitrary: p) simp_all

lemma off_le_advance_list: \<open>off p \<le> off (advance_list is_newline w p)\<close>
  by simp

lemma advance_list_append[simp]:
  \<open>advance_list is_newline (u @ v) p = advance_list is_newline v (advance_list is_newline u p)\<close>
  by (induct u arbitrary: p) simp_all

definition span_at :: \<open>pos \<Rightarrow> 'ch list \<Rightarrow> 'ch span\<close> where
  \<open>span_at p w = \<lparr>s_line = line p, s_col = col p, s_off = off p, s_len = length w, s_txt = w\<rparr>\<close>

text \<open>\<^const>\<open>span_at\<close> is the span of the text \<open>w\<close> starting at \<open>p\<close>. It is well formed:
  it ends where \<^const>\<open>advance_list\<close> stops.\<close>

lemma span_at_stop: \<open>s_off (span_at p w) + s_len (span_at p w) = off (advance_list is_newline w p)\<close>
  by (simp add: span_at_def)

section \<open>Lexer output\<close>

text \<open>A lexed token is a parser token (\<^const>\<open>tok\<close> is its kind, \<^const>\<open>s_txt\<close> of its
  span its text) extended by its trailing trivia, the comments and whitespace up to the
  next token. The parser accepts the extension unchanged (see the token record in
  \<^theory>\<open>TIGER_Token.TIGER_Token\<close>).\<close>

record ('tok, 'ch) lex_token = \<open>('tok, 'ch) token\<close> +
  trivia :: \<open>'ch list\<close>

datatype ('tok, 'ch) lexed = Lexed (header: \<open>'ch list\<close>) (toks: \<open>('tok, 'ch) lex_token list\<close>)

text \<open>A lexed source is its leading trivia and its tokens. \<open>source\<close> gives back
  the text it was lexed from:\<close>

definition source :: \<open>('tok, 'ch) lexed \<Rightarrow> 'ch list\<close> where
  \<open>source l = header l @ concat (map (\<lambda>t. s_txt (span t) @ trivia t) (toks l))\<close>

end
