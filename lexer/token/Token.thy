theory Token
  imports Main
begin

section \<open>Source spans\<close>

text \<open>
  Lexer-to-parser interface: each token is paired with the source span it
  occupies. Only the column \<^text>\<open>s_col\<close> enters the indentation logic; the
  remaining fields serve diagnostics.
\<close>

record 'ch span =
  s_line :: nat
  s_col :: nat
  s_off :: nat
  s_len :: nat
  s_txt :: \<open>'ch list\<close>

section \<open>Parser input: extensible tokens\<close>

record ('tok, 'ch) token =
  tok  :: 'tok
  span :: \<open>'ch span\<close>

notation token.make (\<open>\<langle>_; _\<rangle>\<close>)

text \<open>The parser consumes a list of tokens. The record fixes only what the
  parser reads: the token class \<^const>\<open>tok\<close> and the lexeme \<^const>\<open>span\<close>.
  A client extends it with further fields (trailing trivia, source file
  and the like) through the usual record extension

    \<^theory_text>\<open>record my_token = (my_tok, char) token + trailing :: \<dots>\<close>

  and the parser is agnostic to the extension: it copies each token into
  the corresponding AST leaf, where the extra fields are available to the
  semantic actions of the \<^theory_text>\<open>grammar\<close> command. All parser
  constants are stated over the scheme type \<^typ>\<open>('tok, 'ch, 'm) token_scheme\<close>
  with the extension type \<^text>\<open>'m\<close> free (\<^typ>\<open>unit\<close> for the plain record).\<close>

type_synonym ('m, 'ch, 'tok) tword = \<open>('tok, 'ch, 'm) token_scheme list\<close>

definition tcols :: \<open>('m, 'ch, 'tok) tword \<Rightarrow> ('tok \<times> nat) list\<close> where
  \<open>tcols w = map (\<lambda>t. (tok t, s_col (span t))) w\<close>

text \<open>Layout machinery reads a token word through \<^const>\<open>tcols\<close>, which
  keeps the indentation column of each token and drops the rest of its span
  and any extension fields.\<close>

lemma tcols_Nil [simp]: \<open>tcols [] = []\<close>
  and tcols_Cons [simp]: \<open>tcols (t # w) = (tok t, s_col (span t)) # tcols w\<close>
  by (simp_all add: tcols_def)

lemma length_tcols [simp]: \<open>length (tcols w) = length w\<close>
  and tcols_append [simp]: \<open>tcols (u @ v) = tcols u @ tcols v\<close>
  and tcols_take: \<open>tcols (take n w) = take n (tcols w)\<close>
  and tcols_drop: \<open>tcols (drop n w) = drop n (tcols w)\<close>
  by (simp_all add: tcols_def take_map drop_map)

text \<open>Anchor column of a word: the column of its first token, or \<open>0\<close> for
  the empty word (which is never the outermost anchor of a well-indented
  derivation).\<close>

definition col_of :: \<open>('m, 'ch, 't) tword \<Rightarrow> nat\<close> where
  \<open>col_of w = (case w of [] \<Rightarrow> 0 | x # _ \<Rightarrow> s_col (span x))\<close>

lemma col_of_Nil[simp]: \<open>col_of [] = 0\<close>
  by (simp add: col_of_def)

lemma col_of_Cons[simp]: \<open>col_of (x # xs) = s_col (span x)\<close>
  by (simp add: col_of_def)

section \<open>Positions\<close>

text \<open>A position is a line, a column and a character offset, all counted from \<open>0\<close>. The
  spans above store the start position and the text, so the stop position of a span is
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
  next token. The parser accepts the extension unchanged (see the record text above).\<close>

record ('tok, 'ch) lex_token = \<open>('tok, 'ch) token\<close> +
  trivia :: \<open>'ch list\<close>

datatype ('tok, 'ch) lexed = Lexed (header: \<open>'ch list\<close>) (toks: \<open>('tok, 'ch) lex_token list\<close>)

text \<open>A lexed source is its leading trivia and its tokens. \<open>source\<close> gives back
  the text it was lexed from:\<close>

definition source :: \<open>('tok, 'ch) lexed \<Rightarrow> 'ch list\<close> where
  \<open>source l = header l @ concat (map (\<lambda>t. s_txt (span t) @ trivia t) (toks l))\<close>

end
