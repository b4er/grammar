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
  A client extends it with further fields (trailing trivia, source file,
  \<dots>) through the usual record extension

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

end
