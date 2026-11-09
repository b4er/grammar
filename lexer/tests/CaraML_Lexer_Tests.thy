theory CaraML_Lexer_Tests
  imports CaraML_Lexer.CaraML_Lexer
begin

section \<open>Tests of CaraML's lexer spec\<close>

text \<open>Every token mode has the 47 untagged rules and its tagged ones: the closing brace
  outside holes, the three selectors of its kind, the two string pieces in a hole and the
  three numerals of its kind. \<open>Comment\<close> is exclusive and has its own three rules:\<close>

lemma
  \<open>length (caraml.spec (Tok Outer Spaced)) = 54\<close>
  \<open>length (caraml.spec (Tok Outer AfterOp)) = 54\<close>
  \<open>length (caraml.spec (Tok Hole AfterNonop)) = 55\<close>
  \<open>length (caraml.spec (Tok Fresh Spaced)) = 53\<close>
  \<open>length (caraml.spec Comment) = 3\<close>
  by simp_all

text \<open>The end of a comment pops, and the hook makes the outer mode spaced. The end of a
  string pops a hole, and the hook makes the outer mode one after an operand:\<close>

lemma
  \<open>act (caraml.spec Comment ! 1) u [Comment, Tok Outer AfterOp] = (None, [Tok Outer Spaced])\<close>
  \<open>act (caraml.spec (Tok Hole Spaced) ! 50) u [Tok Hole Spaced, Tok Outer Spaced] =
    (Some StrEnd, [Tok Outer AfterOp])\<close>
  by (simp_all add: mk_act_def operand_end_def)

lemma \<open>caraml.start = Tok Outer Spaced\<close> \<open>caraml.final (Tok Outer AfterOp)\<close>
  \<open>\<not> caraml.final (Tok Hole Spaced)\<close> \<open>\<not> caraml.final Comment\<close>
  by (simp_all add: caraml.start_def caraml.final_def)

subsection \<open>The generated lexer\<close>

text \<open>The first check compiles \<^const>\<open>caraml_lex\<close> and \<^const>\<open>caraml_lex.ok\<close>
  with the table literals (about 40 s), the others reuse them. A minus is a sign after trivia and an operator after an
  operand. A dot after trivia starts a leading selector and one after an operand a
  trailing selector:\<close>

lexer_check (* ~40 s *)
  \<open>map tok (toks (fst (caraml_lex (cp ''let x = f -1 in a-1'')))) =
    [KLet, LId, Assign, LId, IntL, LId, LId, Op, IntL]\<close>
  \<open>map tok (toks (fst (caraml_lex (cp ''r.x .y M.N.0'')))) =
    [LId, TSelL, LSelL, UId, TSelU, TSelN]\<close>
  \<open>caraml_lex.ok (cp ''r.x'')\<close>

text \<open>An interpolated string is a start, the tokens of its hole and an end. A comment
  nests, and an unterminated one ends in \<^const>\<open>Comment\<close>, which is not final:\<close>

lexer_check
  \<open>map tok (toks (fst (caraml_lex ([0x22] @ cp ''a${x}b'' @ [0x22])))) =
    [StrStart, LId, StrEnd]\<close>
  \<open>map tok (toks (fst (caraml_lex (cp ''a {- {- b -} -} c'')))) = [LId, LId]\<close>
  \<open>caraml_lex.ok (cp ''a {- {- b -} -} c'')\<close>
  \<open>\<not> caraml_lex.ok (cp ''a {- b'')\<close>

text \<open>A backticked name is an operator unless it is a keyword, where the guard stops the
  lexer:\<close>

lexer_check
  \<open>map tok (toks (fst (caraml_lex (cp ''a `mod` b'')))) = [LId, Op, LId]\<close>
  \<open>\<not> caraml_lex.ok (cp ''a `let` b'')\<close>

lex caraml_lex \<open>let s = "n = ${n + 1}" -- done\<close>

end
