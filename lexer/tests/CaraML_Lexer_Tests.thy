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

end
