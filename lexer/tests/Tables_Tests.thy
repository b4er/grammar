(* Author: Basil Fürer, Claude *)

theory Tables_Tests
  imports TIGER_Lexer.TIGER_Tables
begin

section \<open>Tests of the tables\<close>

text \<open>Two specs on bytes, with their tables by \<open>eval_table\<close> and the runner on
  them: identifiers, numerals and a keyword in one mode, and Reps' pair \<open>abc\<close>,
  \<open>(abc)\<^sup>*d\<close>, which makes the runner back up
  \<^cite>\<open>\<open>Sect.~1\<close> in "reps1998-maximal-munch-linear"\<close>. The theorems about the
  runners are instances of @{thm [source] run_char_tables}.\<close>

subsection \<open>Identifiers, numerals and a keyword\<close>

datatype tok = KW_IF | IDENT | NUM

definition \<open>letter = [(CHR ''a'', CHR ''z'')]\<close>
definition \<open>digit = [(CHR ''0'', CHR ''9'')]\<close>
definition \<open>space = [(CHR '' '', CHR '' ''), (CHR 0x0A, CHR 0x0A)]\<close>

text \<open>The keyword \<open>if\<close> comes first, so it wins against identifiers on \<open>if\<close> by
  priority and loses on \<open>iff\<close> by length. Whitespace is trivia. There is one mode:\<close>

definition test_rules :: \<open>(tok, char cls, char, unit) rule list\<close> where
  \<open>test_rules = [
    \<lparr>match = Times (Pred [(CHR ''i'', CHR ''i'')]) (Pred [(CHR ''f'', CHR ''f'')]),
     act = \<lambda>_ st. (Some KW_IF, st)\<rparr>,
    \<lparr>match = Times (Pred letter) (Star (Plus (Pred letter) (Pred digit))),
     act = \<lambda>_ st. (Some IDENT, st)\<rparr>,
    \<lparr>match = Times (Pred digit) (Star (Pred digit)), act = \<lambda>_ st. (Some NUM, st)\<rparr>,
    \<lparr>match = Times (Pred space) (Star (Pred space)), act = \<lambda>_ st. (None, st)\<rparr>]\<close>

definition \<open>test_tables = char_tables test_rules\<close>

local_setup \<open>eval_table (\<^binding>\<open>test_tables_code\<close>, \<^term>\<open>test_tables\<close>)\<close>

declare test_tables_code[code]

value \<open>test_tables\<close>

definition \<open>test_run = run_char test_tables\<close>

text \<open>The runner on the tables is the step of the spec:\<close>

theorem test_run_Some_iff:
  \<open>test_run s = Some (i, p, rest) \<longleftrightarrow> char_cls.first_token test_rules i p s \<and> s = p @ rest\<close>
  by (simp add: test_run_def test_tables_def run_char_tables char_cls.run_dfa_Some_iff
      char_cls.minterm_classifier_class_of)

theorem test_run_None_iff:
  \<open>test_run s = None \<longleftrightarrow> (\<nexists>i p. char_cls.first_token test_rules i p s)\<close>
  by (simp add: test_run_def test_tables_def run_char_tables char_cls.run_dfa_None_iff
      char_cls.minterm_classifier_class_of)

text \<open>Priority on \<open>if\<close>, length on \<open>iff\<close>, trivia, and inputs no rule matches:\<close>

value \<open>test_run ''if x''\<close>
value \<open>test_run ''iff x''\<close>
value \<open>test_run ''x1 = 42''\<close>
value \<open>test_run ''42ab''\<close>
value \<open>test_run ''  \<newline> if''\<close>
value \<open>test_run ''= x''\<close>
value \<open>test_run []\<close>

lemma \<open>test_run ''if x'' = Some (0, ''if'', '' x'')\<close> by eval
lemma \<open>test_run ''iff x'' = Some (1, ''iff'', '' x'')\<close> by eval
lemma \<open>test_run ''42ab'' = Some (2, ''42'', ''ab'')\<close> by eval
lemma \<open>test_run ''= x'' = None\<close> by eval

subsection \<open>Backing up\<close>

text \<open>On \<open>abcabd\<close>, the runner reads \<open>abcab\<close>, finds that no rule can match a longer
  prefix and backs up to \<open>abc\<close> \<^cite>\<open>\<open>Sect.~1\<close> in "reps1998-maximal-munch-linear"\<close>:\<close>

definition \<open>chr c = Pred [(c, c)]\<close>

definition reps_rules :: \<open>(nat, char cls, char, unit) rule list\<close> where
  \<open>reps_rules = [
    \<lparr>match = Times (chr CHR ''a'') (Times (chr CHR ''b'') (chr CHR ''c'')),
     act = \<lambda>_ st. (Some 0, st)\<rparr>,
    \<lparr>match = Times (Star (Times (chr CHR ''a'') (Times (chr CHR ''b'') (chr CHR ''c''))))
       (chr CHR ''d''),
     act = \<lambda>_ st. (Some 1, st)\<rparr>]\<close>

definition \<open>reps_tables = char_tables reps_rules\<close>

local_setup \<open>eval_table (\<^binding>\<open>reps_tables_code\<close>, \<^term>\<open>reps_tables\<close>)\<close>

declare reps_tables_code[code]

definition \<open>reps_run = run_char reps_tables\<close>

theorem reps_run_Some_iff:
  \<open>reps_run s = Some (i, p, rest) \<longleftrightarrow> char_cls.first_token reps_rules i p s \<and> s = p @ rest\<close>
  by (simp add: reps_run_def reps_tables_def run_char_tables char_cls.run_dfa_Some_iff
      char_cls.minterm_classifier_class_of)

value \<open>reps_tables\<close>
value \<open>reps_run ''abcabd''\<close>
value \<open>reps_run ''abd''\<close>
value \<open>reps_run ''abcabcd''\<close>

lemma \<open>reps_run ''abcabd'' = Some (0, ''abc'', ''abd'')\<close> by eval
lemma \<open>reps_run ''abd'' = None\<close> by eval
lemma \<open>reps_run ''abcabcd'' = Some (1, ''abcabcd'', [])\<close> by eval

end
