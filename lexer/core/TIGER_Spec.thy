(* Author: Basil Fürer, Claude *)

theory TIGER_Spec
  imports TIGER_Regex TIGER_Lexed
begin

section \<open>The lexer specification\<close>

text \<open>A lexer spec maps each mode to a prioritized list of rules. A rule is a regex over
  syntactic predicates and an action. The action sees the matched text and the mode stack
  (its head is the current mode) and returns the token kind, or \<^const>\<open>None\<close> for
  trivia, and the new stack \<^cite>\<open>\<open>Sect.~10\<close> in "paxson2026-flex-manual"\<close>. The judgments follow Verbatim
  \<^cite>\<open>\<open>Figs.~3--4\<close> in "egolf2021-verbatim-verified-lexer"\<close>: the longest prefix, the
  first rule matching it, and the driver, which stops with the unread residue and the
  stack it stops in.

  The judgments live in the context of \<open>symbolic\<close> and read a rule's regex through the
  denotation \<open>sem\<close> of its predicates (\<^const>\<open>symbolic.lang\<close>).

  An empty match is never a match, and an action returning the empty stack is an error
  (the driver stops before that step). Both make the driver total and deterministic.
  Reps assumes instead that no token regex admits the empty word
  \<^cite>\<open>\<open>Sect.~1\<close> in "reps1998-maximal-munch-linear"\<close>. Here a rule's regex
  may accept it, and \<open>match_rule\<close> drops that match.\<close>

record ('k, 'p, 'ch, 'm) rule =
  match :: \<open>'p rexp\<close>
  act :: \<open>'ch list \<Rightarrow> 'm list \<Rightarrow> 'k option \<times> 'm list\<close>

type_synonym ('k, 'p, 'ch, 'm) lexer_spec = \<open>'m \<Rightarrow> ('k, 'p, 'ch, 'm) rule list\<close>

context symbolic
begin

inductive match_rule :: \<open>('k, 'p, 'ch, 'm) rule \<Rightarrow> 'ch list \<Rightarrow> bool\<close> where
  match_ruleI: \<open>\<lbrakk> p \<in> lang (match \<rho>); p \<noteq> [] \<rbrakk> \<Longrightarrow> match_rule \<rho> p\<close>

text \<open>A rule matches a nonempty word of its language
  \<^cite>\<open>\<open>Fig.~4, FirstToken\<close> in "egolf2021-verbatim-verified-lexer"\<close>.\<close>

inductive max_pref where
  max_prefI:
    \<open>\<lbrakk> s = p @ u; \<rho> \<in> set rs; match_rule \<rho> p;
      \<And>p' u' \<rho>'.
        \<lbrakk> s = p' @ u'; length p < length p'; \<rho>' \<in> set rs \<rbrakk> \<Longrightarrow>
        \<not> match_rule \<rho>' p'
     \<rbrakk> \<Longrightarrow>
     max_pref rs p s\<close>

text \<open>\<open>p\<close> is the longest prefix of \<open>s\<close> that some rule matches
  \<^cite>\<open>\<open>Fig.~3, MaxPref\<close> in "egolf2021-verbatim-verified-lexer"\<close>.\<close>

inductive first_token where
  first_tokenI:
    \<open>\<lbrakk> max_pref rs p s; i < length rs; match_rule (rs ! i) p;
      \<And>j. j < i \<Longrightarrow> \<not> match_rule (rs ! j) p
     \<rbrakk> \<Longrightarrow>
     first_token rs i p s\<close>

text \<open>Rule \<open>i\<close> wins on \<open>s\<close> with lexeme \<open>p\<close>: \<open>p\<close> is the longest match and \<open>i\<close> the first
  rule matching it \<^cite>\<open>\<open>Sect.~7\<close> in "paxson2026-flex-manual"\<close>, as in lex
  \<^cite>\<open>\<open>Sect.~5\<close> in "lesk1975-lex"\<close>.\<close>

inductive step where
  stepI:
    \<open>\<lbrakk> first_token (sp m) i p s;
       act (sp m ! i) p (m # st) = (k, st');
       st' \<noteq> [];
       s = p @ s'
     \<rbrakk> \<Longrightarrow>
     step sp (m # st) s (k, p, st', s')\<close>

text \<open>One step in the stack \<open>m # st\<close> reads the winning lexeme \<open>p\<close>, runs the winning action
  and yields the kind \<open>k\<close>, the new stack and the rest of the input.\<close>

inductive lexes ::
  \<open>('k, 'p, 'ch, 'm) lexer_spec \<Rightarrow> ('ch \<Rightarrow> bool) \<Rightarrow> 'm list \<Rightarrow> pos \<Rightarrow>
    'ch list \<Rightarrow> ('k, 'ch) lexed \<Rightarrow> 'ch list \<Rightarrow> 'm list \<Rightarrow> bool\<close>
for sp is_newline where
  lexes_stop:
    \<open>(\<And>x. \<not> step sp st s x) \<Longrightarrow> lexes sp is_newline st q s (Lexed [] []) s st\<close>
| lexes_token:
    \<open>\<lbrakk> step sp st s (Some k, p, st', s');
       lexes sp is_newline st' (advance_list is_newline p q) s' (Lexed h ts) r st\<^sub>f
     \<rbrakk> \<Longrightarrow>
     lexes sp is_newline st q s
      (Lexed [] (\<lparr>tok = k, span = span_at q p, trivia = h\<rparr> # ts)) r st\<^sub>f\<close>
| lexes_trivia:
    \<open>\<lbrakk> step sp st s (None, p, st', s');
       lexes sp is_newline st' (advance_list is_newline p q) s' (Lexed h ts) r st\<^sub>f
     \<rbrakk> \<Longrightarrow>
     lexes sp is_newline st q s (Lexed (p @ h) ts) r st\<^sub>f\<close>

text \<open>The driver lexes \<open>s\<close> from stack \<open>st\<close> and position \<open>q\<close> into a lexed source, the
  residue \<open>r\<close> where no step applies and the stack \<open>st\<^sub>f\<close> it stops in
  \<^cite>\<open>\<open>Fig.~4, Tokens\<close> in "egolf2021-verbatim-verified-lexer"\<close>. The leading trivia
  of the rest become the trailing trivia of a token, or the header in front of the
  first token. Spans come from \<^const>\<open>advance_list\<close>.

  The final stack says where the input ended, so the end of the input needs no
  sentinel character (flex's \<open><<EOF>>\<close> \<^cite>\<open>\<open>Sect.~12\<close> in "paxson2026-flex-manual"\<close>).
  An empty residue in a stack whose top is not a final mode (an unterminated comment)
  is an error of the consumer's, not of the driver.\<close>

subsection \<open>Some facts\<close>

lemma max_prefD: \<open>max_pref rs p s \<Longrightarrow> (\<exists>u. s = p @ u) \<and> (\<exists>\<rho> \<in> set rs. match_rule \<rho> p)\<close>
  by (blast elim: max_pref.cases)

lemma max_pref_longest:
  assumes \<open>max_pref rs p s\<close> \<open>s = p' @ u'\<close> \<open>length p < length p'\<close> \<open>\<rho>' \<in> set rs\<close>
  shows \<open>\<not> match_rule \<rho>' p'\<close>
  using \<open>max_pref rs p s\<close>
proof (cases rule: max_pref.cases)
  case max_prefI
  then have \<open>\<And>p' u' \<rho>'. \<lbrakk> s = p' @ u'; length p < length p'; \<rho>' \<in> set rs \<rbrakk> \<Longrightarrow> \<not> match_rule \<rho>' p'\<close>
    by blast
  with assms show ?thesis by blast
qed

lemma first_token_max_pref: \<open>first_token rs i p s \<Longrightarrow> max_pref rs p s\<close>
  by (auto elim: first_token.cases)

lemma first_token_match: \<open>first_token rs i p s \<Longrightarrow> match_rule (rs ! i) p\<close>
  by (auto elim: first_token.cases)

lemma first_token_first: \<open>first_token rs i p s \<Longrightarrow> j < i \<Longrightarrow> \<not> match_rule (rs ! j) p\<close>
  by (auto elim: first_token.cases)

lemma first_token_prefix: \<open>first_token rs i p s \<Longrightarrow> \<exists>u. s = p @ u\<close>
  by (auto elim!: first_token.cases max_pref.cases)

lemma step_length_less: \<open>step sp st s (k, p, st', s') \<Longrightarrow> length s' < length s\<close>
  by (auto elim!: step.cases first_token.cases match_rule.cases)

text \<open>Every step consumes input (no empty matches). This is the progress measure of the
  driver.\<close>

lemma lexes_source: \<open>lexes sp is_newline st q s l r st\<^sub>f \<Longrightarrow> source l @ r = s\<close>
  by (induct rule: lexes.induct) (auto simp: source_def span_at_def elim!: step.cases)

section \<open>Surface theorems\<close>

text \<open>The spec is unambiguous: the first token is unique, and so are a step and a whole
  run. This is Verbatim's Uniqueness lemma
  \<^cite>\<open>\<open>Sect.~V-B\<close> in "egolf2021-verbatim-verified-lexer"\<close>, proved the same way: both
  lexemes are maximal prefixes of one string, so they are equal, and of two rules matching
  it the later one cannot win. Verbatim has no modes; here the run also fixes the final
  stack.\<close>

theorem first_token_deterministic:
  assumes \<open>first_token rs i p s\<close> \<open>first_token rs i' p' s\<close>
  shows \<open>i = i' \<and> p = p'\<close>
proof -
  from assms have mp: \<open>max_pref rs p s\<close> and mp': \<open>max_pref rs p' s\<close>
    by (simp_all add: first_token_max_pref)
  from mp obtain u \<rho> where \<open>s = p @ u\<close> \<open>\<rho> \<in> set rs\<close> \<open>match_rule \<rho> p\<close>
    by (blast dest: max_prefD)
  from mp' obtain u' \<rho>' where \<open>s = p' @ u'\<close> \<open>\<rho>' \<in> set rs\<close> \<open>match_rule \<rho>' p'\<close>
    by (blast dest: max_prefD)
  have \<open>\<not> length p < length p'\<close>
    using max_pref_longest[OF mp \<open>s = p' @ u'\<close> _ \<open>\<rho>' \<in> set rs\<close>] \<open>match_rule \<rho>' p'\<close> by blast
  moreover have \<open>\<not> length p' < length p\<close>
    using max_pref_longest[OF mp' \<open>s = p @ u\<close> _ \<open>\<rho> \<in> set rs\<close>] \<open>match_rule \<rho> p\<close> by blast
  ultimately have \<open>p = p'\<close>
    using \<open>s = p @ u\<close> \<open>s = p' @ u'\<close> by simp
  with assms show ?thesis
    by (metis linorder_neqE_nat first_token_first first_token_match)
qed

theorem step_deterministic: \<open>step sp st s x \<Longrightarrow> step sp st s y \<Longrightarrow> x = y\<close>
  by (elim step.cases) (auto dest: first_token_deterministic)

theorem lexes_deterministic:
  assumes \<open>lexes sp is_newline st q s l r st\<^sub>f\<close> \<open>lexes sp is_newline st q s l' r' st\<^sub>f'\<close>
  shows \<open>l = l' \<and> r = r' \<and> st\<^sub>f = st\<^sub>f'\<close>
  using assms
proof (induction arbitrary: l' r' st\<^sub>f' rule: lexes.induct)
  case (lexes_stop st s q)
  from lexes_stop.prems show ?case
    by (cases rule: lexes.cases) (use lexes_stop.hyps in blast)+
next
  case (lexes_token st s k p st' s' q h ts r st\<^sub>f)
  from lexes_token.prems \<open>step sp st s (Some k, p, st', s')\<close> show ?case
    by (cases rule: lexes.cases)
      (auto dest: step_deterministic[OF \<open>step sp st s (Some k, p, st', s')\<close>] lexes_token.IH)
next
  case (lexes_trivia st s p st' s' q h ts r st\<^sub>f)
  from lexes_trivia.prems \<open>step sp st s (None, p, st', s')\<close> show ?case
    by (cases rule: lexes.cases)
      (auto dest: step_deterministic[OF \<open>step sp st s (None, p, st', s')\<close>] lexes_trivia.IH)
qed

text \<open>The driver terminates on every input, whatever the actions do to the stack
  (each step consumes a nonempty lexeme, @{thm [source] step_length_less}). This is the
  termination argument of Verbatim's \<open>lex0\<close>, which recurses on proper suffixes of the input
  \<^cite>\<open>\<open>Sect.~IV\<close> in "egolf2021-verbatim-verified-lexer"\<close>. Verbatim must thread an
  accessibility proof through the function; here the run is an inductive relation and
  totality is a theorem, by induction on the length of the input:\<close>

theorem lexes_total: \<open>\<exists>l r st\<^sub>f. lexes sp is_newline st q s l r st\<^sub>f\<close>
proof (induct s arbitrary: st q rule: length_induct[case_names len])
  case (len s) show ?case
  proof (cases \<open>\<exists>x. step sp st s x\<close>)
    case True
    then obtain k p st' s' where step: \<open>step sp st s (k, p, st', s')\<close>
      by (metis prod_cases4)
    with len obtain l r st\<^sub>f
      where \<open>lexes sp is_newline st' (advance_list is_newline p q) s' l r st\<^sub>f\<close>
      by (meson step_length_less)
    with step show ?thesis
      by (cases l; cases k; blast intro: lexes_token lexes_trivia)
  qed (blast intro: lexes_stop)
qed

end

end
