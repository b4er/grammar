(* Author: Basil Fürer *)

theory TIGER_Lexer
  imports TIGER_Gen
begin

section \<open>The runner\<close>

text \<open>The runner steps the DFA of a mode over the input, remembers the last accepting
  position and its rule, stops at the dead state or at the end of input, and backs up to
  that position \<^cite>\<open>\<open>Sect.~17\<close> in "paxson2026-flex-manual"\<close>
  \<^cite>\<open>\<open>Sect.~2, Fig.~1(a)\<close> in "reps1998-maximal-munch-linear"\<close>. Its surface theorem is
  equality with \<^const>\<open>symbolic.first_token\<close>, the step of the specification. The proof
  follows the shape of \<open>auto_split_lemma\<close> in \<^session>\<open>Functional-Automata\<close>
  (\<open>AutoMaxChop\<close>), Nipkow's scanner \<open>auto_split\<close>
  \<^cite>\<open>\<open>Sect.~5.2\<close> in "nipkow1998-verified-lexical-analysis"\<close>: an invariant on the
  part already read, carried along the scan. Nipkow's scanner has one automaton and no rule
  priorities; here the last accept also records the winning rule.

  The driver over \<^const>\<open>symbolic.lexes\<close> is in theory \<open>TIGER_Driver\<close>. Reps'
  bounded-lookahead linearity \<^cite>\<open>\<open>Sect.~3\<close> in "reps1998-maximal-munch-linear"\<close>
  comes later, and Reps' memoization of failed state-position pairs is deferred.
  Verbatim++ verifies a Reps-style memo of maximal-prefix results across tokens, keyed by
  the length of the suffix, and analyses the result as \<open>O(n log n)\<close>
  \<^cite>\<open>\<open>Sects.~4--5\<close> in "egolf2022-verbatim-plus-plus"\<close>.\<close>

subsection \<open>The scan on tables\<close>

text \<open>The scan reads tables only: the transition table \<open>T\<close>, indexed by state and
  minterm number, the acceptance table \<open>A\<close>, the classifier \<open>cls\<close> from characters to
  minterm numbers (a table lookup at run time) and the index \<open>d\<close> of the dead state. It
  keeps the current state \<open>q\<close>, the number \<open>n\<close> of characters read and the last accept
  as a rule and a length. The initial state is \<open>0\<close> and the empty prefix never counts as
  an accept:\<close>

fun scan ::
  \<open>nat list list \<Rightarrow> nat option list \<Rightarrow> ('ch \<Rightarrow> nat) \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'ch list \<Rightarrow>
    (nat \<times> nat) option \<Rightarrow> (nat \<times> nat) option\<close>
where
  \<open>scan T A cls d q n [] b = b\<close>
| \<open>scan T A cls d q n (c # v) b =
    (let q' = T ! q ! cls c in
     if q' = d then b
     else scan T A cls d q' (Suc n) v (case A ! q' of None \<Rightarrow> b | Some i \<Rightarrow> Some (i, Suc n)))\<close>

text \<open>The runner backs up to the last accept and splits the input there:\<close>

definition run_tables ::
  \<open>nat list list \<Rightarrow> nat option list \<Rightarrow> ('ch \<Rightarrow> nat) \<Rightarrow> nat \<Rightarrow> 'ch list \<Rightarrow>
    (nat \<times> 'ch list \<times> 'ch list) option\<close>
where
  \<open>run_tables T A cls d s =
    map_option (\<lambda>(i, n). (i, take n s, drop n s)) (scan T A cls d 0 0 s None)\<close>

text \<open>An index below the length of the list finds its element:\<close>

lemma nth_index_of_if_less: \<open>index_of Q y < length Q \<Longrightarrow> Q ! index_of Q y = y\<close>
  by (induct Q) auto

subsection \<open>The invariant\<close>

context symbolic
begin

text \<open>After reading \<open>u\<close>, the remembered accept \<open>b\<close> is the longest nonempty prefix of \<open>u\<close>
  that some rule matches, with the least rule matching it. This is \<^const>\<open>first_token\<close>
  on \<open>u\<close>. With no accept, no rule matches a prefix of \<open>u\<close>:\<close>

definition last_accept :: \<open>('k, 'p, 'ch, 'm) rule list \<Rightarrow> 'ch list \<Rightarrow> (nat \<times> nat) option \<Rightarrow> bool\<close>
where
  \<open>last_accept rs u b = (case b of
     None \<Rightarrow> \<forall>p t \<rho>. u = p @ t \<longrightarrow> \<rho> \<in> set rs \<longrightarrow> \<not> match_rule \<rho> p
   | Some (i, n) \<Rightarrow> n \<le> length u \<and> first_token rs i (take n u) u)\<close>

lemma last_accept_Nil: \<open>last_accept rs [] None\<close>
  by (simp add: last_accept_def match_rule.simps)

text \<open>A longest match stays longest when the input grows by words that no rule matches:\<close>

lemma max_pref_append:
  assumes \<open>max_pref rs p u\<close>
    and \<open>\<And>w t \<rho>. v = w @ t \<Longrightarrow> w \<noteq> [] \<Longrightarrow> \<rho> \<in> set rs \<Longrightarrow> \<not> match_rule \<rho> (u @ w)\<close>
  shows \<open>max_pref rs p (u @ v)\<close>
proof -
  from assms(1) obtain r \<rho> where \<open>u = p @ r\<close> \<open>\<rho> \<in> set rs\<close> \<open>match_rule \<rho> p\<close>
    by (blast dest: max_prefD)
  show ?thesis
  proof (rule max_prefI[of \<open>u @ v\<close> p \<open>r @ v\<close> \<rho> rs])
    show \<open>u @ v = p @ r @ v\<close>
      using \<open>u = p @ r\<close> by simp
  next
    fix p' u' \<rho>'
    assume \<open>u @ v = p' @ u'\<close> \<open>length p < length p'\<close> \<open>\<rho>' \<in> set rs\<close>
    from \<open>u @ v = p' @ u'\<close> obtain us where \<open>u = p' @ us \<and> us @ v = u' \<or> u @ us = p' \<and> v = us @ u'\<close>
      unfolding append_eq_append_conv2 by blast
    then show \<open>\<not> match_rule \<rho>' p'\<close>
    proof
      assume \<open>u = p' @ us \<and> us @ v = u'\<close>
      then show ?thesis
        using max_pref_longest[OF assms(1), of p' us \<rho>'] \<open>length p < length p'\<close> \<open>\<rho>' \<in> set rs\<close>
        by blast
    next
      assume \<open>u @ us = p' \<and> v = us @ u'\<close>
      then show ?thesis
        using max_pref_longest[OF assms(1), of p' \<open>[]\<close> \<rho>'] \<open>length p < length p'\<close>
          \<open>\<rho>' \<in> set rs\<close> assms(2)[of us u' \<rho>']
        by (cases \<open>us = []\<close>) auto
    qed
  qed fact+
qed

lemma first_token_append:
  assumes \<open>first_token rs i p u\<close>
    and \<open>\<And>w t \<rho>. v = w @ t \<Longrightarrow> w \<noteq> [] \<Longrightarrow> \<rho> \<in> set rs \<Longrightarrow> \<not> match_rule \<rho> (u @ w)\<close>
  shows \<open>first_token rs i p (u @ v)\<close>
proof -
  from assms(1) have \<open>max_pref rs p u\<close> \<open>i < length rs\<close> \<open>match_rule (rs ! i) p\<close>
    \<open>\<forall>j < i. \<not> match_rule (rs ! j) p\<close>
    by (auto elim: first_token.cases)
  moreover from \<open>max_pref rs p u\<close> assms(2) have \<open>max_pref rs p (u @ v)\<close>
    by (rule max_pref_append)
  ultimately show ?thesis
    by (blast intro: first_tokenI)
qed

lemma last_accept_append:
  assumes \<open>last_accept rs u b\<close>
    and \<open>\<And>w t \<rho>. v = w @ t \<Longrightarrow> w \<noteq> [] \<Longrightarrow> \<rho> \<in> set rs \<Longrightarrow> \<not> match_rule \<rho> (u @ w)\<close>
  shows \<open>last_accept rs (u @ v) b\<close>
proof (cases b)
  case None
  moreover have \<open>\<not> match_rule \<rho> p\<close> if \<open>u @ v = p @ t\<close> \<open>\<rho> \<in> set rs\<close> for p t \<rho>
  proof -
    from \<open>u @ v = p @ t\<close> obtain us where \<open>u = p @ us \<and> us @ v = t \<or> u @ us = p \<and> v = us @ t\<close>
      unfolding append_eq_append_conv2 by blast
    then show ?thesis
    proof
      assume \<open>u = p @ us \<and> us @ v = t\<close>
      with assms(1) None \<open>\<rho> \<in> set rs\<close> show ?thesis
        by (auto simp: last_accept_def)
    next
      assume \<open>u @ us = p \<and> v = us @ t\<close>
      with assms None \<open>\<rho> \<in> set rs\<close> show ?thesis
        by (cases \<open>us = []\<close>) (auto simp: last_accept_def)
    qed
  qed
  ultimately show ?thesis by (simp add: last_accept_def)
next
  case (Some a)
  then obtain i n where \<open>b = Some (i, n)\<close>
    by (cases a) auto
  with assms(1) have \<open>n \<le> length u\<close> \<open>first_token rs i (take n u) u\<close>
    by (simp_all add: last_accept_def)
  with \<open>b = Some (i, n)\<close> show ?thesis
    using first_token_append[OF \<open>first_token rs i (take n u) u\<close> assms(2)]
    by (simp add: last_accept_def)
qed

text \<open>On a nonempty word, the acceptance of the state reached says which rules match it:\<close>

lemma no_match_iff_acc_None:
  \<open>w \<noteq> [] \<Longrightarrow>
    (\<forall>\<rho> \<in> set rs. \<not> match_rule \<rho> w) \<longleftrightarrow> acc (foldl delta_char (init_state rs) w) = None\<close>
  by (auto simp: acc_foldl_delta_char_None_iff match_rule.simps in_set_conv_nth) (metis nth_mem)

lemma first_token_self_if_acc:
  assumes \<open>w \<noteq> []\<close> \<open>acc (foldl delta_char (init_state rs) w) = Some i\<close>
  shows \<open>first_token rs i w w\<close>
proof -
  from assms have \<open>i < length rs\<close> \<open>match_rule (rs ! i) w\<close> \<open>\<forall>j < i. \<not> match_rule (rs ! j) w\<close>
    using acc_foldl_delta_char_match_rule[OF assms(1), of rs i] by blast+
  moreover have \<open>max_pref rs w w\<close>
    by (rule max_prefI[of w w \<open>[]\<close> \<open>rs ! i\<close> rs]) (use calculation in auto)
  ultimately show ?thesis
    by (blast intro: first_tokenI)
qed

end

subsection \<open>The scan keeps the invariant\<close>

context eba
begin

text \<open>A classifier sends every character to a minterm of the mode that holds for it.
  \<^const>\<open>minterm_index\<close> is one. The run-time lexer uses a table:\<close>

definition minterm_classifier :: \<open>('k, 'p, 'ch, 'm) rule list \<Rightarrow> ('ch \<Rightarrow> nat) \<Rightarrow> bool\<close> where
  \<open>minterm_classifier rs cls \<longleftrightarrow>
    (\<forall>c. cls c < length (mode_minterms rs) \<and> sem (snd (mode_minterms rs ! cls c)) c)\<close>

lemma minterm_classifier_minterm_index: \<open>minterm_classifier rs (minterm_index rs)\<close>
  by (simp add: minterm_classifier_def minterm_index)

text \<open>The dead state is the index of the empty state. If the empty state is not
  explored, the index is out of range and never reached:\<close>

definition dead_state :: \<open>('k, 'p, 'ch, 'm) rule list \<Rightarrow> nat\<close> where
  \<open>dead_state rs = index_of (dfa_states (mode_dfa rs)) {}\<close>

definition run_dfa ::
  \<open>('k, 'p, 'ch, 'm) rule list \<Rightarrow> ('ch \<Rightarrow> nat) \<Rightarrow> 'ch list \<Rightarrow>
    (nat \<times> 'ch list \<times> 'ch list) option\<close>
where
  \<open>run_dfa rs cls =
    run_tables (dfa_trans (mode_dfa rs)) (dfa_accept (mode_dfa rs)) cls (dead_state rs)\<close>

text \<open>A transition through the classifier is the step by the character
  (@{thm [source] delta_eq_delta_char}):\<close>

lemma trans_step:
  assumes \<open>minterm_classifier rs cls\<close> \<open>q < length (dfa_states (mode_dfa rs))\<close>
  shows \<open>dfa_trans (mode_dfa rs) ! q ! cls c < length (dfa_states (mode_dfa rs)) \<and>
    dfa_states (mode_dfa rs) ! (dfa_trans (mode_dfa rs) ! q ! cls c) =
      delta_char (dfa_states (mode_dfa rs) ! q) c\<close>
proof -
  let ?M = \<open>mode_minterms rs\<close>
  let ?Q = \<open>dfa_states (mode_dfa rs)\<close>
  let ?k = \<open>cls c\<close>
  let ?q' = \<open>dfa_trans (mode_dfa rs) ! q ! ?k\<close>

  from assms(1) have k: \<open>?k < length ?M\<close> \<open>sem (snd (?M ! ?k)) c\<close>
    unfolding minterm_classifier_def by blast+
  have q': \<open>?q' < length ?Q \<and> ?Q ! ?q' = delta (?Q ! q) (fst (?M ! ?k))\<close>
    using dfa_trans_correct[of q \<open>map fst ?M\<close> rs ?k] assms(2) k(1)
    by (simp add: mode_dfa_def)
  have \<open>?Q ! q \<subseteq> tagged_closure rs\<close>
    using dfa_states_subset[OF nth_mem[OF assms(2)[unfolded mode_dfa_def]]]
    by (simp add: mode_dfa_def)
  moreover have \<open>(fst (?M ! ?k), snd (?M ! ?k)) \<in> set ?M\<close>
    using k(1) by simp
  ultimately have \<open>delta (?Q ! q) (fst (?M ! ?k)) = delta_char (?Q ! q) c\<close>
    using k(2) by (rule delta_eq_delta_char)
  with q' show ?thesis
    by simp
qed

text \<open>The invariant holds after every character the scan reads. At the dead state no
  extension of the input read so far is matched, so stopping there keeps it too:\<close>

lemma scan_last_accept:
  assumes \<open>minterm_classifier rs cls\<close>
    and \<open>q < length (dfa_states (mode_dfa rs))\<close>
    and \<open>dfa_states (mode_dfa rs) ! q = foldl delta_char (init_state rs) u\<close>
    and \<open>last_accept rs u b\<close>
  shows \<open>last_accept rs (u @ v)
    (scan (dfa_trans (mode_dfa rs)) (dfa_accept (mode_dfa rs)) cls (dead_state rs)
      q (length u) v b)\<close>
  using assms(2-)
proof (induct v arbitrary: q u b)
  case (Cons c v)
  let ?Q = \<open>dfa_states (mode_dfa rs)\<close>
  let ?q' = \<open>dfa_trans (mode_dfa rs) ! q ! cls c\<close>
  let ?X = \<open>foldl delta_char (init_state rs) (u @ [c])\<close>
  from trans_step[OF assms(1) Cons.prems(1), of c] Cons.prems(2)
  have q': \<open>?q' < length ?Q\<close> \<open>?Q ! ?q' = ?X\<close>
    by simp_all
  show ?case
  proof (cases \<open>?q' = dead_state rs\<close>)
    case True
    with q' have \<open>?X = {}\<close>
      by (metis dead_state_def nth_index_of_if_less)
    have \<open>\<not> match_rule \<rho> (u @ w)\<close> if \<open>c # v = w @ t\<close> \<open>w \<noteq> []\<close> \<open>\<rho> \<in> set rs\<close> for w t \<rho>
    proof -
      from that(1,2) obtain w' where \<open>w = c # w'\<close>
        by (cases w) auto
      with \<open>?X = {}\<close> have \<open>acc (foldl delta_char (init_state rs) (u @ w)) = None\<close>
        by (simp add: acc_def)
      with \<open>w \<noteq> []\<close> \<open>\<rho> \<in> set rs\<close> show ?thesis
        using no_match_iff_acc_None[of \<open>u @ w\<close> rs] by simp
    qed
    then have \<open>last_accept rs (u @ c # v) b\<close>
      by (rule last_accept_append[OF Cons.prems(3)])
    with True show ?thesis
      by simp
  next
    case False
    let ?b' = \<open>case dfa_accept (mode_dfa rs) ! ?q' of None \<Rightarrow> b | Some i \<Rightarrow> Some (i, Suc (length u))\<close>
    have \<open>dfa_accept (mode_dfa rs) ! ?q' = acc ?X\<close>
      using q' by (simp add: dfa_accept_eq mode_dfa_def)
    have \<open>last_accept rs (u @ [c]) ?b'\<close>
    proof (cases \<open>acc ?X\<close>)
      case None
      then have \<open>\<not> match_rule \<rho> (u @ [c])\<close> if \<open>\<rho> \<in> set rs\<close> for \<rho>
        using no_match_iff_acc_None[of \<open>u @ [c]\<close> rs] that by simp
      then have \<open>last_accept rs (u @ [c]) b\<close>
        by (intro last_accept_append[OF Cons.prems(3)]) (auto simp: Cons_eq_append_conv)
      with None \<open>dfa_accept (mode_dfa rs) ! ?q' = acc ?X\<close> show ?thesis
        by simp
    next
      case (Some i)
      then have \<open>first_token rs i (u @ [c]) (u @ [c])\<close>
        by (intro first_token_self_if_acc) simp_all
      with Some \<open>dfa_accept (mode_dfa rs) ! ?q' = acc ?X\<close> show ?thesis
        by (simp add: last_accept_def)
    qed
    from Cons.hyps[OF q'(1) q'(2) this] False show ?thesis
      by (simp add: Let_def)
  qed
qed simp

lemma last_accept_scan:
  assumes \<open>minterm_classifier rs cls\<close>
  shows \<open>last_accept rs s
    (scan (dfa_trans (mode_dfa rs)) (dfa_accept (mode_dfa rs)) cls (dead_state rs) 0 0 s None)\<close>
proof -
  have \<open>0 < length (dfa_states (mode_dfa rs))\<close>
    \<open>dfa_states (mode_dfa rs) ! 0 = foldl delta_char (init_state rs) []\<close>
    using dfa_run_correct[of rs \<open>[]\<close>] by (simp_all add: dfa_run_def)
  from scan_last_accept[OF assms this last_accept_Nil, of s] show ?thesis
    by simp
qed

lemma run_dfa_sound:
  assumes \<open>minterm_classifier rs cls\<close> \<open>run_dfa rs cls s = Some (i, p, rest)\<close>
  shows \<open>first_token rs i p s \<and> s = p @ rest\<close>
proof -
  from assms(2) obtain n where
    \<open>scan (dfa_trans (mode_dfa rs)) (dfa_accept (mode_dfa rs)) cls (dead_state rs) 0 0 s None =
      Some (i, n)\<close> \<open>p = take n s\<close> \<open>rest = drop n s\<close>
    by (auto simp: run_dfa_def run_tables_def)
  with last_accept_scan[OF assms(1), of s] show ?thesis
    by (simp add: last_accept_def)
qed

lemma run_dfa_None_no_first_token:
  assumes \<open>minterm_classifier rs cls\<close> \<open>run_dfa rs cls s = None\<close>
  shows \<open>\<not> first_token rs i p s\<close>
proof
  assume \<open>first_token rs i p s\<close>
  then obtain u \<rho> where \<open>s = p @ u\<close> \<open>\<rho> \<in> set rs\<close> \<open>match_rule \<rho> p\<close>
    by (blast dest: first_token_max_pref max_prefD)
  moreover from assms have
    \<open>last_accept rs s None\<close>
    using last_accept_scan[OF assms(1), of s] by (simp add: run_dfa_def run_tables_def)
  ultimately show False
    by (auto simp: last_accept_def)
qed

section \<open>Surface theorems\<close>

text \<open>With any classifier into the minterms of the mode, the runner returns exactly the
  winning rule and lexeme of \<^const>\<open>first_token\<close>, and fails exactly when no rule
  matches a nonempty prefix. For one step, this is Verbatim's soundness and completeness
  \<^cite>\<open>\<open>Sects.~V-A, V-C\<close> in "egolf2021-verbatim-verified-lexer"\<close>, which Verbatim
  proves for derivatives, not for a DFA:\<close>

theorem run_dfa_Some_iff:
  assumes \<open>minterm_classifier rs cls\<close>
  shows \<open>run_dfa rs cls s = Some (i, p, rest) \<longleftrightarrow> first_token rs i p s \<and> s = p @ rest\<close>
proof
  assume \<open>run_dfa rs cls s = Some (i, p, rest)\<close>
  with assms show \<open>first_token rs i p s \<and> s = p @ rest\<close>
    by (rule run_dfa_sound)
next
  assume \<open>first_token rs i p s \<and> s = p @ rest\<close>
  then have \<open>first_token rs i p s\<close> \<open>s = p @ rest\<close>
    by blast+
  show \<open>run_dfa rs cls s = Some (i, p, rest)\<close>
  proof (cases \<open>run_dfa rs cls s\<close>)
    case None
    with assms \<open>first_token rs i p s\<close> show ?thesis
      by (blast dest: run_dfa_None_no_first_token)
  next
    case (Some x)
    then obtain i' p' rest' where \<open>run_dfa rs cls s = Some (i', p', rest')\<close>
      by (cases x) auto
    moreover from run_dfa_sound[OF assms this] have \<open>first_token rs i' p' s\<close> \<open>s = p' @ rest'\<close>
      by blast+
    moreover from first_token_deterministic[OF \<open>first_token rs i' p' s\<close> \<open>first_token rs i p s\<close>]
    have \<open>i' = i\<close> \<open>p' = p\<close>
      by simp_all
    ultimately show ?thesis
      using \<open>s = p @ rest\<close> by simp
  qed
qed

theorem run_dfa_None_iff:
  assumes \<open>minterm_classifier rs cls\<close>
  shows \<open>run_dfa rs cls s = None \<longleftrightarrow> (\<nexists>i p. first_token rs i p s)\<close>
proof
  assume \<open>run_dfa rs cls s = None\<close>
  with assms show \<open>\<nexists>i p. first_token rs i p s\<close>
    by (blast dest: run_dfa_None_no_first_token)
next
  assume \<open>\<nexists>i p. first_token rs i p s\<close>
  then show \<open>run_dfa rs cls s = None\<close>
    using run_dfa_Some_iff[OF assms] by (cases \<open>run_dfa rs cls s\<close>) auto
qed

end

end
