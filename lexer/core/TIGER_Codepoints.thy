(* Author: Basil Fürer *)

theory TIGER_Codepoints
  imports TIGER_Tables "HOL-Library.Code_Target_Nat"
begin

section \<open>The codepoint instance\<close>

text \<open>Codepoints are natural numbers, and the range is
  \<open>0 .. 0x10FFFF\<close>. Surrogates are in the range: excluding them is the business of the
  decoder. As \<^typ>\<open>nat\<close> is unbounded, character classes are no Boolean algebra on it
  (the negation of a class holds of no number above the range). We read a class at the
  number clamped to the range instead, so a number above the range lexes as
  \<open>U+10FFFF\<close>, and prove that on an input in range this reading is the plain one
  (\<^const>\<open>in_cls\<close>).

  Generated code represents \<^typ>\<open>nat\<close> by target integers (\<open>Code_Target_Nat\<close>):
  in the default unary representation \<open>0x10FFFF\<close> alone has a million constructors.

  The lexer \<open>cp_lexer\<close> takes the tables of the modes as one array and a
  mode index into it, so modes with the same rules share their tables. Its surface
  theorems hold for every index under which each mode finds its tables. A spec on
  codepoints is read on bytes by \<open>char_spec\<close>, which keeps the part of each
  class below \<open>0x100\<close>.\<close>

subsection \<open>Classes read in the range\<close>

locale range_order = discrete_order bot top succ pred
  for bot top :: \<open>'ch::linorder\<close> and succ pred
begin

definition clamp :: \<open>'ch \<Rightarrow> 'ch\<close> where
  \<open>clamp c = (if c < bot then bot else if top < c then top else c)\<close>

definition in_clamped :: \<open>'ch cls \<Rightarrow> 'ch \<Rightarrow> bool\<close> where
  \<open>in_clamped p c \<longleftrightarrow> in_cls p (clamp c)\<close>

definition sat_clamped :: \<open>'ch cls \<Rightarrow> bool\<close> where
  \<open>sat_clamped p \<longleftrightarrow> sat_cls (clip p)\<close>

lemma clamp_in_range: \<open>bot \<le> clamp c \<and> clamp c \<le> top\<close>
  using bot_le_top by (auto simp: clamp_def)

lemma clamp_id: \<open>\<lbrakk> bot \<le> c; c \<le> top \<rbrakk> \<Longrightarrow> clamp c = c\<close>
  by (auto simp: clamp_def)

lemma in_clamped_iff: \<open>\<lbrakk> bot \<le> c; c \<le> top \<rbrakk> \<Longrightarrow> in_clamped p c \<longleftrightarrow> in_cls p c\<close>
  by (simp add: in_clamped_def clamp_id)

text \<open>Read in the range, classes form an effective Boolean algebra:\<close>

sublocale eba in_clamped cls_top cls_bot cls_conj cls_disj cls_neg sat_clamped
proof unfold_locales
  fix p
  show \<open>sat_clamped p \<longleftrightarrow> (\<exists>c. in_clamped p c)\<close>
    using clamp_in_range clamp_id
    by (auto simp: sat_clamped_def in_clamped_def sat_cls_iff in_cls_clip) metis
qed (simp_all add: in_clamped_def clamp_in_range in_cls_top in_cls_bot in_cls_conj in_cls_disj
    in_cls_neg)

end

subsection \<open>Semantics that agree on the input\<close>

text \<open>The judgments read the denotation only at the characters of the input. Two
  denotations that agree there give the same lexing:\<close>

lemma star_cong:
  assumes \<open>\<And>w. set w \<subseteq> A \<Longrightarrow> w \<in> L \<longleftrightarrow> w \<in> L'\<close> \<open>w \<in> star L\<close> \<open>set w \<subseteq> A\<close>
  shows \<open>w \<in> star L'\<close>
  using assms(2,3) by induct (auto simp: assms(1))

lemma conc_cong:
  assumes \<open>\<And>w. set w \<subseteq> A \<Longrightarrow> w \<in> L1 \<longleftrightarrow> w \<in> L1'\<close> \<open>\<And>w. set w \<subseteq> A \<Longrightarrow> w \<in> L2 \<longleftrightarrow> w \<in> L2'\<close>
    and \<open>set w \<subseteq> A\<close>
  shows \<open>w \<in> L1 @@ L2 \<longleftrightarrow> w \<in> L1' @@ L2'\<close>
proof
  assume \<open>w \<in> L1 @@ L2\<close>
  then obtain u v where \<open>w = u @ v\<close> \<open>u \<in> L1\<close> \<open>v \<in> L2\<close>
    by blast
  with assms show \<open>w \<in> L1' @@ L2'\<close>
    by auto
next
  assume \<open>w \<in> L1' @@ L2'\<close>
  then obtain u v where \<open>w = u @ v\<close> \<open>u \<in> L1'\<close> \<open>v \<in> L2'\<close>
    by blast
  with assms show \<open>w \<in> L1 @@ L2\<close>
    by auto
qed

lemma lang_cong:
  assumes \<open>\<And>p c. c \<in> A \<Longrightarrow> sem p c = sem' p c\<close> \<open>set w \<subseteq> A\<close>
  shows \<open>w \<in> symbolic.lang sem r \<longleftrightarrow> w \<in> symbolic.lang sem' r\<close>
  using assms(2)
proof (induction r arbitrary: w)
  case (Atom p)
  then show ?case
    by (auto simp: assms(1) symbolic.lang.simps)
next
  case (Times r1 r2)
  then show ?case
    using conc_cong[of A \<open>symbolic.lang sem r1\<close> \<open>symbolic.lang sem' r1\<close>
      \<open>symbolic.lang sem r2\<close> \<open>symbolic.lang sem' r2\<close> w]
    by (simp add: symbolic.lang.simps)
next
  case (Star r)
  then show ?case
    using star_cong[of A \<open>symbolic.lang sem r\<close> \<open>symbolic.lang sem' r\<close> w]
      star_cong[of A \<open>symbolic.lang sem' r\<close> \<open>symbolic.lang sem r\<close> w]
    by (auto simp: symbolic.lang.simps)
qed (auto simp: symbolic.lang.simps)

text \<open>In the rest of this subsection \<open>sem\<close> and \<open>sem'\<close> agree on \<open>A\<close>:\<close>

context
  fixes A and sem sem' :: \<open>'p \<Rightarrow> 'ch \<Rightarrow> bool\<close>
  assumes agree: \<open>\<And>p c. c \<in> A \<Longrightarrow> sem p c = sem' p c\<close>
begin

lemma match_rule_cong:
  \<open>set w \<subseteq> A \<Longrightarrow> symbolic.match_rule sem \<rho> w \<longleftrightarrow> symbolic.match_rule sem' \<rho> w\<close>
  using lang_cong[where A = A and sem = sem and sem' = sem', OF agree]
  by (simp add: symbolic.match_rule.simps)

lemma max_pref_cong:
  assumes \<open>set s \<subseteq> A\<close>
  shows \<open>symbolic.max_pref sem (rs :: ('k, 'p, 'ch, 'm) rule list) p s \<longleftrightarrow>
    symbolic.max_pref sem' rs p s\<close>
proof -
  have mr: \<open>symbolic.match_rule sem \<rho>' p' \<longleftrightarrow> symbolic.match_rule sem' \<rho>' p'\<close>
    if \<open>s = p' @ u'\<close> for \<rho>' :: \<open>('k, 'p, 'ch, 'm) rule\<close> and p' u'
    using match_rule_cong[of p'] that assms by simp
  show ?thesis
    unfolding symbolic.max_pref.simps by (metis mr)
qed

lemma first_token_cong:
  assumes \<open>set s \<subseteq> A\<close>
  shows \<open>symbolic.first_token sem (rs :: ('k, 'p, 'ch, 'm) rule list) i p s \<longleftrightarrow>
    symbolic.first_token sem' rs i p s\<close>
proof -
  have \<open>set p \<subseteq> A\<close> if \<open>\<exists>u. s = p @ u\<close>
    using that assms by auto
  then have \<open>(\<exists>u. s = p @ u) \<Longrightarrow>
      symbolic.match_rule sem \<rho> p \<longleftrightarrow> symbolic.match_rule sem' \<rho> p\<close>
    for \<rho> :: \<open>('k, 'p, 'ch, 'm) rule\<close>
    using match_rule_cong by blast
  then show ?thesis
    using max_pref_cong[OF assms] symbolic.max_prefD[of sem rs p s]
      symbolic.max_prefD[of sem' rs p s]
    unfolding symbolic.first_token.simps by metis
qed

lemma step_cong:
  assumes \<open>set s \<subseteq> A\<close>
  shows \<open>symbolic.step sem sp st s x \<longleftrightarrow> symbolic.step sem' sp st s x\<close>
  by (simp add: symbolic.step.simps first_token_cong[OF assms])

lemma lexes_cong_imp:
  assumes \<open>symbolic.lexes sem sp is_newline st q s l r st\<^sub>f\<close> \<open>set s \<subseteq> A\<close>
  shows \<open>symbolic.lexes sem' sp is_newline st q s l r st\<^sub>f\<close>
  using assms
proof (induction rule: symbolic.lexes.induct[of sem, consumes 1, case_names stop token trivia])
  case (stop st s q)
  then have \<open>\<not> symbolic.step sem' sp st s x\<close> for x
    using step_cong[of s sp st x] by blast
  then show ?case
    by (rule symbolic.lexes_stop)
next
  case (token st s k p st' s' q h ts r st\<^sub>f)
  from token.hyps(1) token.prems have \<open>set s' \<subseteq> A\<close>
    by (auto simp: symbolic.step.simps)
  from token.hyps(1) have \<open>symbolic.step sem' sp st s (Some k, p, st', s')\<close>
    by (simp add: step_cong[OF token.prems])
  from this token.IH[OF \<open>set s' \<subseteq> A\<close>] show ?case
    by (rule symbolic.lexes_token)
next
  case (trivia st s p st' s' q h ts r st\<^sub>f)
  from trivia.hyps(1) trivia.prems have \<open>set s' \<subseteq> A\<close>
    by (auto simp: symbolic.step.simps)
  from trivia.hyps(1) have \<open>symbolic.step sem' sp st s (None, p, st', s')\<close>
    by (simp add: step_cong[OF trivia.prems])
  from this trivia.IH[OF \<open>set s' \<subseteq> A\<close>] show ?case
    by (rule symbolic.lexes_trivia)
qed

end

lemma lexes_cong:
  assumes \<open>\<And>p c. c \<in> A \<Longrightarrow> sem p c = sem' p c\<close> \<open>set s \<subseteq> A\<close>
  shows \<open>symbolic.lexes sem sp is_newline st q s l r st\<^sub>f \<longleftrightarrow>
    symbolic.lexes sem' sp is_newline st q s l r st\<^sub>f\<close>
  using lexes_cong_imp[of A sem sem'] lexes_cong_imp[of A sem' sem] assms by (metis (no_types))

context range_order
begin

lemma wf_minterms: \<open>(S, \<mu>) \<in> set (minterms P) \<Longrightarrow> wf_cls \<mu>\<close>
  by (induct P arbitrary: S \<mu>) (auto simp: wf_top wf_conj)

text \<open>The lookup of the clamped character in the minterm table of a mode is a
  classifier into its minterms. Above the range it is the class of \<open>top\<close>:\<close>

lemma minterm_classifier_class_of_clamp:
  \<open>minterm_classifier rs (\<lambda>c. class_of (IArray (class_table (mode_minterms rs))) (clamp c))\<close>
  unfolding minterm_classifier_def
proof
  fix c
  let ?M = \<open>mode_minterms rs\<close>
  have wf: \<open>wf_cls (snd (?M ! k))\<close> if \<open>k < length ?M\<close> for k
    using wf_minterms nth_mem[OF that] by (metis mode_minterms_def prod.collapse)
  have disj: \<open>i = j\<close>
    if \<open>i < length ?M\<close> \<open>j < length ?M\<close> \<open>in_cls (snd (?M ! i)) d\<close> \<open>in_cls (snd (?M ! j)) d\<close>
    for i j d
  proof -
    from that(1,3) wf[of i] have \<open>bot \<le> d\<close> \<open>d \<le> top\<close>
      by (auto simp: wf_cls_def in_range_iff in_cls_iff)
    with that minterms_disjoint show ?thesis
      by (metis in_clamped_iff mode_minterms_def)
  qed
  obtain S \<mu> where \<open>(S, \<mu>) \<in> set ?M\<close> \<open>in_clamped \<mu> c\<close>
    using minterms_cover[of \<open>mode_atoms rs\<close> c] by (auto simp: mode_minterms_def)
  then obtain k where \<open>k < length ?M\<close> \<open>in_cls (snd (?M ! k)) (clamp c)\<close>
    by (metis in_set_conv_nth snd_conv in_clamped_def)
  from class_of_partition[OF wf disj this]
  show \<open>class_of (IArray (class_table ?M)) (clamp c) < length ?M \<and>
    in_clamped (snd (?M ! class_of (IArray (class_table ?M)) (clamp c))) c\<close>
    by (simp add: in_clamped_def)
qed

end

subsection \<open>The interpretation\<close>

global_interpretation cp_cls: range_order \<open>0::nat\<close> \<open>0x10FFFF\<close> Suc \<open>\<lambda>c. c - 1\<close>
  defines cp_clamp = cp_cls.clamp
    and cp_clip = cp_cls.clip
    and cp_sat = cp_cls.sat_clamped
    and cp_merge = cp_cls.merge
    and cp_norm = cp_cls.cls_norm
    and cp_compl_from = cp_cls.compl_from
    and cp_top = cp_cls.cls_top
    and cp_disj = cp_cls.cls_disj
    and cp_neg = cp_cls.cls_neg
    and cp_conj = cp_cls.cls_conj
    and cp_minterms = cp_cls.minterms
    and cp_mode_minterms = cp_cls.mode_minterms
    and cp_mode_dfa = cp_cls.mode_dfa
    and cp_dead_state = cp_cls.dead_state
  by unfold_locales auto

text \<open>As for bytes, we fold the defined constants into the generator's equations by
  hand:\<close>

lemmas cp_sat_code[code] =
  cp_cls.sat_clamped_def[folded cp_clip_def cp_sat_def]

lemmas cp_minterms_code[code] =
  cp_cls.minterms.simps[unfolded cp_top_def cp_conj_def cp_neg_def cp_sat_def,
    folded cp_minterms_def cp_top_def cp_conj_def cp_neg_def cp_sat_def]

lemmas cp_mode_minterms_code[code] =
  cp_cls.mode_minterms_def[unfolded cp_top_def cp_conj_def cp_neg_def cp_sat_def,
    folded cp_mode_minterms_def cp_minterms_def cp_top_def cp_conj_def cp_neg_def cp_sat_def]

lemmas cp_mode_dfa_code[code] =
  cp_cls.mode_dfa_def[unfolded cp_top_def cp_conj_def cp_neg_def cp_sat_def,
    folded cp_mode_dfa_def cp_mode_minterms_def cp_top_def cp_conj_def cp_neg_def cp_sat_def]

lemmas cp_dead_state_code[code] =
  cp_cls.dead_state_def[unfolded cp_top_def cp_conj_def cp_neg_def cp_sat_def,
    folded cp_dead_state_def cp_mode_dfa_def cp_top_def cp_conj_def cp_neg_def cp_sat_def]

lemma cp_mode_minterms_eq: \<open>cp_mode_minterms = cp_cls.mode_minterms\<close>
  by (simp add: cp_mode_minterms_def cp_top_def cp_conj_def cp_neg_def cp_sat_def)

lemma cp_mode_dfa_eq: \<open>cp_mode_dfa = cp_cls.mode_dfa\<close>
  by (simp add: cp_mode_dfa_def cp_top_def cp_conj_def cp_neg_def cp_sat_def)

lemma cp_dead_state_eq: \<open>cp_dead_state = cp_cls.dead_state\<close>
  by (simp add: cp_dead_state_def cp_top_def cp_conj_def cp_neg_def cp_sat_def)

text \<open>Above the range, the classifier reads a number as \<open>U+10FFFF\<close>:\<close>

lemma cp_clamp_eq: \<open>cp_clamp c = min c 0x10FFFF\<close>
  by (simp add: cp_cls.clamp_def)

subsection \<open>Tables and the lexer\<close>

text \<open>The tables of a mode on codepoints, as for bytes:\<close>

type_synonym cp_tables = \<open>(nat \<times> nat \<times> nat) iarray \<times> nat iarray iarray \<times> nat option iarray \<times> nat\<close>

definition cp_tables :: \<open>('k, nat cls, nat, 'm) rule list \<Rightarrow> cp_tables\<close> where
  \<open>cp_tables rs = (IArray (class_table (cp_mode_minterms rs)),
    IArray (map IArray (dfa_trans (cp_mode_dfa rs))), IArray (dfa_accept (cp_mode_dfa rs)),
    cp_dead_state rs)\<close>

text \<open>The sizes of the tables of a mode, on codepoints or bytes: the intervals of the class
  table, the minterms (the columns of the transitions) and the states:\<close>

definition table_size :: \<open>'c iarray \<times> 'n iarray iarray \<times> 'a \<times> 'd \<Rightarrow> nat \<times> nat \<times> nat\<close> where
  \<open>table_size t = (case t of (C, T, A, d) \<Rightarrow>
     (IArray.length C, IArray.length (T !! 0), IArray.length T))\<close>

fun run_cp :: \<open>cp_tables \<Rightarrow> nat list \<Rightarrow> (nat \<times> nat list \<times> nat list) option\<close> where
  \<open>run_cp (C, T, A, d) = run_tables_ia T A (\<lambda>c. class_of C (cp_clamp c)) d\<close>

lemma run_cp_tables:
  \<open>run_cp (cp_tables rs) =
    cp_cls.run_dfa rs (\<lambda>c. class_of (IArray (class_table (cp_cls.mode_minterms rs))) (cp_clamp c))\<close>
  by (simp add: fun_eq_iff cp_tables_def cp_mode_minterms_eq cp_mode_dfa_eq cp_dead_state_eq
      cp_cls.run_tables_ia_eq_run_dfa cp_cls.minterm_classifier_class_of_clamp)

text \<open>The lexer on codepoints takes the tables of all modes as one array and an index
  \<open>ix\<close> into it for each mode, so modes with the same rules share their tables and the
  driver never compares modes. A mode whose index is outside the array has no rules:\<close>

definition cp_lexer ::
  \<open>cp_tables iarray \<Rightarrow> ('m \<Rightarrow> nat) \<Rightarrow> ('k, nat cls, nat, 'm) lexer_spec \<Rightarrow> (nat \<Rightarrow> bool) \<Rightarrow>
    'm list \<Rightarrow> pos \<Rightarrow> nat list \<Rightarrow> ('k, nat) lexed \<times> nat list \<times> 'm list\<close>
where
  \<open>cp_lexer TT ix =
    drive (\<lambda>m. if ix m < IArray.length TT then run_cp (TT !! ix m) else (\<lambda>_. None))\<close>

text \<open>The runner of \<^const>\<open>cp_lexer\<close> runs the modes of \<open>sp\<close> if the index of each mode
  holds its tables or is outside the array for a mode without rules:\<close>

lemma mode_runner_cp_lexer:
  assumes \<open>\<And>m. if ix m < IArray.length TT then TT !! ix m = cp_tables (sp m) else sp m = []\<close>
  shows \<open>cp_cls.mode_runner sp
    (\<lambda>m. if ix m < IArray.length TT then run_cp (TT !! ix m) else (\<lambda>_. None))\<close>
  unfolding cp_cls.mode_runner_def
proof (intro allI)
  fix m s i p rest
  show \<open>(if ix m < IArray.length TT then run_cp (TT !! ix m) else (\<lambda>_. None)) s =
      Some (i, p, rest) \<longleftrightarrow> cp_cls.first_token (sp m) i p s \<and> s = p @ rest\<close>
    using assms[of m]
    by (auto simp: run_cp_tables cp_cls.run_dfa_Some_iff cp_cls.minterm_classifier_class_of_clamp
        cp_cls.first_token.simps split: if_splits)
qed

text \<open>The tables of a spec on the modes \<open>0, \<dots>, n - 1\<close> (\<^const>\<open>list_spec\<close>), with the
  identity as index:\<close>

definition cp_lexer_tables :: \<open>('k, nat cls, nat, nat) rule list list \<Rightarrow> cp_tables iarray\<close> where
  \<open>cp_lexer_tables sps = IArray (map cp_tables sps)\<close>

lemma cp_lexer_tables_index:
  \<open>if id m < IArray.length (cp_lexer_tables sps) then cp_lexer_tables sps !! id m =
    cp_tables (list_spec sps m) else list_spec sps m = []\<close>
  by (simp add: cp_lexer_tables_def list_spec_def)

theorem cp_lexer_list_iff_lexes:
  \<open>cp_lexer (cp_lexer_tables sps) id (list_spec sps) is_newline st q s = (l, r, st\<^sub>f) \<longleftrightarrow>
    cp_cls.lexes (list_spec sps) is_newline st q s l r st\<^sub>f\<close>
  unfolding cp_lexer_def
  by (rule cp_cls.drive_iff_lexes[OF mode_runner_cp_lexer[OF cp_lexer_tables_index]])

theorem cp_lexer_list_iff_lexes_in_range:
  assumes \<open>\<forall>c \<in> set s. c \<le> 0x10FFFF\<close>
  shows \<open>cp_lexer (cp_lexer_tables sps) id (list_spec sps) is_newline st q s = (l, r, st\<^sub>f) \<longleftrightarrow>
    symbolic.lexes in_cls (list_spec sps) is_newline st q s l r st\<^sub>f\<close>
  unfolding cp_lexer_list_iff_lexes
  by (rule lexes_cong[where A = \<open>{.. 0x10FFFF}\<close>]) (use assms in \<open>auto simp: cp_cls.in_clamped_iff\<close>)

subsection \<open>A spec on codepoints read on bytes\<close>

text \<open>A class of codepoints read on bytes is its part below \<open>0x100\<close>. A rule reads its
  lexeme as the codepoints of the bytes:\<close>

definition byte_cls :: \<open>nat cls \<Rightarrow> char cls\<close> where
  \<open>byte_cls ps = [(char_of a, char_of (min b 255)). (a, b) \<leftarrow> ps, a \<le> 255]\<close>

definition char_rule :: \<open>('k, nat cls, nat, 'm) rule \<Rightarrow> ('k, char cls, char, 'm) rule\<close> where
  \<open>char_rule \<rho> = \<lparr>match = map_rexp byte_cls (match \<rho>), act = \<lambda>u. act \<rho> (map of_char u)\<rparr>\<close>

definition char_spec :: \<open>('k, nat cls, nat, 'm) lexer_spec \<Rightarrow> ('k, char cls, char, 'm) lexer_spec\<close>
where
  \<open>char_spec sp m = map char_rule (sp m)\<close>

section \<open>Surface theorems\<close>

text \<open>If the index of each mode holds its tables, the lexer on codepoints is the driver
  of the spec with classes read in the range:\<close>

theorem cp_lexer_iff_lexes:
  assumes \<open>\<forall>m. ix m < IArray.length TT \<and> TT !! ix m = cp_tables (sp m)\<close>
  shows \<open>cp_lexer TT ix sp is_newline st q s = (l, r, st\<^sub>f) \<longleftrightarrow>
    cp_cls.lexes sp is_newline st q s l r st\<^sub>f\<close>
  unfolding cp_lexer_def
  by (rule cp_cls.drive_iff_lexes[OF mode_runner_cp_lexer]) (use assms in auto)

text \<open>On an input in range, it is the driver of the spec with the plain reading
  \<^const>\<open>in_cls\<close> of classes:\<close>

theorem cp_lexer_iff_lexes_in_range:
  assumes \<open>\<forall>m. ix m < IArray.length TT \<and> TT !! ix m = cp_tables (sp m)\<close>
    and \<open>\<forall>c \<in> set s. c \<le> 0x10FFFF\<close>
  shows \<open>cp_lexer TT ix sp is_newline st q s = (l, r, st\<^sub>f) \<longleftrightarrow>
    symbolic.lexes in_cls sp is_newline st q s l r st\<^sub>f\<close>
  unfolding cp_lexer_iff_lexes[OF assms(1)]
  by (rule lexes_cong[where A = \<open>{.. 0x10FFFF}\<close>])
    (use assms(2) in \<open>auto simp: cp_cls.in_clamped_iff\<close>)

end
