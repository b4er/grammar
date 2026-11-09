theory Tables
  imports Driver Intervals "HOL-Library.Char_ord" "HOL-Library.IArray"
begin

section \<open>Tables by evaluation\<close>

text \<open>The generator runs once, at definition time. Its output becomes nullary constants
  whose code equations \<open>eval\<close> produces, and the run-time lexer only indexes them
  \<^cite>\<open>\<open>Sect. 17\<close> in "paxson2026-flex-manual"\<close>. The transition and acceptance
  tables are immutable arrays (\<^typ>\<open>'a iarray\<close>). On the interval instance a character
  finds its minterm by binary search in the intervals of all minterms, sorted by their
  lower ends.

  The correctness of a table is that of its generator, instantiated: the runner on
  arrays is \<^const>\<open>eba.run_dfa\<close> and the classifier is a
  \<^const>\<open>eba.minterm_classifier\<close>, for every spec. No proof looks at a table value.

  The byte instance of the interval algebra is interpreted here, after the generator
  (an interpretation carries only the locale constants defined before it).\<close>

subsection \<open>The runner on arrays\<close>

text \<open>The scan of \<^const>\<open>scan\<close> with array lookups:\<close>

fun scan_ia ::
  \<open>nat iarray iarray \<Rightarrow> nat option iarray \<Rightarrow> ('ch \<Rightarrow> nat) \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow>
    'ch list \<Rightarrow> (nat \<times> nat) option \<Rightarrow> (nat \<times> nat) option\<close>
where
  \<open>scan_ia T A cls d q n [] b = b\<close>
| \<open>scan_ia T A cls d q n (c # v) b =
    (let q' = T !! q !! cls c in
     if q' = d then b
     else scan_ia T A cls d q' (Suc n) v (case A !! q' of None \<Rightarrow> b | Some i \<Rightarrow> Some (i, Suc n)))\<close>

definition run_tables_ia ::
  \<open>nat iarray iarray \<Rightarrow> nat option iarray \<Rightarrow> ('ch \<Rightarrow> nat) \<Rightarrow> nat \<Rightarrow> 'ch list \<Rightarrow>
    (nat \<times> 'ch list \<times> 'ch list) option\<close>
where
  \<open>run_tables_ia T A cls d s =
    map_option (\<lambda>(i, n). (i, take n s, drop n s)) (scan_ia T A cls d 0 0 s None)\<close>

text \<open>The two scans agree as long as no transition leaves the table:\<close>

lemma scan_ia_eq_scan:
  assumes \<open>\<And>q c. q < length T \<Longrightarrow> T ! q ! cls c < length T\<close> \<open>q < length T\<close>
  shows \<open>scan_ia (IArray (map IArray T)) (IArray A) cls d q n s b = scan T A cls d q n s b\<close>
  using assms(2) by (induct s arbitrary: q n b) (simp_all add: Let_def assms(1))

context eba
begin

lemma run_tables_ia_eq_run_dfa:
  assumes \<open>minterm_classifier rs cls\<close>
  shows \<open>run_tables_ia (IArray (map IArray (dfa_trans (mode_dfa rs))))
    (IArray (dfa_accept (mode_dfa rs))) cls (dead_state rs) s = run_dfa rs cls s\<close>
proof -
  let ?T = \<open>dfa_trans (mode_dfa rs)\<close>
  let ?A = \<open>dfa_accept (mode_dfa rs)\<close>
  have len: \<open>length ?T = length (dfa_states (mode_dfa rs))\<close>
    by (simp add: mode_dfa_def length_dfa_trans)
  have \<open>0 < length (dfa_states (mode_dfa rs))\<close>
    using dfa_run_correct[of rs \<open>[]\<close>] by (simp add: dfa_run_def)
  then have \<open>scan_ia (IArray (map IArray ?T)) (IArray ?A) cls (dead_state rs) 0 0 s None =
    scan ?T ?A cls (dead_state rs) 0 0 s None\<close>
    by (intro scan_ia_eq_scan) (use trans_step[OF assms] len in auto)
  then show ?thesis
    by (simp add: run_tables_ia_def run_dfa_def run_tables_def)
qed

end

subsection \<open>Binary search\<close>

text \<open>In an array sorted by first components, the search finds the last entry between
  \<open>l\<close> and \<open>h\<close> whose first component is at most \<open>c\<close>:\<close>

function bsearch :: \<open>('a::linorder \<times> 'b) iarray \<Rightarrow> 'a \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat\<close> where
  \<open>bsearch t c l h =
    (if Suc l < h then
       if fst (t !! ((l + h) div 2)) \<le> c then bsearch t c ((l + h) div 2) h
       else bsearch t c l ((l + h) div 2)
     else l)\<close>
  by pat_completeness auto

termination
  by (relation \<open>measure (\<lambda>(t, c, l, h). h - l)\<close>) auto

declare bsearch.simps[simp del]

lemma bsearch:
  assumes \<open>sorted (map fst (IArray.list_of t))\<close> \<open>l < h\<close> \<open>h \<le> IArray.length t\<close>
    and \<open>fst (t !! l) \<le> c\<close>
  shows \<open>l \<le> bsearch t c l h \<and> bsearch t c l h < h \<and> fst (t !! bsearch t c l h) \<le> c \<and>
    (\<forall>j. bsearch t c l h < j \<longrightarrow> j < h \<longrightarrow> c < fst (t !! j))\<close>
  using assms(2-)
proof (induction \<open>h - l\<close> arbitrary: l h rule: less_induct)
  case less
  let ?m = \<open>(l + h) div 2\<close>
  show ?case
  proof (cases \<open>Suc l < h\<close>)
    case False
    then have \<open>bsearch t c l h = l\<close>
      by (simp add: bsearch.simps)
    with less.prems False show ?thesis
      by auto
  next
    case True
    then have m: \<open>l < ?m\<close> \<open>?m < h\<close>
      by presburger+
    then have d: \<open>h - ?m < h - l\<close> \<open>?m - l < h - l\<close>
      by linarith+
    show ?thesis
    proof (cases \<open>fst (t !! ?m) \<le> c\<close>)
      case True
      with less.hyps[of h ?m] less.prems m d have \<open>?m \<le> bsearch t c ?m h \<and>
        bsearch t c ?m h < h \<and> fst (t !! bsearch t c ?m h) \<le> c \<and>
        (\<forall>j. bsearch t c ?m h < j \<longrightarrow> j < h \<longrightarrow> c < fst (t !! j))\<close>
        by simp
      moreover from True \<open>Suc l < h\<close> have \<open>bsearch t c l h = bsearch t c ?m h\<close>
        by (subst bsearch.simps) simp
      ultimately show ?thesis
        using m by auto
    next
      case False
      have \<open>c < fst (t !! j)\<close> if \<open>?m \<le> j\<close> \<open>j < h\<close> for j
        using False sorted_nth_mono[OF assms(1) that(1)] that(2) less.prems by fastforce
      moreover from False \<open>Suc l < h\<close> have \<open>bsearch t c l h = bsearch t c l ?m\<close>
        by (subst bsearch.simps) simp
      ultimately show ?thesis
        using less.hyps[of ?m l] less.prems m d by (simp, meson not_le)
    qed
  qed
qed

subsection \<open>The minterm table of the interval instance\<close>

text \<open>The minterm table lists every interval of every minterm with the number of its
  minterm, sorted by lower ends. A character looks up the last interval starting at or
  below it:\<close>

definition class_table :: \<open>('s \<times> 'ch::linorder cls) list \<Rightarrow> ('ch \<times> 'ch \<times> nat) list\<close> where
  \<open>class_table M = sort_key fst
    (concat (map (\<lambda>k. map (\<lambda>(l, h). (l, h, k)) (snd (M ! k))) [0 ..< length M]))\<close>

definition class_of :: \<open>('ch::linorder \<times> 'ch \<times> nat) iarray \<Rightarrow> 'ch \<Rightarrow> nat\<close> where
  \<open>class_of t c = snd (snd (t !! bsearch t c 0 (IArray.length t)))\<close>

lemma mem_class_table:
  \<open>x \<in> set (class_table M) \<longleftrightarrow>
    (\<exists>k l h. k < length M \<and> x = (l, h, k) \<and> (l, h) \<in> set (snd (M ! k)))\<close>
  by (force simp: class_table_def)

text \<open>A list of well-formed, pairwise disjoint classes is a partition of the characters
  it covers. The lookup in its table finds the class of each character it covers:\<close>

context discrete_order
begin

text \<open>Two different intervals of a separated class share no character:\<close>

lemma separated_disjoint:
  assumes \<open>separated p\<close> \<open>x \<in> set p\<close> \<open>y \<in> set p\<close> \<open>x \<noteq> y\<close>
    and \<open>fst x \<le> c\<close> \<open>c \<le> snd x\<close> \<open>fst y \<le> c\<close> \<open>c \<le> snd y\<close>
  shows False
proof -
  have sep: \<open>snd (p ! i) < top \<and> succ (snd (p ! i)) < fst (p ! j)\<close>
    if \<open>i < j\<close> \<open>j < length p\<close> for i j
    using assms(1) that by (simp add: separated_def sorted_wrt_iff_nth_less)
  have *: \<open>False\<close> if \<open>u \<in> set p\<close> \<open>w \<in> set p\<close> \<open>u \<noteq> w\<close> \<open>c \<le> snd u\<close> \<open>fst w \<le> c\<close>
    \<open>index_of p u < index_of p w\<close> for u w
  proof -
    from that have \<open>snd u < top\<close> \<open>succ (snd u) < fst w\<close>
      using sep[of \<open>index_of p u\<close> \<open>index_of p w\<close>] index_of_less[of w p] nth_index_of[of u p]
        nth_index_of[of w p]
      by simp_all
    with less_succ[of \<open>snd u\<close>] that(4,5) show False
      by (meson le_less_trans less_le_not_le order.strict_trans)
  qed
  have \<open>index_of p x \<noteq> index_of p y\<close>
    using assms(2-4) by (metis nth_index_of)
  then have \<open>index_of p x < index_of p y \<or> index_of p y < index_of p x\<close>
    by (rule neq_iff[THEN iffD1])
  with *[of x y] *[of y x] assms(2-8) show False
    by blast
qed

text \<open>The intervals of different entries of the table of a partition share no
  character, and each entry is nonempty:\<close>

lemma class_table_disjoint:
  assumes wf: \<open>\<And>k. k < length M \<Longrightarrow> wf_cls (snd (M ! k))\<close>
    and disj: \<open>\<And>i j c. \<lbrakk> i < length M; j < length M; in_cls (snd (M ! i)) c;
      in_cls (snd (M ! j)) c \<rbrakk> \<Longrightarrow> i = j\<close>
    and \<open>x \<in> set (class_table M)\<close> \<open>y \<in> set (class_table M)\<close>
    and \<open>fst x \<le> c\<close> \<open>c \<le> fst (snd x)\<close> \<open>fst y \<le> c\<close> \<open>c \<le> fst (snd y)\<close>
  shows \<open>x = y\<close>
proof -
  from assms(3) obtain k l h where x: \<open>k < length M\<close> \<open>x = (l, h, k)\<close> \<open>(l, h) \<in> set (snd (M ! k))\<close>
    by (auto simp: mem_class_table)
  from assms(4) obtain k' l' h' where
    y: \<open>k' < length M\<close> \<open>y = (l', h', k')\<close> \<open>(l', h') \<in> set (snd (M ! k'))\<close>
    by (auto simp: mem_class_table)
  from x y assms(5-8) have \<open>in_cls (snd (M ! k)) c\<close> \<open>in_cls (snd (M ! k')) c\<close>
    by (auto simp: in_cls_iff intro: bexI[rotated])
  with disj x(1) y(1) have \<open>k' = k\<close>
    by blast
  from wf[OF x(1)] have \<open>separated (snd (M ! k))\<close>
    by (simp add: wf_cls_def)
  with separated_disjoint[of \<open>snd (M ! k)\<close> \<open>(l, h)\<close> \<open>(l', h')\<close> c] x y \<open>k' = k\<close> assms(5-8)
  show \<open>x = y\<close>
    by fastforce
qed

lemma class_table_nonempty:
  assumes wf: \<open>\<And>k. k < length M \<Longrightarrow> wf_cls (snd (M ! k))\<close>
    and \<open>x \<in> set (class_table M)\<close>
  shows \<open>fst x \<le> fst (snd x)\<close>
proof -
  from assms(2) obtain k l h where
    \<open>k < length M\<close> \<open>x = (l, h, k)\<close> \<open>(l, h) \<in> set (snd (M ! k))\<close>
    by (auto simp: mem_class_table)
  with wf[of k] show ?thesis
    by (auto simp: wf_cls_def in_range_iff)
qed

lemma class_of_partition:
  assumes wf: \<open>\<And>k. k < length M \<Longrightarrow> wf_cls (snd (M ! k))\<close>
    and disj: \<open>\<And>i j c. \<lbrakk> i < length M; j < length M; in_cls (snd (M ! i)) c;
      in_cls (snd (M ! j)) c \<rbrakk> \<Longrightarrow> i = j\<close>
    and k: \<open>k < length M\<close> \<open>in_cls (snd (M ! k)) c\<close>
  shows \<open>class_of (IArray (class_table M)) c < length M \<and>
    in_cls (snd (M ! class_of (IArray (class_table M)) c)) c\<close>
proof -
  let ?xs = \<open>class_table M\<close>
  let ?i = \<open>bsearch (IArray ?xs) c 0 (length ?xs)\<close>
  have sorted: \<open>sorted (map fst ?xs)\<close>
    by (simp add: class_table_def)
  from k obtain l h where \<open>(l, h) \<in> set (snd (M ! k))\<close> \<open>l \<le> c\<close> \<open>c \<le> h\<close>
    by (auto simp: in_cls_iff)
  with k(1) obtain j where j: \<open>j < length ?xs\<close> \<open>?xs ! j = (l, h, k)\<close>
    by (metis in_set_conv_nth mem_class_table)
  moreover from j(1) have len: \<open>0 < length ?xs\<close>
    by linarith
  moreover have \<open>fst (?xs ! 0) \<le> c\<close>
    using sorted_nth_mono[OF sorted, of 0 j] j \<open>l \<le> c\<close> len by simp
  ultimately
  have i: \<open>?i < length ?xs\<close> \<open>fst (?xs ! ?i) \<le> c\<close>
    \<open>\<forall>j'. ?i < j' \<longrightarrow> j' < length ?xs \<longrightarrow> c < fst (?xs ! j')\<close>
    using bsearch[of \<open>IArray ?xs\<close> 0 \<open>length ?xs\<close> c] sorted by auto
  with j \<open>l \<le> c\<close> have \<open>j \<le> ?i\<close>
    by (metis fst_conv not_le)
  with sorted_nth_mono[OF sorted this] i(1) j have \<open>l \<le> fst (?xs ! ?i)\<close>
    by simp
  moreover have \<open>fst (?xs ! ?i) \<le> fst (snd (?xs ! ?i))\<close>
    using class_table_nonempty[OF wf] i(1) by simp
  ultimately have \<open>?xs ! ?i = ?xs ! j\<close>
    using class_table_disjoint[OF wf disj, where x = \<open>?xs ! ?i\<close> and y = \<open>?xs ! j\<close>
      and c = \<open>fst (?xs ! ?i)\<close>] i(1,2) j nth_mem[OF j(1)] order.trans[OF i(2) \<open>c \<le> h\<close>]
    by simp
  with j k show ?thesis
    by (simp add: class_of_def)
qed

end

context bounded_discrete_order
begin

lemma wf_minterms: \<open>(S, \<mu>) \<in> set (minterms P) \<Longrightarrow> wf_cls \<mu>\<close>
  by (induct P arbitrary: S \<mu>) (auto simp: wf_top wf_conj)

text \<open>The lookup in the minterm table of a mode is a classifier into its minterms:\<close>

lemma minterm_classifier_class_of:
  \<open>minterm_classifier rs (class_of (IArray (class_table (mode_minterms rs))))\<close>
  unfolding minterm_classifier_def
proof
  fix c
  let ?M = \<open>mode_minterms rs\<close>
  have wf: \<open>wf_cls (snd (?M ! k))\<close> if \<open>k < length ?M\<close> for k
    using wf_minterms nth_mem[OF that] by (metis mode_minterms_def prod.collapse)
  obtain S \<mu> where \<open>(S, \<mu>) \<in> set ?M\<close> \<open>in_cls \<mu> c\<close>
    using minterms_cover[of \<open>mode_atoms rs\<close> c] by (auto simp: mode_minterms_def)
  then obtain k where \<open>k < length ?M\<close> \<open>in_cls (snd (?M ! k)) c\<close>
    by (metis in_set_conv_nth snd_conv)
  from class_of_partition[OF wf _ this] minterms_disjoint
  show \<open>class_of (IArray (class_table ?M)) c < length ?M \<and>
    in_cls (snd (?M ! class_of (IArray (class_table ?M)) c)) c\<close>
    by (metis mode_minterms_def)
qed

end

subsection \<open>The byte instance\<close>

text \<open>Bytes are the first instance. The interpretation follows the generator, so it
  carries the generator's constants (\<open>char_mode_dfa\<close>) and theorems.\<close>

lemma of_char_le_255: \<open>of_char c \<le> (255::nat)\<close>
  using nat_of_char_less_256[of c] by linarith

lemma of_char_minus_mod: \<open>(of_char c - Suc 0) mod 256 = (of_char c - Suc 0 :: nat)\<close>
  by (simp add: less_imp_diff_less)

definition char_succ :: \<open>char \<Rightarrow> char\<close> where
  \<open>char_succ c = char_of (Suc (of_char c))\<close>

definition char_pred :: \<open>char \<Rightarrow> char\<close> where
  \<open>char_pred c = char_of (of_char c - 1 :: nat)\<close>

text \<open>Bytes are a bounded discrete order:\<close>

global_interpretation char_cls:
  bounded_discrete_order \<open>char_of (0::nat)\<close> \<open>char_of (255::nat)\<close> char_succ char_pred
  defines char_clip = char_cls.clip
    and char_merge = char_cls.merge
    and char_norm = char_cls.cls_norm
    and char_compl_from = char_cls.compl_from
    and char_top = char_cls.cls_top
    and char_disj = char_cls.cls_disj
    and char_neg = char_cls.cls_neg
    and char_conj = char_cls.cls_conj
    and char_minterms = char_cls.minterms
    and char_mode_minterms = char_cls.mode_minterms
    and char_mode_dfa = char_cls.mode_dfa
    and char_dead_state = char_cls.dead_state
  by unfold_locales
    (auto simp: less_eq_char_def less_char_def char_succ_def char_pred_def of_char_le_255
      of_char_minus_mod)

text \<open>The \<open>defines\<close> clause does not fold \<^const>\<open>char_minterms\<close> into the
  equations of \<open>char_cls.minterms\<close>, so we fold it by hand:\<close>

lemmas char_minterms_code[code] =
  char_cls.minterms.simps[unfolded char_top_def char_conj_def char_neg_def,
    folded char_minterms_def char_top_def char_conj_def char_neg_def]

text \<open>The \<open>defines\<close> clause does not fold the generator's equations either:\<close>

lemmas char_mode_minterms_code[code] =
  char_cls.mode_minterms_def[unfolded char_top_def char_conj_def char_neg_def,
    folded char_mode_minterms_def char_minterms_def char_top_def char_conj_def char_neg_def]

lemmas char_mode_dfa_code[code] =
  char_cls.mode_dfa_def[unfolded char_top_def char_conj_def char_neg_def,
    folded char_mode_dfa_def char_mode_minterms_def char_top_def char_conj_def char_neg_def]

lemmas char_dead_state_code[code] =
  char_cls.dead_state_def[unfolded char_top_def char_conj_def char_neg_def,
    folded char_dead_state_def char_mode_dfa_def char_top_def char_conj_def char_neg_def]

text \<open>In the theorems of the interpretation the constants appear unfolded:\<close>

lemma char_mode_minterms_eq: \<open>char_mode_minterms = char_cls.mode_minterms\<close>
  by (simp add: char_mode_minterms_def char_top_def char_conj_def char_neg_def)

lemma char_mode_dfa_eq: \<open>char_mode_dfa = char_cls.mode_dfa\<close>
  by (simp add: char_mode_dfa_def char_top_def char_conj_def char_neg_def)

lemma char_dead_state_eq: \<open>char_dead_state = char_cls.dead_state\<close>
  by (simp add: char_dead_state_def char_top_def char_conj_def char_neg_def)

text \<open>The tables of a mode on bytes are the minterm table, the transitions, the
  acceptance and the dead state. One constant holds all four, so one evaluation
  produces them:\<close>

type_synonym char_tables = \<open>(char \<times> char \<times> nat) iarray \<times> nat iarray iarray \<times> nat option iarray \<times> nat\<close>

definition char_tables :: \<open>('k, char cls, char, 'm) rule list \<Rightarrow> char_tables\<close> where
  \<open>char_tables rs = (IArray (class_table (char_mode_minterms rs)),
    IArray (map IArray (dfa_trans (char_mode_dfa rs))), IArray (dfa_accept (char_mode_dfa rs)),
    char_dead_state rs)\<close>

fun run_char :: \<open>char_tables \<Rightarrow> char list \<Rightarrow> (nat \<times> char list \<times> char list) option\<close> where
  \<open>run_char (C, T, A, d) = run_tables_ia T A (class_of C) d\<close>

text \<open>The runner on the tables of a mode is \<^const>\<open>char_cls.run_dfa\<close>:\<close>

lemma run_char_tables:
  \<open>run_char (char_tables rs) =
    char_cls.run_dfa rs (class_of (IArray (class_table (char_cls.mode_minterms rs))))\<close>
  by (simp add: fun_eq_iff char_tables_def char_mode_minterms_eq char_mode_dfa_eq
      char_dead_state_eq char_cls.run_tables_ia_eq_run_dfa char_cls.minterm_classifier_class_of)

text \<open>The lexer on bytes takes the tables of all modes as one array and an index \<open>ix\<close>
  into it for each mode, so modes with the same rules share their tables and the driver
  never compares modes. A mode whose index is outside the array has no rules:\<close>

definition char_lexer ::
  \<open>char_tables iarray \<Rightarrow> ('m \<Rightarrow> nat) \<Rightarrow> ('k, char cls, char, 'm) lexer_spec \<Rightarrow>
    (char \<Rightarrow> bool) \<Rightarrow> 'm list \<Rightarrow> pos \<Rightarrow> char list \<Rightarrow> ('k, char) lexed \<times> char list \<times> 'm list\<close>
where
  \<open>char_lexer TT ix =
    drive (\<lambda>m. if ix m < IArray.length TT then run_char (TT !! ix m) else (\<lambda>_. None))\<close>

text \<open>The runner of \<^const>\<open>char_lexer\<close> runs the modes of \<open>sp\<close> if the index of each
  mode holds its tables or is outside the array for a mode without rules:\<close>

lemma mode_runner_char_lexer:
  assumes \<open>\<And>m. if ix m < IArray.length TT then TT !! ix m = char_tables (sp m) else sp m = []\<close>
  shows \<open>char_cls.mode_runner sp
    (\<lambda>m. if ix m < IArray.length TT then run_char (TT !! ix m) else (\<lambda>_. None))\<close>
  unfolding char_cls.mode_runner_def
proof (intro allI)
  fix m s i p rest
  show \<open>(if ix m < IArray.length TT then run_char (TT !! ix m) else (\<lambda>_. None)) s =
      Some (i, p, rest) \<longleftrightarrow> char_cls.first_token (sp m) i p s \<and> s = p @ rest\<close>
    using assms[of m]
    by (auto simp: run_char_tables char_cls.run_dfa_Some_iff char_cls.minterm_classifier_class_of
        char_cls.first_token.simps split: if_splits)
qed

text \<open>If the index of each mode holds its tables, the lexer on bytes is
  \<^const>\<open>char_cls.lexes\<close>:\<close>

theorem char_lexer_iff_lexes:
  assumes \<open>\<forall>m. ix m < IArray.length TT \<and> TT !! ix m = char_tables (sp m)\<close>
  shows \<open>char_lexer TT ix sp is_newline st q s = (l, r, st\<^sub>f) \<longleftrightarrow>
    char_cls.lexes sp is_newline st q s l r st\<^sub>f\<close>
  unfolding char_lexer_def
  by (rule char_cls.drive_iff_lexes[OF mode_runner_char_lexer]) (use assms in auto)

text \<open>The tables of a spec on the modes \<open>0, \<dots>, n - 1\<close> (\<^const>\<open>list_spec\<close>), with the
  identity as index:\<close>

definition char_lexer_tables :: \<open>('k, char cls, char, nat) rule list list \<Rightarrow> char_tables iarray\<close>
where
  \<open>char_lexer_tables sps = IArray (map char_tables sps)\<close>

theorem char_lexer_list_iff_lexes:
  \<open>char_lexer (char_lexer_tables sps) id (list_spec sps) is_newline st q s = (l, r, st\<^sub>f) \<longleftrightarrow>
    char_cls.lexes (list_spec sps) is_newline st q s l r st\<^sub>f\<close>
  unfolding char_lexer_def
  by (rule char_cls.drive_iff_lexes[OF mode_runner_char_lexer])
    (simp add: char_lexer_tables_def list_spec_def)

subsection \<open>Code equations by evaluation\<close>

text \<open>\<open>eval_eq ctxt t\<close> evaluates the closed term \<open>t\<close> to a value \<open>v\<close> and proves \<open>t = v\<close>
  by \<open>eval\<close>. \<open>eval_table b t\<close> notes this equation as \<open>b\<close> for a nullary constant \<open>t\<close>.
  Declared \<open>[code]\<close>, the equation replaces the definition in generated code:\<close>

ML \<open>
fun eval_eq ctxt t =
  let
    val v = Value_Command.value ctxt t
    val eqn = HOLogic.mk_Trueprop (HOLogic.mk_eq (t, v))
  in
    Goal.prove ctxt [] [] eqn (fn {context = ctxt, ...} =>
      CONVERSION (Code_Runtime.dynamic_holds_conv ctxt) 1 THEN resolve_tac ctxt [TrueI] 1)
  end

fun eval_table (b, t) lthy = snd (Local_Theory.note ((b, []), [eval_eq lthy t]) lthy)
\<close>

end
