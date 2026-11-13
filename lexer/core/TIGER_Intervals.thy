(* Author: Basil Fürer *)

theory TIGER_Intervals
  imports TIGER_Pred_Algebra
begin

section \<open>Character classes as interval lists\<close>

text \<open>A character class is a list of closed intervals \<open>(lo, hi)\<close> and denotes the
  characters in one of them. A well-formed class is sorted, and its intervals are
  nonempty, disjoint and nonadjacent. Owens et al. label transitions with character sets
  because iterating over a large alphabet such as Unicode is impractical
  \<^cite>\<open>\<open>Sect.~4.2\<close> in "owens2009-regex-derivatives-reexamined"\<close>. Lists of intervals
  are closed under the Boolean operations and so form an effective Boolean algebra
  \<^cite>\<open>\<open>Sect.~2\<close> in "dantoni2014-minimization-symbolic-automata"\<close>; single ranges
  are not \<^cite>\<open>\<open>Sect.~6.2\<close> in "dantoni2014-minimization-symbolic-automata"\<close>.

  The alphabet is a bounded discrete linear order (bytes, codepoints). Its bottom, top,
  successor and predecessor are parameters of the locale \<open>discrete_order\<close>,
  not a type class. Its axioms speak only about the range from bottom to top (\<^typ>\<open>nat\<close>
  with a bound is an instance). The locale \<open>bounded_discrete_order\<close> adds that
  the range is the whole type.

  The operations accept any list and return well-formed classes. We prove their
  denotations relative to the range and interpret \<^locale>\<open>eba\<close> in
  \<open>bounded_discrete_order\<close>. Negation is the gaps of the normal form, and
  conjunction follows from De Morgan's law. The instance on \<^typ>\<open>char\<close> is in
  \<open>TIGER_Tables\<close> (an interpretation carries only the locale constants defined before it, so
  it follows the generator).\<close>

type_synonym 'ch cls = \<open>('ch \<times> 'ch) list\<close>

fun in_cls :: \<open>'ch::ord cls \<Rightarrow> 'ch \<Rightarrow> bool\<close> where
  \<open>in_cls [] c \<longleftrightarrow> False\<close>
| \<open>in_cls ((l, h) # p) c \<longleftrightarrow> l \<le> c \<and> c \<le> h \<or> in_cls p c\<close>

text \<open>The denotation of a class depends only on its set of intervals:\<close>

lemma in_cls_append[simp]: \<open>in_cls (p @ q) c \<longleftrightarrow> in_cls p c \<or> in_cls q c\<close>
  by (induct p c rule: in_cls.induct) auto

lemma in_cls_iff: \<open>in_cls p c \<longleftrightarrow> (\<exists>x \<in> set p. fst x \<le> c \<and> c \<le> snd x)\<close>
  by (induct p c rule: in_cls.induct) auto

lemma in_cls_sort_key[simp]: \<open>in_cls (sort_key f p) c \<longleftrightarrow> in_cls p c\<close>
  by (simp add: in_cls_iff)

lemma not_in_cls_if_less: \<open>\<forall>x \<in> set p. c < fst x \<Longrightarrow> \<not> in_cls p (c::'ch::linorder)\<close>
  by (auto simp: in_cls_iff not_le)

fun sat_cls :: \<open>'ch::ord cls \<Rightarrow> bool\<close> where
  \<open>sat_cls [] \<longleftrightarrow> False\<close>
| \<open>sat_cls ((l, h) # p) \<longleftrightarrow> l \<le> h \<or> sat_cls p\<close>

text \<open>A class is satisfiable when one of its intervals is nonempty:\<close>

lemma sat_cls_iff: \<open>sat_cls p \<longleftrightarrow> (\<exists>c. in_cls p (c::'ch::order))\<close>
  by (induct p rule: sat_cls.induct) (auto intro: order_trans)

subsection \<open>The alphabet\<close>

text \<open>Within the range from \<open>bot\<close> to \<open>top\<close>, \<open>succ c\<close> is the least character above
  \<open>c\<close> and \<open>pred c\<close> the greatest below it:\<close>

locale discrete_order =
  fixes bot :: \<open>'ch::linorder\<close>
    and top :: 'ch
    and succ :: \<open>'ch \<Rightarrow> 'ch\<close>
    and pred :: \<open>'ch \<Rightarrow> 'ch\<close>
  assumes bot_le_top: \<open>bot \<le> top\<close>
    and succ_le_iff: \<open>c < top \<Longrightarrow> succ c \<le> d \<longleftrightarrow> c < d\<close>
    and le_pred_iff: \<open>bot < c \<Longrightarrow> d \<le> pred c \<longleftrightarrow> d < c\<close>
begin

lemma less_succ: \<open>c < top \<Longrightarrow> c < succ c\<close>
  using succ_le_iff[of c \<open>succ c\<close>] by simp

lemma succ_le_top: \<open>c < top \<Longrightarrow> succ c \<le> top\<close>
  using succ_le_iff[of c top] by simp

lemma pred_less: \<open>bot < c \<Longrightarrow> pred c < c\<close>
  using le_pred_iff[of c \<open>pred c\<close>] by simp

lemma succ_pred: \<open>\<lbrakk> bot < c; c \<le> top \<rbrakk> \<Longrightarrow> succ (pred c) = c\<close>
proof -
  assume \<open>bot < c\<close> \<open>c \<le> top\<close>
  then have \<open>pred c < c\<close> \<open>pred c < top\<close>
    using pred_less[of c] by auto
  then have \<open>succ (pred c) \<le> c\<close> \<open>pred c < succ (pred c)\<close>
    using succ_le_iff[of \<open>pred c\<close> c] less_succ[of \<open>pred c\<close>] by auto
  with \<open>bot < c\<close> show ?thesis
    using le_pred_iff[of c \<open>succ (pred c)\<close>] by auto
qed

subsection \<open>Well-formed classes\<close>

fun in_range :: \<open>'ch cls \<Rightarrow> bool\<close> where
  \<open>in_range [] \<longleftrightarrow> True\<close>
| \<open>in_range ((l, h) # p) \<longleftrightarrow> bot \<le> l \<and> l \<le> h \<and> h \<le> top \<and> in_range p\<close>

definition separated :: \<open>'ch cls \<Rightarrow> bool\<close> where
  \<open>separated = sorted_wrt (\<lambda>x y. snd x < top \<and> succ (snd x) < fst y)\<close>

definition wf_cls :: \<open>'ch cls \<Rightarrow> bool\<close> where
  \<open>wf_cls p \<longleftrightarrow> in_range p \<and> separated p\<close>

text \<open>A class is in range when its intervals are nonempty and lie between \<open>bot\<close> and
  \<open>top\<close>. It is separated when each interval ends before the successor of the end of
  every earlier one (so the intervals are sorted, disjoint and nonadjacent):\<close>

lemma in_range_iff: \<open>in_range p \<longleftrightarrow> (\<forall>x \<in> set p. bot \<le> fst x \<and> fst x \<le> snd x \<and> snd x \<le> top)\<close>
  by (induct p rule: in_range.induct) auto

lemma in_range_append[simp]: \<open>in_range (p @ q) \<longleftrightarrow> in_range p \<and> in_range q\<close>
  by (auto simp: in_range_iff)

lemma in_range_sort_key[simp]: \<open>in_range (sort_key f p) \<longleftrightarrow> in_range p\<close>
  by (simp add: in_range_iff)

subsection \<open>Normal form\<close>

definition clip :: \<open>'ch cls \<Rightarrow> 'ch cls\<close> where
  \<open>clip p = filter (\<lambda>(l, h). l \<le> h) (map (\<lambda>(l, h). (max bot l, min h top)) p)\<close>

text \<open>Clipping cuts the intervals to the range and drops the empty ones:\<close>

lemma in_range_clip: \<open>in_range (clip p)\<close>
  by (induct p rule: in_range.induct) (auto simp: clip_def)

lemma in_cls_clip: \<open>in_cls (clip p) c \<longleftrightarrow> bot \<le> c \<and> c \<le> top \<and> in_cls p c\<close>
  by (induct p rule: in_range.induct) (auto simp: clip_def)

fun merge :: \<open>'ch cls \<Rightarrow> 'ch cls\<close> where
  \<open>merge ((l, h) # (l', h') # p) =
    (if l' \<le> h \<or> l' = succ h then merge ((l, max h h') # p)
     else (l, h) # merge ((l', h') # p))\<close>
| \<open>merge p = p\<close>

lemmas merge_induct = merge.induct[case_names Cons_Cons Nil Single]

text \<open>Merging joins overlapping and adjacent neighbours of a list sorted by lower
  bounds. It keeps the first lower bound and takes the others from its input:\<close>

lemma merge_hd: \<open>p \<noteq> [] \<Longrightarrow> merge p \<noteq> [] \<and> fst (hd (merge p)) = fst (hd p)\<close>
  by (induct p rule: merge_induct) auto

lemma merge_ConsE:
  obtains h' p' where \<open>merge ((l, h) # p) = (l, h') # p'\<close>
  using merge_hd[of \<open>(l, h) # p\<close>] by (cases \<open>merge ((l, h) # p)\<close>) auto

lemma fst_merge_subset: \<open>fst ` set (merge p) \<subseteq> fst ` set p\<close>
  by (induct p rule: merge_induct) auto

lemma in_range_merge: \<open>in_range p \<Longrightarrow> in_range (merge p)\<close>
  by (induct p rule: merge_induct) (auto simp: max_def)

lemma in_join_iff:
  assumes \<open>l \<le> l'\<close> \<open>l' \<le> h \<or> l' = succ h\<close> \<open>h' \<le> top\<close>
  shows \<open>l \<le> c \<and> c \<le> max h h' \<longleftrightarrow> l \<le> c \<and> c \<le> h \<or> l' \<le> c \<and> c \<le> h'\<close>
proof -
  have \<open>l' \<le> c\<close> if \<open>h < c\<close> \<open>c \<le> h'\<close>
    using assms that succ_le_iff[of h c] by auto
  with assms show ?thesis
    by (cases \<open>c \<le> h\<close>) (auto simp: max_def)
qed

lemma in_cls_merge:
  \<open>\<lbrakk> sorted (map fst p); in_range p \<rbrakk> \<Longrightarrow> in_cls (merge p) c \<longleftrightarrow> in_cls p c\<close>
proof (induct p rule: merge_induct)
  case (Cons_Cons l h l' h' p)
  show ?case
  proof (cases \<open>l' \<le> h \<or> l' = succ h\<close>)
    case True
    moreover from Cons_Cons.prems
    have \<open>sorted (map fst ((l, max h h') # p))\<close> \<open>in_range ((l, max h h') # p)\<close>
      by (auto simp: max_def)
    ultimately show ?thesis
      using Cons_Cons in_join_iff[of l l' h h' c] by auto
  next
    case False
    with Cons_Cons show ?thesis
      by auto
  qed
qed simp_all

lemma separated_merge: \<open>\<lbrakk> sorted (map fst p); in_range p \<rbrakk> \<Longrightarrow> separated (merge p)\<close>
proof (induct p rule: merge_induct)
  case (Cons_Cons l h l' h' p)
  show ?case
  proof (cases \<open>l' \<le> h \<or> l' = succ h\<close>)
    case True
    moreover from Cons_Cons.prems
    have \<open>sorted (map fst ((l, max h h') # p))\<close> \<open>in_range ((l, max h h') # p)\<close>
      by (auto simp: max_def)
    ultimately show ?thesis
      using Cons_Cons by auto
  next
    case False
    with Cons_Cons.prems have \<open>h < top\<close>
      by auto
    with False have \<open>succ h < l'\<close>
      using succ_le_iff[of h l'] by auto
    moreover have \<open>l' \<le> fst x\<close> if \<open>x \<in> set (merge ((l', h') # p))\<close> for x
      using that fst_merge_subset[of \<open>(l', h') # p\<close>] Cons_Cons.prems by fastforce
    ultimately show ?thesis
      using False Cons_Cons by (auto simp: separated_def intro: less_le_trans)
  qed
qed (simp_all add: separated_def)

definition cls_norm :: \<open>'ch cls \<Rightarrow> 'ch cls\<close> where
  \<open>cls_norm p = merge (sort_key fst (clip p))\<close>

text \<open>The normal form of a class is well-formed and denotes its characters in range:\<close>

lemma wf_cls_norm: \<open>wf_cls (cls_norm p)\<close>
  by (simp add: wf_cls_def cls_norm_def in_range_merge separated_merge in_range_clip)

lemma in_cls_norm: \<open>in_cls (cls_norm p) c \<longleftrightarrow> bot \<le> c \<and> c \<le> top \<and> in_cls p c\<close>
  by (simp add: cls_norm_def in_cls_merge in_range_clip in_cls_clip)

subsection \<open>Complement\<close>

fun compl_from :: \<open>'ch \<Rightarrow> 'ch cls \<Rightarrow> 'ch cls\<close> where
  \<open>compl_from c [] = [(c, top)]\<close>
| \<open>compl_from c ((l, h) # p) =
    (if c < l then [(c, pred l)] else []) @ (if h < top then compl_from (succ h) p else [])\<close>

lemmas compl_from_induct = compl_from.induct[case_names Nil Cons]

text \<open>The gaps of a well-formed class from \<open>c\<close> on are its complement from \<open>c\<close> to \<open>top\<close>:\<close>

lemma in_cls_compl_from:
  assumes \<open>wf_cls p\<close> \<open>\<forall>x \<in> set p. c \<le> fst x\<close> \<open>bot \<le> c\<close> \<open>c \<le> top\<close>
  shows \<open>in_cls (compl_from c p) d \<longleftrightarrow> c \<le> d \<and> d \<le> top \<and> \<not> in_cls p d\<close>
  using assms
proof (induct c p rule: compl_from_induct)
  case (Cons c l h p)
  from Cons.prems have \<open>bot \<le> l\<close> \<open>l \<le> h\<close> \<open>h \<le> top\<close> \<open>c \<le> l\<close> \<open>wf_cls p\<close>
    and above: \<open>\<forall>x \<in> set p. h < top \<and> succ h < fst x\<close>
    by (simp_all add: wf_cls_def separated_def)
  have ih: \<open>in_cls (compl_from (succ h) p) d \<longleftrightarrow> succ h \<le> d \<and> d \<le> top \<and> \<not> in_cls p d\<close>
    if \<open>h < top\<close>
  proof -
    have \<open>h < succ h\<close> \<open>succ h \<le> top\<close>
      using that less_succ succ_le_top by auto
    with that \<open>wf_cls p\<close> above \<open>bot \<le> l\<close> \<open>l \<le> h\<close> show ?thesis
      by (intro Cons.hyps) auto
  qed
  have \<open>\<not> in_cls p d\<close> if \<open>d \<le> h\<close>
    using above that less_succ[of h] by (intro not_in_cls_if_less) auto
  then show ?case
    using \<open>c \<le> l\<close> \<open>l \<le> h\<close> \<open>h \<le> top\<close> \<open>bot \<le> c\<close> ih le_pred_iff[of l d] succ_le_iff[of h d]
    by (cases \<open>d < l\<close>) auto
qed simp

lemma wf_compl_from:
  assumes \<open>wf_cls p\<close> \<open>\<forall>x \<in> set p. c \<le> fst x\<close> \<open>bot \<le> c\<close> \<open>c \<le> top\<close>
  shows \<open>wf_cls (compl_from c p) \<and> (\<forall>x \<in> set (compl_from c p). c \<le> fst x)\<close>
  using assms
proof (induct c p rule: compl_from_induct)
  case (Nil c)
  then show ?case
    by (simp add: wf_cls_def separated_def)
next
  case (Cons c l h p)
  from Cons.prems have \<open>bot \<le> l\<close> \<open>l \<le> h\<close> \<open>h \<le> top\<close> \<open>c \<le> l\<close> \<open>wf_cls p\<close>
    and above: \<open>\<forall>x \<in> set p. h < top \<and> succ h < fst x\<close>
    by (simp_all add: wf_cls_def separated_def)
  define r where \<open>r = (if h < top then compl_from (succ h) p else [])\<close>
  have \<open>wf_cls r \<and> (\<forall>x \<in> set r. succ h \<le> fst x \<and> h < top)\<close>
  proof (cases \<open>h < top\<close>)
    case True
    then have \<open>h < succ h\<close> \<open>succ h \<le> top\<close>
      using less_succ succ_le_top by auto
    with True \<open>wf_cls p\<close> above \<open>bot \<le> l\<close> \<open>l \<le> h\<close>
    have \<open>wf_cls (compl_from (succ h) p) \<and> (\<forall>x \<in> set (compl_from (succ h) p). succ h \<le> fst x)\<close>
      by (intro Cons.hyps) auto
    with True show ?thesis
      by (simp add: r_def)
  qed (simp add: r_def wf_cls_def separated_def)
  then have \<open>wf_cls r\<close> \<open>\<forall>x \<in> set r. l < fst x\<close>
    using \<open>l \<le> h\<close> less_succ[of h] by auto
  moreover have \<open>compl_from c ((l, h) # p) = (if c < l then [(c, pred l)] else []) @ r\<close>
    by (simp add: r_def)
  moreover have \<open>pred l < top\<close> \<open>succ (pred l) = l\<close> \<open>c \<le> pred l\<close> if \<open>c < l\<close>
  proof -
    from that \<open>bot \<le> c\<close> have \<open>bot < l\<close>
      by simp
    with that \<open>l \<le> h\<close> \<open>h \<le> top\<close> show \<open>pred l < top\<close> \<open>succ (pred l) = l\<close> \<open>c \<le> pred l\<close>
      using pred_less[of l] succ_pred[of l] le_pred_iff[of l c] by auto
  qed
  ultimately show ?case
    using \<open>bot \<le> c\<close> \<open>c \<le> l\<close>
    by (cases \<open>c < l\<close>) (auto simp: wf_cls_def separated_def sorted_wrt_append)
qed

subsection \<open>The operations\<close>

definition cls_top :: \<open>'ch cls\<close> where
  \<open>cls_top = [(bot, top)]\<close>

definition cls_bot :: \<open>'ch cls\<close> where
  \<open>cls_bot = []\<close>

definition cls_disj :: \<open>'ch cls \<Rightarrow> 'ch cls \<Rightarrow> 'ch cls\<close> where
  \<open>cls_disj p q = cls_norm (p @ q)\<close>

definition cls_neg :: \<open>'ch cls \<Rightarrow> 'ch cls\<close> where
  \<open>cls_neg p = compl_from bot (cls_norm p)\<close>

definition cls_conj :: \<open>'ch cls \<Rightarrow> 'ch cls \<Rightarrow> 'ch cls\<close> where
  \<open>cls_conj p q = cls_neg (cls_disj (cls_neg p) (cls_neg q))\<close>

text \<open>The operations denote the Boolean operations on the range:\<close>

lemma in_cls_top: \<open>in_cls cls_top c \<longleftrightarrow> bot \<le> c \<and> c \<le> top\<close>
  by (simp add: cls_top_def)

lemma in_cls_bot: \<open>\<not> in_cls cls_bot c\<close>
  by (simp add: cls_bot_def)

lemma in_cls_disj: \<open>in_cls (cls_disj p q) c \<longleftrightarrow> bot \<le> c \<and> c \<le> top \<and> (in_cls p c \<or> in_cls q c)\<close>
  by (simp add: cls_disj_def in_cls_norm)

lemma in_cls_neg: \<open>in_cls (cls_neg p) c \<longleftrightarrow> bot \<le> c \<and> c \<le> top \<and> \<not> in_cls p c\<close>
proof -
  have \<open>\<forall>x \<in> set (cls_norm p). bot \<le> fst x\<close>
    using wf_cls_norm by (simp add: wf_cls_def in_range_iff)
  then show ?thesis
    using wf_cls_norm bot_le_top by (auto simp: cls_neg_def in_cls_compl_from in_cls_norm)
qed

lemma in_cls_conj: \<open>in_cls (cls_conj p q) c \<longleftrightarrow> bot \<le> c \<and> c \<le> top \<and> in_cls p c \<and> in_cls q c\<close>
  by (auto simp: cls_conj_def in_cls_neg in_cls_disj)

text \<open>All of them return well-formed classes:\<close>

lemma wf_top: \<open>wf_cls cls_top\<close>
  by (simp add: cls_top_def wf_cls_def separated_def bot_le_top)

lemma wf_bot: \<open>wf_cls cls_bot\<close>
  by (simp add: cls_bot_def wf_cls_def separated_def)

lemma wf_disj: \<open>wf_cls (cls_disj p q)\<close>
  by (simp add: cls_disj_def wf_cls_norm)

lemma wf_neg: \<open>wf_cls (cls_neg p)\<close>
proof -
  have \<open>\<forall>x \<in> set (cls_norm p). bot \<le> fst x\<close>
    using wf_cls_norm by (simp add: wf_cls_def in_range_iff)
  then show ?thesis
    using wf_compl_from wf_cls_norm bot_le_top by (simp add: cls_neg_def)
qed

lemma wf_conj: \<open>wf_cls (cls_conj p q)\<close>
  by (simp add: cls_conj_def wf_neg)

end

subsection \<open>The effective Boolean algebra\<close>

text \<open>When the range is the whole type, character classes form an effective Boolean
  algebra:\<close>

locale bounded_discrete_order = discrete_order +
  assumes bot_le: \<open>bot \<le> c\<close>
    and le_top: \<open>c \<le> top\<close>
begin

sublocale eba in_cls cls_top cls_bot cls_conj cls_disj cls_neg sat_cls
  by unfold_locales
    (simp_all add: bot_le le_top in_cls_top in_cls_bot in_cls_conj in_cls_disj in_cls_neg
      sat_cls_iff)

end

end
