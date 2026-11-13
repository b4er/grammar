(* Author: Basil Fürer, Claude *)

theory TIGER_Pred_Algebra
  imports TIGER_Regex
begin

section \<open>Effective Boolean algebras of predicates\<close>

text \<open>An effective Boolean algebra on the predicates \<open>'p\<close> has a top and a bottom
  predicate, conjunction, disjunction, negation and a satisfiability test, all sound for
  the denotation \<open>sem\<close> \<^cite>\<open>\<open>Sect.~2\<close> in "dantoni2014-minimization-symbolic-automata"\<close>.
  The generator needs it to compute the minterms of the atoms of a mode.

  Equality of predicates is HOL equality, so it is syntactic. Equal predicates denote the
  same set, but predicates with the same denotation need not be equal (the generator
  never needs the converse).\<close>

locale eba = symbolic sem
  for sem :: \<open>'p \<Rightarrow> 'ch \<Rightarrow> bool\<close> +
  fixes top :: 'p
    and bot :: 'p
    and conj :: \<open>'p \<Rightarrow> 'p \<Rightarrow> 'p\<close>
    and disj :: \<open>'p \<Rightarrow> 'p \<Rightarrow> 'p\<close>
    and neg :: \<open>'p \<Rightarrow> 'p\<close>
    and sat :: \<open>'p \<Rightarrow> bool\<close>
  assumes sem_top[simp]: \<open>sem top c\<close>
    and sem_bot[simp]: \<open>\<not> sem bot c\<close>
    and sem_conj[simp]: \<open>sem (conj p q) c \<longleftrightarrow> sem p c \<and> sem q c\<close>
    and sem_disj[simp]: \<open>sem (disj p q) c \<longleftrightarrow> sem p c \<or> sem q c\<close>
    and sem_neg[simp]: \<open>sem (neg p) c \<longleftrightarrow> \<not> sem p c\<close>
    and sat_iff: \<open>sat p \<longleftrightarrow> (\<exists>c. sem p c)\<close>
begin

text \<open>The test \<open>sat\<close> is dv14's \<open>IsSat\<close>. A minterm is satisfiable when some character
  satisfies all its conjuncts:\<close>

lemma sat_conj_iff: \<open>sat (conj p q) \<longleftrightarrow> (\<exists>c. sem p c \<and> sem q c)\<close>
  by (simp add: sat_iff)

subsection \<open>Minterms\<close>

text \<open>The minterms of a list \<open>P\<close> of predicates are the satisfiable conjunctions of
  each predicate of \<open>P\<close> or its negation. Each entry pairs its signature (the
  predicates taken positively) with the conjunction. The recursion is the minterm tree
  of \<^cite>\<open>\<open>Fig.~2\<close> in "dantoni2014-minimization-symbolic-automata"\<close>, refined by the
  predicates from the last to the first. A leaf is split by \<open>p\<close> into \<open>p \<and> \<mu>\<close> and
  \<open>\<not> p \<and> \<mu>\<close>, and the unsatisfiable parts are pruned (the paper keeps an unsplit
  leaf instead, which denotes the same set).\<close>

primrec minterms :: \<open>'p list \<Rightarrow> ('p set \<times> 'p) list\<close> where
  minterms_Nil: \<open>minterms [] = [({}, top)]\<close>
| minterms_Cons: \<open>minterms (p # P) = concat (map (\<lambda>(S, \<mu>).
    filter (sat \<circ> snd) [(insert p S, conj p \<mu>), (S, conj (neg p) \<mu>)]) (minterms P))\<close>

lemma mem_minterms_Cons[simp]:
  \<open>(S, \<mu>) \<in> set (minterms (p # P)) \<longleftrightarrow> (\<exists>S\<^sub>0 \<mu>\<^sub>0. (S\<^sub>0, \<mu>\<^sub>0) \<in> set (minterms P) \<and>
    ((S, \<mu>) = (insert p S\<^sub>0, conj p \<mu>\<^sub>0) \<and> sat (conj p \<mu>\<^sub>0) \<or>
     (S, \<mu>) = (S\<^sub>0, conj (neg p) \<mu>\<^sub>0) \<and> sat (conj (neg p) \<mu>\<^sub>0)))\<close>
  by (auto split: if_splits)

declare minterms_Cons[simp del]

text \<open>An entry denotes exactly the characters whose signature in \<open>P\<close> is its own.
  This is the invariant behind the four properties below:\<close>

lemma sem_minterm_iff:
  assumes \<open>(S, \<mu>) \<in> set (minterms P)\<close>
  shows \<open>sat \<mu> \<and> S \<subseteq> set P \<and> (\<forall>c. sem \<mu> c \<longleftrightarrow> S = {p \<in> set P. sem p c})\<close>
  using assms
proof (induction P arbitrary: S \<mu>)
  case (Cons p P)
  then obtain S\<^sub>0 \<mu>\<^sub>0 where \<open>(S\<^sub>0, \<mu>\<^sub>0) \<in> set (minterms P)\<close>
    and new: \<open>(S, \<mu>) = (insert p S\<^sub>0, conj p \<mu>\<^sub>0) \<and> sat (conj p \<mu>\<^sub>0) \<or>
      (S, \<mu>) = (S\<^sub>0, conj (neg p) \<mu>\<^sub>0) \<and> sat (conj (neg p) \<mu>\<^sub>0)\<close>
    by auto
  with Cons.IH have old: \<open>S\<^sub>0 \<subseteq> set P\<close> \<open>\<forall>c. sem \<mu>\<^sub>0 c \<longleftrightarrow> S\<^sub>0 = {q \<in> set P. sem q c}\<close>
    by auto
  from new show ?case
  proof (elim disjE conjE)
    assume \<open>(S, \<mu>) = (insert p S\<^sub>0, conj p \<mu>\<^sub>0)\<close> \<open>sat (conj p \<mu>\<^sub>0)\<close>
    moreover from \<open>sat (conj p \<mu>\<^sub>0)\<close> old obtain e
      where \<open>sem p e\<close> \<open>S\<^sub>0 = {q \<in> set P. sem q e}\<close>
      by (auto simp: sat_iff)
    ultimately show ?thesis
      using old by (auto simp: set_eq_iff)
  next
    assume \<open>(S, \<mu>) = (S\<^sub>0, conj (neg p) \<mu>\<^sub>0)\<close> \<open>sat (conj (neg p) \<mu>\<^sub>0)\<close>
    moreover from \<open>sat (conj (neg p) \<mu>\<^sub>0)\<close> old obtain e
      where \<open>\<not> sem p e\<close> \<open>S\<^sub>0 = {q \<in> set P. sem q e}\<close>
      by (auto simp: sat_iff)
    ultimately show ?thesis
      using old by (auto simp: set_eq_iff)
  qed
qed (auto simp: sat_iff[of top])

text \<open>The minterms cover the alphabet, are pairwise disjoint, have exact signatures and
  are satisfiable. Together they make the minterms a partition of the alphabet into the
  classes of characters with the same signature
  \<^cite>\<open>\<open>Sect.~4, Fig.~2\<close> in "dantoni2014-minimization-symbolic-automata"\<close>:\<close>

lemma minterms_cover: \<open>\<exists>S \<mu>. (S, \<mu>) \<in> set (minterms P) \<and> sem \<mu> c\<close>
proof (induction P)
  case (Cons p P)
  then obtain S \<mu> where \<open>(S, \<mu>) \<in> set (minterms P)\<close> \<open>sem \<mu> c\<close>
    by blast
  then show ?case
  proof (cases \<open>sem p c\<close>)
    case True
    with \<open>(S, \<mu>) \<in> set (minterms P)\<close> \<open>sem \<mu> c\<close>
    have \<open>(insert p S, conj p \<mu>) \<in> set (minterms (p # P))\<close>
      unfolding mem_minterms_Cons sat_conj_iff by blast
    with True \<open>sem \<mu> c\<close> show ?thesis
      by (metis sem_conj)
  next
    case False
    with \<open>(S, \<mu>) \<in> set (minterms P)\<close> \<open>sem \<mu> c\<close>
    have \<open>(S, conj (neg p) \<mu>) \<in> set (minterms (p # P))\<close>
      unfolding mem_minterms_Cons sat_conj_iff sem_neg by blast
    with False \<open>sem \<mu> c\<close> show ?thesis
      by (metis sem_conj sem_neg)
  qed
qed simp

lemma sorted_wrt_concat_map:
  assumes \<open>sorted_wrt R xs\<close> \<open>\<And>x. x \<in> set xs \<Longrightarrow> sorted_wrt R (f x)\<close>
    and \<open>\<And>x y u v. \<lbrakk> R x y; u \<in> set (f x); v \<in> set (f y) \<rbrakk> \<Longrightarrow> R u v\<close>
  shows \<open>sorted_wrt R (concat (map f xs))\<close>
  using assms by (induction xs) (auto simp: sorted_wrt_append)

lemma minterms_sorted_wrt:
  \<open>sorted_wrt (\<lambda>x y. \<forall>c. \<not> (sem (snd x) c \<and> sem (snd y) c)) (minterms P)\<close>
proof (induction P)
  case (Cons p P)
  let ?R = \<open>\<lambda>x y. \<forall>c. \<not> (sem (snd x) c \<and> sem (snd y) c)\<close>
  let ?f = \<open>\<lambda>(S, \<mu>). filter (sat \<circ> snd) [(insert p S, conj p \<mu>), (S, conj (neg p) \<mu>)]\<close>
  have sub: \<open>\<lbrakk> u \<in> set (?f x); sem (snd u) c \<rbrakk> \<Longrightarrow> sem (snd x) c\<close> for u x c
    by (cases x) (auto split: if_splits)
  have sorted_f: \<open>sorted_wrt ?R (?f x)\<close> for x
    by (cases x) (auto intro!: sorted_wrt_filter)
  have cross: \<open>\<lbrakk> ?R x y; u \<in> set (?f x); v \<in> set (?f y) \<rbrakk> \<Longrightarrow> ?R u v\<close> for x y u v
    using sub by blast
  show ?case
    using sorted_wrt_concat_map[OF Cons.IH sorted_f cross] by (simp add: minterms_Cons)
qed simp

lemma minterms_disjoint:
  assumes \<open>i < length (minterms P)\<close> \<open>j < length (minterms P)\<close>
    and \<open>sem (snd (minterms P ! i)) c\<close> \<open>sem (snd (minterms P ! j)) c\<close>
  shows \<open>i = j\<close>
  using minterms_sorted_wrt[of P] assms
  by (cases i j rule: linorder_cases; auto simp: sorted_wrt_iff_nth_less)

lemma minterms_exact: \<open>\<lbrakk> (S, \<mu>) \<in> set (minterms P); sem \<mu> c \<rbrakk> \<Longrightarrow> S = {p \<in> set P. sem p c}\<close>
  using sem_minterm_iff by blast

lemma minterms_sat: \<open>(S, \<mu>) \<in> set (minterms P) \<Longrightarrow> sat \<mu>\<close>
  using sem_minterm_iff by blast

text \<open>The partial derivatives by all characters of one minterm are equal, and equal
  to the partial derivative by its signature, as long as the minterms are taken over a
  superset of the atoms \<^cite>\<open>\<open>Lemma~9, Thm.~12\<close> in "keil2014-symbolic-regex-inequalities"\<close>:\<close>

lemma pderiv_eq_pderiv_cls_minterm:
  assumes \<open>atoms r \<subseteq> set P\<close> \<open>(S, \<mu>) \<in> set (minterms P)\<close> \<open>sem \<mu> c\<close>
  shows \<open>pderiv c r = pderiv_cls S r\<close>
proof -
  from assms have \<open>sig r c = S \<inter> atoms r\<close>
    by (auto simp: sig_def dest: minterms_exact)
  then show ?thesis
    by (simp add: pderiv_eq_pderiv_cls_sig pderiv_cls_Int_atoms)
qed

text \<open>The number of minterms is exponential in the length of \<open>P\<close> in the worst case.
  For the bit predicates \<open>\<beta>\<^sub>i\<close> (the characters whose \<open>i\<close>-th bit is set), every
  signature is realized by exactly one character, so \<open>k\<close> predicates have \<open>2\<^sup>k\<close>
  minterms \<^cite>\<open>\<open>Ex.~2\<close> in "dantoni2014-minimization-symbolic-automata"\<close>. A mode with
  many overlapping classes needs local minterms (minterms of the atoms that a DFA state
  can read, rather than of the whole mode). D'Antoni and Veanes compute local minterms to
  avoid the global partition when they minimize a symbolic automaton
  \<^cite>\<open>\<open>Sect.~5\<close> in "dantoni2014-minimization-symbolic-automata"\<close>; here they
  would serve DFA construction.\<close>

end

end
