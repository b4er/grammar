theory Gen
  imports Spec Pred_Algebra "HOL-Library.While_Combinator"
begin

section \<open>The DFA of a mode\<close>

text \<open>One DFA per mode reads all rules of the mode at once (regular vectors
  \<^cite>\<open>\<open>Sect. 6\<close> in "brzozowski1964-derivatives-regular-expressions"\<close>). A state is a
  finite set of pairs of a rule index and a partial derivative. It is the subset
  construction over partial derivatives \<^cite>\<open>\<open>Prop. 4.3\<close> in
  "antimirov1996-partial-derivatives"\<close>, tagged with rule indices. Transitions are indexed
  by the minterms of the mode's atoms \<^cite>\<open>\<open>Fig. 2\<close> in
  "dantoni2014-minimization-symbolic-automata"\<close>, and a state accepts with the least index
  of a nullable pair \<^cite>\<open>\<open>Sect. 8\<close> in "paxson2026-flex-manual"\<close>.

  The states are explored by a worklist over \<^const>\<open>while_option\<close>, as in the closure of
  \<^session>\<open>Regular-Sets\<close> (\<open>Equivalence_Checking\<close>), generalized to a list of states
  numbered in the order of discovery. Exploration is total, since every reachable state is
  a set of pairs from a finite closure of the rules under partial derivatives
  (@{thm [source] finite_pderiv_closure}).

  We prove that exploration terminates, that a transition by a minterm is the step by any
  of its characters, that the generated tables follow these steps, and that the accepting
  rule of a word is the least rule whose language contains it. Nothing here is trusted:
  every lemma relates the generator output to \<^const>\<open>symbolic.lang\<close>.\<close>

subsection \<open>Exploration by worklist\<close>

text \<open>The states reachable from \<open>x\<close> by a transition function \<open>f\<close> over the letters
  \<open>as\<close>:\<close>

definition reach :: \<open>('s \<Rightarrow> 'a \<Rightarrow> 's) \<Rightarrow> 'a list \<Rightarrow> 's \<Rightarrow> 's set\<close> where
  \<open>reach f as x = {foldl f x w | w. set w \<subseteq> set as}\<close>

lemma start_in_reach: \<open>x \<in> reach f as x\<close>
  by (auto simp: reach_def intro: exI[of _ \<open>[]\<close>])

lemma step_in_reach:
  assumes \<open>y \<in> reach f as x\<close> \<open>a \<in> set as\<close>
  shows \<open>f y a \<in> reach f as x\<close>
proof -
  from assms(1) obtain w where \<open>y = foldl f x w\<close> \<open>set w \<subseteq> set as\<close>
    by (auto simp: reach_def)
  with assms(2) show ?thesis
    by (auto simp: reach_def intro!: exI[of _ \<open>w @ [a]\<close>])
qed

lemma reach_subset:
  assumes \<open>x \<in> A\<close> \<open>\<And>y a. \<lbrakk> y \<in> A; a \<in> set as \<rbrakk> \<Longrightarrow> f y a \<in> A\<close>
  shows \<open>reach f as x \<subseteq> A\<close>
proof -
  have \<open>\<lbrakk> y \<in> A; set w \<subseteq> set as \<rbrakk> \<Longrightarrow> foldl f y w \<in> A\<close> for y w
    using assms(2) by (induct w arbitrary: y) auto
  with assms(1) show ?thesis
    by (auto simp: reach_def)
qed

text \<open>A worklist state \<open>(Q, n)\<close> holds the states found so far, in the order of
  discovery, of which the first \<open>n\<close> are processed. A step processes \<open>Q ! n\<close> and appends
  its new successors:\<close>

definition add_new :: \<open>'s list \<Rightarrow> 's \<Rightarrow> 's list\<close> where
  \<open>add_new Q y = (if y \<in> set Q then Q else Q @ [y])\<close>

definition explore_step :: \<open>('s \<Rightarrow> 'a \<Rightarrow> 's) \<Rightarrow> 'a list \<Rightarrow> 's list \<times> nat \<Rightarrow> 's list \<times> nat\<close>
  where
  \<open>explore_step f as = (\<lambda>(Q, n). (foldl add_new Q (map (f (Q ! n)) as), Suc n))\<close>

definition explore :: \<open>('s \<Rightarrow> 'a \<Rightarrow> 's) \<Rightarrow> 'a list \<Rightarrow> 's \<Rightarrow> ('s list \<times> nat) option\<close> where
  \<open>explore f as x = while_option (\<lambda>(Q, n). n < length Q) (explore_step f as) ([x], 0)\<close>

lemma foldl_add_new_append: \<open>\<exists>zs. foldl add_new Q ys = Q @ zs\<close>
proof (induct ys arbitrary: Q)
  case (Cons y ys)
  have \<open>add_new Q y = Q @ (if y \<in> set Q then [] else [y])\<close>
    by (simp add: add_new_def)
  moreover obtain zs where \<open>foldl add_new (add_new Q y) ys = add_new Q y @ zs\<close>
    using Cons by blast
  ultimately show ?case
    by (metis append_assoc foldl_Cons)
qed simp

lemma set_foldl_add_new: \<open>set (foldl add_new Q ys) = set Q \<union> set ys\<close>
  by (induct ys arbitrary: Q) (auto simp: add_new_def)

lemma distinct_foldl_add_new: \<open>distinct Q \<Longrightarrow> distinct (foldl add_new Q ys)\<close>
  by (induct ys arbitrary: Q) (auto simp: add_new_def)

text \<open>The invariant of the worklist: the found states are distinct and reachable, the
  start comes first and the successors of the processed states are found:\<close>

definition explore_inv :: \<open>('s \<Rightarrow> 'a \<Rightarrow> 's) \<Rightarrow> 'a list \<Rightarrow> 's \<Rightarrow> 's list \<times> nat \<Rightarrow> bool\<close>
  where
  \<open>explore_inv f as x = (\<lambda>(Q, n). distinct Q \<and> n \<le> length Q \<and> Q \<noteq> [] \<and> Q ! 0 = x \<and>
    set Q \<subseteq> reach f as x \<and> (\<forall>k < n. \<forall>a \<in> set as. f (Q ! k) a \<in> set Q))\<close>

lemma explore_inv_start: \<open>explore_inv f as x ([x], 0)\<close>
  by (simp add: explore_inv_def start_in_reach)

lemma explore_inv_step:
  assumes \<open>explore_inv f as x s\<close> \<open>case s of (Q, n) \<Rightarrow> n < length Q\<close>
  shows \<open>explore_inv f as x (explore_step f as s)\<close>
proof (cases s)
  case (Pair Q n)
  let ?Q' = \<open>foldl add_new Q (map (f (Q ! n)) as)\<close>
  obtain zs where Q': \<open>?Q' = Q @ zs\<close>
    using foldl_add_new_append by blast
  then have set_zs: \<open>set Q \<union> set zs = set Q \<union> f (Q ! n) ` set as\<close>
    using set_foldl_add_new[of Q \<open>map (f (Q ! n)) as\<close>] by simp
  from assms Pair have inv: \<open>explore_inv f as x (Q, n)\<close> and \<open>n < length Q\<close>
    by simp_all
  then have \<open>Q ! n \<in> reach f as x\<close>
    by (auto simp: explore_inv_def)
  then have \<open>f (Q ! n) ` set as \<subseteq> reach f as x\<close>
    by (auto intro: step_in_reach)
  with inv set_zs have \<open>set (Q @ zs) \<subseteq> reach f as x\<close>
    by (simp add: explore_inv_def)
  moreover have \<open>k < Suc n \<Longrightarrow> a \<in> set as \<Longrightarrow> f ((Q @ zs) ! k) a \<in> set (Q @ zs)\<close> for k a
    using inv \<open>n < length Q\<close> set_zs by (auto simp: explore_inv_def nth_append less_Suc_eq)
  moreover from inv Q' have \<open>distinct (Q @ zs)\<close>
    using distinct_foldl_add_new[of Q \<open>map (f (Q ! n)) as\<close>] by (simp add: explore_inv_def)
  moreover from Pair Q' have \<open>explore_step f as s = (Q @ zs, Suc n)\<close>
    by (simp add: explore_step_def)
  ultimately show ?thesis
    using inv \<open>n < length Q\<close> by (simp add: explore_inv_def nth_append)
qed

text \<open>A result of the worklist is the reachable set, closed under the transitions:\<close>

lemma explore_result:
  assumes \<open>explore f as x = Some (Q, n)\<close>
  shows \<open>n = length Q \<and> distinct Q \<and> Q \<noteq> [] \<and> Q ! 0 = x \<and> set Q = reach f as x \<and>
    (\<forall>q \<in> set Q. \<forall>a \<in> set as. f q a \<in> set Q)\<close>
proof -
  have \<open>explore_inv f as x (Q, n)\<close>
    using explore_inv_step assms[unfolded explore_def] explore_inv_start
    by (rule while_option_rule)
  moreover from assms have \<open>\<not> n < length Q\<close>
    unfolding explore_def by (auto dest: while_option_stop)
  ultimately have inv: \<open>explore_inv f as x (Q, length Q)\<close> and \<open>n = length Q\<close>
    by (auto simp: explore_inv_def)
  then have \<open>\<forall>k < length Q. \<forall>a \<in> set as. f (Q ! k) a \<in> set Q\<close>
    by (simp add: explore_inv_def)
  then have closed: \<open>\<forall>q \<in> set Q. \<forall>a \<in> set as. f q a \<in> set Q\<close>
    by (auto simp: in_set_conv_nth[of _ Q])
  with inv have \<open>reach f as x \<subseteq> set Q\<close>
    by (intro reach_subset) (auto simp: explore_inv_def intro: nth_mem)
  with inv closed \<open>n = length Q\<close> show ?thesis
    by (auto simp: explore_inv_def)
qed

text \<open>The worklist terminates when the reachable set is finite (each step processes one
  more state, and the found states are distinct and reachable):\<close>

lemma explore_Some:
  assumes \<open>finite (reach f as x)\<close>
  shows \<open>\<exists>Q. explore f as x = Some (Q, length Q)\<close>
proof -
  have \<open>\<exists>t. explore f as x = Some t\<close>
    unfolding explore_def
  proof (rule measure_while_option_Some[where P = \<open>explore_inv f as x\<close>
        and f = \<open>\<lambda>(Q, n). card (reach f as x) - n\<close>])
    fix t
    assume inv: \<open>explore_inv f as x t\<close> and b: \<open>case t of (Q, n) \<Rightarrow> n < length Q\<close>
    obtain Q n where t: \<open>t = (Q, n)\<close>
      by (cases t) blast
    from inv b have inv': \<open>explore_inv f as x (explore_step f as t)\<close>
      by (rule explore_inv_step)
    obtain Q' where step: \<open>explore_step f as t = (Q', Suc n)\<close>
      by (simp add: explore_step_def t)
    with inv' have \<open>Suc n \<le> length Q'\<close> \<open>distinct Q'\<close> \<open>set Q' \<subseteq> reach f as x\<close>
      by (auto simp: explore_inv_def)
    then have \<open>Suc n \<le> card (reach f as x)\<close>
      using card_mono[OF assms \<open>set Q' \<subseteq> reach f as x\<close>] distinct_card[OF \<open>distinct Q'\<close>]
      by simp
    with inv' step t show \<open>explore_inv f as x (explore_step f as t) \<and>
      (case explore_step f as t of (Q, n) \<Rightarrow> card (reach f as x) - n) <
      (case t of (Q, n) \<Rightarrow> card (reach f as x) - n)\<close>
      by simp
  qed (rule explore_inv_start)
  then obtain Q n where \<open>explore f as x = Some (Q, n)\<close>
    by auto
  with explore_result[OF this] show ?thesis
    by blast
qed

text \<open>The transition table of an explored list of states holds the index of each
  successor:\<close>

primrec index_of :: \<open>'s list \<Rightarrow> 's \<Rightarrow> nat\<close> where
  \<open>index_of [] y = 0\<close>
| \<open>index_of (z # Q) y = (if z = y then 0 else Suc (index_of Q y))\<close>

lemma index_of_less: \<open>y \<in> set Q \<Longrightarrow> index_of Q y < length Q\<close>
  by (induct Q) auto

lemma nth_index_of: \<open>y \<in> set Q \<Longrightarrow> Q ! index_of Q y = y\<close>
  by (induct Q) auto

definition table :: \<open>('s \<Rightarrow> 'a \<Rightarrow> 's) \<Rightarrow> 'a list \<Rightarrow> 's list \<Rightarrow> nat list list\<close> where
  \<open>table f as Q = map (\<lambda>q. map (\<lambda>a. index_of Q (f q a)) as) Q\<close>

lemma table_correct:
  assumes \<open>\<forall>q \<in> set Q. \<forall>a \<in> set as. f q a \<in> set Q\<close> \<open>k < length Q\<close> \<open>j < length as\<close>
  shows \<open>table f as Q ! k ! j < length Q \<and> Q ! (table f as Q ! k ! j) = f (Q ! k) (as ! j)\<close>
  using assms by (simp add: table_def index_of_less nth_index_of)

subsection \<open>States, transitions and acceptance\<close>

type_synonym 'p state = \<open>(nat \<times> 'p rexp) set\<close>

text \<open>The initial state pairs every rule with its regex. A transition by the class
  \<open>S\<close> takes the partial derivatives of every pair and keeps its rule index:\<close>

definition init_state :: \<open>('k, 'p, 'ch, 'm) rule list \<Rightarrow> 'p state\<close> where
  \<open>init_state rs = set (map (\<lambda>i. (i, match (rs ! i))) [0 ..< length rs])\<close>

definition delta :: \<open>'p state \<Rightarrow> 'p set \<Rightarrow> 'p state\<close> where
  \<open>delta X S = (\<Union>(i, r) \<in> X. {i} \<times> pderiv_cls S r)\<close>

lemma mem_init_state[simp]:
  \<open>(i, r) \<in> init_state rs \<longleftrightarrow> i < length rs \<and> r = match (rs ! i)\<close>
  by (auto simp: init_state_def)

text \<open>The empty state is dead:\<close>

lemma delta_empty[simp]: \<open>delta {} S = {}\<close>
  by (simp add: delta_def)

text \<open>A state accepts with the least rule index of a nullable pair
  \<^cite>\<open>\<open>Fig. 4, FirstToken\<close> in "egolf2021-verbatim-verified-lexer"\<close>:\<close>

definition acc :: \<open>'p state \<Rightarrow> nat option\<close> where
  \<open>acc X = (if \<exists>i r. (i, r) \<in> X \<and> nullable r
    then Some (LEAST i. \<exists>r. (i, r) \<in> X \<and> nullable r) else None)\<close>

lemma acc_Some_iff:
  \<open>acc X = Some i \<longleftrightarrow>
    (\<exists>r. (i, r) \<in> X \<and> nullable r) \<and> (\<forall>j < i. \<not> (\<exists>r. (j, r) \<in> X \<and> nullable r))\<close>
  (is \<open>_ \<longleftrightarrow> ?N i \<and> (\<forall>j < i. \<not> ?N j)\<close>)
proof
  assume \<open>acc X = Some i\<close>
  then have \<open>\<exists>i. ?N i\<close> \<open>i = (LEAST i. ?N i)\<close>
    by (auto simp: acc_def split: if_splits)
  then show \<open>?N i \<and> (\<forall>j < i. \<not> ?N j)\<close>
    using LeastI_ex[of ?N] not_less_Least[of _ ?N] by blast
next
  assume N: \<open>?N i \<and> (\<forall>j < i. \<not> ?N j)\<close>
  have \<open>(LEAST i. ?N i) = i\<close>
  proof (rule Least_equality)
    show \<open>?N i\<close>
      using N by blast
  next
    fix j
    assume \<open>?N j\<close>
    with N show \<open>i \<le> j\<close>
      by (meson leI)
  qed
  with N show \<open>acc X = Some i\<close>
    by (auto simp: acc_def)
qed

lemma acc_None_iff: \<open>acc X = None \<longleftrightarrow> (\<forall>i. \<not> (\<exists>r. (i, r) \<in> X \<and> nullable r))\<close>
  by (auto simp: acc_def)

text \<open>On a state given by a list, the least index is a minimum:\<close>

lemma acc_code[code]:
  \<open>acc (set xs) = (let ns = map fst (filter (nullable \<circ> snd) xs) in
    if ns = [] then None else Some (Min (set ns)))\<close>
proof -
  let ?P = \<open>\<lambda>i. \<exists>r. (i, r) \<in> set xs \<and> nullable r\<close>
  have P: \<open>{i. ?P i} = set (map fst (filter (nullable \<circ> snd) xs))\<close>
    by (auto intro: rev_image_eqI)
  show ?thesis
  proof (cases \<open>\<exists>i. ?P i\<close>)
    case True
    with P have \<open>(LEAST i. ?P i) = Min {i. ?P i}\<close>
      by (subst Least_Min) auto
    with True P show ?thesis
      by (auto simp: acc_def Let_def filter_empty_conv)
  next
    case False
    then have \<open>filter (nullable \<circ> snd) xs = []\<close>
      by (auto simp: filter_empty_conv)
    with False show ?thesis
      by (simp add: acc_def)
  qed
qed

subsection \<open>The bound on the states\<close>

lemma pderivs_cls_snoc: \<open>pderivs_cls (Ss @ [S]) r = \<Union> (pderiv_cls S ` pderivs_cls Ss r)\<close>
  by (induct Ss arbitrary: r) auto

lemma in_pderiv_closure_self: \<open>r \<in> pderiv_closure r\<close>
  by (auto simp: pderiv_closure_def intro: exI[of _ \<open>[]\<close>])

lemma pderiv_cls_subset_pderiv_closure:
  assumes \<open>r \<in> pderiv_closure r\<^sub>0\<close>
  shows \<open>pderiv_cls S r \<subseteq> pderiv_closure r\<^sub>0\<close>
proof -
  from assms obtain Ss where \<open>r \<in> pderivs_cls Ss r\<^sub>0\<close>
    by (auto simp: pderiv_closure_def)
  then have \<open>pderiv_cls S r \<subseteq> pderivs_cls (Ss @ [S]) r\<^sub>0\<close>
    by (auto simp: pderivs_cls_snoc)
  then show ?thesis
    by (auto simp: pderiv_closure_def)
qed

lemma atoms_pderiv_cls: \<open>r' \<in> pderiv_cls S r \<Longrightarrow> atoms r' \<subseteq> atoms r\<close>
proof (induct r arbitrary: r')
  case (Plus r s)
  then show ?case
    by (auto dest!: Plus.hyps)
next
  case (Times r s)
  then show ?case
    by (auto split: if_splits dest!: Times.hyps)
next
  case (Star r)
  then show ?case
    by (auto dest!: Star.hyps)
qed (auto split: if_splits)

lemma atoms_pderivs_cls: \<open>r' \<in> pderivs_cls Ss r \<Longrightarrow> atoms r' \<subseteq> atoms r\<close>
proof (induct Ss arbitrary: r)
  case (Cons S Ss)
  then obtain r'' where \<open>r'' \<in> pderiv_cls S r\<close> \<open>r' \<in> pderivs_cls Ss r''\<close>
    by auto
  with Cons.hyps have \<open>atoms r' \<subseteq> atoms r''\<close>
    by blast
  also from \<open>r'' \<in> pderiv_cls S r\<close> have \<open>\<dots> \<subseteq> atoms r\<close>
    by (rule atoms_pderiv_cls)
  finally show ?case .
qed simp

lemma atoms_if_in_pderiv_closure: \<open>r' \<in> pderiv_closure r \<Longrightarrow> atoms r' \<subseteq> atoms r\<close>
  by (auto simp: pderiv_closure_def dest!: atoms_pderivs_cls)

text \<open>Every state is a set of pairs of a rule index and a partial derivative of that
  rule's regex. These pairs are finitely many, at most the sum of the rules' alphabetic
  widths plus one each \<^cite>\<open>\<open>Thm. 3.4\<close> in "antimirov1996-partial-derivatives"\<close>:\<close>

definition tagged_closure :: \<open>('k, 'p, 'ch, 'm) rule list \<Rightarrow> (nat \<times> 'p rexp) set\<close> where
  \<open>tagged_closure rs = (\<Union>i < length rs. {i} \<times> pderiv_closure (match (rs ! i)))\<close>

lemma finite_tagged_closure: \<open>finite (tagged_closure rs)\<close>
  by (simp add: tagged_closure_def finite_pderiv_closure)

lemma card_tagged_closure_le:
  \<open>card (tagged_closure rs) \<le> (\<Sum>i < length rs. awidth (match (rs ! i)) + 1)\<close>
proof -
  have \<open>card (tagged_closure rs) \<le> (\<Sum>i < length rs. card (pderiv_closure (match (rs ! i))))\<close>
    using card_UN_le[of \<open>{..<length rs}\<close> \<open>\<lambda>i. {i} \<times> pderiv_closure (match (rs ! i))\<close>]
    by (simp add: tagged_closure_def card_cartesian_product_singleton)
  also have \<open>\<dots> \<le> (\<Sum>i < length rs. awidth (match (rs ! i)) + 1)\<close>
    by (rule sum_mono) (rule card_pderiv_closure_le_awidth)
  finally show ?thesis .
qed

lemma init_state_subset: \<open>init_state rs \<subseteq> tagged_closure rs\<close>
  by (auto simp: tagged_closure_def in_pderiv_closure_self)

lemma delta_subset:
  assumes \<open>X \<subseteq> tagged_closure rs\<close>
  shows \<open>delta X S \<subseteq> tagged_closure rs\<close>
proof
  fix x
  assume \<open>x \<in> delta X S\<close>
  then obtain i r r' where \<open>(i, r) \<in> X\<close> \<open>r' \<in> pderiv_cls S r\<close> \<open>x = (i, r')\<close>
    by (auto simp: delta_def)
  with assms show \<open>x \<in> tagged_closure rs\<close>
    by (auto simp: tagged_closure_def dest: pderiv_cls_subset_pderiv_closure)
qed

lemma reach_subset_Pow: \<open>reach delta Ss (init_state rs) \<subseteq> Pow (tagged_closure rs)\<close>
  by (rule reach_subset) (auto simp: init_state_subset delta_subset)

text \<open>Exploration of the states of a mode terminates, whatever the classes:\<close>

theorem explore_dfa_Some: \<open>\<exists>Q. explore delta Ss (init_state rs) = Some (Q, length Q)\<close>
  by (rule explore_Some, rule finite_subset[OF reach_subset_Pow]) (simp add: finite_tagged_closure)

subsection \<open>The generator\<close>

text \<open>The generator explores the states of a mode over a list of classes and returns
  them with the transition table, indexed by state and class number, and the
  acceptance table. The states are for the proofs only (the runner reads the two
  tables):\<close>

record 'p dfa =
  dfa_states :: \<open>'p state list\<close>
  dfa_trans :: \<open>nat list list\<close>
  dfa_accept :: \<open>nat option list\<close>

definition dfa :: \<open>'p set list \<Rightarrow> ('k, 'p, 'ch, 'm) rule list \<Rightarrow> 'p dfa\<close> where
  \<open>dfa Ss rs = (let Q = fst (the (explore delta Ss (init_state rs))) in
    \<lparr>dfa_states = Q, dfa_trans = table delta Ss Q, dfa_accept = map acc Q\<rparr>)\<close>

lemma dfa_states_explored:
  \<open>explore delta Ss (init_state rs) =
    Some (dfa_states (dfa Ss rs), length (dfa_states (dfa Ss rs)))\<close>
  using explore_dfa_Some[of Ss rs] by (auto simp: dfa_def Let_def)

lemmas dfa_states_explore_result = explore_result[OF dfa_states_explored]

lemma dfa_states_subset: \<open>X \<in> set (dfa_states (dfa Ss rs)) \<Longrightarrow> X \<subseteq> tagged_closure rs\<close>
  using dfa_states_explore_result[of Ss rs] reach_subset_Pow by blast

text \<open>The number of states is bounded by the alphabetic widths of the rules:\<close>

theorem length_dfa_states_le:
  \<open>length (dfa_states (dfa Ss rs)) \<le> 2 ^ (\<Sum>i < length rs. awidth (match (rs ! i)) + 1)\<close>
proof -
  let ?Q = \<open>dfa_states (dfa Ss rs)\<close>
  have \<open>distinct ?Q\<close>
    using dfa_states_explore_result[of Ss rs] by blast
  then have \<open>length ?Q = card (set ?Q)\<close>
    by (simp add: distinct_card)
  also have \<open>\<dots> \<le> card (Pow (tagged_closure rs))\<close>
    using dfa_states_subset by (intro card_mono) (auto simp: finite_tagged_closure)
  also have \<open>\<dots> \<le> 2 ^ (\<Sum>i < length rs. awidth (match (rs ! i)) + 1)\<close>
    using card_tagged_closure_le[of rs] by (simp add: card_Pow finite_tagged_closure)
  finally show ?thesis .
qed

lemma dfa_trans_eq: \<open>dfa_trans (dfa Ss rs) = table delta Ss (dfa_states (dfa Ss rs))\<close>
  by (simp add: dfa_def Let_def)

lemma length_dfa_trans: \<open>length (dfa_trans (dfa Ss rs)) = length (dfa_states (dfa Ss rs))\<close>
  by (simp add: dfa_def Let_def table_def)

lemma length_dfa_trans_row:
  \<open>k < length (dfa_states (dfa Ss rs)) \<Longrightarrow> length (dfa_trans (dfa Ss rs) ! k) = length Ss\<close>
  by (simp add: dfa_def Let_def table_def)

lemma dfa_trans_correct:
  assumes \<open>k < length (dfa_states (dfa Ss rs))\<close> \<open>j < length Ss\<close>
  shows \<open>dfa_trans (dfa Ss rs) ! k ! j < length (dfa_states (dfa Ss rs)) \<and>
    dfa_states (dfa Ss rs) ! (dfa_trans (dfa Ss rs) ! k ! j) =
      delta (dfa_states (dfa Ss rs) ! k) (Ss ! j)\<close>
proof -
  have \<open>\<forall>X \<in> set (dfa_states (dfa Ss rs)). \<forall>S \<in> set Ss. delta X S \<in> set (dfa_states (dfa Ss rs))\<close>
    using dfa_states_explore_result[of Ss rs] by blast
  from table_correct[OF this assms] show ?thesis
    by (simp add: dfa_trans_eq)
qed

lemma dfa_accept_eq: \<open>dfa_accept (dfa Ss rs) = map acc (dfa_states (dfa Ss rs))\<close>
  by (simp add: dfa_def Let_def)

subsection \<open>Correctness by character and by word\<close>

context symbolic
begin

text \<open>The step of a state by a character takes the partial derivatives by that
  character:\<close>

definition delta_char :: \<open>'p state \<Rightarrow> 'ch \<Rightarrow> 'p state\<close> where
  \<open>delta_char X c = (\<Union>(i, r) \<in> X. {i} \<times> pderiv c r)\<close>

lemma foldl_delta_char: \<open>foldl delta_char X w = (\<Union>(i, r) \<in> X. {i} \<times> pderivs w r)\<close>
  by (induct w arbitrary: X) (auto simp: delta_char_def)

text \<open>Reading \<open>w\<close> from the initial state reaches a nullable pair of rule \<open>i\<close> exactly
  when \<open>w\<close> is in the language of rule \<open>i\<close> (@{thm [source] Derivs_pderivs}):\<close>

lemma nullable_in_foldl_delta_char_iff:
  \<open>(\<exists>r. (i, r) \<in> foldl delta_char (init_state rs) w \<and> nullable r) \<longleftrightarrow>
    i < length rs \<and> w \<in> lang (match (rs ! i))\<close>
proof -
  have \<open>w \<in> lang r \<longleftrightarrow> [] \<in> Derivs w (lang r)\<close> for r
    by (simp add: Derivs_def)
  then have \<open>w \<in> lang r \<longleftrightarrow> (\<exists>r' \<in> pderivs w r. nullable r')\<close> for r
    by (simp add: Derivs_pderivs nullable_iff)
  then show ?thesis
    by (auto simp: foldl_delta_char Bex_def)
qed

lemma acc_foldl_delta_char_Some_iff:
  \<open>acc (foldl delta_char (init_state rs) w) = Some i \<longleftrightarrow>
    i < length rs \<and> w \<in> lang (match (rs ! i)) \<and> (\<forall>j < i. w \<notin> lang (match (rs ! j)))\<close>
  unfolding acc_Some_iff nullable_in_foldl_delta_char_iff by auto

lemma acc_foldl_delta_char_None_iff:
  \<open>acc (foldl delta_char (init_state rs) w) = None \<longleftrightarrow>
    (\<forall>i < length rs. w \<notin> lang (match (rs ! i)))\<close>
  unfolding acc_None_iff nullable_in_foldl_delta_char_iff by auto

text \<open>On a nonempty word, the accepting rule is the first rule that matches it in the
  sense of \<^const>\<open>match_rule\<close>:\<close>

lemma acc_foldl_delta_char_match_rule:
  assumes \<open>w \<noteq> []\<close>
  shows \<open>acc (foldl delta_char (init_state rs) w) = Some i \<longleftrightarrow>
    i < length rs \<and> match_rule (rs ! i) w \<and> (\<forall>j < i. \<not> match_rule (rs ! j) w)\<close>
  using assms by (auto simp: acc_foldl_delta_char_Some_iff match_rule.simps)

text \<open>The dead state stays dead:\<close>

lemma foldl_delta_char_empty[simp]: \<open>foldl delta_char {} w = {}\<close>
  by (simp add: foldl_delta_char)

end

subsection \<open>The DFA of a mode over its minterms\<close>

text \<open>The atoms of a mode, collected as \<open>add_atoms\<close> does in \<^session>\<open>Regular-Sets\<close>
  (\<open>Equivalence_Checking\<close>):\<close>

primrec atom_list :: \<open>'p rexp \<Rightarrow> 'p list\<close> where
  \<open>atom_list Zero = []\<close>
| \<open>atom_list One = []\<close>
| \<open>atom_list (Atom p) = [p]\<close>
| \<open>atom_list (Plus r s) = atom_list r @ atom_list s\<close>
| \<open>atom_list (Times r s) = atom_list r @ atom_list s\<close>
| \<open>atom_list (Star r) = atom_list r\<close>

lemma set_atom_list[simp]: \<open>set (atom_list r) = atoms r\<close>
  by (induct r) auto

definition mode_atoms :: \<open>('k, 'p, 'ch, 'm) rule list \<Rightarrow> 'p list\<close> where
  \<open>mode_atoms rs = remdups (concat (map (atom_list \<circ> match) rs))\<close>

lemma atoms_subset_mode_atoms: \<open>i < length rs \<Longrightarrow> atoms (match (rs ! i)) \<subseteq> set (mode_atoms rs)\<close>
  by (auto simp: mode_atoms_def intro: nth_mem)

context eba
begin

definition mode_minterms :: \<open>('k, 'p, 'ch, 'm) rule list \<Rightarrow> ('p set \<times> 'p) list\<close> where
  \<open>mode_minterms rs = minterms (mode_atoms rs)\<close>

definition mode_dfa :: \<open>('k, 'p, 'ch, 'm) rule list \<Rightarrow> 'p dfa\<close> where
  \<open>mode_dfa rs = dfa (map fst (mode_minterms rs)) rs\<close>

text \<open>A transition by a minterm is the step by any character of it
  \<^cite>\<open>\<open>Thm. 12\<close> in "keil2014-symbolic-regex-inequalities"\<close>:\<close>

lemma delta_eq_delta_char:
  assumes \<open>X \<subseteq> tagged_closure rs\<close> \<open>(S, \<mu>) \<in> set (mode_minterms rs)\<close> \<open>sem \<mu> c\<close>
  shows \<open>delta X S = delta_char X c\<close>
proof -
  have \<open>pderiv_cls S r = pderiv c r\<close> if \<open>(i, r) \<in> X\<close> for i r
  proof -
    from that assms(1) have \<open>i < length rs\<close> \<open>r \<in> pderiv_closure (match (rs ! i))\<close>
      by (auto simp: tagged_closure_def)
    then have \<open>atoms r \<subseteq> set (mode_atoms rs)\<close>
      by (meson atoms_if_in_pderiv_closure atoms_subset_mode_atoms order_trans)
    with assms(2,3) show ?thesis
      by (simp add: pderiv_eq_pderiv_cls_minterm mode_minterms_def)
  qed
  then show ?thesis
    unfolding delta_def delta_char_def by (auto intro!: SUP_cong)
qed

text \<open>The minterm of a character. The run-time lexer replaces it by a table lookup:\<close>

definition minterm_index :: \<open>('k, 'p, 'ch, 'm) rule list \<Rightarrow> 'ch \<Rightarrow> nat\<close> where
  \<open>minterm_index rs c =
    (LEAST k. k < length (mode_minterms rs) \<and> sem (snd (mode_minterms rs ! k)) c)\<close>

lemma minterm_index:
  \<open>minterm_index rs c < length (mode_minterms rs) \<and>
    sem (snd (mode_minterms rs ! minterm_index rs c)) c\<close>
proof -
  obtain S \<mu> where \<open>(S, \<mu>) \<in> set (mode_minterms rs)\<close> \<open>sem \<mu> c\<close>
    using minterms_cover[of \<open>mode_atoms rs\<close> c] unfolding mode_minterms_def by blast
  then obtain k where \<open>k < length (mode_minterms rs) \<and> sem (snd (mode_minterms rs ! k)) c\<close>
    by (metis in_set_conv_nth snd_conv)
  then show ?thesis
    unfolding minterm_index_def by (rule LeastI)
qed

text \<open>The tables run on a word, a character at a time through its minterm:\<close>

definition dfa_run :: \<open>('k, 'p, 'ch, 'm) rule list \<Rightarrow> 'ch list \<Rightarrow> nat\<close> where
  \<open>dfa_run rs w = foldl (\<lambda>q c. dfa_trans (mode_dfa rs) ! q ! minterm_index rs c) 0 w\<close>

lemma dfa_run_from_correct:
  assumes \<open>q < length (dfa_states (mode_dfa rs))\<close>
  shows \<open>foldl (\<lambda>q c. dfa_trans (mode_dfa rs) ! q ! minterm_index rs c) q w
      < length (dfa_states (mode_dfa rs)) \<and>
    dfa_states (mode_dfa rs) ! foldl (\<lambda>q c. dfa_trans (mode_dfa rs) ! q ! minterm_index rs c) q w
      = foldl delta_char (dfa_states (mode_dfa rs) ! q) w\<close>
  using assms
proof (induct w arbitrary: q)
  case (Cons c w)
  let ?M = \<open>mode_minterms rs\<close>
  let ?Q = \<open>dfa_states (mode_dfa rs)\<close>
  let ?k = \<open>minterm_index rs c\<close>
  let ?q' = \<open>dfa_trans (mode_dfa rs) ! q ! ?k\<close>
  from minterm_index have k: \<open>?k < length ?M\<close> \<open>sem (snd (?M ! ?k)) c\<close>
    by blast+
  have q': \<open>?q' < length ?Q \<and> ?Q ! ?q' = delta (?Q ! q) (fst (?M ! ?k))\<close>
    using dfa_trans_correct[of q \<open>map fst ?M\<close> rs ?k] Cons.prems k(1)
    by (simp add: mode_dfa_def)
  have \<open>?Q ! q \<subseteq> tagged_closure rs\<close>
    using dfa_states_subset[OF nth_mem[OF Cons.prems[unfolded mode_dfa_def]]]
    by (simp add: mode_dfa_def)
  moreover have \<open>(fst (?M ! ?k), snd (?M ! ?k)) \<in> set ?M\<close>
    using k(1) by simp
  ultimately have \<open>delta (?Q ! q) (fst (?M ! ?k)) = delta_char (?Q ! q) c\<close>
    using k(2) by (rule delta_eq_delta_char)
  with q' Cons.hyps[of ?q'] show ?case
    by simp
qed simp

text \<open>The state the tables reach on \<open>w\<close> is the step of the initial state by \<open>w\<close>:\<close>

theorem dfa_run_correct:
  \<open>dfa_run rs w < length (dfa_states (mode_dfa rs)) \<and>
    dfa_states (mode_dfa rs) ! dfa_run rs w = foldl delta_char (init_state rs) w\<close>
  using dfa_run_from_correct[of 0 rs w] dfa_states_explore_result[of _ rs]
  by (simp add: dfa_run_def mode_dfa_def)

text \<open>The acceptance table names the least rule whose language contains the word read:\<close>

theorem dfa_run_accept_Some_iff:
  \<open>dfa_accept (mode_dfa rs) ! dfa_run rs w = Some i \<longleftrightarrow>
    i < length rs \<and> w \<in> lang (match (rs ! i)) \<and> (\<forall>j < i. w \<notin> lang (match (rs ! j)))\<close>
  using dfa_run_correct[of rs w]
  by (simp add: mode_dfa_def dfa_accept_eq acc_foldl_delta_char_Some_iff)

theorem dfa_run_accept_None_iff:
  \<open>dfa_accept (mode_dfa rs) ! dfa_run rs w = None \<longleftrightarrow>
    (\<forall>i < length rs. w \<notin> lang (match (rs ! i)))\<close>
  using dfa_run_correct[of rs w]
  by (simp add: mode_dfa_def dfa_accept_eq acc_foldl_delta_char_None_iff)

end

end
