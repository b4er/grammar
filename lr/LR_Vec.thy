theory LR_Vec
  imports LR_Parser.LR_Sparse
begin

section \<open>A state-indexed driver with precomputed closures\<close>

text \<open>The set-anchored drivers of \<^text>\<open>LR_Driver\<close> and \<^text>\<open>LR_Sparse\<close> compute a
  closure after every step as a fixpoint over the kernel's anchor sets.  The
  closure's \<^emph>\<open>shape\<close> is a property of the LR(0) state alone: which productions
  get a slot, and from which kernel item each slot's anchors descend, through
  which chain of right-hand-side relations.  Only the anchor sets are
  input-dependent, and a chain of relations acts on an anchor set as one of three
  transfers: the identity (\<^const>\<open>Eq\<close>), the up-set from the least anchor plus an
  offset (\<^const>\<open>Gt\<close>, \<^const>\<open>Ge\<close>), or the up-set from a constant
  (\<^const>\<open>Any\<close>).  The driver of this theory tabulates, per state, its items,
  the transfer from each kernel item to each slot, the predecessor of each
  kernel item under each symbol, and its reduce cells, so that a step does no
  search: it indexes.

  The driver returns what \<^const>\<open>dparse\<close> returns on every input, for a grammar
  whose automaton is deterministic (\<^const>\<open>mdet\<close>).  Without determinism the two
  could pick different reduce candidates, since this driver's items are in table
  order rather than in the order the kernels happen to arrive in.\<close>

subsection \<open>Canonical anchor sets\<close>

text \<open>\<^const>\<open>irep_union\<close> concatenates and \<^const>\<open>irep_pre\<close> materialises intervals,
  so anchor sets of the running drivers carry duplicates.  The operations here
  keep a set sorted and duplicate-free, with the finite part of an
  \<^const>\<open>UpRep\<close> below its bound; only the set an operation denotes enters the
  correctness argument.\<close>

fun merge :: \<open>nat list \<Rightarrow> nat list \<Rightarrow> nat list\<close> where
  \<open>merge [] ys = ys\<close>
| \<open>merge xs [] = xs\<close>
| \<open>merge (x # xs) (y # ys) =
    (if x < y then x # merge xs (y # ys)
     else if y < x then y # merge (x # xs) ys else x # merge xs ys)\<close>

lemma set_merge [simp]: \<open>set (merge xs ys) = set xs \<union> set ys\<close>
  by (induction xs ys rule: merge.induct) auto

fun cunion :: \<open>indrep \<Rightarrow> indrep \<Rightarrow> indrep\<close> where
  \<open>cunion (FinRep xs) (FinRep ys) = FinRep (merge xs ys)\<close>
| \<open>cunion (FinRep xs) (UpRep ys n) = UpRep (filter (\<lambda>i. i < n) (merge xs ys)) n\<close>
| \<open>cunion (UpRep xs n) (FinRep ys) = UpRep (filter (\<lambda>i. i < n) (merge xs ys)) n\<close>
| \<open>cunion (UpRep xs n) (UpRep ys m) = UpRep (filter (\<lambda>i. i < min n m) (merge xs ys)) (min n m)\<close>

lemma cunion_set [simp]: \<open>irep_set (cunion R S) = irep_set R \<union> irep_set S\<close>
  by (cases R; cases S) auto

text \<open>The set with the up-set from \<open>t\<close> added.\<close>

fun cup :: \<open>nat \<Rightarrow> indrep \<Rightarrow> indrep\<close> where
  \<open>cup t (FinRep xs) = UpRep (filter (\<lambda>i. i < t) xs) t\<close>
| \<open>cup t (UpRep xs n) = UpRep (filter (\<lambda>i. i < min t n) xs) (min t n)\<close>

lemma cup_set [simp]: \<open>irep_set (cup t R) = irep_set R \<union> {m. t \<le> m}\<close>
  by (cases R) auto

fun cinter :: \<open>indrep \<Rightarrow> indrep \<Rightarrow> indrep\<close> where
  \<open>cinter (FinRep xs) S = FinRep (filter (\<lambda>i. irep_mem i S) xs)\<close>
| \<open>cinter (UpRep xs n) (FinRep ys) = FinRep (filter (\<lambda>i. irep_mem i (UpRep xs n)) ys)\<close>
| \<open>cinter (UpRep xs n) (UpRep ys m) =
     UpRep (filter (\<lambda>i. i < max n m)
       (merge (filter (\<lambda>i. irep_mem i (UpRep ys m)) xs) (filter (\<lambda>i. irep_mem i (UpRep xs n)) ys)))
       (max n m)\<close>

lemma cinter_set [simp]: \<open>irep_set (cinter R S) = irep_set R \<inter> irep_set S\<close>
  by (cases R; cases S) auto

text \<open>The elements below a bound, as a finite set.\<close>

fun cbelow :: \<open>nat \<Rightarrow> indrep \<Rightarrow> indrep\<close> where
  \<open>cbelow b (FinRep xs) = FinRep (filter (\<lambda>i. i < b) xs)\<close>
| \<open>cbelow b (UpRep xs n) = FinRep (filter (\<lambda>i. i < b) xs @ [n..<b])\<close>

lemma cbelow_set [simp]: \<open>irep_set (cbelow b R) = irep_set R \<inter> {i. i < b}\<close>
  by (cases R) auto

lemma fold_max_lt_iff: \<open>i < fold max ys a \<longleftrightarrow> i < a \<or> (\<exists>y \<in> set ys. i < y)\<close> for ys :: \<open>nat list\<close>
  using Max.set_eq_fold[of a ys, symmetric] by (simp add: Max_gr_iff)

lemma fold_max_le_iff: \<open>i \<le> fold max ys a \<longleftrightarrow> i \<le> a \<or> (\<exists>y \<in> set ys. i \<le> y)\<close> for ys :: \<open>nat list\<close>
  using Max.set_eq_fold[of a ys, symmetric] by (simp add: Max_ge_iff)

lemma up_unbounded: \<open>\<exists>j \<in> A \<union> Collect ((\<le>) n). x < j\<close> \<open>\<exists>j \<in> A \<union> Collect ((\<le>) n). x \<le> j\<close>
  for n x :: nat
  by (rule bexI[of _ \<open>max (Suc x) n\<close>]; simp)+

text \<open>The parent anchors in \<open>R\<close> compatible with a child anchor in \<open>RA\<close>:
  \<^term>\<open>irep_inter R (irep_pre q RA)\<close> without materialising the preimage.\<close>

definition cpre :: \<open>irel \<Rightarrow> indrep \<Rightarrow> indrep \<Rightarrow> indrep\<close> where
  \<open>cpre q RA R = (case q of
     Eq \<Rightarrow> cinter R RA
   | Gt \<Rightarrow> (case RA of FinRep ys \<Rightarrow> (if ys = [] then FinRep [] else cbelow (fold max ys 0) R)
            | UpRep _ _ \<Rightarrow> R)
   | Ge \<Rightarrow> (case RA of FinRep ys \<Rightarrow> (if ys = [] then FinRep [] else cbelow (Suc (fold max ys 0)) R)
            | UpRep _ _ \<Rightarrow> R)
   | Any \<Rightarrow> (if irep_nonempty RA then R else FinRep []))\<close>

lemma cpre_set [simp]: \<open>irep_set (cpre q RA R) = irep_set R \<inter> irep_set (irep_pre q RA)\<close>
proof (cases q)
  case Gt
  then show ?thesis
    by (cases RA) (auto simp: cpre_def fold_max_lt_iff up_unbounded simp del: irep_pre.simps)
next
  case Ge
  then show ?thesis
    by (cases RA) (auto simp: cpre_def fold_max_le_iff less_Suc_eq_le up_unbounded ex_in_conv simp del: irep_pre.simps)
qed (auto simp: cpre_def)

subsection \<open>Anchor-set transfers\<close>

text \<open>A transfer is a join of up to three parts: the identity, the up-set from
  the least anchor shifted by \<open>d\<close>, and the up-set from a constant \<open>d\<close> (present only
  when the set is non-empty).  The relations of the grammar are transfers, and
  transfers are closed under join and composition.\<close>

type_synonym eff = \<open>bool \<times> nat option \<times> nat option\<close>

definition sh :: \<open>nat \<Rightarrow> nat set \<Rightarrow> nat set\<close> where \<open>sh d S = {m. \<exists>j \<in> S. j + d \<le> m}\<close>
definition cn :: \<open>nat \<Rightarrow> nat set \<Rightarrow> nat set\<close> where \<open>cn d S = {m. S \<noteq> {} \<and> d \<le> m}\<close>

definition osh :: \<open>nat option \<Rightarrow> nat set \<Rightarrow> nat set\<close> where
  \<open>osh s S = (case s of None \<Rightarrow> {} | Some d \<Rightarrow> sh d S)\<close>
definition ocn :: \<open>nat option \<Rightarrow> nat set \<Rightarrow> nat set\<close> where
  \<open>ocn c S = (case c of None \<Rightarrow> {} | Some d \<Rightarrow> cn d S)\<close>

fun eff_set :: \<open>eff \<Rightarrow> nat set \<Rightarrow> nat set\<close> where
  \<open>eff_set (i, s, c) S = (if i then S else {}) \<union> osh s S \<union> ocn c S\<close>

abbreviation ebot :: eff where \<open>ebot \<equiv> (False, None, None)\<close>
abbreviation eid :: eff where \<open>eid \<equiv> (True, None, None)\<close>

fun of_rel :: \<open>irel \<Rightarrow> eff\<close> where
  \<open>of_rel Eq = (True, None, None)\<close>
| \<open>of_rel Gt = (False, Some 1, None)\<close>
| \<open>of_rel Ge = (False, Some 0, None)\<close>
| \<open>of_rel Any = (False, None, Some 0)\<close>

lemma eff_set_of_rel: \<open>eff_set (of_rel q) S = {j. \<exists>i \<in> S. irel_sat q j i}\<close>
  by (cases q) (auto simp: osh_def ocn_def sh_def cn_def Suc_le_eq)

lemma eff_set_img: \<open>eff_set (of_rel q) (irep_set R) = irep_set (irep_img q R)\<close>
  by (simp add: eff_set_of_rel)

lemma osh_simps [simp]: \<open>osh None S = {}\<close> \<open>osh (Some d) S = sh d S\<close>
  and ocn_simps [simp]: \<open>ocn None S = {}\<close> \<open>ocn (Some d) S = cn d S\<close>
  by (simp_all add: osh_def ocn_def)

lemma sh_empty [simp]: \<open>sh d {} = {}\<close> and cn_empty [simp]: \<open>cn d {} = {}\<close>
  by (simp_all add: sh_def cn_def)

lemma osh_empty [simp]: \<open>osh s {} = {}\<close> and ocn_empty [simp]: \<open>ocn c {} = {}\<close>
  by (simp_all add: osh_def ocn_def split: option.splits)

lemma eff_set_empty [simp]: \<open>eff_set e {} = {}\<close>
  by (cases e) simp

lemma eff_set_bot [simp]: \<open>eff_set ebot S = {}\<close>
  by (simp add: osh_def ocn_def)

lemma eff_set_id [simp]: \<open>eff_set eid S = S\<close>
  by (simp add: osh_def ocn_def)

lemma sh_UN: \<open>sh d (\<Union> \<A>) = \<Union> (sh d ` \<A>)\<close> and cn_UN: \<open>cn d (\<Union> \<A>) = \<Union> (cn d ` \<A>)\<close>
  unfolding sh_def cn_def by auto

lemma osh_UN: \<open>osh s (\<Union> \<A>) = \<Union> (osh s ` \<A>)\<close> and ocn_UN: \<open>ocn c (\<Union> \<A>) = \<Union> (ocn c ` \<A>)\<close>
  unfolding osh_def ocn_def by (auto simp: sh_UN cn_UN split: option.splits)

lemma eff_set_UN: \<open>eff_set e (\<Union> \<A>) = \<Union> (eff_set e ` \<A>)\<close>
  by (cases e) (auto simp: osh_UN ocn_UN)

lemma eff_set_Un: \<open>eff_set e (A \<union> B) = eff_set e A \<union> eff_set e B\<close>
  using eff_set_UN[of e \<open>{A, B}\<close>] by simp

lemma eff_set_mono: \<open>A \<subseteq> B \<Longrightarrow> eff_set e A \<subseteq> eff_set e B\<close>
  by (metis eff_set_Un subset_Un_eq)

text \<open>Join: the parts of both.  The joins of the shifts and of the constants are
  their minima, since a smaller offset gives a larger up-set.\<close>

definition omin :: \<open>nat option \<Rightarrow> nat option \<Rightarrow> nat option\<close> where
  \<open>omin a b = (case a of None \<Rightarrow> b | Some x \<Rightarrow> (case b of None \<Rightarrow> Some x | Some y \<Rightarrow> Some (min x y)))\<close>

lemma sh_min: \<open>sh (min x y) S = sh x S \<union> sh y S\<close> and cn_min: \<open>cn (min x y) S = cn x S \<union> cn y S\<close>
  unfolding sh_def cn_def min_def
  by (auto 0 3 intro: le_trans add_left_mono) (meson add_le_cancel_left le_trans nat_le_linear)

lemma omin_simps [simp]:
  \<open>omin None b = b\<close> \<open>omin a None = a\<close> \<open>omin (Some x) (Some y) = Some (min x y)\<close>
  by (simp_all add: omin_def split: option.split)

lemma osh_omin: \<open>osh (omin a b) S = osh a S \<union> osh b S\<close>
  and ocn_omin: \<open>ocn (omin a b) S = ocn a S \<union> ocn b S\<close>
  unfolding osh_def ocn_def omin_def by (auto simp: sh_min cn_min split: option.splits)

fun ejoin :: \<open>eff \<Rightarrow> eff \<Rightarrow> eff\<close> where
  \<open>ejoin (i\<^sub>1, s\<^sub>1, c\<^sub>1) (i\<^sub>2, s\<^sub>2, c\<^sub>2) = (i\<^sub>1 \<or> i\<^sub>2, omin s\<^sub>1 s\<^sub>2, omin c\<^sub>1 c\<^sub>2)\<close>

lemma eff_set_join: \<open>eff_set (ejoin e f) S = eff_set e S \<union> eff_set f S\<close>
  by (cases e; cases f) (auto simp: osh_omin ocn_omin)

lemma eff_set_fold_ejoin: \<open>eff_set (fold ejoin xs a) S = eff_set a S \<union> (\<Union>x \<in> set xs. eff_set x S)\<close>
  by (induction xs arbitrary: a) (auto simp: eff_set_join)

text \<open>Composition, \<open>e\<^sub>2\<close> after \<open>e\<^sub>1\<close>: a shift after a shift adds the offsets, a
  constant after anything stays, a shift after a constant is a constant.\<close>

lemma sh_sh: \<open>sh d\<^sub>2 (sh d\<^sub>1 S) = sh (d\<^sub>1 + d\<^sub>2) S\<close>
  unfolding sh_def by (auto 0 3 intro: le_trans[OF add_right_mono] simp: add.assoc[symmetric])

lemma cn_sh: \<open>cn d\<^sub>2 (sh d\<^sub>1 S) = cn d\<^sub>2 S\<close>
  unfolding sh_def cn_def by auto

lemma sh_cn: \<open>sh d\<^sub>2 (cn d\<^sub>1 S) = cn (d\<^sub>1 + d\<^sub>2) S\<close>
  unfolding sh_def cn_def by auto

lemma cn_cn: \<open>cn d\<^sub>2 (cn d\<^sub>1 S) = cn d\<^sub>2 S\<close>
  unfolding cn_def by auto

lemma sh_absorb: \<open>d \<le> d' \<Longrightarrow> sh d' S \<subseteq> sh d S\<close> and cn_absorb: \<open>d \<le> d' \<Longrightarrow> cn d' S \<subseteq> cn d S\<close>
  unfolding sh_def cn_def by (auto intro: le_trans[OF add_left_mono])

text \<open>What a transfer \<open>e\<close> does after a shift, and after a constant, by \<open>d\<close>.\<close>

fun aft_sh :: \<open>nat \<Rightarrow> eff \<Rightarrow> eff\<close> where
  \<open>aft_sh d (i, s, c) = (False, omin (if i then Some d else None) (map_option ((+) d) s), c)\<close>

fun aft_cn :: \<open>nat \<Rightarrow> eff \<Rightarrow> eff\<close> where
  \<open>aft_cn d (i, s, c) =
     (False, None, omin (if i then Some d else None) (omin (map_option ((+) d) s) c))\<close>

lemma eff_set_after_sh: \<open>eff_set e (sh d S) = eff_set (aft_sh d e) S\<close>
proof (cases e)
  case (fields i s c)
  then show ?thesis
    using sh_absorb[of d \<open>d + _\<close> S]
    by (cases i; cases s; cases c) (auto simp: sh_sh cn_sh sh_min)
qed

lemma eff_set_after_cn: \<open>eff_set e (cn d S) = eff_set (aft_cn d e) S\<close>
proof (cases e)
  case (fields i s c)
  then show ?thesis
    using cn_absorb[of d \<open>d + _\<close> S]
    by (cases i; cases s; cases c) (auto simp: sh_cn cn_cn cn_min)
qed

fun ecomp :: \<open>eff \<Rightarrow> eff \<Rightarrow> eff\<close> where
  \<open>ecomp e\<^sub>2 (i\<^sub>1, s\<^sub>1, c\<^sub>1) =
     ejoin (if i\<^sub>1 then e\<^sub>2 else ebot)
      (ejoin (case s\<^sub>1 of None \<Rightarrow> ebot | Some d \<Rightarrow> aft_sh d e\<^sub>2)
             (case c\<^sub>1 of None \<Rightarrow> ebot | Some d \<Rightarrow> aft_cn d e\<^sub>2))\<close>

lemma eff_set_comp: \<open>eff_set (ecomp e\<^sub>2 e\<^sub>1) S = eff_set e\<^sub>2 (eff_set e\<^sub>1 S)\<close>
proof (cases e\<^sub>1)
  case (fields i s c)
  have \<open>eff_set e\<^sub>2 (osh s S) = eff_set (case s of None \<Rightarrow> ebot | Some d \<Rightarrow> aft_sh d e\<^sub>2) S\<close>
    by (cases s) (simp_all add: eff_set_after_sh)
  moreover have \<open>eff_set e\<^sub>2 (ocn c S) = eff_set (case c of None \<Rightarrow> ebot | Some d \<Rightarrow> aft_cn d e\<^sub>2) S\<close>
    by (cases c) (simp_all add: eff_set_after_cn)
  moreover have \<open>eff_set e\<^sub>2 (if i then S else {}) = eff_set (if i then e\<^sub>2 else ebot) S\<close>
    by simp
  ultimately show ?thesis
    by (simp only: fields ecomp.simps eff_set.simps[of i s c] eff_set_Un eff_set_join Un_assoc)
qed

subsection \<open>The transfer order and its well-foundedness\<close>

text \<open>A transfer below another denotes a subset for every argument.  Every
  ascending chain is finite: the identity is added at most once, and each offset,
  once present, only decreases.\<close>

fun ole :: \<open>nat option \<Rightarrow> nat option \<Rightarrow> bool\<close> where
  \<open>ole None _ = True\<close>
| \<open>ole (Some d) None = False\<close>
| \<open>ole (Some d) (Some d') = (d' \<le> d)\<close>

fun ele :: \<open>eff \<Rightarrow> eff \<Rightarrow> bool\<close> where
  \<open>ele (i\<^sub>1, s\<^sub>1, c\<^sub>1) (i\<^sub>2, s\<^sub>2, c\<^sub>2) = ((i\<^sub>1 \<longrightarrow> i\<^sub>2) \<and> ole s\<^sub>1 s\<^sub>2 \<and> ole c\<^sub>1 c\<^sub>2)\<close>

lemma ole_refl [simp]: \<open>ole a a\<close>
  by (cases a) simp_all

lemma ole_trans: \<open>ole a b \<Longrightarrow> ole b c \<Longrightarrow> ole a c\<close>
  by (cases a; cases b; cases c) simp_all

lemma ole_omin1: \<open>ole a (omin a b)\<close> and ole_omin2: \<open>ole b (omin a b)\<close>
  by (cases a; cases b; simp add: omin_def)+

lemma ele_refl [simp]: \<open>ele e e\<close>
  by (cases e) simp

lemma ele_trans: \<open>ele e f \<Longrightarrow> ele f g \<Longrightarrow> ele e g\<close>
  by (cases e; cases f; cases g) (auto intro: ole_trans)

lemma ele_join1: \<open>ele e (ejoin e f)\<close> and ele_join2: \<open>ele f (ejoin e f)\<close>
  by (cases e; cases f; simp add: ole_omin1 ole_omin2)+

lemma ele_fold_ejoin: \<open>ele a (fold ejoin xs a)\<close>
proof -
  have \<open>ele b a \<Longrightarrow> ele b (fold ejoin xs a)\<close> for b
  proof (induction xs arbitrary: a)
    case (Cons x xs)
    from Cons.prems have \<open>ele b (ejoin x a)\<close> by (rule ele_trans) (rule ele_join2)
    then have \<open>ele b (fold ejoin xs (ejoin x a))\<close> by (rule Cons.IH)
    then show ?case by simp
  qed simp
  then show ?thesis by simp
qed

fun omeas :: \<open>nat option \<Rightarrow> nat \<times> nat\<close> where
  \<open>omeas None = (1, 0)\<close>
| \<open>omeas (Some d) = (0, d)\<close>

lemma ole_omeas:
  \<open>ole a b \<Longrightarrow> a \<noteq> b \<Longrightarrow> (omeas b, omeas a) \<in> less_than <*lex*> less_than\<close>
  by (cases a; cases b) auto

text \<open>An increase raises the identity flag, or keeps it and decreases the shift,
  or keeps both and decreases the constant.\<close>

lemma wf_eff_inc: \<open>wf {(f, e). ele e f \<and> e \<noteq> f}\<close>
proof -
  have wo: \<open>wf {(b, a). ole a b \<and> a \<noteq> b}\<close>
    by (rule wf_subset[OF wf_inv_image[OF wf_lex_prod[OF wf_less_than wf_less_than]], of _ omeas])
      (auto dest: ole_omeas)
  have wb: \<open>wf {(True, False)}\<close>
    by (rule wf_subset[OF wf_inv_image[OF wf_less_than], of _ \<open>\<lambda>b. if b then 0 else 1\<close>]) auto
  have \<open>{(f, e). ele e f \<and> e \<noteq> f} \<subseteq>
      {(True, False)} <*lex*> ({(b, a). ole a b \<and> a \<noteq> b} <*lex*> {(b, a). ole a b \<and> a \<noteq> b})\<close>
    by clarsimp (metis (full_types))
  then show ?thesis by (rule wf_subset[rotated]) (intro wf_lex_prod wb wo)
qed

lemma list_all2_ne_lex:
  assumes \<open>list_all2 ele xs ys\<close> and \<open>xs \<noteq> ys\<close>
  shows \<open>(ys, xs) \<in> lex {(f, e). ele e f \<and> e \<noteq> f}\<close>
  using assms
proof (induction rule: list_all2_induct)
  case (Cons x xs y ys)
  show ?case
  proof (cases \<open>x = y\<close>)
    case True
    with Cons have \<open>(ys, xs) \<in> lex {(f, e). ele e f \<and> e \<noteq> f}\<close> by simp
    then show ?thesis unfolding True lex_conv
      by clarsimp (metis Cons_eq_appendI)
  next
    case False
    then have \<open>ele x y \<and> x \<noteq> y\<close> using Cons.hyps(1) by blast
    moreover have \<open>y # ys = [] @ y # ys\<close> \<open>x # xs = [] @ x # xs\<close> by simp_all
    moreover have \<open>length (y # ys) = length (x # xs)\<close>
      using list_all2_lengthD[OF Cons.hyps(2)] by simp
    ultimately show ?thesis unfolding lex_conv by (simp only: mem_Collect_eq case_prod_conv) blast
  qed
qed simp

lemma wf_eff_list_inc: \<open>wf {(ys, xs). list_all2 ele xs ys \<and> xs \<noteq> ys}\<close>
  by (rule wf_subset[OF wf_lex[OF wf_eff_inc]]) (auto simp: list_all2_ne_lex)

declare eff_set.simps [simp del]

subsection \<open>The closure graph\<close>

text \<open>A closure round sends the anchor set of a nonterminal \<open>c\<close> through the
  first symbol of each production of \<open>c\<close>: an edge to \<open>a\<close>, labelled with the
  relation of that symbol.  The table invariant \<open>ntl_ok\<close> says that only
  nonterminals with a number have productions.\<close>

definition tedge :: \<open>('n, 't) stab \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> irel \<Rightarrow> bool\<close> where
  \<open>tedge T c a q \<longleftrightarrow> c < s_np T \<and> a < s_np T \<and>
     (\<exists>k \<in> set (ntl T c). \<exists>rest. rrhs (s_recs T !! k) = (Nt a, q) # rest)\<close>

definition ntl_ok :: \<open>('n, 't) stab \<Rightarrow> bool\<close> where
  \<open>ntl_ok T \<longleftrightarrow> (\<forall>c. s_np T \<le> c \<longrightarrow> ntl T c = [])\<close>

lemma ntl_ok_mk_stab: \<open>ntl_ok (mk_stab G Shn gt sts redtab)\<close>
  unfolding ntl_ok_def ntl_mk_stab
  by (auto intro!: filter_False) (metis le_trans lids_nth_le not_le)

lemma nx_set_slot:
  \<open>nx_set np a (r, 0, R) =
     \<Union>{irep_set (irep_img q R) |q. a < np \<and> (\<exists>rest. rrhs r = (Nt a, q) # rest)}\<close>
  by (auto simp: nx_set_def sitem_nx_def neq_Nil_conv split: list.splits sym.splits prod.splits)

lemma sslot_kset_tedge:
  assumes \<open>ntl_ok T\<close>
  shows \<open>kset a (sslot_nx T c R) = \<Union>{eff_set (of_rel q) (irep_set R) |q. tedge T c a q}\<close>
proof (cases \<open>c < s_np T\<close>)
  case True
  have \<open>kset a (sslot_nx T c R) = \<Union> (nx_set (s_np T) a ` (\<lambda>k. (s_recs T !! k, 0, R)) ` set (ntl T c))\<close>
    unfolding sslot_nx_def
    using map_filter_nx_set[of a \<open>s_np T\<close> \<open>map (\<lambda>k. (s_recs T !! k, 0, R)) (ntl T c)\<close>]
    by (simp add: map_filter_map o_def)
  also have \<open>\<dots> = \<Union>{eff_set (of_rel q) (irep_set R) |q. tedge T c a q}\<close>
    using True by (auto simp: nx_set_slot tedge_def eff_set_img)
  finally show ?thesis .
next
  case False
  with assms show ?thesis by (simp add: ntl_ok_def sslot_nx_def tedge_def List.map_filter_def)
qed


text \<open>A round on anchor-set assignments: the kernel's sets, and every edge's
  image of the set at its source.\<close>

definition sem_round :: \<open>('n, 't) stab \<Rightarrow> (nat \<times> indrep) list \<Rightarrow> (nat \<Rightarrow> nat set) \<Rightarrow> nat \<Rightarrow> nat set\<close> where
  \<open>sem_round T kn \<nu> a = kset a kn \<union> \<Union>{eff_set (of_rel q) (\<nu> c) |c q. tedge T c a q}\<close>

lemma sem_round_mono: \<open>(\<And>c. \<nu> c \<subseteq> \<mu> c) \<Longrightarrow> sem_round T kn \<nu> a \<subseteq> sem_round T kn \<mu> a\<close>
proof -
  assume le: \<open>\<And>c. \<nu> c \<subseteq> \<mu> c\<close>
  have \<open>eff_set (of_rel q) (\<nu> c) \<subseteq> eff_set (of_rel q) (\<mu> c)\<close> for q c by (rule eff_set_mono[OF le])
  then show ?thesis unfolding sem_round_def by fast
qed

lemma UN_keys_slk:
  assumes d: \<open>distinct (map fst N)\<close> and f: \<open>\<And>c. f c {} = {}\<close>
  shows \<open>(\<Union>(c, R) \<in> set N. f c (irep_set R)) = (\<Union>c. f c (irep_set (slk N c)))\<close>
proof (intro equalityI subsetI)
  fix x assume \<open>x \<in> (\<Union>(c, R) \<in> set N. f c (irep_set R))\<close>
  then obtain c R where \<open>(c, R) \<in> set N\<close> \<open>x \<in> f c (irep_set R)\<close> by blast
  with d have \<open>x \<in> f c (irep_set (slk N c))\<close> by (simp add: slk_in)
  then show \<open>x \<in> (\<Union>c. f c (irep_set (slk N c)))\<close> by blast
next
  fix x assume \<open>x \<in> (\<Union>c. f c (irep_set (slk N c)))\<close>
  then obtain c where x: \<open>x \<in> f c (irep_set (slk N c))\<close> by blast
  show \<open>x \<in> (\<Union>(c, R) \<in> set N. f c (irep_set R))\<close>
  proof (cases \<open>c \<in> fst ` set N\<close>)
    case True
    then obtain R where \<open>(c, R) \<in> set N\<close> by force
    with d x show ?thesis by (auto simp: slk_in)
  next
    case False
    with x f show ?thesis by (simp add: slk_notin)
  qed
qed

lemma sround_distinct: \<open>distinct (map fst (sround T kn N))\<close>
  unfolding sround_def by (rule fold_sins_distinct) simp

lemma siter_distinct: \<open>distinct (map fst (siter T kn t))\<close>
  by (cases t) (simp_all add: sround_distinct)

lemma sround_sem:
  assumes ok: \<open>ntl_ok T\<close> and d: \<open>distinct (map fst N)\<close>
  shows \<open>irep_set (slk (sround T kn N) a) = sem_round T kn (\<lambda>c. irep_set (slk N c)) a\<close>
proof -
  let ?f = \<open>\<lambda>c S. \<Union>{eff_set (of_rel q) S |q. tedge T c a q}\<close>
  have \<open>irep_set (slk (sround T kn N) a) = kset a kn \<union> (\<Union>(c, R) \<in> set N. kset a (sslot_nx T c R))\<close>
    by (simp add: sround_def fold_sins_set kset_filter_ne kset_concat_map)
  also have \<open>(\<Union>(c, R) \<in> set N. kset a (sslot_nx T c R)) = (\<Union>(c, R) \<in> set N. ?f c (irep_set R))\<close>
    by (simp add: sslot_kset_tedge[OF ok])
  also have \<open>\<dots> = (\<Union>c. ?f c (irep_set (slk N c)))\<close>
    by (rule UN_keys_slk[OF d]) auto
  finally show ?thesis by (auto simp: sem_round_def)
qed

subsection \<open>Paths and their transfers\<close>

text \<open>The transfer of a path in the closure graph, from a kernel nonterminal
  \<open>b\<close>: the composition of the relations on its edges.\<close>

inductive treach :: \<open>('n, 't) stab \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> eff \<Rightarrow> bool\<close> for T b where
  treach_refl: \<open>treach T b b eid\<close>
| treach_edge: \<open>treach T b c e \<Longrightarrow> tedge T c a q \<Longrightarrow> treach T b a (ecomp (of_rel q) e)\<close>

definition tpaths :: \<open>('n, 't) stab \<Rightarrow> (nat \<times> indrep) list \<Rightarrow> nat \<Rightarrow> nat set\<close> where
  \<open>tpaths T kn a = \<Union>{eff_set e (irep_set R) |b R e. (b, R) \<in> set kn \<and> treach T b a e}\<close>

lemma kset_le_tpaths: \<open>kset a kn \<subseteq> tpaths T kn a\<close>
proof
  fix x assume \<open>x \<in> kset a kn\<close>
  then obtain R where R: \<open>(a, R) \<in> set kn\<close> and x: \<open>x \<in> irep_set R\<close> by (auto simp: kset_def)
  have \<open>eff_set eid (irep_set R) \<in> {eff_set e (irep_set R') |b R' e. (b, R') \<in> set kn \<and> treach T b a e}\<close>
    using R treach_refl[of T a] by blast
  with x show \<open>x \<in> tpaths T kn a\<close> unfolding tpaths_def eff_set_id by blast
qed

lemma sem_round_tpaths: \<open>sem_round T kn (tpaths T kn) a \<subseteq> tpaths T kn a\<close>
proof -
  have \<open>eff_set (of_rel q) (tpaths T kn c) \<subseteq> tpaths T kn a\<close> if \<open>tedge T c a q\<close> for c q
  proof
    fix x assume \<open>x \<in> eff_set (of_rel q) (tpaths T kn c)\<close>
    then obtain b R e where \<open>(b, R) \<in> set kn\<close> \<open>treach T b c e\<close>
        \<open>x \<in> eff_set (of_rel q) (eff_set e (irep_set R))\<close>
      unfolding tpaths_def by (auto simp: eff_set_UN)
    with that show \<open>x \<in> tpaths T kn a\<close>
      unfolding tpaths_def by (blast intro: treach_edge eff_set_comp[THEN equalityD2, THEN subsetD])
  qed
  then show ?thesis unfolding sem_round_def using kset_le_tpaths by blast
qed

lemma siter_le_tpaths:
  assumes \<open>ntl_ok T\<close>
  shows \<open>irep_set (slk (siter T kn t) a) \<subseteq> tpaths T kn a\<close>
proof (induction t arbitrary: a)
  case (Suc t)
  have \<open>irep_set (slk (siter T kn (Suc t)) a) = sem_round T kn (\<lambda>c. irep_set (slk (siter T kn t) c)) a\<close>
    by (simp add: sround_sem[OF assms siter_distinct])
  also have \<open>\<dots> \<subseteq> sem_round T kn (tpaths T kn) a\<close>
    by (rule sem_round_mono) (rule Suc.IH)
  also have \<open>\<dots> \<subseteq> tpaths T kn a\<close> by (rule sem_round_tpaths)
  finally show ?case .
qed simp

text \<open>Conversely, a set assignment that a round does not enlarge contains every
  path's image.\<close>

lemma tpaths_le_post:
  assumes post: \<open>\<And>a. sem_round T kn \<nu> a \<subseteq> \<nu> a\<close>
  shows \<open>tpaths T kn a \<subseteq> \<nu> a\<close>
proof -
  have \<open>eff_set e (irep_set R) \<subseteq> \<nu> a\<close> if \<open>treach T b a e\<close> \<open>(b, R) \<in> set kn\<close> for b a e R
    using that(1)
  proof induction
    case treach_refl
    have \<open>irep_set R \<subseteq> kset b kn\<close> using that(2) by (auto simp: kset_def)
    also have \<open>\<dots> \<subseteq> \<nu> b\<close> using post[of b] by (simp add: sem_round_def)
    finally show ?case by simp
  next
    case (treach_edge c e a q)
    have \<open>eff_set (ecomp (of_rel q) e) (irep_set R) = eff_set (of_rel q) (eff_set e (irep_set R))\<close>
      by (rule eff_set_comp)
    also have \<open>\<dots> \<subseteq> eff_set (of_rel q) (\<nu> c)\<close> by (rule eff_set_mono[OF treach_edge.IH])
    also have \<open>\<dots> \<subseteq> \<nu> a\<close> using post[of a] treach_edge.hyps(2) unfolding sem_round_def by blast
    finally show ?case .
  qed
  then show ?thesis unfolding tpaths_def by blast
qed

text \<open>So the fixpoint the sparse closure computes is the union of the path
  images, whenever its loop stops.\<close>

definition sfix_loop :: \<open>('n, 't) stab \<Rightarrow> (nat \<times> indrep) list \<Rightarrow>
    ((nat \<times> indrep) list \<times> (nat \<times> indrep) list) option\<close> where
  \<open>sfix_loop T kn = while_option (\<lambda>(N, N'). \<not> ssub N' N)
     (\<lambda>(N, N'). (N', sround T kn N')) ([], sround T kn [])\<close>

lemma ssub_le:
  assumes \<open>ssub N' N\<close> shows \<open>irep_set (slk N' a) \<subseteq> irep_set (slk N a)\<close>
proof (cases \<open>map_of N' a\<close>)
  case (Some R)
  then have \<open>(a, R) \<in> set N'\<close> by (rule map_of_SomeD)
  with assms Some show ?thesis by (auto simp: ssub_def list_all_iff slk_def)
qed (simp add: slk_def)

lemma sfix_tpaths:
  assumes ok: \<open>ntl_ok T\<close> and stop: \<open>sfix_loop T kn \<noteq> None\<close>
  shows \<open>irep_set (slk (sfix T kn) a) = tpaths T kn a\<close>
proof -
  obtain N N' where loop: \<open>sfix_loop T kn = Some (N, N')\<close> using stop by auto
  let ?P = \<open>\<lambda>p. \<exists>t. fst p = siter T kn t \<and> snd p = siter T kn (Suc t)\<close>
  have \<open>?P (N, N')\<close>
  proof (rule while_option_rule[OF _ loop[unfolded sfix_loop_def]])
    fix p assume \<open>?P p\<close>
    then obtain t where \<open>fst p = siter T kn t\<close> \<open>snd p = siter T kn (Suc t)\<close> by blast
    then show \<open>?P ((\<lambda>(N, N'). (N', sround T kn N')) p)\<close>
      by (intro exI[of _ \<open>Suc t\<close>]) (simp add: case_prod_beta)
  qed (intro exI[of _ 0]; simp)
  then obtain t where N: \<open>N = siter T kn t\<close> and N': \<open>N' = siter T kn (Suc t)\<close> by auto
  have sub: \<open>ssub N' N\<close> using while_option_stop[OF loop[unfolded sfix_loop_def]] by simp
  have fx: \<open>sfix T kn = N\<close> using loop by (simp add: sfix_def sfix_loop_def)
  have post: \<open>sem_round T kn (\<lambda>c. irep_set (slk N c)) b \<subseteq> irep_set (slk N b)\<close> for b
    using ssub_le[OF sub, of b] by (simp add: N N' sround_sem[OF ok siter_distinct])
  show ?thesis
    unfolding fx using siter_le_tpaths[OF ok, of kn t a] tpaths_le_post[OF post, of a]
    by (auto simp: N)
qed


subsection \<open>The saturated transfer table\<close>

text \<open>For each source nonterminal \<open>b\<close>, a row with the join of the transfers of
  all paths from \<open>b\<close> to each nonterminal: the least fixpoint of the edges,
  reached by iteration, since the transfer order has no infinite ascending
  chains.\<close>

definition hd_nt :: \<open>('n, 't) prec \<Rightarrow> (nat \<times> irel) option\<close> where
  \<open>hd_nt r = (case rrhs r of (Nt a, q) # _ \<Rightarrow> Some (a, q) | _ \<Rightarrow> None)\<close>

lemma hd_nt_eq: \<open>hd_nt r = Some (a, q) \<longleftrightarrow> (\<exists>rest. rrhs r = (Nt a, q) # rest)\<close>
  by (auto simp: hd_nt_def split: list.split sym.split prod.split)

definition tin :: \<open>('n, 't) stab \<Rightarrow> nat \<Rightarrow> (nat \<times> irel) list\<close> where
  \<open>tin T a = concat (map (\<lambda>c. List.map_filter (\<lambda>k. case hd_nt (s_recs T !! k) of
       Some (a', q) \<Rightarrow> if a' = a then Some (c, q) else None | None \<Rightarrow> None) (ntl T c))
     [0..<s_np T])\<close>

lemma set_tin: \<open>a < s_np T \<Longrightarrow> set (tin T a) = {(c, q). tedge T c a q}\<close>
proof -
  have c: \<open>(case h of Some (a', q') \<Rightarrow> if a' = a then Some (x, q') else None | None \<Rightarrow> None) = Some (y, q)
      \<longleftrightarrow> h = Some (a, q) \<and> y = x\<close> for h :: \<open>(nat \<times> irel) option\<close> and x y :: nat and q
    by (cases h) (auto split: if_splits)
  assume \<open>a < s_np T\<close>
  then show ?thesis
    by (auto simp: tin_def tedge_def in_map_filter c hd_nt_eq[symmetric] simp del: IArray.sub_def)
qed

definition tr_step :: \<open>('n, 't) stab \<Rightarrow> eff list \<Rightarrow> eff list\<close> where
  \<open>tr_step T row = map (\<lambda>a. fold ejoin (map (\<lambda>(c, q). ecomp (of_rel q) (row ! c)) (tin T a)) (row ! a))
     [0..<s_np T]\<close>

definition tinit :: \<open>nat \<Rightarrow> nat \<Rightarrow> eff list\<close> where
  \<open>tinit n b = map (\<lambda>a. if a = b then eid else ebot) [0..<n]\<close>

definition trow_loop :: \<open>('n, 't) stab \<Rightarrow> nat \<Rightarrow> eff list option\<close> where
  \<open>trow_loop T b = while_option (\<lambda>row. tr_step T row \<noteq> row) (tr_step T) (tinit (s_np T) b)\<close>

definition trow :: \<open>('n, 't) stab \<Rightarrow> nat \<Rightarrow> eff list\<close> where
  \<open>trow T b = the (trow_loop T b)\<close>

lemma length_tr_step [simp]: \<open>length (tr_step T row) = s_np T\<close>
  by (simp add: tr_step_def)

lemma tr_step_nth: \<open>a < s_np T \<Longrightarrow>
    tr_step T row ! a = fold ejoin (map (\<lambda>(c, q). ecomp (of_rel q) (row ! c)) (tin T a)) (row ! a)\<close>
  by (simp add: tr_step_def)

lemma tr_step_inc: \<open>length row = s_np T \<Longrightarrow> list_all2 ele row (tr_step T row)\<close>
  by (simp add: list_all2_conv_all_nth tr_step_nth ele_fold_ejoin)

lemma trow_loop_Some: \<open>trow_loop T b \<noteq> None\<close>
proof -
  let ?P = \<open>\<lambda>row. length row = s_np T\<close>
  have \<open>{(t, s). (?P s \<and> tr_step T s \<noteq> s) \<and> t = tr_step T s} \<subseteq> {(ys, xs). list_all2 ele xs ys \<and> xs \<noteq> ys}\<close>
    using tr_step_inc by fastforce
  then have \<open>wf {(t, s). (?P s \<and> tr_step T s \<noteq> s) \<and> t = tr_step T s}\<close>
    by (rule wf_subset[OF wf_eff_list_inc])
  then have \<open>\<exists>r. trow_loop T b = Some r\<close>
    unfolding trow_loop_def by (rule wf_while_option_Some) (simp_all add: tinit_def)
  then show ?thesis by auto
qed

text \<open>The semantic invariant of the iteration: every entry is below the paths,
  and the source's entry contains the identity.\<close>

definition tpath_set :: \<open>('n, 't) stab \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat set \<Rightarrow> nat set\<close> where
  \<open>tpath_set T b a S = \<Union>{eff_set e S |e. treach T b a e}\<close>

lemma tpath_set_edge:
  assumes \<open>tedge T c a q\<close>
  shows \<open>eff_set (of_rel q) (tpath_set T b c S) \<subseteq> tpath_set T b a S\<close>
proof
  fix x assume \<open>x \<in> eff_set (of_rel q) (tpath_set T b c S)\<close>
  then obtain e where e: \<open>treach T b c e\<close> and x: \<open>x \<in> eff_set (of_rel q) (eff_set e S)\<close>
    unfolding tpath_set_def eff_set_UN by blast
  have \<open>eff_set (ecomp (of_rel q) e) S \<in> {eff_set e S |e. treach T b a e}\<close>
    using treach_edge[OF e assms] by blast
  with x show \<open>x \<in> tpath_set T b a S\<close> unfolding tpath_set_def eff_set_comp by blast
qed

definition trow_inv :: \<open>('n, 't) stab \<Rightarrow> nat \<Rightarrow> eff list \<Rightarrow> bool\<close> where
  \<open>trow_inv T b row \<longleftrightarrow> length row = s_np T \<and>
     (\<forall>a < s_np T. \<forall>S. eff_set (row ! a) S \<subseteq> tpath_set T b a S) \<and>
     (\<forall>S. b < s_np T \<longrightarrow> S \<subseteq> eff_set (row ! b) S)\<close>

lemma trow_inv_init: \<open>trow_inv T b (tinit (s_np T) b)\<close>
proof -
  have \<open>S \<subseteq> tpath_set T b b S\<close> for S
  proof -
    have \<open>eff_set eid S \<in> {eff_set e S |e. treach T b b e}\<close> using treach_refl[of T b] by blast
    then show ?thesis unfolding tpath_set_def eff_set_id by blast
  qed
  then show ?thesis by (simp add: trow_inv_def tinit_def)
qed

lemma tr_step_set:
  assumes \<open>a < s_np T\<close>
  shows \<open>eff_set (tr_step T row ! a) S =
    eff_set (row ! a) S \<union> \<Union>{eff_set (of_rel q) (eff_set (row ! c) S) |c q. tedge T c a q}\<close>
proof -
  have \<open>eff_set (tr_step T row ! a) S =
      eff_set (row ! a) S \<union> (\<Union>(c, q) \<in> set (tin T a). eff_set (of_rel q) (eff_set (row ! c) S))\<close>
    using assms by (simp add: tr_step_nth eff_set_fold_ejoin case_prod_beta eff_set_comp)
  also have \<open>(\<Union>(c, q) \<in> set (tin T a). eff_set (of_rel q) (eff_set (row ! c) S)) =
      \<Union>{eff_set (of_rel q) (eff_set (row ! c) S) |c q. tedge T c a q}\<close>
    using assms by (auto simp: set_tin)
  finally show ?thesis .
qed

lemma trow_inv_step:
  assumes inv: \<open>trow_inv T b row\<close>
  shows \<open>trow_inv T b (tr_step T row)\<close>
  unfolding trow_inv_def
proof (intro conjI allI impI)
  show \<open>length (tr_step T row) = s_np T\<close> by simp
next
  fix a S assume a: \<open>a < s_np T\<close>
  have \<open>eff_set (of_rel q) (eff_set (row ! c) S) \<subseteq> tpath_set T b a S\<close> if e: \<open>tedge T c a q\<close> for c q
  proof -
    have \<open>c < s_np T\<close> using e by (simp add: tedge_def)
    with inv have \<open>eff_set (row ! c) S \<subseteq> tpath_set T b c S\<close> by (simp add: trow_inv_def)
    then have \<open>eff_set (of_rel q) (eff_set (row ! c) S) \<subseteq> eff_set (of_rel q) (tpath_set T b c S)\<close>
      by (rule eff_set_mono)
    also have \<open>\<dots> \<subseteq> tpath_set T b a S\<close> by (rule tpath_set_edge[OF e])
    finally show ?thesis .
  qed
  moreover have \<open>eff_set (row ! a) S \<subseteq> tpath_set T b a S\<close> using inv a by (simp add: trow_inv_def)
  ultimately show \<open>eff_set (tr_step T row ! a) S \<subseteq> tpath_set T b a S\<close>
    unfolding tr_step_set[OF a] by blast
next
  fix S assume b: \<open>b < s_np T\<close>
  with inv have \<open>S \<subseteq> eff_set (row ! b) S\<close> by (simp add: trow_inv_def)
  then show \<open>S \<subseteq> eff_set (tr_step T row ! b) S\<close> unfolding tr_step_set[OF b] by blast
qed

lemma trow_some: obtains r where \<open>trow_loop T b = Some r\<close> \<open>trow T b = r\<close>
  using trow_loop_Some[of T b] by (auto simp: trow_def)

lemma trow_inv_trow: \<open>trow_inv T b (trow T b)\<close>
proof -
  obtain r where r: \<open>trow_loop T b = Some r\<close> and t: \<open>trow T b = r\<close> by (rule trow_some)
  have \<open>trow_inv T b r\<close>
    using while_option_rule[where P = \<open>trow_inv T b\<close>, OF trow_inv_step r[unfolded trow_loop_def]
        trow_inv_init] .
  with t show ?thesis by simp
qed

lemma tr_step_trow: \<open>tr_step T (trow T b) = trow T b\<close>
proof -
  obtain r where r: \<open>trow_loop T b = Some r\<close> and t: \<open>trow T b = r\<close> by (rule trow_some)
  from while_option_stop[OF r[unfolded trow_loop_def]] t show ?thesis by simp
qed

lemma trow_sem:
  assumes b: \<open>b < s_np T\<close> and a: \<open>a < s_np T\<close>
  shows \<open>eff_set (trow T b ! a) S = tpath_set T b a S\<close>
proof
  show \<open>eff_set (trow T b ! a) S \<subseteq> tpath_set T b a S\<close>
    using trow_inv_trow[of T b] a by (simp add: trow_inv_def)
  have \<open>eff_set e S \<subseteq> eff_set (trow T b ! a') S\<close> if \<open>treach T b a' e\<close> for a' e
    using that
  proof induction
    case treach_refl
    then show ?case using trow_inv_trow[of T b] b by (simp add: trow_inv_def)
  next
    case (treach_edge c e a q)
    have a': \<open>a < s_np T\<close> using treach_edge.hyps(2) by (simp add: tedge_def)
    have \<open>eff_set (ecomp (of_rel q) e) S = eff_set (of_rel q) (eff_set e S)\<close> by (rule eff_set_comp)
    also have \<open>\<dots> \<subseteq> eff_set (of_rel q) (eff_set (trow T b ! c) S)\<close>
      by (rule eff_set_mono[OF treach_edge.IH])
    also have \<open>\<dots> \<subseteq> eff_set (tr_step T (trow T b) ! a) S\<close>
      using treach_edge.hyps(2) unfolding tr_step_set[OF a'] by blast
    finally show ?case by (simp only: tr_step_trow)
  qed
  then show \<open>tpath_set T b a S \<subseteq> eff_set (trow T b ! a) S\<close> unfolding tpath_set_def by blast
qed

text \<open>The closure's anchor set of a numbered nonterminal, from the kernel
  without a fixpoint.\<close>

lemma sfix_trow:
  assumes ok: \<open>ntl_ok T\<close> and stop: \<open>sfix_loop T kn \<noteq> None\<close>
    and kn: \<open>\<And>b R. (b, R) \<in> set kn \<Longrightarrow> b < s_np T\<close> and a: \<open>a < s_np T\<close>
  shows \<open>irep_set (slk (sfix T kn) a) = (\<Union>(b, R) \<in> set kn. eff_set (trow T b ! a) (irep_set R))\<close>
proof -
  have \<open>irep_set (slk (sfix T kn) a) = tpaths T kn a\<close> by (rule sfix_tpaths[OF ok stop])
  also have \<open>\<dots> = (\<Union>(b, R) \<in> set kn. tpath_set T b a (irep_set R))\<close>
    unfolding tpaths_def tpath_set_def by blast
  also have \<open>\<dots> = (\<Union>(b, R) \<in> set kn. eff_set (trow T b ! a) (irep_set R))\<close>
    by (rule SUP_cong[OF refl]) (auto simp: trow_sem[OF kn a])
  finally show ?thesis .
qed



subsection \<open>Applying a transfer\<close>

text \<open>The least anchor of a non-empty set, and a transfer applied to a set.\<close>

fun imin :: \<open>indrep \<Rightarrow> nat\<close> where
  \<open>imin (FinRep []) = 0\<close>
| \<open>imin (FinRep (x # xs)) = fold min xs x\<close>
| \<open>imin (UpRep xs n) = fold min xs n\<close>

lemma fold_min_le_iff: \<open>fold min ys a \<le> i \<longleftrightarrow> a \<le> i \<or> (\<exists>y \<in> set ys. y \<le> i)\<close> for ys :: \<open>nat list\<close>
  using Min.set_eq_fold[of a ys, symmetric] by (simp add: Min_le_iff)

lemma fold_min_mem: \<open>fold min ys a \<in> insert a (set ys)\<close> for ys :: \<open>nat list\<close>
  using Min.set_eq_fold[of a ys, symmetric] Min_in[of \<open>insert a (set ys)\<close>] by simp

lemma imin_le_iff: \<open>irep_set R \<noteq> {} \<Longrightarrow> imin R \<le> i \<longleftrightarrow> (\<exists>j \<in> irep_set R. j \<le> i)\<close>
proof (cases R)
  case (FinRep xs)
  assume \<open>irep_set R \<noteq> {}\<close>
  with FinRep show ?thesis by (cases xs) (auto simp: fold_min_le_iff)
next
  case (UpRep xs n)
  then show ?thesis by (auto simp: fold_min_le_iff intro: le_trans)
qed

lemma sh_imin:
  assumes ne: \<open>irep_set R \<noteq> {}\<close>
  shows \<open>sh d (irep_set R) = {m. imin R + d \<le> m}\<close>
proof -
  have l: \<open>imin R \<le> j\<close> if \<open>j \<in> irep_set R\<close> for j
    using imin_le_iff[OF ne, of j] that by blast
  obtain j\<^sub>0 where j\<^sub>0: \<open>j\<^sub>0 \<in> irep_set R\<close> \<open>j\<^sub>0 \<le> imin R\<close>
    using imin_le_iff[OF ne, of \<open>imin R\<close>] by blast
  with l have \<open>j\<^sub>0 = imin R\<close> by (simp add: le_antisym)
  with j\<^sub>0 l show ?thesis
    by (auto simp: sh_def intro: le_trans[OF add_right_mono])
qed

definition eapp :: \<open>eff \<Rightarrow> indrep \<Rightarrow> indrep\<close> where
  \<open>eapp e R = (if irep_nonempty R then (case e of (i, s, c) \<Rightarrow>
     let R\<^sub>1 = (if i then R else FinRep []);
         R\<^sub>2 = (case s of None \<Rightarrow> R\<^sub>1 | Some d \<Rightarrow> cup (imin R + d) R\<^sub>1)
     in (case c of None \<Rightarrow> R\<^sub>2 | Some d \<Rightarrow> cup d R\<^sub>2))
   else FinRep [])\<close>

lemma eapp_set [simp]: \<open>irep_set (eapp e R) = eff_set e (irep_set R)\<close>
proof (cases \<open>irep_set R = {}\<close>)
  case False
  obtain i s c where e: \<open>e = (i, s, c)\<close> by (cases e)
  show ?thesis
    using False sh_imin[OF False]
    by (cases s; cases c) (auto simp: eapp_def e eff_set.simps cn_def)
qed (simp add: eapp_def)



subsection \<open>The tables\<close>

text \<open>The items of state \<open>j\<close>: its LR(0) closure, in the order \<^const>\<open>creach\<close>
  lists them.  A frame of the driver is a state with one anchor set per item.
  An item is a \<^emph>\<open>slot\<close> when the closure adds it: dot \<open>0\<close> of a grammar
  production.  The others, the \<^emph>\<open>kernel positions\<close>, get their anchors from the
  predecessor frame; a slot gets its anchors from the kernel positions, through
  the transfer of the closure graph (\<^const>\<open>trow\<close>).\<close>

definition vits :: \<open>('n, 't) is_cfg \<Rightarrow> ('n, 't) citem list list \<Rightarrow> nat \<Rightarrow> ('n, 't) citem list\<close> where
  \<open>vits G sts j = (if j < length sts then creach G (sts ! j) else [])\<close>

definition is_slot :: \<open>('n, 't) is_cfg \<Rightarrow> ('n, 't) citem \<Rightarrow> bool\<close> where
  \<open>is_slot G it \<longleftrightarrow> snd it = 0 \<and> fst it \<in> set (iprods G)\<close>

definition getR :: \<open>indrep list \<Rightarrow> nat \<Rightarrow> indrep\<close> where
  \<open>getR av k = (if k < length av then av ! k else FinRep [])\<close>

definition iget :: \<open>'a iarray \<Rightarrow> nat \<Rightarrow> 'a \<Rightarrow> 'a\<close> where
  \<open>iget xs k d = (if k < IArray.length xs then xs !! k else d)\<close>

definition nnum :: \<open>('n, 't) is_cfg \<Rightarrow> 'n \<Rightarrow> 'n \<Rightarrow> nat\<close> where
  \<open>nnum G Shn B = ntidx (map fst (eprods G Shn)) B\<close>

text \<open>The nonterminal after an item's dot, if the grammar has productions for it,
  with the relation it carries.\<close>

definition vnext_nt :: \<open>('n, 't) is_cfg \<Rightarrow> ('n, 't) citem \<Rightarrow> ('n \<times> irel) option\<close> where
  \<open>vnext_nt G it = (case it of (p, m) \<Rightarrow> if m < length (snd p) then
     (case snd p ! m of (Nt B, q) \<Rightarrow> if B \<in> fst ` set (iprods G) then Some (B, q) else None
      | _ \<Rightarrow> None) else None)\<close>

text \<open>The contributions to a slot: per kernel position whose item expects a
  nonterminal, the transfer from that position's anchors to the slot's.\<close>

definition vcontrib :: \<open>('n, 't) is_cfg \<Rightarrow> 'n \<Rightarrow> ('n, 't) stab \<Rightarrow> ('n, 't) citem list \<Rightarrow>
    ('n, 't) citem \<Rightarrow> (nat \<times> eff) list\<close> where
  \<open>vcontrib G Shn T its it = (if is_slot G it then
     List.map_filter (\<lambda>kk. if is_slot G (its ! kk) then None else
       (case vnext_nt G (its ! kk) of None \<Rightarrow> None
        | Some (B, q) \<Rightarrow> Some (kk, ecomp (trow T (nnum G Shn B) ! nnum G Shn (fst (fst it))) (of_rel q))))
       [0..<length its]
   else [])\<close>

text \<open>The kernel of a successor under \<open>X\<close>: per item of the successor state, the
  position of its predecessor in the state left and the relation of the symbol
  crossed.\<close>

definition vkmap :: \<open>('n, 't) citem list \<Rightarrow> ('n, 't) sym \<Rightarrow> ('n, 't) citem list \<Rightarrow>
    (nat \<times> irel) option list\<close> where
  \<open>vkmap its X its' = map (\<lambda>(p, m). if 0 < m \<and> m \<le> length (snd p) \<and> fst (snd p ! (m - 1)) = X
     then Some (ntidx its (p, m - 1), snd (snd p ! (m - 1))) else None) its'\<close>

definition ventry :: \<open>('n, 't) is_cfg \<Rightarrow> (('n, 't) sym \<times> nat) list list \<Rightarrow> ('n, 't) citem list list \<Rightarrow>
    nat \<Rightarrow> ('n, 't) sym \<Rightarrow> (nat \<times> (nat \<times> irel) option list) option\<close> where
  \<open>ventry G gt sts j X = (let j' = dnext gt sts j X in
     if j' < length sts then Some (j', vkmap (vits G sts j) X (vits G sts j')) else None)\<close>

text \<open>The completed items of a state, each at its first position, with the
  number of the nonterminal it reduces to; the reduce cells per token and at the
  end of the input, by position.\<close>

definition vcomps :: \<open>('n, 't) is_cfg \<Rightarrow> 'n \<Rightarrow> ('n, 't) citem list \<Rightarrow> (nat \<times> nat \<times> ('n \<times> ('n, 't) rhs)) list\<close> where
  \<open>vcomps G Shn its = List.map_filter (\<lambda>s. case its ! s of (pr, m) \<Rightarrow>
     if m = length (snd pr) \<and> ntidx its (pr, m) = s then Some (s, nnum G Shn (fst pr), pr) else None)
     [0..<length its]\<close>

definition vcells :: \<open>('n, 't) citem list \<Rightarrow> nat \<Rightarrow> ('n, 't) lacell list \<Rightarrow> 't option \<Rightarrow> (nat \<times> wrel) list\<close> where
  \<open>vcells its j cells t = List.map_filter (\<lambda>(i', (pr, n), t', \<tau>).
     if i' = j \<and> n = length (snd pr) \<and> t' = t then Some (ntidx its (pr, n), \<tau>) else None) cells\<close>

text \<open>The tokens the tables number: the grammar's terminals and those of the
  reduce cells.\<close>

definition vtoks :: \<open>('n, 't) is_cfg \<Rightarrow> ('n, 't) lacell list list \<Rightarrow> 't list\<close> where
  \<open>vtoks G redtab = remdups ([a. Tm a \<leftarrow> gram_syms G] @
     List.map_filter (\<lambda>(i', itm, t, \<tau>). t) (concat redtab))\<close>

datatype ('n, 't) vtab = VTab
  (v_lal: \<open>('t \<times> nat) list\<close>)
  (v_miss: nat)
  (v_sh: \<open>(nat \<times> (nat \<times> irel) option list) option iarray iarray\<close>)
  (v_go: \<open>(nat \<times> (nat \<times> irel) option list) option iarray iarray\<close>)
  (v_ct: \<open>(nat \<times> eff) list list iarray\<close>)
  (v_cp: \<open>(nat \<times> nat \<times> ('n \<times> ('n, 't) rhs)) list iarray\<close>)
  (v_cl: \<open>(nat \<times> wrel) list iarray iarray\<close>)
  (v_ce: \<open>nat list iarray\<close>)
  (v_fin: \<open>nat iarray\<close>)
  (v_av0: \<open>nat \<times> indrep list\<close>)
  (v_ind0: nat)

definition vnum :: \<open>('n, 't) vtab \<Rightarrow> 't \<Rightarrow> nat\<close> where
  \<open>vnum V a = (case map_of (v_lal V) a of Some l \<Rightarrow> l | None \<Rightarrow> v_miss V)\<close>

subsection \<open>The driver\<close>

text \<open>A successor frame: the kernel anchors through the predecessor map, then
  the slots from the kernel; no frame when the kernel is dead.\<close>

definition vkav :: \<open>(nat \<times> irel) option list \<Rightarrow> indrep list \<Rightarrow> indrep \<Rightarrow> indrep list\<close> where
  \<open>vkav km av RA = map (\<lambda>x. case x of None \<Rightarrow> FinRep [] | Some (ps, q) \<Rightarrow> cpre q RA (getR av ps)) km\<close>

definition vfill :: \<open>(nat \<times> eff) list list \<Rightarrow> indrep list \<Rightarrow> indrep list\<close> where
  \<open>vfill cts kav = map (\<lambda>(R, cs). fold (\<lambda>(kk, e) acc. cunion acc (eapp e (getR kav kk))) cs R)
     (zip kav cts)\<close>

definition vgo :: \<open>('n, 't) vtab \<Rightarrow> nat \<times> (nat \<times> irel) option list \<Rightarrow> indrep list \<Rightarrow> indrep \<Rightarrow>
    (nat \<times> indrep list) option\<close> where
  \<open>vgo V e av RA = (case e of (j', km) \<Rightarrow> let kav = vkav km av RA in
     if list_ex irep_nonempty kav then Some (j', vfill (iget (v_ct V) j' []) kav) else None)\<close>

datatype ('n, 't) vact = VShift | VReduce nat nat \<open>'n \<times> ('n, 't) rhs\<close>

fun vdec :: \<open>('n, 't) vact \<Rightarrow> ('n, 't) dact\<close> where
  \<open>vdec VShift = DShift\<close>
| \<open>vdec (VReduce s b pr) = DReduce pr\<close>

type_synonym vframes = \<open>(nat \<times> indrep list) list\<close>

definition vmstep :: \<open>('n, 't) vtab \<Rightarrow> vframes \<times> ('t \<times> nat) list \<Rightarrow> ('n, 't) vact \<Rightarrow>
    (vframes \<times> ('t \<times> nat) list) option\<close> where
  \<open>vmstep V fw act = (case fw of (fs, w) \<Rightarrow> (case fs of [] \<Rightarrow> None | (j, av) # _ \<Rightarrow>
     (case act of
        VShift \<Rightarrow> (case w of [] \<Rightarrow> None | (a, c) # w' \<Rightarrow>
          (case iget (iget (v_sh V) j (IArray [])) (vnum V a) None of None \<Rightarrow> None
           | Some e \<Rightarrow> map_option (\<lambda>f. (f # fs, w')) (vgo V e av (FinRep [c]))))
      | VReduce s b pr \<Rightarrow> (let n = length (snd pr) in
          if n < length fs then (case fs ! n of (j\<^sub>0, av\<^sub>0) \<Rightarrow>
            (case iget (iget (v_go V) j\<^sub>0 (IArray [])) b None of None \<Rightarrow> None
             | Some e \<Rightarrow> map_option (\<lambda>f. (f # drop n fs, w)) (vgo V e av\<^sub>0 (getR av s))))
          else None))))\<close>

definition vlic :: \<open>('n, 't) vtab \<Rightarrow> nat \<Rightarrow> ('t \<times> nat) list \<Rightarrow> nat \<Rightarrow> indrep \<Rightarrow> bool\<close> where
  \<open>vlic V j w s RS = (case w of [] \<Rightarrow> s \<in> set (iget (v_ce V) j [])
     | (a, c) # _ \<Rightarrow> list_ex (\<lambda>(s', \<tau>). s' = s \<and> irep_ex_wsat \<tau> c RS)
         (iget (iget (v_cl V) j (IArray [])) (vnum V a) []))\<close>

definition vcands :: \<open>('n, 't) vtab \<Rightarrow> nat \<Rightarrow> indrep list \<Rightarrow> ('t \<times> nat) list \<Rightarrow> ('n, 't) vact list\<close> where
  \<open>vcands V j av w = (let reds = map (\<lambda>(s, b, pr). VReduce s b pr)
       (filter (\<lambda>(s, b, pr). let RS = getR av s in irep_nonempty RS \<and> vlic V j w s RS) (iget (v_cp V) j []))
     in (case w of [] \<Rightarrow> reds | _ \<Rightarrow> VShift # reds))\<close>

fun vpick :: \<open>('n, 't) vtab \<Rightarrow> vframes \<times> ('t \<times> nat) list \<Rightarrow> ('n, 't) vact list \<Rightarrow>
    (('n, 't) vact \<times> vframes \<times> ('t \<times> nat) list) option\<close> where
  \<open>vpick V fw [] = None\<close>
| \<open>vpick V fw (act # acts) = (case vmstep V fw act of Some r \<Rightarrow> Some (act, r) | None \<Rightarrow> vpick V fw acts)\<close>

type_synonym ('m, 'ch, 'n, 't) vst =
  \<open>vframes \<times> ('t \<times> nat) list \<times> ('m, 'ch, 't) tword \<times> ('m, 'ch, 'n, 't) ast list\<close>

definition vstep :: \<open>('n, 't) vtab \<Rightarrow> ('m, 'ch, 'n, 't) vst \<Rightarrow> ('m, 'ch, 'n, 't) vst option\<close> where
  \<open>vstep V st = (case st of (fs, w, v, tstk) \<Rightarrow> (case fs of [] \<Rightarrow> None | (j, av) # _ \<Rightarrow>
     (case vpick V (fs, w) (vcands V j av w) of None \<Rightarrow> None
      | Some (act, fs', w') \<Rightarrow> (case tstep (vdec act) (v, tstk) of (v', tstk') \<Rightarrow> Some (fs', w', v', tstk')))))\<close>

definition vfinal :: \<open>('n, 't) vtab \<Rightarrow> ('m, 'ch, 'n, 't) vst \<Rightarrow> bool\<close> where
  \<open>vfinal V st = (case st of (fs, w, v, tstk) \<Rightarrow> w = [] \<and> (case fs of [] \<Rightarrow> False
     | (j, av) # _ \<Rightarrow> irep_mem (v_ind0 V) (getR av (iget (v_fin V) j 0))))\<close>

partial_function (option) vrun :: \<open>('n, 't) vtab \<Rightarrow> ('m, 'ch, 'n, 't) vst \<Rightarrow> ('m, 'ch, 'n, 't) ast option\<close>
  where
  \<open>vrun V st = (case st of (fs, w, v, tstk) \<Rightarrow>
     if vfinal V st then (case tstk of t # _ \<Rightarrow> Some t | [] \<Rightarrow> None)
     else Option.bind (vstep V st) (vrun V))\<close>

lemmas vrun_simps [code] = vrun.simps

text \<open>The tables of a grammar.\<close>

definition vinit_frame :: \<open>('n, 't) is_cfg \<Rightarrow> 'n \<Rightarrow> ('n, 't) stab \<Rightarrow> ('n, 't) citem list list \<Rightarrow> nat \<times> indrep list\<close> where
  \<open>vinit_frame G Shn T sts = (let i\<^sub>0 = st_find sts (lr0_start G Shn); its = vits G sts i\<^sub>0 in
     (i\<^sub>0, vfill (map (vcontrib G Shn T its) its)
       (map (\<lambda>it. if it = (start_prod G Shn, 0) then FinRep [istart_ind G] else FinRep []) its)))\<close>

definition mk_vtab :: \<open>('n, 't) is_cfg \<Rightarrow> 'n \<Rightarrow> ('n, 't) stab \<Rightarrow> ('n, 't) citem list list \<Rightarrow>
    (('n, 't) sym \<times> nat) list list \<Rightarrow> ('n, 't) lacell list list \<Rightarrow> ('n, 't) vtab\<close> where
  \<open>mk_vtab G Shn T sts gt redtab = (let toks = vtoks G redtab; ns = [0..<length sts];
       ps = eprods G Shn in
     VTab (zip toks [0..<length toks]) (length toks)
       (IArray (map (\<lambda>j. IArray (map (\<lambda>a. ventry G gt sts j (Tm a)) toks)) ns))
       (IArray (map (\<lambda>j. IArray (map (\<lambda>b. ventry G gt sts j (Nt (fst (ps ! b)))) [0..<length ps])) ns))
       (IArray (map (\<lambda>j. map (vcontrib G Shn T (vits G sts j)) (vits G sts j)) ns))
       (IArray (map (\<lambda>j. vcomps G Shn (vits G sts j)) ns))
       (IArray (map (\<lambda>j. IArray (map (\<lambda>a. vcells (vits G sts j) j (redtab ! j) (Some a)) toks)) ns))
       (IArray (map (\<lambda>j. map fst (vcells (vits G sts j) j (redtab ! j) None)) ns))
       (IArray (map (\<lambda>j. ntidx (vits G sts j) (start_prod G Shn, 1)) ns))
       (vinit_frame G Shn T sts)
       (istart_ind G))\<close>



section \<open>The vector driver runs the dense one\<close>

subsection \<open>Anchor sets by item\<close>

text \<open>The anchors an item list gives a core item, over all its copies; only
  this enters the relation between a frame of the dense driver and a vector of
  anchor sets.\<close>

definition aset :: \<open>('n, 't) xitem list \<Rightarrow> ('n, 't) citem \<Rightarrow> nat set\<close> where
  \<open>aset xs it = \<Union> {irep_set R |R. (fst it, snd it, R) \<in> set xs}\<close>

lemma aset_Nil [simp]: \<open>aset [] it = {}\<close>
  by (simp add: aset_def)

lemma aset_Cons [simp]:
  \<open>aset ((p, m, R) # xs) it = (if (p, m) = it then irep_set R else {}) \<union> aset xs it\<close>
  by (cases it) (auto simp: aset_def)

lemma aset_append [simp]: \<open>aset (xs @ ys) it = aset xs it \<union> aset ys it\<close>
  by (auto simp: aset_def)

lemma aset_filter_ine [simp]: \<open>aset (filter ine xs) it = aset xs it\<close>
  by (auto simp: aset_def ine_def)

lemma aset_xeq: \<open>xeq xs ys \<Longrightarrow> aset xs it = aset ys it\<close>
  unfolding xrel_def by (induction rule: list_all2_induct) (auto split: prod.splits)

lemma aset_red: \<open>irep_set (red_set CL pr) = aset CL (pr, length (snd pr))\<close>
  by (simp add: red_set_correct aset_def)

lemma aset_ne_lcore: \<open>aset xs it \<noteq> {} \<longleftrightarrow> it \<in> lcore xs\<close>
  by (cases it) (auto simp: aset_def lcore_def)

lemma aset_coh:
  assumes c: \<open>coh xs\<close> and mem: \<open>(p, m, R) \<in> set xs\<close>
  shows \<open>aset xs (p, m) = irep_set R\<close>
proof -
  have e: \<open>irep_set R' = irep_set R\<close> if \<open>(p, m, R') \<in> set xs\<close> for R'
    using c[unfolded coh_def, rule_format, OF that mem] .
  have \<open>{irep_set R' |R'. (p, m, R') \<in> set xs} = {irep_set R}\<close> using mem e by blast
  then show ?thesis by (simp add: aset_def)
qed

lemma aset_notin: \<open>it \<notin> lcore xs \<Longrightarrow> aset xs it = {}\<close>
  using aset_ne_lcore by blast

lemma live_aset: \<open>live xs \<longleftrightarrow> (\<exists>it. aset xs it \<noteq> {})\<close>
  by (auto simp: live_lcore aset_ne_lcore)

lemma aset_lgoto:
  \<open>aset (lgoto xs X RA) (p, m) = (if 0 < m \<and> m \<le> length (snd p) \<and> fst (snd p ! (m - 1)) = X
     then aset xs (p, m - 1) \<inter> irep_set (irep_pre (snd (snd p ! (m - 1))) RA) else {})\<close>
proof (induction xs)
  case (Cons x xs)
  obtain p' m' R where x: \<open>x = (p', m', R)\<close> by (cases x)
  show ?case
    using Cons.IH by (cases m) (auto simp: x lgoto_def)
qed (simp add: lgoto_def)



subsection \<open>The closure by item\<close>

text \<open>The closure's anchor set at an item: the kernel's, and at a slot the
  transfers from every kernel item expecting a nonterminal.  The route is the
  sparse closure (\<^const>\<open>sclosure\<close>), whose fixpoint is the union of the paths
  (@{thm [source] sfix_trow}).\<close>

definition venc :: \<open>('n, 't) is_cfg \<Rightarrow> 'n \<Rightarrow> ('n, 't) xitem list \<Rightarrow> ('n, 't) sitem list\<close> where
  \<open>venc G Shn X = map (\<lambda>(p, m, R). (mkrec (eprods G Shn) p, m, R)) (filter ine X)\<close>

lemma map_sdec_venc: \<open>map sdec (venc G Shn X) = filter ine X\<close>
  by (induction X) (auto simp: venc_def)

lemma skrel_venc:
  assumes \<open>\<And>p m R. (p, m, R) \<in> set X \<Longrightarrow> irep_nonempty R \<Longrightarrow> p \<in> set (eprods G Shn)\<close>
  shows \<open>skrel G Shn X (venc G Shn X)\<close>
proof -
  have \<open>swf (eprods G Shn) (venc G Shn X)\<close> unfolding swf_def
  proof
    fix x assume \<open>x \<in> set (venc G Shn X)\<close>
    then obtain p m R where \<open>(p, m, R) \<in> set X\<close> \<open>irep_nonempty R\<close> \<open>x = (mkrec (eprods G Shn) p, m, R)\<close>
      by (auto simp: venc_def)
    with assms show \<open>case x of (r, m, R) \<Rightarrow> r \<in> mkrec (eprods G Shn) ` set (eprods G Shn)\<close> by auto
  qed
  then show ?thesis by (simp add: skrel_def map_sdec_venc)
qed

lemma sfix_loop_some:
  assumes T: \<open>T = mk_stab G Shn gt sts redtab\<close> and r: \<open>skrel G Shn K Ks\<close>
  shows \<open>sfix_loop T (skn T Ks) \<noteq> None\<close>
proof -
  let ?kn = \<open>skn T Ks\<close>
  obtain k where \<open>xstable G K (xiter G K k)\<close>
    using xcls_stable_ex by blast
  then have \<open>while_option (\<lambda>t. \<not> xstable G K (xiter G K t)) Suc 0 = Some (xfuel G K)\<close>
    unfolding xfuel_def by (rule nat_search_Some)
  moreover have
    \<open>map_option (\<lambda>t. (siter T ?kn t, siter T ?kn (Suc t)))
       (while_option (\<lambda>t. \<not> xstable G K (xiter G K t)) Suc 0) =
     while_option (\<lambda>(N, N'). \<not> ssub N' N) (\<lambda>(N, N'). (N', sround T ?kn N'))
       (siter T ?kn 0, siter T ?kn (Suc 0))\<close>
    by (rule while_option_commute[where f = \<open>\<lambda>t. (siter T ?kn t, siter T ?kn (Suc t))\<close> and s = 0])
      (simp_all only: xstable_diter[OF xeq_refl] ssub_lockstep[OF T r, simplified siter_simps] siter_simps case_prod_conv)
  ultimately have
    \<open>while_option (\<lambda>(N, N'). \<not> ssub N' N) (\<lambda>(N, N'). (N', sround T ?kn N')) ([], sround T ?kn []) =
     Some (siter T ?kn (xfuel G K), siter T ?kn (Suc (xfuel G K)))\<close>
    by simp
  then show ?thesis by (simp add: sfix_loop_def)
qed

lemma skn_key_less:
  assumes T: \<open>T = mk_stab G Shn gt sts redtab\<close> and w: \<open>swf (eprods G Shn) Ks\<close>
    and b: \<open>(b, R) \<in> set (skn T Ks)\<close>
  shows \<open>b < s_np T\<close>
proof -
  from b skn_keys[OF T w] have \<open>b \<in> set (lids G Shn)\<close> by force
  then obtain k where \<open>k < length (iprods G)\<close> \<open>lids G Shn ! k = b\<close> by (auto simp: in_set_conv_nth)
  with lids_nth_le[of k G Shn] show ?thesis by (simp add: T)
qed

lemma sitem_nx_vnext:
  \<open>sitem_nx (length (iprods G)) (mkrec (eprods G Shn) p, m, R) =
     map_option (\<lambda>(B, q). (nnum G Shn B, irep_img q R)) (vnext_nt G (p, m))\<close>
proof (cases \<open>m < length (snd p)\<close>)
  case True
  obtain X q where Xq: \<open>snd p ! m = (X, q)\<close> by (cases \<open>snd p ! m\<close>)
  show ?thesis
  proof (cases X)
    case (Nt B)
    with True Xq lhs_id_less[of G Shn B] show ?thesis
      by (cases p) (simp add: sitem_nx_def vnext_nt_def nnum_def)
  qed (use True Xq in \<open>cases p, simp add: sitem_nx_def vnext_nt_def\<close>)
qed (cases p, simp add: sitem_nx_def vnext_nt_def)

text \<open>The transfers into a nonterminal, summed over the kernel's items.\<close>

definition vin :: \<open>('n, 't) is_cfg \<Rightarrow> 'n \<Rightarrow> ('n, 't) stab \<Rightarrow> ('n, 't) xitem list \<Rightarrow> nat \<Rightarrow> nat set\<close> where
  \<open>vin G Shn T X a = \<Union>{eff_set (ecomp (trow T (nnum G Shn B) ! a) (of_rel q)) (aset X it) |it B q.
     vnext_nt G it = Some (B, q)}\<close>

lemma skn_paths:
  assumes T: \<open>T = mk_stab G Shn gt sts redtab\<close>
  shows \<open>(\<Union>(b, R) \<in> set (skn T (venc G Shn X)). eff_set (trow T b ! a) (irep_set R)) = vin G Shn T X a\<close>
proof (rule set_eqI)
  fix x
  have im: \<open>aset X it = \<Union> (irep_set ` {R. (fst it, snd it, R) \<in> set X})\<close> for it
    unfolding aset_def by blast
  have sub: \<open>(fst it, snd it, R) \<in> set X \<Longrightarrow> irep_set R \<subseteq> aset X it\<close> for R it
    unfolding im by blast
  have D: \<open>x \<in> eff_set e (aset X it) \<Longrightarrow> \<exists>R. (fst it, snd it, R) \<in> set X \<and> x \<in> eff_set e (irep_set R)\<close> for e it
    unfolding im eff_set_UN by blast
  let ?E = \<open>\<lambda>B q. ecomp (trow T (nnum G Shn B) ! a) (of_rel q)\<close>
  have mv: \<open>x \<in> vin G Shn T X a \<longleftrightarrow> (\<exists>p m R B q. (p, m, R) \<in> set X \<and> vnext_nt G (p, m) = Some (B, q) \<and>
      x \<in> eff_set (?E B q) (irep_set R))\<close> (is \<open>_ \<longleftrightarrow> ?r\<close>)
  proof
    assume \<open>x \<in> vin G Shn T X a\<close>
    then obtain it B q where i: \<open>vnext_nt G it = Some (B, q)\<close> \<open>x \<in> eff_set (?E B q) (aset X it)\<close>
      unfolding vin_def by blast
    from D[OF i(2)] obtain R where \<open>(fst it, snd it, R) \<in> set X\<close> \<open>x \<in> eff_set (?E B q) (irep_set R)\<close>
      by blast
    with i(1) show ?r by (metis prod.collapse)
  next
    assume ?r
    then obtain p m R B q where r: \<open>(p, m, R) \<in> set X\<close> \<open>vnext_nt G (p, m) = Some (B, q)\<close>
      \<open>x \<in> eff_set (?E B q) (irep_set R)\<close> by blast
    have \<open>irep_set R \<subseteq> aset X (p, m)\<close> using sub[of \<open>(p, m)\<close> R] r(1) by simp
    from eff_set_mono[OF this, of \<open>?E B q\<close>] r(3) have \<open>x \<in> eff_set (?E B q) (aset X (p, m))\<close>
      by blast
    with r(2) show \<open>x \<in> vin G Shn T X a\<close> unfolding vin_def by blast
  qed
  have nx: \<open>sitem_nx (s_np T) (mkrec (eprods G Shn) p, m, R) =
      map_option (\<lambda>(B, q). (nnum G Shn B, irep_img q R)) (vnext_nt G (p, m))\<close> for p m R
    using sitem_nx_vnext by (simp add: T)
  have ev: \<open>eff_set (?E B q) (irep_set R) = eff_set (trow T (nnum G Shn B) ! a) (irep_set (irep_img q R))\<close>
    for B q R by (simp only: eff_set_comp eff_set_img)
  have sk: \<open>(b, R) \<in> set (skn T (venc G Shn X)) \<longleftrightarrow>
      R \<noteq> FinRep [] \<and> (\<exists>s \<in> set (venc G Shn X). sitem_nx (s_np T) s = Some (b, R))\<close> for b R
    by (auto simp: skn_def in_map_filter)
  have vc: \<open>s \<in> set (venc G Shn X) \<longleftrightarrow>
      (\<exists>p m R. (p, m, R) \<in> set X \<and> irep_nonempty R \<and> s = (mkrec (eprods G Shn) p, m, R))\<close> for s
    by (force simp: venc_def)
  show \<open>x \<in> (\<Union>(b, R) \<in> set (skn T (venc G Shn X)). eff_set (trow T b ! a) (irep_set R)) \<longleftrightarrow> x \<in> vin G Shn T X a\<close>
  proof
    assume \<open>x \<in> (\<Union>(b, R) \<in> set (skn T (venc G Shn X)). eff_set (trow T b ! a) (irep_set R))\<close>
    then obtain b R where bR: \<open>(b, R) \<in> set (skn T (venc G Shn X))\<close> \<open>x \<in> eff_set (trow T b ! a) (irep_set R)\<close>
      by blast
    then obtain s where s: \<open>s \<in> set (venc G Shn X)\<close> \<open>sitem_nx (s_np T) s = Some (b, R)\<close>
      unfolding sk by blast
    then obtain p m R' where \<open>(p, m, R') \<in> set X\<close> \<open>s = (mkrec (eprods G Shn) p, m, R')\<close>
      unfolding vc by blast
    with s(2) have pm: \<open>(p, m, R') \<in> set X\<close>
        \<open>sitem_nx (s_np T) (mkrec (eprods G Shn) p, m, R') = Some (b, R)\<close>
      by simp_all
    then obtain B q where v: \<open>vnext_nt G (p, m) = Some (B, q)\<close>
        and br: \<open>b = nnum G Shn B\<close> \<open>R = irep_img q R'\<close>
      unfolding nx by auto
    from bR(2) have \<open>x \<in> eff_set (?E B q) (irep_set R')\<close> unfolding ev br .
    with pm(1) v show \<open>x \<in> vin G Shn T X a\<close> unfolding mv by blast
  next
    assume \<open>x \<in> vin G Shn T X a\<close>
    then obtain p m R B q where r: \<open>(p, m, R) \<in> set X\<close> \<open>vnext_nt G (p, m) = Some (B, q)\<close>
        \<open>x \<in> eff_set (?E B q) (irep_set R)\<close>
      unfolding mv by blast
    then have ne: \<open>irep_nonempty R\<close> by (metis empty_iff eff_set_empty irep_nonempty_correct)
    from r(3) have x: \<open>x \<in> eff_set (trow T (nnum G Shn B) ! a) (irep_set (irep_img q R))\<close> by (simp only: ev)
    then have \<open>irep_set (irep_img q R) \<noteq> {}\<close> by (metis empty_iff eff_set_empty)
    then have i: \<open>irep_img q R \<noteq> FinRep []\<close> by (metis irep_nonempty_iff irep_nonempty_correct)
    have s: \<open>(mkrec (eprods G Shn) p, m, R) \<in> set (venc G Shn X)\<close> unfolding vc using r(1) ne by blast
    have \<open>(nnum G Shn B, irep_img q R) \<in> set (skn T (venc G Shn X))\<close>
      unfolding sk by (intro conjI i bexI[OF _ s]) (simp add: nx r(2))
    with x show \<open>x \<in> (\<Union>(b, R) \<in> set (skn T (venc G Shn X)). eff_set (trow T b ! a) (irep_set R))\<close>
      by blast
  qed
qed

lemma slk_sfix_vin:
  assumes T: \<open>T = mk_stab G Shn gt sts redtab\<close>
    and w: \<open>\<And>p m R. (p, m, R) \<in> set X \<Longrightarrow> irep_nonempty R \<Longrightarrow> p \<in> set (eprods G Shn)\<close>
    and A: \<open>A \<in> fst ` set (iprods G)\<close>
  shows \<open>irep_set (slk (sfix T (skn T (venc G Shn X))) (nnum G Shn A)) = vin G Shn T X (nnum G Shn A)\<close>
proof -
  have r: \<open>skrel G Shn X (venc G Shn X)\<close> by (rule skrel_venc[OF w])
  have ok: \<open>ntl_ok T\<close> by (simp add: T ntl_ok_mk_stab)
  have a: \<open>nnum G Shn A < s_np T\<close> using A lhs_id_less[of G Shn A] by (simp add: T nnum_def)
  have \<open>irep_set (slk (sfix T (skn T (venc G Shn X))) (nnum G Shn A)) =
      (\<Union>(b, R) \<in> set (skn T (venc G Shn X)). eff_set (trow T b ! nnum G Shn A) (irep_set R))\<close>
    by (rule sfix_trow[OF ok sfix_loop_some[OF T r] skn_key_less[OF T skrel_swf[OF r]] a])
  then show ?thesis by (simp add: skn_paths[OF T])
qed

lemma cl_aset:
  assumes T: \<open>T = mk_stab G Shn gt sts redtab\<close>
    and w: \<open>\<And>p m R. (p, m, R) \<in> set X \<Longrightarrow> irep_nonempty R \<Longrightarrow> p \<in> set (eprods G Shn)\<close>
  shows \<open>aset (xclosure_auto G X) it =
    aset X it \<union> (if is_slot G it then vin G Shn T X (nnum G Shn (fst (fst it))) else {})\<close>
proof -
  let ?n = \<open>length (iprods G)\<close>
  let ?Ks = \<open>venc G Shn X\<close>
  let ?N = \<open>sfix T (skn T ?Ks)\<close>
  let ?ks = \<open>filter (\<lambda>k. lids G Shn ! k \<in> fst ` set ?N) [0..<?n]\<close>
  have r: \<open>skrel G Shn X ?Ks\<close> by (rule skrel_venc[OF w])
  have inv: \<open>sinv G Shn ?N\<close>
    unfolding sfix_siter[OF T r] by (rule siter_inv[OF T skrel_swf[OF r]])
  have fne: \<open>filter (\<lambda>(_, _, R). irep_nonempty R) ?Ks = filter ine ?Ks\<close>
    by (rule filter_cong) (auto simp: ine_def simp del: irep_nonempty_correct)
  have sparse: \<open>map sdec (sclosure T ?Ks) =
      map sdec (filter ine ?Ks) @ map (\<lambda>k. (iprods G ! k, 0, slk ?N (lids G Shn ! k))) ?ks\<close>
    using inv unfolding sclosure_def Let_def fne sinv_def
    by (simp add: ntl_concat[OF T] recs_sel[OF T] del: IArray.sub_def cong: map_cong)
  have kern: \<open>aset (map sdec (filter ine ?Ks)) it = aset X it\<close>
    by (simp add: map_sdec_filter map_sdec_venc)
  have slots: \<open>aset (map (\<lambda>k. (iprods G ! k, 0, slk ?N (lids G Shn ! k))) ?ks) it =
      (if is_slot G it then irep_set (slk ?N (nnum G Shn (fst (fst it)))) else {})\<close>
    proof (cases \<open>is_slot G it\<close>)
    case True
    let ?b = \<open>nnum G Shn (fst (fst it))\<close>
    let ?S = \<open>{irep_set R |R. (fst it, snd it, R) \<in> set (map (\<lambda>k. (iprods G ! k, 0, slk ?N (lids G Shn ! k))) ?ks)}\<close>
    have l: \<open>lids G Shn ! k = ?b\<close> if \<open>k < ?n\<close> \<open>iprods G ! k = fst it\<close> for k
      using that by (simp add: lids_nth nnum_def)
    from True obtain k where k: \<open>k < ?n\<close> \<open>iprods G ! k = fst it\<close> \<open>snd it = 0\<close>
      by (auto simp: is_slot_def in_set_conv_nth)
    have sub: \<open>?S \<subseteq> {irep_set (slk ?N ?b)}\<close> using l by auto
    show ?thesis
    proof (cases \<open>?b \<in> fst ` set ?N\<close>)
      case True
      have \<open>(fst it, snd it, slk ?N ?b) \<in> set (map (\<lambda>k. (iprods G ! k, 0, slk ?N (lids G Shn ! k))) ?ks)\<close>
        using k True l[OF k(1,2)] by (force intro!: image_eqI[of _ _ k])
      then have \<open>?S = {irep_set (slk ?N ?b)}\<close> using sub by blast
      with \<open>is_slot G it\<close> show ?thesis by (simp add: aset_def)
    next
      case False
      then have \<open>irep_set (slk ?N ?b) = {}\<close> by (simp add: slk_notin)
      with sub \<open>is_slot G it\<close> show ?thesis unfolding aset_def by auto
    qed
  next
    case False
    then show ?thesis by (auto simp: aset_def is_slot_def)
  qed
  have \<open>aset (xclosure_auto G X) it = aset (filter ine (dclosure G X)) it\<close>
    by (simp add: aset_xeq[OF xclosure_auto_dclosure[OF xeq_refl]])
  also have \<open>\<dots> = aset (map sdec (sclosure T ?Ks)) it\<close> by (rule aset_xeq[OF sclosure_rel[OF T r]])
  also have \<open>\<dots> = aset X it \<union> (if is_slot G it then irep_set (slk ?N (nnum G Shn (fst (fst it)))) else {})\<close>
    unfolding sparse aset_append kern slots ..
  also have \<open>\<dots> = aset X it \<union> (if is_slot G it then vin G Shn T X (nnum G Shn (fst (fst it))) else {})\<close>
    using slk_sfix_vin[OF T w] by (auto simp: is_slot_def)
  finally show ?thesis .
qed



subsection \<open>Filling a frame\<close>

text \<open>A kernel vector stands for a kernel \<open>X\<close> at the items of a state when it
  holds the kernel's anchor set at every position but the slots, which it leaves
  empty.\<close>

definition vkrel :: \<open>('n, 't) is_cfg \<Rightarrow> ('n, 't) citem list \<Rightarrow> ('n, 't) xitem list \<Rightarrow> indrep list \<Rightarrow> bool\<close> where
  \<open>vkrel G its X kav \<longleftrightarrow> length kav = length its \<and>
     (\<forall>s < length its. irep_set (kav ! s) = (if is_slot G (its ! s) then {} else aset X (its ! s)))\<close>

lemma fold_cunion_set:
  \<open>irep_set (fold (\<lambda>(kk, e) acc. cunion acc (eapp e (getR kav kk))) cs R) =
     irep_set R \<union> (\<Union>(kk, e) \<in> set cs. eff_set e (irep_set (getR kav kk)))\<close>
  by (induction cs arbitrary: R) auto

lemma length_vfill [simp]: \<open>length (vfill cts kav) = min (length kav) (length cts)\<close>
  by (simp add: vfill_def)

lemma vfill_nth:
  \<open>s < length kav \<Longrightarrow> s < length cts \<Longrightarrow>
   vfill cts kav ! s = fold (\<lambda>(kk, e) acc. cunion acc (eapp e (getR kav kk))) (cts ! s) (kav ! s)\<close>
  by (simp add: vfill_def)

lemma vcontrib_set:
  \<open>(kk, e) \<in> set (vcontrib G Shn T its it) \<longleftrightarrow> is_slot G it \<and> kk < length its \<and> \<not> is_slot G (its ! kk) \<and>
     (\<exists>B q. vnext_nt G (its ! kk) = Some (B, q) \<and>
        e = ecomp (trow T (nnum G Shn B) ! nnum G Shn (fst (fst it))) (of_rel q))\<close>
proof -
  let ?f = \<open>\<lambda>kk. if is_slot G (its ! kk) then None else
       (case vnext_nt G (its ! kk) of None \<Rightarrow> None
        | Some (B, q) \<Rightarrow> Some (kk, ecomp (trow T (nnum G Shn B) ! nnum G Shn (fst (fst it))) (of_rel q)))\<close>
  have f: \<open>?f x = Some (kk, e) \<longleftrightarrow> x = kk \<and> \<not> is_slot G (its ! kk) \<and>
      (\<exists>B q. vnext_nt G (its ! kk) = Some (B, q) \<and>
        e = ecomp (trow T (nnum G Shn B) ! nnum G Shn (fst (fst it))) (of_rel q))\<close> for x
    by (auto split: option.splits)
  show ?thesis
  proof (cases \<open>is_slot G it\<close>)
    case True
    then show ?thesis unfolding vcontrib_def by (simp only: True if_True in_map_filter f) auto
  qed (simp add: vcontrib_def)
qed

lemma vfill_cl:
  assumes T: \<open>T = mk_stab G Shn gt sts redtab\<close>
    and w: \<open>\<And>p m R. (p, m, R) \<in> set X \<Longrightarrow> irep_nonempty R \<Longrightarrow> p \<in> set (eprods G Shn)\<close>
    and k: \<open>vkrel G its X kav\<close>
    and cov: \<open>\<And>it. aset X it \<noteq> {} \<Longrightarrow> it \<in> set its\<close>
    and ns: \<open>\<And>it. is_slot G it \<Longrightarrow> aset X it = {}\<close>
    and s: \<open>s < length its\<close>
  shows \<open>irep_set (vfill (map (vcontrib G Shn T its) its) kav ! s) = aset (xclosure_auto G X) (its ! s)\<close>
proof -
  let ?it = \<open>its ! s\<close>
  let ?C = \<open>\<Union>(kk, e) \<in> set (vcontrib G Shn T its ?it). eff_set e (irep_set (getR kav kk))\<close>
  have cl: \<open>aset (xclosure_auto G X) it =
      aset X it \<union> (if is_slot G it then vin G Shn T X (nnum G Shn (fst (fst it))) else {})\<close> for it
    by (rule cl_aset[OF T]) (rule w)
  have lk: \<open>length kav = length its\<close> using k by (simp add: vkrel_def)
  have v: \<open>irep_set (vfill (map (vcontrib G Shn T its) its) kav ! s) = irep_set (kav ! s) \<union> ?C\<close>
    using s lk by (simp add: vfill_nth fold_cunion_set)
  show ?thesis
  proof (cases \<open>is_slot G ?it\<close>)
    case False
    then have \<open>vcontrib G Shn T its ?it = []\<close> by (simp add: vcontrib_def)
    with False k s show ?thesis unfolding v cl by (simp add: vkrel_def)
  next
    case True
    let ?a = \<open>nnum G Shn (fst (fst ?it))\<close>
    have C: \<open>?C = vin G Shn T X ?a\<close>
    proof (rule set_eqI, rule iffI)
      fix x assume \<open>x \<in> ?C\<close>
      then obtain kk e where c: \<open>(kk, e) \<in> set (vcontrib G Shn T its ?it)\<close>
          and x: \<open>x \<in> eff_set e (irep_set (getR kav kk))\<close>
        by blast
      from c obtain B q where kk: \<open>kk < length its\<close> \<open>\<not> is_slot G (its ! kk)\<close>
          and B: \<open>vnext_nt G (its ! kk) = Some (B, q)\<close>
          and e: \<open>e = ecomp (trow T (nnum G Shn B) ! ?a) (of_rel q)\<close>
        unfolding vcontrib_set by blast
      have \<open>irep_set (getR kav kk) = aset X (its ! kk)\<close>
        using k kk lk by (simp add: vkrel_def getR_def)
      with x e have \<open>x \<in> eff_set (ecomp (trow T (nnum G Shn B) ! ?a) (of_rel q)) (aset X (its ! kk))\<close>
        by simp
      with B show \<open>x \<in> vin G Shn T X ?a\<close> unfolding vin_def by blast
    next
      fix x assume \<open>x \<in> vin G Shn T X ?a\<close>
      then obtain it' B q where B: \<open>vnext_nt G it' = Some (B, q)\<close>
          and x: \<open>x \<in> eff_set (ecomp (trow T (nnum G Shn B) ! ?a) (of_rel q)) (aset X it')\<close>
        unfolding vin_def by blast
      then have \<open>aset X it' \<noteq> {}\<close> by (metis empty_iff eff_set_empty)
      then have it': \<open>it' \<in> set its\<close> \<open>\<not> is_slot G it'\<close> using cov ns by blast+
      then obtain kk where kk: \<open>kk < length its\<close> \<open>its ! kk = it'\<close> by (auto simp: in_set_conv_nth)
      have \<open>irep_set (getR kav kk) = aset X it'\<close>
        using k kk lk it'(2) by (simp add: vkrel_def getR_def)
      moreover have \<open>(kk, ecomp (trow T (nnum G Shn B) ! ?a) (of_rel q)) \<in> set (vcontrib G Shn T its ?it)\<close>
        unfolding vcontrib_set using True kk it'(2) B by blast
      ultimately show \<open>x \<in> ?C\<close> using x by (intro UN_I) auto
    qed
    have \<open>irep_set (kav ! s) = {}\<close> using True k s by (simp add: vkrel_def)
    with True show ?thesis unfolding v C cl by (simp add: ns)
  qed
qed



subsection \<open>The successor's kernel\<close>

text \<open>A frame stands for a closure \<open>CL\<close> when it holds the closure's anchor set at
  every item of its state.\<close>

definition vfr :: \<open>('n, 't) xitem list \<Rightarrow> ('n, 't) citem list \<Rightarrow> indrep list \<Rightarrow> bool\<close> where
  \<open>vfr CL its av \<longleftrightarrow> length av = length its \<and> (\<forall>s < length its. irep_set (av ! s) = aset CL (its ! s))\<close>

lemma vfr_getR:
  assumes fr: \<open>vfr CL its av\<close> and cov: \<open>lcore CL \<subseteq> set its\<close>
  shows \<open>irep_set (getR av (ntidx its it)) = aset CL it\<close>
proof (cases \<open>it \<in> set its\<close>)
  case True
  then have \<open>ntidx its it < length its\<close> \<open>its ! ntidx its it = it\<close> by (simp_all add: ntidx_less ntidx_nth)
  with fr show ?thesis by (simp add: vfr_def getR_def)
next
  case False
  with cov have \<open>aset CL it = {}\<close> by (intro aset_notin) blast
  with False fr show ?thesis by (simp add: vfr_def getR_def ntidx_notin)
qed

lemma length_vkav [simp]: \<open>length (vkav km av RA) = length km\<close>
  by (simp add: vkav_def)

lemma length_vkmap [simp]: \<open>length (vkmap its X its') = length its'\<close>
  by (simp add: vkmap_def)

lemma vkav_krel:
  assumes fr: \<open>vfr CL its av\<close> and cov: \<open>lcore CL \<subseteq> set its\<close>
  shows \<open>vkrel G its' (lgoto CL X RA) (vkav (vkmap its X its') av RA)\<close>
  unfolding vkrel_def
proof (intro conjI allI impI)
  fix s assume s: \<open>s < length its'\<close>
  obtain p m where pm: \<open>its' ! s = (p, m)\<close> by (cases \<open>its' ! s\<close>)
  have \<open>irep_set (vkav (vkmap its X its') av RA ! s) =
      (if 0 < m \<and> m \<le> length (snd p) \<and> fst (snd p ! (m - 1)) = X
       then aset CL (p, m - 1) \<inter> irep_set (irep_pre (snd (snd p ! (m - 1))) RA) else {})\<close>
    using s pm vfr_getR[OF fr cov] by (simp add: vkav_def vkmap_def)
  then show \<open>irep_set (vkav (vkmap its X its') av RA ! s) =
      (if is_slot G (its' ! s) then {} else aset (lgoto CL X RA) (its' ! s))\<close>
    by (simp add: pm aset_lgoto is_slot_def)
qed simp


subsection \<open>Frames of a reachable configuration\<close>

text \<open>Every frame of a reachable configuration is live: a step pushes a live
  frame and keeps a suffix of the old stack.  So every frame has a state, its
  closure stays inside that state's items, and its anchored items come from the
  productions the sparse tables number.\<close>

lemma imreach_frames_live:
  \<open>imreach G Shn gt sts ic \<Longrightarrow> X \<in> set (fst (fst ic)) \<Longrightarrow> live X\<close>
proof (induction arbitrary: X rule: imreach.induct)
  case (imreach_init w)
  then show ?case by (simp add: xinit_def live_def)
next
  case (imreach_step ic act ic')
  obtain Xs w istk where ic: \<open>ic = ((Xs, w), istk)\<close> by (metis prod.exhaust)
  obtain Xs' w' istk' where ic': \<open>ic' = ((Xs', w'), istk')\<close> by (metis prod.exhaust)
  have ms: \<open>mstep_cached G (map (xclosure_auto G) Xs) (Xs, w) act = Some (Xs', w')\<close>
    using imstep_mstep[OF imreach_step.hyps(2)] by (simp add: ic ic' mstep_def)
  have hd: \<open>live (hd Xs')\<close> and ne: \<open>Xs' \<noteq> []\<close>
    using imreach_step.hyps(3) by (simp_all add: ic' dlive_def)
  have tl: \<open>set (tl Xs') \<subseteq> set Xs\<close>
  proof (cases act)
    case DShift
    show ?thesis by (rule mstep_shift_shape[OF ms[unfolded DShift]]) auto
  next
    case (DReduce pr)
    show ?thesis by (rule mstep_reduce_shape[OF ms[unfolded DReduce]]) (auto dest: in_set_dropD)
  qed
  from ne obtain Y Ys where Xs': \<open>Xs' = Y # Ys\<close> by (cases Xs') auto
  from imreach_step.prems hd tl imreach_step.IH show ?case by (auto simp: ic ic' Xs')
qed

lemma didx_ok_drop: \<open>didx_ok G sts Xs istk \<Longrightarrow> didx_ok G sts (drop k Xs) (drop k istk)\<close>
  by (auto simp: didx_ok_def)

lemma frame_cov:
  assumes ok: \<open>didx_ok G sts Xs istk\<close> and k: \<open>k < length Xs\<close> and lv: \<open>live (Xs ! k)\<close>
  shows \<open>istk ! k < length sts\<close> and \<open>lcore (xclosure_auto G (Xs ! k)) \<subseteq> set (vits G sts (istk ! k))\<close>
proof -
  have ok': \<open>didx_ok G sts (drop k Xs) (drop k istk)\<close> by (rule didx_ok_drop[OF ok])
  have ne: \<open>drop k Xs \<noteq> []\<close> using k by simp
  have li: \<open>length istk = length Xs\<close> by (rule didx_ok_len[OF ok])
  have hX: \<open>hd (drop k Xs) = Xs ! k\<close> and hi: \<open>hd (drop k istk) = istk ! k\<close>
    using k li by (simp_all add: hd_drop_conv_nth)
  from lv obtain pr m R where \<open>(pr, m, R) \<in> set (Xs ! k)\<close> and \<open>irep_nonempty R\<close>
    unfolding live_def list_ex_iff by fastforce
  moreover from this obtain j where \<open>j \<in> irep_set R\<close> by auto
  ultimately have \<open>(pr, m, R) \<in> set (xclosure_auto G (hd (drop k Xs)))\<close> and \<open>j \<in> irep_set R\<close>
    using hX xclosure_auto_kernel_sub[of \<open>Xs ! k\<close> G] by auto
  from didx_ok_creach(1)[OF ok' ne this] show lt: \<open>istk ! k < length sts\<close> by (simp add: hi)
  show \<open>lcore (xclosure_auto G (Xs ! k)) \<subseteq> set (vits G sts (istk ! k))\<close>
  proof
    fix it assume \<open>it \<in> lcore (xclosure_auto G (Xs ! k))\<close>
    then obtain pr m R where it: \<open>it = (pr, m)\<close> and mem: \<open>(pr, m, R) \<in> set (xclosure_auto G (Xs ! k))\<close>
      and \<open>irep_nonempty R\<close> unfolding lcore_def by blast
    then obtain j where \<open>j \<in> irep_set R\<close> by auto
    from didx_ok_creach(2)[OF ok' ne, of pr m R j] mem this hX hi lt
    show \<open>it \<in> set (vits G sts (istk ! k))\<close> by (simp add: it vits_def)
  qed
qed

lemma frame_eprods:
  assumes tab: \<open>tables_ok G Shn sts gt L\<close> and ok: \<open>didx_ok G sts Xs istk\<close> and k: \<open>k < length Xs\<close>
    and mem: \<open>(p, m, R) \<in> set (Xs ! k)\<close> and R: \<open>irep_nonempty R\<close>
  shows \<open>p \<in> set (eprods G Shn)\<close>
proof -
  have \<open>(p, m) \<in> lcore (Xs ! k)\<close> using mem R unfolding lcore_def by blast
  with didx_okD[OF ok k] have \<open>(p, m) \<in> set (sts ! (istk ! k))\<close> and \<open>istk ! k < length sts\<close> by auto
  moreover from tab have \<open>\<forall>s \<in> set sts. set s \<subseteq> cuniv G Shn\<close> by (simp add: tables_ok_def)
  ultimately have \<open>(p, m) \<in> cuniv G Shn\<close> by (meson nth_mem subsetD)
  then show ?thesis by (auto simp: cuniv_def eprods_def start_prod_def)
qed

lemma closure_eprods:
  assumes tab: \<open>tables_ok G Shn sts gt L\<close> and j: \<open>j < length sts\<close>
    and mem: \<open>it \<in> set (vits G sts j)\<close>
  shows \<open>fst it \<in> set (eprods G Shn)\<close>
proof -
  from tab j have \<open>set (sts ! j) \<subseteq> cuniv G Shn\<close> by (simp add: tables_ok_def)
  then have \<open>set (vits G sts j) \<subseteq> cuniv G Shn\<close> using j by (simp add: vits_def creach_univ)
  with mem show ?thesis by (cases it) (auto simp: cuniv_def eprods_def start_prod_def)
qed

text \<open>The vector frames stand for the dense ones: same states, and each vector
  holds its frame's closure.\<close>

definition vrel :: \<open>('n, 't) is_cfg \<Rightarrow> ('n, 't) citem list list \<Rightarrow> ('n, 't) xitem list list \<Rightarrow>
    nat list \<Rightarrow> vframes \<Rightarrow> bool\<close> where
  \<open>vrel G sts Xs istk fs \<longleftrightarrow> map fst fs = istk \<and> length Xs = length fs \<and>
     (\<forall>k < length fs. vfr (xclosure_auto G (Xs ! k)) (vits G sts (istk ! k)) (snd (fs ! k)))\<close>

lemma vrel_push:
  \<open>vrel G sts Xs istk fs \<Longrightarrow> vfr (xclosure_auto G X) (vits G sts j) av \<Longrightarrow>
     vrel G sts (X # Xs) (j # istk) ((j, av) # fs)\<close>
  by (auto simp: vrel_def nth_Cons split: nat.split)

lemma vrel_drop: \<open>vrel G sts Xs istk fs \<Longrightarrow> vrel G sts (drop n Xs) (drop n istk) (drop n fs)\<close>
  by (auto simp: vrel_def drop_map)

lemma vrel_nth:
  assumes \<open>vrel G sts Xs istk fs\<close> and \<open>k < length fs\<close>
  shows \<open>fst (fs ! k) = istk ! k\<close> and \<open>vfr (xclosure_auto G (Xs ! k)) (vits G sts (istk ! k)) (snd (fs ! k))\<close>
  using assms by (auto simp: vrel_def)


subsection \<open>Looking up the tables\<close>

lemma map_of_zip_upt:
  \<open>map_of (zip xs [k..<k + length xs]) a = (if a \<in> set xs then Some (k + ntidx xs a) else None)\<close>
proof (induction xs arbitrary: k)
  case (Cons x xs)
  from Cons.IH[of \<open>Suc k\<close>] show ?case by (auto simp del: upt_Suc simp add: upt_conv_Cons)
qed simp

lemma iget_IArray [simp]: \<open>iget (IArray xs) k d = (if k < length xs then xs ! k else d)\<close>
  by (simp add: iget_def)

lemma vnum_mk: \<open>V = mk_vtab G Shn T sts gt redtab \<Longrightarrow> vnum V a = ntidx (vtoks G redtab) a\<close>
  using map_of_zip_upt[of \<open>vtoks G redtab\<close> 0 a]
  by (auto simp: vnum_def mk_vtab_def Let_def ntidx_notin)

lemma v_sh_mk:
  assumes V: \<open>V = mk_vtab G Shn T sts gt redtab\<close> and j: \<open>j < length sts\<close>
  shows \<open>iget (iget (v_sh V) j (IArray [])) (vnum V a) None =
    (if a \<in> set (vtoks G redtab) then ventry G gt sts j (Tm a) else None)\<close>
  using j by (simp add: vnum_mk[OF V]) (simp add: V mk_vtab_def Let_def ntidx_less ntidx_nth)

lemma v_go_mk:
  assumes V: \<open>V = mk_vtab G Shn T sts gt redtab\<close> and j: \<open>j < length sts\<close> and b: \<open>b < length (eprods G Shn)\<close>
  shows \<open>iget (iget (v_go V) j (IArray [])) b None = ventry G gt sts j (Nt (fst (eprods G Shn ! b)))\<close>
  using j b by (simp add: V mk_vtab_def Let_def del: upt_Suc)

lemma v_ct_mk:
  assumes V: \<open>V = mk_vtab G Shn T sts gt redtab\<close> and j: \<open>j < length sts\<close>
  shows \<open>iget (v_ct V) j [] = map (vcontrib G Shn T (vits G sts j)) (vits G sts j)\<close>
  using j by (simp add: V mk_vtab_def Let_def)

lemma v_cp_mk:
  assumes V: \<open>V = mk_vtab G Shn T sts gt redtab\<close> and j: \<open>j < length sts\<close>
  shows \<open>iget (v_cp V) j [] = vcomps G Shn (vits G sts j)\<close>
  using j by (simp add: V mk_vtab_def Let_def)

lemma v_cl_mk:
  assumes V: \<open>V = mk_vtab G Shn T sts gt redtab\<close> and j: \<open>j < length sts\<close>
  shows \<open>iget (iget (v_cl V) j (IArray [])) (vnum V a) [] =
    (if a \<in> set (vtoks G redtab) then vcells (vits G sts j) j (redtab ! j) (Some a) else [])\<close>
  using j by (simp add: vnum_mk[OF V]) (simp add: V mk_vtab_def Let_def ntidx_less ntidx_nth)

lemma v_ce_mk:
  assumes V: \<open>V = mk_vtab G Shn T sts gt redtab\<close> and j: \<open>j < length sts\<close>
  shows \<open>iget (v_ce V) j [] = map fst (vcells (vits G sts j) j (redtab ! j) None)\<close>
  using j by (simp add: V mk_vtab_def Let_def)

lemma v_fin_mk:
  assumes V: \<open>V = mk_vtab G Shn T sts gt redtab\<close> and j: \<open>j < length sts\<close>
  shows \<open>iget (v_fin V) j 0 = ntidx (vits G sts j) (start_prod G Shn, 1)\<close>
  using j by (simp add: V mk_vtab_def Let_def)

lemma v_ind0_mk: \<open>V = mk_vtab G Shn T sts gt redtab \<Longrightarrow> v_ind0 V = istart_ind G\<close>
  by (simp add: mk_vtab_def Let_def)

lemma v_av0_mk: \<open>V = mk_vtab G Shn T sts gt redtab \<Longrightarrow> v_av0 V = vinit_frame G Shn T sts\<close>
  by (simp add: mk_vtab_def Let_def)

lemma vcomps_set:
  \<open>(s, b, pr) \<in> set (vcomps G Shn its) \<longleftrightarrow>
     (pr, length (snd pr)) \<in> set its \<and> s = ntidx its (pr, length (snd pr)) \<and> b = nnum G Shn (fst pr)\<close>
  (is \<open>?L \<longleftrightarrow> ?R\<close>)
proof
  assume ?L
  then obtain x where x: \<open>x < length its\<close> and e: \<open>(case its ! x of (pr', m) \<Rightarrow>
      if m = length (snd pr') \<and> ntidx its (pr', m) = x then Some (x, nnum G Shn (fst pr'), pr')
      else None) = Some (s, b, pr)\<close>
    unfolding vcomps_def in_map_filter by auto
  obtain pr' m where i: \<open>its ! x = (pr', m)\<close> by (cases \<open>its ! x\<close>)
  from e i have \<open>pr' = pr\<close> \<open>m = length (snd pr)\<close> \<open>s = x\<close> \<open>b = nnum G Shn (fst pr)\<close> \<open>ntidx its (pr, m) = x\<close>
    by (auto split: if_splits)
  with x i show ?R by (metis nth_mem)
next
  assume r: ?R
  then have \<open>s < length its\<close> \<open>its ! s = (pr, length (snd pr))\<close> by (simp_all add: ntidx_less ntidx_nth)
  with r show ?L unfolding vcomps_def in_map_filter by force
qed

lemma vcells_set:
  \<open>(s', \<tau>) \<in> set (vcells its j cells t) \<longleftrightarrow>
     (\<exists>pr. (j, (pr, length (snd pr)), t, \<tau>) \<in> set cells \<and> s' = ntidx its (pr, length (snd pr)))\<close>
  unfolding vcells_def in_map_filter
  apply (rule iffI)
   apply (erule bexE)
  subgoal for x by (cases x) (auto split: if_splits, blast)
  by (force split: if_splits)


subsection \<open>A successor frame\<close>

text \<open>The anchors of a successor kernel depend on the anchor set crossed only
  through its elements, so the vector driver may cross a different
  representation of the same set.\<close>

lemma aset_lgoto_cong:
  \<open>irep_set RA' = irep_set RA \<Longrightarrow> aset (lgoto CL X RA') it = aset (lgoto CL X RA) it\<close>
  by (cases it) (simp add: aset_lgoto)

lemma vkrel_cong: \<open>vkrel G its X kav \<Longrightarrow> (\<And>it. aset X' it = aset X it) \<Longrightarrow> vkrel G its X' kav\<close>
  by (simp add: vkrel_def)

lemma aset_lgoto_slot: \<open>is_slot G it \<Longrightarrow> aset (lgoto CL X RA) it = {}\<close>
  by (cases it) (simp add: aset_lgoto is_slot_def)

lemma vgo_succ:
  assumes T: \<open>T = mk_stab G Shn gt sts redtab\<close> and V: \<open>V = mk_vtab G Shn T sts gt redtab\<close>
    and fr: \<open>vfr CL (vits G sts j) av\<close> and cov: \<open>lcore CL \<subseteq> set (vits G sts j)\<close>
    and RA: \<open>irep_set RA' = irep_set RA\<close>
    and j': \<open>j' < length sts\<close> and k': \<open>lcore (lgoto CL Y RA) \<subseteq> set (sts ! j')\<close>
    and w: \<open>\<And>p m R. (p, m, R) \<in> set (lgoto CL Y RA) \<Longrightarrow> irep_nonempty R \<Longrightarrow> p \<in> set (eprods G Shn)\<close>
  obtains av' where
    \<open>vgo V (j', vkmap (vits G sts j) Y (vits G sts j')) av RA' =
       (if live (lgoto CL Y RA) then Some (j', av') else None)\<close>
    and \<open>vfr (xclosure_auto G (lgoto CL Y RA)) (vits G sts j') av'\<close>
proof -
  let ?its = \<open>vits G sts j'\<close> and ?X = \<open>lgoto CL Y RA\<close>
  let ?kav = \<open>vkav (vkmap (vits G sts j) Y ?its) av RA'\<close>
  let ?av = \<open>vfill (map (vcontrib G Shn T ?its) ?its) ?kav\<close>
  have k: \<open>vkrel G ?its ?X ?kav\<close>
    by (rule vkrel_cong[OF vkav_krel[OF fr cov]]) (rule aset_lgoto_cong[OF RA, symmetric])
  have its: \<open>?its = creach G (sts ! j')\<close> using j' by (simp add: vits_def)
  have cov': \<open>it \<in> set ?its\<close> if \<open>aset ?X it \<noteq> {}\<close> for it
    using that k' creach_superset[of \<open>sts ! j'\<close> G] its by (auto simp: aset_ne_lcore)
  have ns: \<open>aset ?X it = {}\<close> if \<open>is_slot G it\<close> for it using that by (rule aset_lgoto_slot)
  have kl: \<open>length ?kav = length ?its\<close> by simp
  have kn: \<open>irep_set (?kav ! s) = (if is_slot G (?its ! s) then {} else aset ?X (?its ! s))\<close>
    if \<open>s < length ?its\<close> for s
    using k that unfolding vkrel_def by blast
  have lx: \<open>list_ex irep_nonempty ?kav \<longleftrightarrow> live ?X\<close>
  proof
    assume \<open>list_ex irep_nonempty ?kav\<close>
    then obtain s where s: \<open>s < length ?its\<close> and ne: \<open>irep_nonempty (?kav ! s)\<close>
      using kl by (metis in_set_conv_nth list_ex_iff)
    with kn[OF s] have \<open>aset ?X (?its ! s) \<noteq> {}\<close> by (auto split: if_splits)
    then show \<open>live ?X\<close> using live_aset by blast
  next
    assume \<open>live ?X\<close>
    then obtain it where ne: \<open>aset ?X it \<noteq> {}\<close> by (auto simp: live_aset)
    then have m: \<open>it \<in> set ?its\<close> by (rule cov')
    let ?s = \<open>ntidx ?its it\<close>
    have s: \<open>?s < length ?its\<close> and si: \<open>?its ! ?s = it\<close> using m by (simp_all add: ntidx_less ntidx_nth)
    have \<open>\<not> is_slot G it\<close> using ne ns by blast
    with kn[OF s] si ne have \<open>irep_set (?kav ! ?s) \<noteq> {}\<close> by simp
    with s kl show \<open>list_ex irep_nonempty ?kav\<close>
      by (metis nth_mem list_ex_iff irep_nonempty_correct)
  qed
  have \<open>vfr (xclosure_auto G ?X) ?its ?av\<close>
    unfolding vfr_def
  proof (intro conjI allI impI)
    show \<open>length ?av = length ?its\<close> by simp
    fix s assume s: \<open>s < length ?its\<close>
    show \<open>irep_set (?av ! s) = aset (xclosure_auto G ?X) (?its ! s)\<close>
      by (rule vfill_cl[OF T w k cov' ns]) (assumption | rule s)+
  qed
  moreover have \<open>vgo V (j', vkmap (vits G sts j) Y ?its) av RA' =
      (if live ?X then Some (j', ?av) else None)\<close>
    using lx by (simp add: vgo_def v_ct_mk[OF V j'])
  ultimately show ?thesis using that by blast
qed


subsection \<open>Crossing a symbol\<close>

lemma vits_cuniv:
  assumes tab: \<open>tables_ok G Shn sts gt L\<close> and j: \<open>j < length sts\<close>
  shows \<open>set (vits G sts j) \<subseteq> cuniv G Shn\<close>
proof -
  from tab j have \<open>set (sts ! j) \<subseteq> cuniv G Shn\<close> by (simp add: tables_ok_def)
  then show ?thesis using j by (simp add: vits_def creach_univ)
qed

lemma live_lgoto_gram_sym:
  assumes tab: \<open>tables_ok G Shn sts gt L\<close> and j: \<open>j < length sts\<close>
    and cov: \<open>lcore CL \<subseteq> set (vits G sts j)\<close> and lv: \<open>live (lgoto CL Y RA)\<close>
  shows \<open>Y \<in> set (gram_syms G)\<close>
proof -
  from lv obtain p m where ne: \<open>aset (lgoto CL Y RA) (p, m) \<noteq> {}\<close> by (auto simp: live_aset)
  then have m: \<open>0 < m\<close> \<open>m \<le> length (snd p)\<close> and Y: \<open>fst (snd p ! (m - 1)) = Y\<close>
    and \<open>aset CL (p, m - 1) \<noteq> {}\<close> by (auto simp: aset_lgoto split: if_splits)
  then have \<open>(p, m - 1) \<in> cuniv G Shn\<close>
    using cov vits_cuniv[OF tab j] by (auto simp: aset_ne_lcore)
  from cuniv_next_gram_syms[OF this] m Y show ?thesis by simp
qed

lemma tm_vtoks: \<open>Tm a \<in> set (gram_syms G) \<Longrightarrow> a \<in> set (vtoks G redtab)\<close>
  by (force simp: vtoks_def)

text \<open>The successor of frame \<open>d\<close> under \<open>Y\<close>: the vector driver finds an entry
  and a live kernel exactly when the dense successor is live, and then its
  frame holds the dense successor's closure.\<close>

lemma vgo_ventry:
  assumes T: \<open>T = mk_stab G Shn gt sts redtab\<close> and V: \<open>V = mk_vtab G Shn T sts gt redtab\<close>
    and tab: \<open>tables_ok G Shn sts gt L\<close>
    and ok: \<open>didx_ok G sts Xs istk\<close> and d: \<open>d < length Xs\<close> and lvd: \<open>live (Xs ! d)\<close>
    and fr: \<open>vfr (xclosure_auto G (Xs ! d)) (vits G sts (istk ! d)) av\<close>
    and RA: \<open>irep_set RA' = irep_set RA\<close>
  obtains av' where
    \<open>(case ventry G gt sts (istk ! d) Y of None \<Rightarrow> None | Some e \<Rightarrow> vgo V e av RA') =
       (if live (lgoto (xclosure_auto G (Xs ! d)) Y RA)
        then Some (dnext gt sts (istk ! d) Y, av') else None)\<close>
    and \<open>vfr (xclosure_auto G (lgoto (xclosure_auto G (Xs ! d)) Y RA))
           (vits G sts (dnext gt sts (istk ! d) Y)) av'\<close>
proof -
  let ?j = \<open>istk ! d\<close> and ?CL = \<open>xclosure_auto G (Xs ! d)\<close>
  let ?X = \<open>lgoto ?CL Y RA\<close> and ?j' = \<open>dnext gt sts (istk ! d) Y\<close>
  have j: \<open>?j < length sts\<close> and cov: \<open>lcore ?CL \<subseteq> set (vits G sts ?j)\<close>
    by (rule frame_cov[OF ok d lvd])+
  have okp: \<open>didx_ok G sts (?X # drop d Xs) (?j' # drop d istk)\<close>
    by (rule didx_ok_push[OF tab ok d])
  have w: \<open>p \<in> set (eprods G Shn)\<close> if \<open>(p, m, R) \<in> set ?X\<close> and \<open>irep_nonempty R\<close> for p m R
    using frame_eprods[OF tab okp, of 0 p m R] that by simp
  show ?thesis
  proof (cases \<open>live ?X\<close>)
    case True
    then have \<open>lcore ?X \<noteq> {}\<close> by (simp add: live_lcore)
    with didx_okD[OF okp, of 0] have j': \<open>?j' < length sts\<close> and k': \<open>lcore ?X \<subseteq> set (sts ! ?j')\<close>
      by simp_all
    obtain av' where g: \<open>vgo V (?j', vkmap (vits G sts ?j) Y (vits G sts ?j')) av RA' =
        (if live ?X then Some (?j', av') else None)\<close>
      and f: \<open>vfr (xclosure_auto G ?X) (vits G sts ?j') av'\<close>
      by (rule vgo_succ[OF T V fr cov RA j' k']) (rule w, assumption+)
    show ?thesis by (rule that[of av']) (use g f j' in \<open>simp_all add: ventry_def Let_def\<close>)
  next
    case False
    show ?thesis
    proof (cases \<open>?j' < length sts\<close>)
      case j': True
      have k': \<open>lcore ?X \<subseteq> set (sts ! ?j')\<close> using False by (simp add: live_lcore)
      obtain av' where g: \<open>vgo V (?j', vkmap (vits G sts ?j) Y (vits G sts ?j')) av RA' =
          (if live ?X then Some (?j', av') else None)\<close>
        and f: \<open>vfr (xclosure_auto G ?X) (vits G sts ?j') av'\<close>
        by (rule vgo_succ[OF T V fr cov RA j' k']) (rule w, assumption+)
      show ?thesis by (rule that[of av']) (use g f False j' in \<open>simp_all add: ventry_def Let_def\<close>)
    next
      case j': False
      show ?thesis by (rule that[of \<open>[]\<close>]) (use False j' in \<open>simp_all add: ventry_def Let_def vits_def vfr_def\<close>)
    qed
  qed
qed


subsection \<open>One action\<close>

lemma vrel_head:
  assumes tab: \<open>tables_ok G Shn sts gt L\<close> and ir: \<open>imreach G Shn gt sts ((Xs, w), istk)\<close>
    and r: \<open>vrel G sts Xs istk fs\<close>
  obtains j av fs\<^sub>0 where \<open>fs = (j, av) # fs\<^sub>0\<close> and \<open>hd istk = j\<close> and \<open>Xs \<noteq> []\<close> and \<open>live (hd Xs)\<close>
    and \<open>j < length sts\<close> and \<open>lcore (xclosure_auto G (hd Xs)) \<subseteq> set (vits G sts j)\<close>
    and \<open>vfr (xclosure_auto G (hd Xs)) (vits G sts j) av\<close> and \<open>didx_ok G sts Xs istk\<close>
proof -
  have ok: \<open>didx_ok G sts Xs istk\<close> using imreach_didx_ok[OF tab ir] by simp
  have ne: \<open>Xs \<noteq> []\<close> and lv: \<open>live (hd Xs)\<close> using imreach_dlive[OF ir] by (simp_all add: dlive_def)
  have lf: \<open>length fs = length Xs\<close> and li: \<open>length istk = length Xs\<close>
    using r didx_ok_len[OF ok] by (simp_all add: vrel_def)
  obtain j av fs\<^sub>0 where fs: \<open>fs = (j, av) # fs\<^sub>0\<close> using ne lf by (cases fs) auto
  have ni: \<open>istk \<noteq> []\<close> using ne li by auto
  have hX: \<open>hd Xs = Xs ! 0\<close> and hi: \<open>hd istk = istk ! 0\<close> using ne ni by (simp_all add: hd_conv_nth)
  have j: \<open>hd istk = j\<close> using vrel_nth(1)[OF r, of 0] by (simp add: fs hi)
  have lv0: \<open>live (Xs ! 0)\<close> using lv hX by simp
  have d0: \<open>0 < length Xs\<close> using ne by simp
  show ?thesis
  proof (rule that[OF fs j ne lv])
    show \<open>j < length sts\<close> and \<open>lcore (xclosure_auto G (hd Xs)) \<subseteq> set (vits G sts j)\<close>
      using frame_cov[OF ok d0 lv0] hX hi j by simp_all
    show \<open>vfr (xclosure_auto G (hd Xs)) (vits G sts j) av\<close>
      using vrel_nth(2)[OF r, of 0] hX hi j by (simp add: fs)
  qed (rule ok)
qed

lemma vmstep_shift:
  assumes T: \<open>T = mk_stab G Shn gt sts redtab\<close> and V: \<open>V = mk_vtab G Shn T sts gt redtab\<close>
    and tab: \<open>tables_ok G Shn sts gt L\<close> and ir: \<open>imreach G Shn gt sts ((Xs, w), istk)\<close>
    and r: \<open>vrel G sts Xs istk fs\<close>
  shows \<open>case vmstep V (fs, w) VShift of
      None \<Rightarrow> (\<forall>ic'. imstep G gt sts ((Xs, w), istk) DShift = Some ic' \<longrightarrow> \<not> dlive (fst ic'))
    | Some (fs', w') \<Rightarrow> \<exists>Xs' istk'. imstep G gt sts ((Xs, w), istk) DShift = Some ((Xs', w'), istk') \<and>
        dlive (Xs', w') \<and> vrel G sts Xs' istk' fs'\<close>
proof -
  obtain j av fs\<^sub>0 where fs: \<open>fs = (j, av) # fs\<^sub>0\<close> and hj: \<open>hd istk = j\<close> and ne: \<open>Xs \<noteq> []\<close>
    and lv: \<open>live (hd Xs)\<close> and j: \<open>j < length sts\<close>
    and cov: \<open>lcore (xclosure_auto G (hd Xs)) \<subseteq> set (vits G sts j)\<close>
    and fr: \<open>vfr (xclosure_auto G (hd Xs)) (vits G sts j) av\<close> and ok: \<open>didx_ok G sts Xs istk\<close>
    by (rule vrel_head[OF tab ir r])
  show ?thesis
  proof (cases w)
    case Nil
    then show ?thesis by (simp add: fs vmstep_def imstep_def mstep_def mstep_cached_def)
  next
    case (Cons ac w')
    obtain a c where w: \<open>w = (a, c) # w'\<close> using Cons by (cases ac) auto
    let ?CL = \<open>xclosure_auto G (hd Xs)\<close>
    let ?X = \<open>lgoto ?CL (Tm a) (FinRep [c])\<close> and ?j' = \<open>dnext gt sts j (Tm a)\<close>
    have im: \<open>imstep G gt sts ((Xs, w), istk) DShift = Some ((?X # Xs, w'), ?j' # istk)\<close>
      using ne hj by (simp add: imstep_def mstep_def mstep_cached_def w hd_map)
    have li: \<open>length istk = length Xs\<close> by (rule didx_ok_len[OF ok])
    have ni: \<open>istk \<noteq> []\<close> using ne li by auto
    have hX: \<open>Xs ! 0 = hd Xs\<close> and hi: \<open>istk ! 0 = hd istk\<close> using ne ni by (simp_all add: hd_conv_nth)
    have d0: \<open>0 < length Xs\<close> and lv0: \<open>live (Xs ! 0)\<close> using ne lv hX by simp_all
    have fr0: \<open>vfr (xclosure_auto G (Xs ! 0)) (vits G sts (istk ! 0)) av\<close> using fr hX hi hj by simp
    obtain av' where g: \<open>(case ventry G gt sts j (Tm a) of None \<Rightarrow> None
          | Some e \<Rightarrow> vgo V e av (FinRep [c])) = (if live ?X then Some (?j', av') else None)\<close>
      and f: \<open>vfr (xclosure_auto G ?X) (vits G sts ?j') av'\<close>
      by (rule vgo_ventry[OF T V tab ok d0 lv0 fr0 refl, where Y = \<open>Tm a\<close>, unfolded hX hi hj])
    have a: \<open>a \<in> set (vtoks G redtab)\<close> if \<open>live ?X\<close>
      using live_lgoto_gram_sym[OF tab j cov that] by (rule tm_vtoks)
    have vm: \<open>vmstep V (fs, w) VShift =
        map_option (\<lambda>f. (f # fs, w')) (if live ?X then Some (?j', av') else None)\<close>
    proof (cases \<open>a \<in> set (vtoks G redtab)\<close>)
      case True
      then show ?thesis using g
        by (cases \<open>ventry G gt sts j (Tm a)\<close>) (simp_all add: vmstep_def fs w v_sh_mk[OF V j])
    next
      case False
      then show ?thesis using a by (auto simp: vmstep_def fs w v_sh_mk[OF V j])
    qed
    show ?thesis
    proof (cases \<open>live ?X\<close>)
      case True
      have \<open>vrel G sts (?X # Xs) (?j' # istk) ((?j', av') # fs)\<close> by (rule vrel_push[OF r f])
      with True im show ?thesis by (simp add: vm dlive_def)
    next
      case False
      with im show ?thesis by (simp add: vm dlive_def)
    qed
  qed
qed

lemma vmstep_reduce:
  assumes T: \<open>T = mk_stab G Shn gt sts redtab\<close> and V: \<open>V = mk_vtab G Shn T sts gt redtab\<close>
    and tab: \<open>tables_ok G Shn sts gt L\<close> and ir: \<open>imreach G Shn gt sts ((Xs, w), istk)\<close>
    and r: \<open>vrel G sts Xs istk fs\<close>
    and c: \<open>(s, b, pr) \<in> set (vcomps G Shn (vits G sts (hd istk)))\<close>
    and ne: \<open>irep_nonempty (getR (snd (hd fs)) s)\<close>
  shows \<open>case vmstep V (fs, w) (VReduce s b pr) of
      None \<Rightarrow> (\<forall>ic'. imstep G gt sts ((Xs, w), istk) (DReduce pr) = Some ic' \<longrightarrow> \<not> dlive (fst ic'))
    | Some (fs', w') \<Rightarrow> \<exists>Xs' istk'. imstep G gt sts ((Xs, w), istk) (DReduce pr) = Some ((Xs', w'), istk') \<and>
        dlive (Xs', w') \<and> vrel G sts Xs' istk' fs'\<close>
proof -
  obtain j av fs\<^sub>0 where fs: \<open>fs = (j, av) # fs\<^sub>0\<close> and hj: \<open>hd istk = j\<close> and nX: \<open>Xs \<noteq> []\<close>
    and lv: \<open>live (hd Xs)\<close> and j: \<open>j < length sts\<close>
    and cov: \<open>lcore (xclosure_auto G (hd Xs)) \<subseteq> set (vits G sts j)\<close>
    and fr: \<open>vfr (xclosure_auto G (hd Xs)) (vits G sts j) av\<close> and ok: \<open>didx_ok G sts Xs istk\<close>
    by (rule vrel_head[OF tab ir r])
  let ?n = \<open>length (snd pr)\<close> and ?CL = \<open>xclosure_auto G (hd Xs)\<close>
  from c have m: \<open>(pr, ?n) \<in> set (vits G sts j)\<close> and s: \<open>s = ntidx (vits G sts j) (pr, ?n)\<close>
    and b: \<open>b = nnum G Shn (fst pr)\<close> by (simp_all add: vcomps_set hj)
  have RS: \<open>irep_set (getR av s) = irep_set (red_set ?CL pr)\<close>
    using vfr_getR[OF fr cov] by (simp add: s aset_red)
  have RSne: \<open>irep_nonempty (red_set ?CL pr)\<close> using ne RS by (simp add: fs)
  have fp: \<open>fst pr \<in> set (map fst (eprods G Shn))\<close> using closure_eprods[OF tab j m] by simp
  have bl: \<open>b < length (eprods G Shn)\<close> using fp ntidx_less[of \<open>map fst (eprods G Shn)\<close>]
    by (simp add: b nnum_def)
  have bf: \<open>fst (eprods G Shn ! b) = fst pr\<close>
    using ntidx_nth[OF fp] bl by (simp add: b nnum_def)
  have lf: \<open>length fs = length Xs\<close> using r by (simp add: vrel_def)
  show ?thesis
  proof (cases \<open>?n < length Xs\<close>)
    case False
    then show ?thesis using lf by (simp add: fs vmstep_def imstep_def mstep_def mstep_cached_def)
  next
    case n: True
    let ?j\<^sub>0 = \<open>istk ! ?n\<close> and ?CL\<^sub>0 = \<open>xclosure_auto G (Xs ! ?n)\<close>
    let ?X = \<open>lgoto ?CL\<^sub>0 (Nt (fst pr)) (red_set ?CL pr)\<close> and ?j' = \<open>dnext gt sts ?j\<^sub>0 (Nt (fst pr))\<close>
    have im: \<open>imstep G gt sts ((Xs, w), istk) (DReduce pr) = Some ((?X # drop ?n Xs, w), ?j' # drop ?n istk)\<close>
      using n nX RSne by (simp add: imstep_def mstep_def mstep_cached_def hd_map)
    have lv\<^sub>0: \<open>live (Xs ! ?n)\<close> using imreach_frames_live[OF ir] n by simp
    obtain av\<^sub>0 where fsn: \<open>fs ! ?n = (?j\<^sub>0, av\<^sub>0)\<close> and fr\<^sub>0: \<open>vfr ?CL\<^sub>0 (vits G sts ?j\<^sub>0) av\<^sub>0\<close>
      using vrel_nth[OF r] n lf by (metis prod.collapse)
    have j\<^sub>0: \<open>?j\<^sub>0 < length sts\<close> by (rule frame_cov(1)[OF ok n lv\<^sub>0])
    obtain av' where g: \<open>(case ventry G gt sts ?j\<^sub>0 (Nt (fst pr)) of None \<Rightarrow> None
          | Some e \<Rightarrow> vgo V e av\<^sub>0 (getR av s)) = (if live ?X then Some (?j', av') else None)\<close>
      and f: \<open>vfr (xclosure_auto G ?X) (vits G sts ?j') av'\<close>
      by (rule vgo_ventry[OF T V tab ok n lv\<^sub>0 fr\<^sub>0 RS])
    have vm: \<open>vmstep V (fs, w) (VReduce s b pr) =
        map_option (\<lambda>f. (f # drop ?n fs, w)) (if live ?X then Some (?j', av') else None)\<close>
      using g n lf fsn fs
      by (cases \<open>ventry G gt sts ?j\<^sub>0 (Nt (fst pr))\<close>) (simp_all add: vmstep_def v_go_mk[OF V j\<^sub>0 bl] bf)
    show ?thesis
    proof (cases \<open>live ?X\<close>)
      case True
      have \<open>vrel G sts (?X # drop ?n Xs) (?j' # drop ?n istk) ((?j', av') # drop ?n fs)\<close>
        by (rule vrel_push[OF vrel_drop[OF r] f])
      with True im show ?thesis by (simp add: vm dlive_def)
    next
      case False
      with im show ?thesis by (simp add: vm dlive_def)
    qed
  qed
qed


subsection \<open>The candidates\<close>

lemma vlic_dlic:
  assumes V: \<open>V = mk_vtab G Shn T sts gt redtab\<close> and j: \<open>j < length sts\<close> and jr: \<open>j < length redtab\<close>
    and m: \<open>(pr, length (snd pr)) \<in> set (vits G sts j)\<close>
    and s: \<open>s = ntidx (vits G sts j) (pr, length (snd pr))\<close>
    and RS: \<open>irep_set RS' = irep_set RS\<close>
  shows \<open>vlic V j w s RS' \<longleftrightarrow> dlic j (redtab ! j) w pr RS\<close>
proof -
  let ?its = \<open>vits G sts j\<close> and ?n = \<open>length (snd pr)\<close> and ?cells = \<open>redtab ! j\<close>
  have nt: \<open>s = ntidx ?its (pr', length (snd pr')) \<longleftrightarrow> pr' = pr\<close> for pr'
    using ntidx_eq_iff[OF m, of \<open>(pr', length (snd pr'))\<close>] s by auto
  have vc: \<open>(s, \<tau>) \<in> set (vcells ?its j ?cells t) \<longleftrightarrow> (j, (pr, ?n), t, \<tau>) \<in> set ?cells\<close> for t \<tau>
    unfolding vcells_set by (simp add: nt del: split_paired_Ex)
  show ?thesis
  proof (cases w)
    case Nil
    have \<open>vlic V j w s RS' \<longleftrightarrow> (\<exists>\<tau>. (s, \<tau>) \<in> set (vcells ?its j ?cells None))\<close>
      by (force simp: vlic_def Nil v_ce_mk[OF V j])
    also have \<open>\<dots> \<longleftrightarrow> dlic j ?cells w pr RS\<close>
      by (auto simp: vc dlic_def Nil list_ex_iff)
    finally show ?thesis .
  next
    case (Cons ac w')
    obtain a c where w: \<open>w = (a, c) # w'\<close> using Cons by (cases ac) auto
    have tok: \<open>a \<in> set (vtoks G redtab)\<close> if \<open>(j, (pr, ?n), Some a, \<tau>) \<in> set ?cells\<close> for \<tau>
    proof -
      have \<open>(j, (pr, ?n), Some a, \<tau>) \<in> set (concat redtab)\<close> using that jr by auto
      then show ?thesis by (force simp: vtoks_def in_map_filter)
    qed
    have \<open>vlic V j w s RS' \<longleftrightarrow> (\<exists>\<tau>. (j, (pr, ?n), Some a, \<tau>) \<in> set ?cells \<and> irep_ex_wsat \<tau> c RS')\<close>
      using tok by (auto simp: vlic_def w v_cl_mk[OF V j] list_ex_iff vc)
    also have \<open>\<dots> \<longleftrightarrow> dlic j ?cells w pr RS\<close>
      using RS by (auto simp: dlic_def w list_ex_iff)
    finally show ?thesis .
  qed
qed

lemma vcands_dcands:
  assumes V: \<open>V = mk_vtab G Shn T sts gt redtab\<close> and j: \<open>j < length sts\<close> and jr: \<open>j < length redtab\<close>
    and fr: \<open>vfr CL (vits G sts j) av\<close> and cov: \<open>lcore CL \<subseteq> set (vits G sts j)\<close> and ne: \<open>Xs \<noteq> []\<close>
  shows \<open>vdec ` set (vcands V j av w) = set (dcands G j (redtab ! j) CL (Xs, w))\<close>
proof (intro equalityI subsetI)
  fix a assume \<open>a \<in> vdec ` set (vcands V j av w)\<close>
  then obtain act where act: \<open>act \<in> set (vcands V j av w)\<close> and a: \<open>a = vdec act\<close> by blast
  show \<open>a \<in> set (dcands G j (redtab ! j) CL (Xs, w))\<close>
  proof (cases act)
    case VShift
    then have \<open>w \<noteq> []\<close> using act by (auto simp: vcands_def split: list.splits)
    with ne show ?thesis using dcands_shift[of \<open>(Xs, w)\<close>] by (simp add: a VShift)
  next
    case (VReduce s b pr)
    from act have c: \<open>(s, b, pr) \<in> set (vcomps G Shn (vits G sts j))\<close>
      and nz: \<open>irep_nonempty (getR av s)\<close> and lc: \<open>vlic V j w s (getR av s)\<close>
      by (auto simp: vcands_def VReduce v_cp_mk[OF V j] Let_def split: list.splits)
    from c have m: \<open>(pr, length (snd pr)) \<in> set (vits G sts j)\<close>
      and s: \<open>s = ntidx (vits G sts j) (pr, length (snd pr))\<close> by (simp_all add: vcomps_set)
    have RS: \<open>irep_set (getR av s) = irep_set (red_set CL pr)\<close>
      using vfr_getR[OF fr cov] by (simp add: s aset_red)
    have dl: \<open>dlic j (redtab ! j) w pr (red_set CL pr)\<close> using lc vlic_dlic[OF V j jr m s RS] by simp
    have rn: \<open>irep_nonempty (red_set CL pr)\<close> using nz RS by simp
    then obtain R where \<open>(pr, length (snd pr), R) \<in> set CL\<close> by (meson red_set_nonempty_iff)
    from dcands_reduceI[of \<open>(Xs, w)\<close>, OF _ this rn] ne dl show ?thesis by (simp add: a VReduce)
  qed
next
  fix a assume a: \<open>a \<in> set (dcands G j (redtab ! j) CL (Xs, w))\<close>
  show \<open>a \<in> vdec ` set (vcands V j av w)\<close>
  proof (cases a)
    case DShift
    then have \<open>w \<noteq> []\<close> using a ne by (cases w) (auto simp: dcands_def Let_def)
    then have \<open>VShift \<in> set (vcands V j av w)\<close> by (auto simp: vcands_def Let_def split: list.splits)
    then show ?thesis by (force simp: DShift)
  next
    case (DReduce pr)
    let ?n = \<open>length (snd pr)\<close>
    from dcands_reduceD[OF a[unfolded DReduce]] have rn: \<open>irep_nonempty (red_set CL pr)\<close>
      and dl: \<open>dlic j (redtab ! j) w pr (red_set CL pr)\<close> by simp_all
    have m: \<open>(pr, ?n) \<in> set (vits G sts j)\<close>
      using rn cov aset_red[of CL pr] by (auto simp: aset_ne_lcore)
    let ?s = \<open>ntidx (vits G sts j) (pr, ?n)\<close>
    have RS: \<open>irep_set (getR av ?s) = irep_set (red_set CL pr)\<close>
      using vfr_getR[OF fr cov] by (simp add: aset_red)
    have c: \<open>(?s, nnum G Shn (fst pr), pr) \<in> set (vcomps G Shn (vits G sts j))\<close>
      by (simp add: vcomps_set m)
    have lc: \<open>vlic V j w ?s (getR av ?s)\<close> using dl vlic_dlic[OF V j jr m refl RS] by simp
    have \<open>VReduce ?s (nnum G Shn (fst pr)) pr \<in> set (vcands V j av w)\<close>
      using c rn RS lc by (force simp: vcands_def v_cp_mk[OF V j] Let_def split: list.splits)
    then show ?thesis by (force simp: DReduce)
  qed
qed


subsection \<open>One step\<close>

lemma vpick_SomeD: \<open>vpick V fw acts = Some (act, r) \<Longrightarrow> act \<in> set acts \<and> vmstep V fw act = Some r\<close>
  by (induction acts) (auto split: option.splits)

lemma vpick_NoneD: \<open>vpick V fw acts = None \<Longrightarrow> act \<in> set acts \<Longrightarrow> vmstep V fw act = None\<close>
  by (induction acts) (auto split: option.splits)

text \<open>A vector state stands for a reachable dense one with the same input,
  tree stack and frames.\<close>

definition vst_rel :: \<open>('n, 't) is_cfg \<Rightarrow> 'n \<Rightarrow> ('n, 't) citem list list \<Rightarrow> (('n, 't) sym \<times> nat) list list \<Rightarrow>
    ('m, 'ch, 'n, 't) dst \<Rightarrow> ('m, 'ch, 'n, 't) vst \<Rightarrow> bool\<close> where
  \<open>vst_rel G Shn sts gt st vs \<longleftrightarrow> (case st of ((Xs, w), cstk, istk, v, tstk) \<Rightarrow>
     vs = (fst vs, w, v, tstk) \<and> vrel G sts Xs istk (fst vs) \<and>
     imreach G Shn gt sts ((Xs, w), istk) \<and> dfollow_ok G sts st)\<close>

lemma vstep_dstep:
  assumes T: \<open>T = mk_stab G Shn gt sts redtab\<close> and V: \<open>V = mk_vtab G Shn T sts gt redtab\<close>
    and stc: \<open>sts = pr0_states G Shn\<close> and gtc: \<open>gt = pgtab G sts\<close>
    and rt: \<open>redtab = red_buckets G Shn (length sts)\<close> and det: \<open>mdet G Shn\<close>
    and rel: \<open>vst_rel G Shn sts gt st vs\<close>
  shows \<open>case dstep G gt sts redtab st of None \<Rightarrow> vstep V vs = None
     | Some st' \<Rightarrow> \<exists>vs'. vstep V vs = Some vs' \<and> vst_rel G Shn sts gt st' vs'\<close>
proof -
  let ?L = \<open>la_fix G Shn\<close>
  have tab: \<open>tables_ok G Shn sts gt ?L\<close> using tables_ok_concrete[of G Shn] stc gtc by simp
  obtain Xs w cstk istk v tstk where st: \<open>st = ((Xs, w), cstk, istk, v, tstk)\<close>
    by (metis prod.exhaust)
  obtain fs where vs: \<open>vs = (fs, w, v, tstk)\<close> and r: \<open>vrel G sts Xs istk fs\<close>
    and ir: \<open>imreach G Shn gt sts ((Xs, w), istk)\<close> and inv: \<open>dfollow_ok G sts st\<close>
    using rel by (cases vs) (auto simp: vst_rel_def st)
  obtain j av fs\<^sub>0 where fs: \<open>fs = (j, av) # fs\<^sub>0\<close> and hj: \<open>hd istk = j\<close> and ne: \<open>Xs \<noteq> []\<close>
    and j: \<open>j < length sts\<close>
    and cov: \<open>lcore (xclosure_auto G (hd Xs)) \<subseteq> set (vits G sts j)\<close>
    and fr: \<open>vfr (xclosure_auto G (hd Xs)) (vits G sts j) av\<close> and ok: \<open>didx_ok G sts Xs istk\<close>
    by (rule vrel_head[OF tab ir r])
  have cs: \<open>cstk = map (xclosure_auto G) Xs\<close> using inv by (simp add: st dfollow_ok_def)
  have jr: \<open>j < length redtab\<close> using j by (simp add: rt)
  obtain istk\<^sub>0 where ist: \<open>istk = j # istk\<^sub>0\<close>
    using hj ok ne by (cases istk) (auto simp: didx_ok_def)
  obtain X\<^sub>0 Xs\<^sub>0 where Xs: \<open>Xs = X\<^sub>0 # Xs\<^sub>0\<close> using ne by (cases Xs) auto
  let ?CL = \<open>xclosure_auto G (hd Xs)\<close>
  let ?A = \<open>vcands V j av w\<close> and ?D = \<open>dcands G j (redtab ! j) ?CL (Xs, w)\<close>
  have AD: \<open>vdec ` set ?A = set ?D\<close> by (rule vcands_dcands[OF V j jr fr cov ne])
  have dsN: \<open>dstep G gt sts redtab st = None \<longleftrightarrow> dpick G cstk (Xs, w) ?D = None\<close>
    by (simp add: dstep_def st ist cs Xs jr split: option.splits dact.splits)
  have vsE: \<open>vstep V vs = (case vpick V (fs, w) ?A of None \<Rightarrow> None
      | Some (act, fs', w') \<Rightarrow> (case tstep (vdec act) (v, tstk) of (v', tstk') \<Rightarrow> Some (fs', w', v', tstk')))\<close>
    by (simp add: vstep_def vs fs)
  have mc: \<open>mstep_cached G cstk (Xs, w) a = mstep G (Xs, w) a\<close> for a by (simp add: mstep_def cs)
  have vm: \<open>case vmstep V (fs, w) act of
      None \<Rightarrow> (\<forall>ic'. imstep G gt sts ((Xs, w), istk) (vdec act) = Some ic' \<longrightarrow> \<not> dlive (fst ic'))
    | Some (fs', w') \<Rightarrow> \<exists>Xs' istk'. imstep G gt sts ((Xs, w), istk) (vdec act) = Some ((Xs', w'), istk') \<and>
        dlive (Xs', w') \<and> vrel G sts Xs' istk' fs'\<close> if act: \<open>act \<in> set ?A\<close> for act
  proof (cases act)
    case VShift
    show ?thesis using vmstep_shift[OF T V tab ir r] unfolding VShift vdec.simps .
  next
    case (VReduce s b pr)
    from act have c: \<open>(s, b, pr) \<in> set (vcomps G Shn (vits G sts (hd istk)))\<close>
      and nz: \<open>irep_nonempty (getR (snd (hd fs)) s)\<close>
      by (auto simp: vcands_def VReduce v_cp_mk[OF V j] Let_def hj fs split: list.splits)
    show ?thesis using vmstep_reduce[OF T V tab ir r c nz] unfolding VReduce vdec.simps .
  qed
  show ?thesis
  proof (cases \<open>vpick V (fs, w) ?A\<close>)
    case None
    have \<open>dpick G cstk (Xs, w) ?D = None\<close>
    proof (rule ccontr)
      assume \<open>dpick G cstk (Xs, w) ?D \<noteq> None\<close>
      then obtain a gc' where \<open>dpick G cstk (Xs, w) ?D = Some (a, gc')\<close> by auto
      from dpick_sound[OF this] have a: \<open>a \<in> set ?D\<close> and m: \<open>mstep G (Xs, w) a = Some gc'\<close>
        and lv: \<open>dlive gc'\<close> by (simp_all add: mc)
      from a AD obtain act where act: \<open>act \<in> set ?A\<close> and aa: \<open>a = vdec act\<close> by blast
      have \<open>vmstep V (fs, w) act = None\<close> by (rule vpick_NoneD[OF None act])
      with vm[OF act] have \<open>\<forall>ic'. imstep G gt sts ((Xs, w), istk) a = Some ic' \<longrightarrow> \<not> dlive (fst ic')\<close>
        by (simp add: aa)
      with m lv show False by (simp add: imstep_def)
    qed
    with dsN None show ?thesis by (simp add: vsE)
  next
    case (Some x)
    then obtain act fs' w' where vp: \<open>vpick V (fs, w) ?A = Some (act, fs', w')\<close>
      by (metis prod.exhaust)
    from vpick_SomeD[OF vp] have act: \<open>act \<in> set ?A\<close> and vms: \<open>vmstep V (fs, w) act = Some (fs', w')\<close>
      by simp_all
    from vm[OF act] vms obtain Xs' istk' where
      im: \<open>imstep G gt sts ((Xs, w), istk) (vdec act) = Some ((Xs', w'), istk')\<close>
      and lv: \<open>dlive (Xs', w')\<close> and r': \<open>vrel G sts Xs' istk' fs'\<close> by auto
    have lic: \<open>\<forall>pr. vdec act = DReduce pr \<longrightarrow> lic_at G ?L sts ((Xs, w), istk) pr\<close>
    proof (intro allI impI)
      fix pr assume \<open>vdec act = DReduce pr\<close>
      with act AD have \<open>DReduce pr \<in> set ?D\<close> by force
      from dcands_reduceD[OF this] have \<open>dlic j (redtab ! j) w pr (red_set ?CL pr)\<close> by simp
      then have \<open>dlic_L j ?L w pr (red_set ?CL pr)\<close>
        using dlic_buckets[of j \<open>length sts\<close> ?L] j by (simp add: rt red_buckets_def)
      then show \<open>lic_at G ?L sts ((Xs, w), istk) pr\<close> using j by (simp add: lic_at_def hj)
    qed
    from dstep_of_imstep_exact[OF tab stc gtc refl rt det ir inv[unfolded st] im lv lic, unfolded fst_conv]
    obtain v' tstk' where tp: \<open>(v', tstk') = tstep (vdec act) (v, tstk)\<close>
      and ds: \<open>dstep G gt sts redtab ((Xs, w), cstk, istk, v, tstk)
          = Some ((Xs', w'), map (xclosure_auto G) Xs', istk', v', tstk')\<close>
      and inv': \<open>dfollow_ok G sts ((Xs', w'), map (xclosure_auto G) Xs', istk', v', tstk')\<close>
      by blast
    have ir': \<open>imreach G Shn gt sts ((Xs', w'), istk')\<close> using imreach_step[OF ir im] lv by simp
    have \<open>vstep V vs = Some (fs', w', v', tstk')\<close> using vsE vp tp[symmetric] by simp
    moreover have \<open>vst_rel G Shn sts gt ((Xs', w'), map (xclosure_auto G) Xs', istk', v', tstk')
        (fs', w', v', tstk')\<close> using r' ir' inv' by (simp add: vst_rel_def)
    ultimately show ?thesis using ds by (simp add: st)
  qed
qed


subsection \<open>Acceptance\<close>

lemma vfinal_gfinal:
  assumes T: \<open>T = mk_stab G Shn gt sts redtab\<close> and V: \<open>V = mk_vtab G Shn T sts gt redtab\<close>
    and tab: \<open>tables_ok G Shn sts gt L\<close> and fn: \<open>fresh_name G Shn\<close>
    and ir: \<open>imreach G Shn gt sts ((Xs, w), istk)\<close> and r: \<open>vrel G sts Xs istk fs\<close>
  shows \<open>vfinal V (fs, w, v, tstk) \<longleftrightarrow> gfinal G Shn (Xs, w)\<close>
proof -
  obtain j av fs\<^sub>0 where fs: \<open>fs = (j, av) # fs\<^sub>0\<close> and ne: \<open>Xs \<noteq> []\<close> and j: \<open>j < length sts\<close>
    and cov: \<open>lcore (xclosure_auto G (hd Xs)) \<subseteq> set (vits G sts j)\<close>
    and fr: \<open>vfr (xclosure_auto G (hd Xs)) (vits G sts j) av\<close> and ok: \<open>didx_ok G sts Xs istk\<close>
    by (rule vrel_head[OF tab ir r])
  have w: \<open>p \<in> set (eprods G Shn)\<close> if \<open>(p, m, R) \<in> set (hd Xs)\<close> \<open>irep_nonempty R\<close> for p m R
    using frame_eprods[OF tab ok, of 0] that ne by (simp add: hd_conv_nth)
  have ns: \<open>\<not> is_slot G (start_prod G Shn, Suc 0)\<close> by (simp add: is_slot_def)
  have A: \<open>irep_set (getR av (iget (v_fin V) j 0)) = aset (hd Xs) (start_prod G Shn, Suc 0)\<close>
    using vfr_getR[OF fr cov, of \<open>(start_prod G Shn, Suc 0)\<close>] cl_aset[OF T w, where it = \<open>(start_prod G Shn, Suc 0)\<close>] ns
    by (simp add: v_fin_mk[OF V j])
  have E: \<open>list_ex (\<lambda>(pr, m, R). fst pr = Shn \<and> m = Suc 0 \<and> irep_mem (istart_ind G) R) (hd Xs) \<longleftrightarrow>
      istart_ind G \<in> aset (hd Xs) (start_prod G Shn, Suc 0)\<close>
  proof
    assume \<open>list_ex (\<lambda>(pr, m, R). fst pr = Shn \<and> m = Suc 0 \<and> irep_mem (istart_ind G) R) (hd Xs)\<close>
    then obtain pr R where m: \<open>(pr, Suc 0, R) \<in> set (hd Xs)\<close> and l: \<open>fst pr = Shn\<close>
      and i: \<open>istart_ind G \<in> irep_set R\<close>
      unfolding list_ex_iff by force
    have \<open>pr \<in> set (eprods G Shn)\<close> using w[OF m] i by auto
    then have \<open>pr = start_prod G Shn\<close> using l fn
      by (force simp: eprods_def start_prod_def fresh_name_def)
    then show \<open>istart_ind G \<in> aset (hd Xs) (start_prod G Shn, Suc 0)\<close> using m i by (auto simp: aset_def)
  next
    assume \<open>istart_ind G \<in> aset (hd Xs) (start_prod G Shn, Suc 0)\<close>
    then obtain R where \<open>(start_prod G Shn, Suc 0, R) \<in> set (hd Xs)\<close> and \<open>istart_ind G \<in> irep_set R\<close>
      by (auto simp: aset_def)
    then show \<open>list_ex (\<lambda>(pr, m, R). fst pr = Shn \<and> m = Suc 0 \<and> irep_mem (istart_ind G) R) (hd Xs)\<close>
      unfolding list_ex_iff by (force simp: start_prod_def)
  qed
  show ?thesis using A E ne by (simp add: vfinal_def gfinal_def fs v_ind0_mk[OF V])
qed

subsection \<open>The run\<close>

text \<open>The concrete tables, bundled so that the run inductions can carry them.\<close>

definition vctx :: \<open>('n, 't) is_cfg \<Rightarrow> 'n \<Rightarrow> (('n, 't) sym \<times> nat) list list \<Rightarrow> ('n, 't) citem list list \<Rightarrow>
    ('n, 't) lacell list list \<Rightarrow> ('n, 't) vtab \<Rightarrow> bool\<close> where
  \<open>vctx G Shn gt sts redtab V \<longleftrightarrow> V = mk_vtab G Shn (mk_stab G Shn gt sts redtab) sts gt redtab \<and>
     sts = pr0_states G Shn \<and> gt = pgtab G sts \<and> redtab = red_buckets G Shn (length sts) \<and>
     mdet G Shn \<and> fresh_name G Shn\<close>

lemma vctx_step:
  assumes c: \<open>vctx G Shn gt sts redtab V\<close> and r: \<open>vst_rel G Shn sts gt st vs\<close>
  shows \<open>case dstep G gt sts redtab st of None \<Rightarrow> vstep V vs = None
     | Some st' \<Rightarrow> \<exists>vs'. vstep V vs = Some vs' \<and> vst_rel G Shn sts gt st' vs'\<close>
  using c vstep_dstep[OF refl _ _ _ _ _ r] by (simp add: vctx_def)

lemma vctx_final:
  assumes c: \<open>vctx G Shn gt sts redtab V\<close> and r: \<open>vst_rel G Shn sts gt st vs\<close>
  obtains gc cstk istk v tstk fs where \<open>st = (gc, cstk, istk, v, tstk)\<close> \<open>vs = (fs, snd gc, v, tstk)\<close>
    \<open>vfinal V vs \<longleftrightarrow> gfinal G Shn gc\<close>
proof -
  obtain Xs w cstk istk v tstk where st: \<open>st = ((Xs, w), cstk, istk, v, tstk)\<close>
    by (metis prod.exhaust)
  obtain fs where vs: \<open>vs = (fs, w, v, tstk)\<close> and rr: \<open>vrel G sts Xs istk fs\<close>
    and ir: \<open>imreach G Shn gt sts ((Xs, w), istk)\<close>
    using r by (cases vs) (auto simp: vst_rel_def st)
  have tab: \<open>tables_ok G Shn sts gt (la_fix G Shn)\<close>
    using c tables_ok_concrete[of G Shn] by (simp add: vctx_def)
  have V: \<open>V = mk_vtab G Shn (mk_stab G Shn gt sts redtab) sts gt redtab\<close>
    and fn: \<open>fresh_name G Shn\<close> using c by (simp_all add: vctx_def)
  have \<open>vfinal V vs \<longleftrightarrow> gfinal G Shn (Xs, w)\<close>
    unfolding vs by (rule vfinal_gfinal[OF refl V tab fn ir rr])
  then show thesis using that[of \<open>(Xs, w)\<close> cstk istk v tstk fs] st vs by simp
qed

lemma drun_nh_imp_v:
  assumes run: \<open>drun_nh G Shn gt sts redtab st = Some t\<close>
  shows \<open>\<forall>V vs. vctx G Shn gt sts redtab V \<longrightarrow> vst_rel G Shn sts gt st vs \<longrightarrow> vrun V vs = Some t\<close>
proof (rule drun_nh.raw_induct[OF _ run], goal_cases)
  case (1 f G Shn gt sts redtab st t)
  show ?case
  proof (intro impI allI)
    fix V vs assume c: \<open>vctx G Shn gt sts redtab V\<close> and r: \<open>vst_rel G Shn sts gt st vs\<close>
    obtain gc cstk istk v tstk fs where st: \<open>st = (gc, cstk, istk, v, tstk)\<close>
      and vs: \<open>vs = (fs, snd gc, v, tstk)\<close> and gf: \<open>vfinal V vs \<longleftrightarrow> gfinal G Shn gc\<close>
      by (rule vctx_final[OF c r])
    show \<open>vrun V vs = Some t\<close>
    proof (cases \<open>gfinal G Shn gc\<close>)
      case True
      with "1"(2) gf show ?thesis unfolding st vs by (subst vrun.simps) simp
    next
      case False
      with "1"(2) obtain st\<^sub>1 where sp: \<open>dstep G gt sts redtab st = Some st\<^sub>1\<close>
        and rec: \<open>f G Shn gt sts redtab st\<^sub>1 = Some t\<close>
        unfolding st by (auto simp: bind_eq_Some_conv)
      from vctx_step[OF c r] sp obtain vs\<^sub>1 where
        sp': \<open>vstep V vs = Some vs\<^sub>1\<close> and r1: \<open>vst_rel G Shn sts gt st\<^sub>1 vs\<^sub>1\<close>
        by auto
      from "1"(1)[OF rec] c r1 have \<open>vrun V vs\<^sub>1 = Some t\<close> by blast
      with False gf sp' show ?thesis unfolding vs by (subst vrun.simps) (simp add: vs[symmetric])
    qed
  qed
qed

lemma vrun_imp_nh:
  assumes run: \<open>vrun V vs = Some t\<close>
  shows \<open>\<forall>G Shn gt sts redtab st. vctx G Shn gt sts redtab V \<longrightarrow> vst_rel G Shn sts gt st vs \<longrightarrow>
    drun_nh G Shn gt sts redtab st = Some t\<close>
proof (rule vrun.raw_induct[OF _ run], goal_cases)
  case (1 f V vs t)
  show ?case
  proof (intro impI allI)
    fix G Shn gt sts redtab st
    assume c: \<open>vctx G Shn gt sts redtab V\<close> and r: \<open>vst_rel G Shn sts gt st vs\<close>
    obtain gc cstk istk v tstk fs where st: \<open>st = (gc, cstk, istk, v, tstk)\<close>
      and vs: \<open>vs = (fs, snd gc, v, tstk)\<close> and gf: \<open>vfinal V vs \<longleftrightarrow> gfinal G Shn gc\<close>
      by (rule vctx_final[OF c r])
    show \<open>drun_nh G Shn gt sts redtab st = Some t\<close>
    proof (cases \<open>vfinal V vs\<close>)
      case True
      with "1"(2) gf show ?thesis unfolding st vs by (subst drun_nh.simps) simp
    next
      case False
      with "1"(2) obtain vs\<^sub>1 where sp': \<open>vstep V vs = Some vs\<^sub>1\<close>
        and rec: \<open>f V vs\<^sub>1 = Some t\<close>
        unfolding vs by (auto simp: bind_eq_Some_conv vs[symmetric])
      from vctx_step[OF c r] sp' obtain st\<^sub>1 where
        sp: \<open>dstep G gt sts redtab st = Some st\<^sub>1\<close> and r1: \<open>vst_rel G Shn sts gt st\<^sub>1 vs\<^sub>1\<close>
        by (cases \<open>dstep G gt sts redtab st\<close>) auto
      from "1"(1)[OF rec] c r1 have \<open>drun_nh G Shn gt sts redtab st\<^sub>1 = Some t\<close> by blast
      with False gf sp show ?thesis unfolding st by (subst drun_nh.simps) simp
    qed
  qed
qed

lemma drun_nh_eq_v:
  assumes c: \<open>vctx G Shn gt sts redtab V\<close> and r: \<open>vst_rel G Shn sts gt st vs\<close>
  shows \<open>drun_nh G Shn gt sts redtab st = vrun V vs\<close>
proof (cases \<open>drun_nh G Shn gt sts redtab st\<close>)
  case None
  show ?thesis
  proof (rule ccontr)
    assume \<open>drun_nh G Shn gt sts redtab st \<noteq> vrun V vs\<close>
    with None obtain t where \<open>vrun V vs = Some t\<close> by (cases \<open>vrun V vs\<close>) auto
    from vrun_imp_nh[OF this, rule_format, OF c r] None show False by simp
  qed
next
  case (Some t)
  from drun_nh_imp_v[OF this, rule_format, OF c r] Some show ?thesis by simp
qed


subsection \<open>The initial frame\<close>

lemma vinit_vrel:
  assumes T: \<open>T = mk_stab G Shn gt sts redtab\<close> and tab: \<open>tables_ok G Shn sts gt L\<close>
    and fn: \<open>fresh_name G Shn\<close>
  shows \<open>vrel G sts [xinit G Shn] [st_find sts (lr0_start G Shn)] [vinit_frame G Shn T sts]\<close>
proof -
  let ?i = \<open>st_find sts (lr0_start G Shn)\<close> and ?X = \<open>xinit G Shn\<close>
  let ?its = \<open>vits G sts ?i\<close>
  let ?kav = \<open>map (\<lambda>it. if it = (start_prod G Shn, 0) then FinRep [istart_ind G] else FinRep []) ?its\<close>
  obtain t where t: \<open>t \<in> set sts\<close> \<open>set t = set (lr0_start G Shn)\<close>
    using tab unfolding tables_ok_def by blast
  from st_find_found[OF t] have i: \<open>?i < length sts\<close> and si: \<open>set (sts ! ?i) = {(start_prod G Shn, 0)}\<close>
    by (simp_all add: lr0_start_def)
  have its: \<open>(start_prod G Shn, 0) \<in> set ?its\<close>
    using i si creach_superset[of \<open>sts ! ?i\<close> G] by (auto simp: vits_def)
  have \<open>start_prod G Shn \<notin> set (iprods G)\<close> using fn by (force simp: fresh_name_def start_prod_def)
  then have nsl: \<open>\<not> is_slot G (start_prod G Shn, 0)\<close> by (simp add: is_slot_def)
  have ax: \<open>aset ?X it = (if it = (start_prod G Shn, 0) then {istart_ind G} else {})\<close> for it
    by (cases it) (auto simp: xinit_def start_prod_def)
  have k: \<open>vkrel G ?its ?X ?kav\<close> using nsl by (auto simp: vkrel_def ax)
  have w: \<open>p \<in> set (eprods G Shn)\<close> if \<open>(p, m, R) \<in> set ?X\<close> \<open>irep_nonempty R\<close> for p m R
    using that by (simp add: xinit_def eprods_def)
  have cov: \<open>it \<in> set ?its\<close> if \<open>aset ?X it \<noteq> {}\<close> for it using that its by (simp add: ax split: if_splits)
  have ns: \<open>aset ?X it = {}\<close> if \<open>is_slot G it\<close> for it using that nsl by (auto simp: ax)
  have \<open>irep_set (vfill (map (vcontrib G Shn T ?its) ?its) ?kav ! s) = aset (xclosure_auto G ?X) (?its ! s)\<close>
    if \<open>s < length ?its\<close> for s
    using T w k cov ns that by (rule vfill_cl)
  then have \<open>vfr (xclosure_auto G ?X) ?its (vfill (map (vcontrib G Shn T ?its) ?its) ?kav)\<close>
    by (simp add: vfr_def)
  then show ?thesis by (simp add: vrel_def vinit_frame_def Let_def)
qed

subsection \<open>Correctness\<close>

text \<open>On a grammar without LALR conflicts the vector driver computes the parse of the
  dense driver, and hence of the specification.\<close>

theorem vrun_dparse:
  assumes fn: \<open>fresh_name G Shn\<close> and det: \<open>mdet G Shn\<close>
    and sts: \<open>sts = pr0_states G Shn\<close> and gt: \<open>gt = pgtab G sts\<close>
    and rt: \<open>redtab = red_buckets G Shn (length sts)\<close>
    and V: \<open>V = mk_vtab G Shn (mk_stab G Shn gt sts redtab) sts gt redtab\<close>
  shows \<open>vrun V ([v_av0 V], tcols w, w, []) = dparse G Shn w\<close>
proof -
  have c: \<open>vctx G Shn gt sts redtab V\<close> using assms by (simp add: vctx_def)
  have tab: \<open>tables_ok G Shn sts gt (la_fix G Shn)\<close> using tables_ok_concrete[of G Shn] sts gt by simp
  have \<open>vst_rel G Shn sts gt (dinit G Shn sts w) ([v_av0 V], tcols w, w, [])\<close>
    using vinit_vrel[OF refl tab fn] imreach_init[of G Shn gt sts \<open>tcols w\<close>]
      dfollow_ok_dinit[of G Shn w]
    by (simp add: vst_rel_def dinit_def v_av0_mk[OF V] sts)
  then have \<open>drun_nh G Shn gt sts redtab (dinit G Shn sts w) = vrun V ([v_av0 V], tcols w, w, [])\<close>
    by (rule drun_nh_eq_v[OF c])
  moreover have \<open>dparse G Shn w = drun_nh G Shn gt sts redtab (dinit G Shn sts w)\<close>
    using dparse_via_tables_nh[OF sts[symmetric] gt[symmetric] rt[symmetric] refl refl refl]
    by (simp add: dinit_def)
  ultimately show ?thesis by simp
qed


text \<open>The parser over the vector driver, for the code generator: the tables as
  constants; the generator obtains \<^const>\<open>mdet\<close> from the evaluated
  \<open>rlalr_conflicts G Shn = []\<close> (\<open>rlalr_sufficient\<close>).\<close>

lemma dparse_via_tables_v:
  assumes st: \<open>pr0_states G Shn = sts\<close>
    and gt: \<open>pgtab G sts = gtab\<close>
    and rt: \<open>red_buckets G Shn (length sts) = redtab\<close>
    and fr: \<open>fresh_name G Shn\<close>
    and det: \<open>mdet G Shn\<close>
    and tb: \<open>mk_stab G Shn gtab sts redtab = stb\<close>
    and vt: \<open>mk_vtab G Shn stb sts gtab redtab = vtb\<close>
  shows \<open>dparse G Shn w = vrun vtb ([v_av0 vtb], tcols w, w, [])\<close>
  using vrun_dparse[OF fr det st[symmetric] gt[symmetric] rt[symmetric], of vtb w]
    tb vt by simp


section \<open>Runtime determinism\<close>

text \<open>The vector driver orders its reductions by table position, the dense one by
  closure order.  Without \<^const>\<open>mdet\<close> the two agree on a step when a shift is
  live (both try it first) or when exactly one action is live; the vector driver
  checks this at run time and reports a conflict otherwise.\<close>

subsection \<open>The dense step from its pick\<close>

text \<open>\<^text>\<open>dstep_of_imstep_exact\<close> with the pick as a premise instead of
  \<^const>\<open>mdet\<close>.\<close>

lemma dstep_of_dpick:
  assumes tab: \<open>tables_ok G Shn sts gt L\<close>
    and stc: \<open>sts = pr0_states G Shn\<close>
    and gtc: \<open>gt = pgtab G sts\<close>
    and Lc: \<open>L = la_fix G Shn\<close>
    and rt: \<open>redtab = red_buckets G Shn (length sts)\<close>
    and ireach: \<open>imreach G Shn gt sts ((Xs, w), istk)\<close>
    and inv: \<open>dfollow_ok G sts ((Xs, w), cstk, istk, v, tstk)\<close>
    and step: \<open>imstep G gt sts ((Xs, w), istk) act = Some (gc', istk')\<close>
    and live: \<open>dlive gc'\<close>
    and lic: \<open>\<forall>pr. act = DReduce pr \<longrightarrow> lic_at G L sts ((Xs, w), istk) pr\<close>
    and pick_of: \<open>act \<in> set (dcands G (hd istk) (redtab ! hd istk) (xclosure_auto G (hd Xs)) (Xs, w)) \<Longrightarrow>
      dpick G cstk (Xs, w) (dcands G (hd istk) (redtab ! hd istk) (xclosure_auto G (hd Xs)) (Xs, w))
        = Some (act, gc')\<close>
  shows \<open>act \<in> set (dcands G (hd istk) (redtab ! hd istk) (xclosure_auto G (hd Xs)) (Xs, w)) \<and>
         (\<exists>v' tstk'. (v', tstk') = tstep act (v, tstk) \<and>
            dstep G gt sts redtab ((Xs, w), cstk, istk, v, tstk)
              = Some (gc', map (xclosure_auto G) (fst gc'), istk', v', tstk') \<and>
            dfollow_ok G sts (gc', map (xclosure_auto G) (fst gc'), istk', v', tstk'))\<close>
proof -
  from inv have cstk_eq: \<open>cstk = map (xclosure_auto G) Xs\<close>
    and ok: \<open>didx_ok G sts Xs istk\<close> and vw: \<open>w = tcols v\<close>
    and lens: \<open>Suc (length tstk) = length Xs\<close>
    unfolding dfollow_ok_def by auto
  have len_i: \<open>length istk = length Xs\<close> by (rule didx_ok_len[OF ok])
  have ms: \<open>mstep G (Xs, w) act = Some gc'\<close>
    using imstep_mstep[of G gt sts \<open>((Xs, w), istk)\<close> act \<open>(gc', istk')\<close>] step by simp
  have msc: \<open>mstep_cached G cstk (Xs, w) act = Some gc'\<close>
    using ms unfolding mstep_def cstk_eq by simp
  have Xs_ne: \<open>Xs \<noteq> []\<close>
    using msc unfolding mstep_cached_def
    by (auto split: dact.splits list.splits if_splits)
  then have istk_ne: \<open>istk \<noteq> []\<close> using len_i by auto
  have hd_cstk: \<open>hd cstk = xclosure_auto G (hd Xs)\<close>
    using cstk_eq Xs_ne by (simp add: hd_map)
  have i_lt: \<open>hd istk < length sts\<close>
    using didx_ok_hd_lt[OF ok] imreach_dlive[OF ireach] by simp
  have gc'_ne: \<open>fst gc' \<noteq> []\<close> and gc'_live: \<open>live (hd (fst gc'))\<close>
    using live unfolding dlive_def by (cases gc'; simp)+
  let ?i = \<open>hd istk\<close> and ?CL = \<open>xclosure_auto G (hd Xs)\<close>
  let ?cells = \<open>cell_buckets L (length sts) ! ?i\<close>
  have rt': \<open>redtab = cell_buckets L (length sts)\<close>
    unfolding rt Lc stc by (rule cell_buckets_red_buckets[symmetric])
  have req: \<open>?cells = red_buckets G Shn (length (pr0_states G Shn)) ! ?i\<close>
    unfolding Lc stc by (simp add: cell_buckets_red_buckets)
  have ireach': \<open>imreach G Shn (pgtab G (pr0_states G Shn)) (pr0_states G Shn) ((Xs, w), istk)\<close>
    using ireach unfolding gtc stc .
  have cells_eq: \<open>(if ?i < length redtab then redtab ! ?i else []) = ?cells\<close>
    using i_lt rt' by simp
  have CL_eq: \<open>(case cstk of [] \<Rightarrow> [] | c # _ \<Rightarrow> c) = ?CL\<close>
    using cstk_eq Xs_ne hd_cstk by (cases cstk) auto
  have i_eq: \<open>(case istk of [] \<Rightarrow> length sts | j # _ \<Rightarrow> j) = ?i\<close>
    using istk_ne by (cases istk) auto
  have cstk_eq': \<open>cstk = map (xclosure_auto G) (fst (Xs, w))\<close> using cstk_eq by simp
  have cells_rt: \<open>redtab ! ?i = ?cells\<close> using rt' by simp
  show ?thesis
  proof (cases act)
    case DShift
    have sh: \<open>mstep_cached G cstk (Xs, w) DShift = Some gc'\<close> using msc DShift by simp
    obtain a c w' where w_eq: \<open>w = (a, c) # w'\<close>
      and gc'_eq: \<open>gc' = (lgoto (hd cstk) (Tm a) (FinRep [c]) # Xs, w')\<close>
      using sh unfolding mstep_cached_def by (auto split: list.splits if_splits)
    have v_ne: \<open>v \<noteq> []\<close> using vw w_eq by auto
    then obtain t\<^sub>0 v\<^sub>0 where v_eq: \<open>v = t\<^sub>0 # v\<^sub>0\<close> by (cases v) auto
    have a_eq: \<open>a = tok t\<^sub>0\<close> and w'_eq: \<open>w' = tcols v\<^sub>0\<close>
      using vw w_eq v_eq unfolding tcols_def by auto
    have offered: \<open>DShift \<in> set (dcands G ?i ?cells ?CL (Xs, w))\<close>
      by (rule dcands_shift) (use Xs_ne w_eq in auto)
    have pick: \<open>dpick G cstk (Xs, w) (dcands G ?i ?cells ?CL (Xs, w)) = Some (DShift, gc')\<close>
      using pick_of offered DShift cells_rt by simp
    have dstep_eq: \<open>dstep G gt sts redtab ((Xs, w), cstk, istk, v, tstk) =
        Some (gc', xclosure_auto G (hd (fst gc')) # cstk,
              dnext gt sts ?i (Tm (tok (hd v))) # istk, tl v, Leaf (hd v) # tstk)\<close>
      unfolding dstep_def rt' by (simp add: Let_def i_eq CL_eq i_lt pick)
    have istk'_eq: \<open>istk' = dnext gt sts ?i (Tm a) # istk\<close>
      using step ms unfolding imstep_def DShift by (simp add: w_eq)
    have cstk'_eq: \<open>xclosure_auto G (hd (fst gc')) # cstk = map (xclosure_auto G) (fst gc')\<close>
      using gc'_eq cstk_eq by simp
    have i\<^sub>0: \<open>istk ! 0 = hd istk\<close> using istk_ne by (simp add: hd_conv_nth)
    have x\<^sub>0: \<open>Xs ! 0 = hd Xs\<close> using Xs_ne by (simp add: hd_conv_nth)
    have push: \<open>didx_ok G sts (fst gc') istk'\<close>
      using didx_ok_push[OF tab ok, of 0 \<open>Tm a\<close> \<open>FinRep [c]\<close>] Xs_ne
        gc'_live[unfolded gc'_eq] gc'_eq istk'_eq
      by (simp add: i\<^sub>0 x\<^sub>0 hd_cstk live_nonempty)
    show ?thesis
    proof (intro conjI exI)
      show \<open>act \<in> set (dcands G ?i (redtab ! ?i) ?CL (Xs, w))\<close>
        using offered unfolding DShift cells_rt .
      show \<open>(tl v, Leaf (hd v) # tstk) = tstep act (v, tstk)\<close>
        unfolding DShift by simp
      show \<open>dstep G gt sts redtab ((Xs, w), cstk, istk, v, tstk) =
          Some (gc', map (xclosure_auto G) (fst gc'), istk', tl v, Leaf (hd v) # tstk)\<close>
        unfolding dstep_eq cstk'_eq istk'_eq using a_eq v_eq by simp
      show \<open>dfollow_ok G sts (gc', map (xclosure_auto G) (fst gc'), istk',
              tl v, Leaf (hd v) # tstk)\<close>
        unfolding dfollow_ok_def using push gc'_eq w'_eq v_eq lens by simp
    qed
  next
    case (DReduce pr)
    let ?k = \<open>length (snd pr)\<close>
    have red: \<open>mstep_cached G cstk (Xs, w) (DReduce pr) = Some gc'\<close> using msc DReduce by simp
    have k_lt: \<open>?k < length Xs\<close> and RS_ne: \<open>irep_nonempty (red_set (hd cstk) pr)\<close>
      and gc'_eq: \<open>gc' = (lgoto (cstk ! ?k) (Nt (fst pr)) (red_set (hd cstk) pr) # drop ?k Xs, w)\<close>
      using red unfolding mstep_cached_def by (auto simp: Let_def split: if_splits)
    have RS_ne': \<open>irep_nonempty (red_set ?CL pr)\<close> using RS_ne hd_cstk by simp
    obtain R where compR: \<open>(pr, ?k, R) \<in> set ?CL\<close>
      using RS_ne' unfolding red_set_nonempty_iff by auto
    have dlicL: \<open>dlic_L ?i L w pr (red_set ?CL pr)\<close>
      using lic DReduce unfolding lic_at_def by simp
    have dlic': \<open>dlic ?i ?cells w pr (red_set ?CL pr)\<close>
      by (rule dlic_buckets[OF i_lt, THEN iffD2, OF dlicL])
    have offered: \<open>DReduce pr \<in> set (dcands G ?i ?cells ?CL (Xs, w))\<close>
      by (rule dcands_reduceI[OF _ compR RS_ne']) (use Xs_ne dlic' in auto)
    have pick: \<open>dpick G cstk (Xs, w) (dcands G ?i ?cells ?CL (Xs, w)) = Some (DReduce pr, gc')\<close>
      using pick_of offered DReduce cells_rt by simp
    have dstep_eq: \<open>dstep G gt sts redtab ((Xs, w), cstk, istk, v, tstk) =
        Some (gc', xclosure_auto G (hd (fst gc')) # drop ?k cstk,
              dnext gt sts (istk ! ?k) (Nt (fst pr)) # drop ?k istk, v,
              Node (fst pr) (rev (take ?k tstk)) # drop ?k tstk)\<close>
      unfolding dstep_def rt' by (simp add: Let_def i_eq CL_eq i_lt pick)
    have istk'_eq: \<open>istk' = dnext gt sts (istk ! ?k) (Nt (fst pr)) # drop ?k istk\<close>
      using step ms unfolding imstep_def DReduce by simp
    have cstk'_eq: \<open>xclosure_auto G (hd (fst gc')) # drop ?k cstk =
        map (xclosure_auto G) (fst gc')\<close>
      using gc'_eq cstk_eq by (simp add: drop_map)
    have cstk_k: \<open>cstk ! ?k = xclosure_auto G (Xs ! ?k)\<close> using cstk_eq k_lt by simp
    have push: \<open>didx_ok G sts (fst gc') istk'\<close>
      using didx_ok_push[OF tab ok k_lt, of \<open>Nt (fst pr)\<close> \<open>red_set (hd cstk) pr\<close>]
        gc'_live[unfolded gc'_eq] gc'_eq istk'_eq cstk_k
      by (simp add: live_nonempty)
    show ?thesis
    proof (intro conjI exI)
      show \<open>act \<in> set (dcands G ?i (redtab ! ?i) ?CL (Xs, w))\<close>
        using offered unfolding DReduce cells_rt .
      show \<open>(v, Node (fst pr) (rev (take ?k tstk)) # drop ?k tstk) = tstep act (v, tstk)\<close>
        unfolding DReduce by simp
      show \<open>dstep G gt sts redtab ((Xs, w), cstk, istk, v, tstk) =
          Some (gc', map (xclosure_auto G) (fst gc'), istk', v,
                Node (fst pr) (rev (take ?k tstk)) # drop ?k tstk)\<close>
        unfolding dstep_eq cstk'_eq istk'_eq by simp
      show \<open>dfollow_ok G sts (gc', map (xclosure_auto G) (fst gc'), istk', v,
              Node (fst pr) (rev (take ?k tstk)) # drop ?k tstk)\<close>
        unfolding dfollow_ok_def using push gc'_eq vw lens k_lt by simp
    qed
  qed
qed


subsection \<open>The checked driver\<close>

text \<open>The first live action, provided it is a shift or no later action is live;
  \<open>None\<close> on a conflict between live reductions, \<open>Some None\<close> when nothing is live.\<close>

fun vchoose :: \<open>('n, 't) vtab \<Rightarrow> vframes \<times> ('t \<times> nat) list \<Rightarrow> ('n, 't) vact list \<Rightarrow>
    (('n, 't) vact \<times> vframes \<times> ('t \<times> nat) list) option option\<close> where
  \<open>vchoose V fw [] = Some None\<close>
| \<open>vchoose V fw (a # acts) = (case vmstep V fw a of
     None \<Rightarrow> vchoose V fw acts
   | Some r \<Rightarrow> if a = VShift \<or> \<not> list_ex (\<lambda>b. vmstep V fw b \<noteq> None) acts then Some (Some (a, r))
              else None)\<close>

definition vstep_u :: \<open>('n, 't) vtab \<Rightarrow> ('m, 'ch, 'n, 't) vst \<Rightarrow> ('m, 'ch, 'n, 't) vst option option\<close> where
  \<open>vstep_u V st = (case st of (fs, w, v, tstk) \<Rightarrow> (case fs of [] \<Rightarrow> Some None | (j, av) # _ \<Rightarrow>
     (case vchoose V (fs, w) (vcands V j av w) of None \<Rightarrow> None | Some None \<Rightarrow> Some None
      | Some (Some (act, fs', w')) \<Rightarrow>
          (case tstep (vdec act) (v, tstk) of (v', tstk') \<Rightarrow> Some (Some (fs', w', v', tstk'))))))\<close>

text \<open>\<open>None\<close>: a conflict was met (or the run diverges); \<open>Some r\<close>: the dense result.\<close>

partial_function (option) vrun_u ::
  \<open>('n, 't) vtab \<Rightarrow> ('m, 'ch, 'n, 't) vst \<Rightarrow> ('m, 'ch, 'n, 't) ast option option\<close>
  where
  \<open>vrun_u V st = (case st of (fs, w, v, tstk) \<Rightarrow>
     if vfinal V st then Some (case tstk of t # _ \<Rightarrow> Some t | [] \<Rightarrow> None)
     else (case vstep_u V st of None \<Rightarrow> None | Some None \<Rightarrow> Some None
       | Some (Some st') \<Rightarrow> vrun_u V st'))\<close>

lemmas vrun_u_simps [code] = vrun_u.simps

lemma vchoose_SomeD:
  \<open>vchoose V fw acts = Some (Some (a, r)) \<Longrightarrow> a \<in> set acts \<and> vmstep V fw a = Some r \<and>
     (a = VShift \<or> (\<forall>b \<in> set acts. b \<noteq> a \<longrightarrow> vmstep V fw b = None))\<close>
  by (induction V fw acts rule: vchoose.induct)
     (auto split: option.splits if_splits simp: list_ex_iff
       simp del: split_paired_All split_paired_Ex)

lemma vchoose_NoneD: \<open>vchoose V fw acts = Some None \<Longrightarrow> b \<in> set acts \<Longrightarrow> vmstep V fw b = None\<close>
  by (induction V fw acts rule: vchoose.induct) (auto split: option.splits if_splits)

lemma dpick_unique:
  assumes \<open>a \<in> set D\<close> and \<open>mstep_cached G cstk gc a = Some g\<close> and \<open>dlive g\<close>
    and \<open>\<And>d g'. d \<in> set D \<Longrightarrow> d \<noteq> a \<Longrightarrow> mstep_cached G cstk gc d = Some g' \<Longrightarrow> \<not> dlive g'\<close>
  shows \<open>dpick G cstk gc D = Some (a, g)\<close>
  using assms
proof (induction D)
  case (Cons d D)
  then show ?case by (cases \<open>d = a\<close>) (auto split: option.splits simp del: split_paired_All)
qed simp

lemma dpick_none:
  assumes \<open>\<And>d g'. d \<in> set D \<Longrightarrow> mstep_cached G cstk gc d = Some g' \<Longrightarrow> \<not> dlive g'\<close>
  shows \<open>dpick G cstk gc D = None\<close>
  using assms by (induction D) (auto split: option.splits)

lemma vstep_u_dstep:
  assumes T: \<open>T = mk_stab G Shn gt sts redtab\<close> and V: \<open>V = mk_vtab G Shn T sts gt redtab\<close>
    and stc: \<open>sts = pr0_states G Shn\<close> and gtc: \<open>gt = pgtab G sts\<close>
    and rt: \<open>redtab = red_buckets G Shn (length sts)\<close>
    and rel: \<open>vst_rel G Shn sts gt st vs\<close>
  shows \<open>vstep_u V vs = Some None \<Longrightarrow> dstep G gt sts redtab st = None\<close>
    and \<open>vstep_u V vs = Some (Some vs') \<Longrightarrow>
      \<exists>st'. dstep G gt sts redtab st = Some st' \<and> vst_rel G Shn sts gt st' vs'\<close>
proof -
  let ?L = \<open>la_fix G Shn\<close>
  have tab: \<open>tables_ok G Shn sts gt ?L\<close> using tables_ok_concrete[of G Shn] stc gtc by simp
  obtain Xs w cstk istk v tstk where st: \<open>st = ((Xs, w), cstk, istk, v, tstk)\<close>
    by (metis prod.exhaust)
  obtain fs where vs: \<open>vs = (fs, w, v, tstk)\<close> and r: \<open>vrel G sts Xs istk fs\<close>
    and ir: \<open>imreach G Shn gt sts ((Xs, w), istk)\<close> and inv: \<open>dfollow_ok G sts st\<close>
    using rel by (cases vs) (auto simp: vst_rel_def st)
  obtain j av fs\<^sub>0 where fs: \<open>fs = (j, av) # fs\<^sub>0\<close> and hj: \<open>hd istk = j\<close> and ne: \<open>Xs \<noteq> []\<close>
    and j: \<open>j < length sts\<close>
    and cov: \<open>lcore (xclosure_auto G (hd Xs)) \<subseteq> set (vits G sts j)\<close>
    and fr: \<open>vfr (xclosure_auto G (hd Xs)) (vits G sts j) av\<close> and ok: \<open>didx_ok G sts Xs istk\<close>
    by (rule vrel_head[OF tab ir r])
  have cs: \<open>cstk = map (xclosure_auto G) Xs\<close> using inv by (simp add: st dfollow_ok_def)
  have jr: \<open>j < length redtab\<close> using j by (simp add: rt)
  obtain istk\<^sub>0 where ist: \<open>istk = j # istk\<^sub>0\<close>
    using hj ok ne by (cases istk) (auto simp: didx_ok_def)
  obtain X\<^sub>0 Xs\<^sub>0 where Xs: \<open>Xs = X\<^sub>0 # Xs\<^sub>0\<close> using ne by (cases Xs) auto
  let ?CL = \<open>xclosure_auto G (hd Xs)\<close>
  let ?A = \<open>vcands V j av w\<close> and ?D = \<open>dcands G j (redtab ! j) ?CL (Xs, w)\<close>
  have AD: \<open>vdec ` set ?A = set ?D\<close> by (rule vcands_dcands[OF V j jr fr cov ne])
  have dsE: \<open>dstep G gt sts redtab st = None \<longleftrightarrow> dpick G cstk (Xs, w) ?D = None\<close>
    by (simp add: dstep_def st ist cs Xs jr split: option.splits dact.splits)
  have mc: \<open>mstep_cached G cstk (Xs, w) a = mstep G (Xs, w) a\<close> for a by (simp add: mstep_def cs)
  have vm: \<open>case vmstep V (fs, w) act of
      None \<Rightarrow> (\<forall>ic'. imstep G gt sts ((Xs, w), istk) (vdec act) = Some ic' \<longrightarrow> \<not> dlive (fst ic'))
    | Some (fs', w') \<Rightarrow> \<exists>Xs' istk'. imstep G gt sts ((Xs, w), istk) (vdec act) = Some ((Xs', w'), istk') \<and>
        dlive (Xs', w') \<and> vrel G sts Xs' istk' fs'\<close> if act: \<open>act \<in> set ?A\<close> for act
  proof (cases act)
    case VShift
    show ?thesis using vmstep_shift[OF T V tab ir r] unfolding VShift vdec.simps .
  next
    case (VReduce s b pr)
    from act have c: \<open>(s, b, pr) \<in> set (vcomps G Shn (vits G sts (hd istk)))\<close>
      and nz: \<open>irep_nonempty (getR (snd (hd fs)) s)\<close>
      by (auto simp: vcands_def VReduce v_cp_mk[OF V j] Let_def hj fs split: list.splits)
    show ?thesis using vmstep_reduce[OF T V tab ir r c nz] unfolding VReduce vdec.simps .
  qed
  text \<open>A vector action without a step: its dense counterpart has no live step.\<close>
  have dead: \<open>\<not> dlive g'\<close> if \<open>act \<in> set ?A\<close> \<open>vmstep V (fs, w) act = None\<close>
    \<open>mstep_cached G cstk (Xs, w) (vdec act) = Some g'\<close> for act g'
  proof -
    from vm[OF that(1)] that(2)
    have \<open>\<forall>ic'. imstep G gt sts ((Xs, w), istk) (vdec act) = Some ic' \<longrightarrow> \<not> dlive (fst ic')\<close> by simp
    with that(3) show ?thesis by (simp add: imstep_def mc)
  qed
  show \<open>dstep G gt sts redtab st = None\<close> if vn: \<open>vstep_u V vs = Some None\<close>
  proof -
    have ch: \<open>vchoose V (fs, w) ?A = Some None\<close>
      using vn by (simp add: vstep_u_def vs fs split: option.splits prod.splits)
    have \<open>dpick G cstk (Xs, w) ?D = None\<close>
    proof (rule dpick_none)
      fix d g' assume d: \<open>d \<in> set ?D\<close> and m: \<open>mstep_cached G cstk (Xs, w) d = Some g'\<close>
      from d AD obtain b where b: \<open>b \<in> set ?A\<close> and db: \<open>d = vdec b\<close> by blast
      show \<open>\<not> dlive g'\<close> using dead[OF b vchoose_NoneD[OF ch b]] m db by simp
    qed
    with dsE show ?thesis by simp
  qed
  show \<open>\<exists>st'. dstep G gt sts redtab st = Some st' \<and> vst_rel G Shn sts gt st' vs'\<close>
    if vy: \<open>vstep_u V vs = Some (Some vs')\<close>
  proof -
    obtain act fs' w' where ch: \<open>vchoose V (fs, w) ?A = Some (Some (act, fs', w'))\<close>
      and vs': \<open>vs' = (case tstep (vdec act) (v, tstk) of (v', tstk') \<Rightarrow> (fs', w', v', tstk'))\<close>
      using vy by (auto simp: vstep_u_def vs fs split: option.splits prod.splits)
    from vchoose_SomeD[OF ch] have act: \<open>act \<in> set ?A\<close> and vms: \<open>vmstep V (fs, w) act = Some (fs', w')\<close>
      and alt: \<open>act = VShift \<or> (\<forall>b \<in> set ?A. b \<noteq> act \<longrightarrow> vmstep V (fs, w) b = None)\<close> by simp_all
    from vm[OF act] vms obtain Xs' istk' where
      im: \<open>imstep G gt sts ((Xs, w), istk) (vdec act) = Some ((Xs', w'), istk')\<close>
      and lv: \<open>dlive (Xs', w')\<close> and r': \<open>vrel G sts Xs' istk' fs'\<close> by auto
    have ms: \<open>mstep_cached G cstk (Xs, w) (vdec act) = Some (Xs', w')\<close>
      using im by (simp add: imstep_def mc split: option.splits)
    have pick: \<open>dpick G cstk (Xs, w) ?D = Some (vdec act, (Xs', w'))\<close>
      using alt
    proof
      assume sh: \<open>act = VShift\<close>
      with act have \<open>w \<noteq> []\<close> by (auto simp: vcands_def Let_def split: list.splits)
      then obtain rest where \<open>?D = DShift # rest\<close> using ne by (cases w) (auto simp: dcands_def Let_def)
      with ms lv sh show ?thesis by simp
    next
      assume un: \<open>\<forall>b \<in> set ?A. b \<noteq> act \<longrightarrow> vmstep V (fs, w) b = None\<close>
      show ?thesis
      proof (rule dpick_unique[OF _ ms lv])
        show \<open>vdec act \<in> set ?D\<close> using act AD by blast
        fix d g' assume d: \<open>d \<in> set ?D\<close> \<open>d \<noteq> vdec act\<close> and m: \<open>mstep_cached G cstk (Xs, w) d = Some g'\<close>
        from d(1) AD obtain b where b: \<open>b \<in> set ?A\<close> and db: \<open>d = vdec b\<close> by blast
        with d(2) have \<open>b \<noteq> act\<close> by blast
        with un b have \<open>vmstep V (fs, w) b = None\<close> by blast
        from dead[OF b this] m db show \<open>\<not> dlive g'\<close> by simp
      qed
    qed
    have lic: \<open>\<forall>pr. vdec act = DReduce pr \<longrightarrow> lic_at G ?L sts ((Xs, w), istk) pr\<close>
    proof (intro allI impI)
      fix pr assume \<open>vdec act = DReduce pr\<close>
      with act AD have \<open>DReduce pr \<in> set ?D\<close> by force
      from dcands_reduceD[OF this] have \<open>dlic j (redtab ! j) w pr (red_set ?CL pr)\<close> by simp
      then have \<open>dlic_L j ?L w pr (red_set ?CL pr)\<close>
        using dlic_buckets[of j \<open>length sts\<close> ?L] j by (simp add: rt red_buckets_def)
      then show \<open>lic_at G ?L sts ((Xs, w), istk) pr\<close> using j by (simp add: lic_at_def hj)
    qed
    from dstep_of_dpick[OF tab stc gtc refl rt ir inv[unfolded st] im lv lic, unfolded fst_conv]
      pick hj
    obtain v' tstk' where tp: \<open>(v', tstk') = tstep (vdec act) (v, tstk)\<close>
      and ds: \<open>dstep G gt sts redtab ((Xs, w), cstk, istk, v, tstk)
          = Some ((Xs', w'), map (xclosure_auto G) Xs', istk', v', tstk')\<close>
      and inv': \<open>dfollow_ok G sts ((Xs', w'), map (xclosure_auto G) Xs', istk', v', tstk')\<close>
      by blast
    have ir': \<open>imreach G Shn gt sts ((Xs', w'), istk')\<close> using imreach_step[OF ir im] lv by simp
    have \<open>vs' = (fs', w', v', tstk')\<close> using vs' tp[symmetric] by simp
    moreover have \<open>vst_rel G Shn sts gt ((Xs', w'), map (xclosure_auto G) Xs', istk', v', tstk')
        (fs', w', v', tstk')\<close> using r' ir' inv' by (simp add: vst_rel_def)
    ultimately show ?thesis using ds by (simp add: st)
  qed
qed


subsection \<open>The checked run\<close>

definition vctx_u :: \<open>('n, 't) is_cfg \<Rightarrow> 'n \<Rightarrow> (('n, 't) sym \<times> nat) list list \<Rightarrow> ('n, 't) citem list list \<Rightarrow>
    ('n, 't) lacell list list \<Rightarrow> ('n, 't) vtab \<Rightarrow> bool\<close> where
  \<open>vctx_u G Shn gt sts redtab V \<longleftrightarrow> V = mk_vtab G Shn (mk_stab G Shn gt sts redtab) sts gt redtab \<and>
     sts = pr0_states G Shn \<and> gt = pgtab G sts \<and> redtab = red_buckets G Shn (length sts) \<and>
     fresh_name G Shn\<close>

lemma vctx_u_final:
  assumes c: \<open>vctx_u G Shn gt sts redtab V\<close> and r: \<open>vst_rel G Shn sts gt st vs\<close>
  obtains gc cstk istk v tstk fs where \<open>st = (gc, cstk, istk, v, tstk)\<close> \<open>vs = (fs, snd gc, v, tstk)\<close>
    \<open>vfinal V vs \<longleftrightarrow> gfinal G Shn gc\<close>
proof -
  obtain Xs w cstk istk v tstk where st: \<open>st = ((Xs, w), cstk, istk, v, tstk)\<close>
    by (metis prod.exhaust)
  obtain fs where vs: \<open>vs = (fs, w, v, tstk)\<close> and rr: \<open>vrel G sts Xs istk fs\<close>
    and ir: \<open>imreach G Shn gt sts ((Xs, w), istk)\<close>
    using r by (cases vs) (auto simp: vst_rel_def st)
  have tab: \<open>tables_ok G Shn sts gt (la_fix G Shn)\<close>
    using c tables_ok_concrete[of G Shn] by (simp add: vctx_u_def)
  have V: \<open>V = mk_vtab G Shn (mk_stab G Shn gt sts redtab) sts gt redtab\<close>
    and fn: \<open>fresh_name G Shn\<close> using c by (simp_all add: vctx_u_def)
  have \<open>vfinal V vs \<longleftrightarrow> gfinal G Shn (Xs, w)\<close>
    unfolding vs by (rule vfinal_gfinal[OF refl V tab fn ir rr])
  then show thesis using that[of \<open>(Xs, w)\<close> cstk istk v tstk fs] st vs by simp
qed

lemma vrun_u_sound:
  assumes run: \<open>vrun_u V vs = Some r\<close>
  shows \<open>\<forall>G Shn gt sts redtab st. vctx_u G Shn gt sts redtab V \<longrightarrow> vst_rel G Shn sts gt st vs \<longrightarrow>
    drun_nh G Shn gt sts redtab st = r\<close>
proof (rule vrun_u.raw_induct[OF _ run], goal_cases)
  case (1 f V vs r)
  show ?case
  proof (intro impI allI)
    fix G Shn gt sts redtab st
    assume c: \<open>vctx_u G Shn gt sts redtab V\<close> and rl: \<open>vst_rel G Shn sts gt st vs\<close>
    obtain gc cstk istk v tstk fs where st: \<open>st = (gc, cstk, istk, v, tstk)\<close>
      and vs: \<open>vs = (fs, snd gc, v, tstk)\<close> and gf: \<open>vfinal V vs \<longleftrightarrow> gfinal G Shn gc\<close>
      by (rule vctx_u_final[OF c rl])
    have V: \<open>V = mk_vtab G Shn (mk_stab G Shn gt sts redtab) sts gt redtab\<close>
      and stc: \<open>sts = pr0_states G Shn\<close> and gtc: \<open>gt = pgtab G sts\<close>
      and rt: \<open>redtab = red_buckets G Shn (length sts)\<close> using c by (simp_all add: vctx_u_def)
    note su = vstep_u_dstep[OF refl V stc gtc rt rl]
    show \<open>drun_nh G Shn gt sts redtab st = r\<close>
    proof (cases \<open>vfinal V vs\<close>)
      case True
      with "1"(2) gf show ?thesis unfolding st vs by (subst drun_nh.simps) simp
    next
      case False
      show ?thesis
      proof (cases \<open>vstep_u V vs\<close>)
        case None
        with False "1"(2) show ?thesis unfolding vs by (simp add: vs[symmetric])
      next
        case (Some x)
        show ?thesis
        proof (cases x)
          case None
          with Some False "1"(2) have r: \<open>r = None\<close> unfolding vs by (simp add: vs[symmetric])
          from su(1) Some None have \<open>dstep G gt sts redtab st = None\<close> by simp
          with False gf r show ?thesis unfolding st by (subst drun_nh.simps) simp
        next
          case (Some vs\<^sub>1)
          with \<open>vstep_u V vs = Some x\<close> False "1"(2) have rec: \<open>f V vs\<^sub>1 = Some r\<close>
            unfolding vs by (simp add: vs[symmetric])
          from su(2) \<open>vstep_u V vs = Some x\<close> Some obtain st\<^sub>1 where
            sp: \<open>dstep G gt sts redtab st = Some st\<^sub>1\<close> and r1: \<open>vst_rel G Shn sts gt st\<^sub>1 vs\<^sub>1\<close>
            by blast
          from "1"(1)[OF rec] c r1 have \<open>drun_nh G Shn gt sts redtab st\<^sub>1 = r\<close> by blast
          with False gf sp show ?thesis unfolding st by (subst drun_nh.simps) simp
        qed
      qed
    qed
  qed
qed

theorem vrun_u_dparse:
  assumes fn: \<open>fresh_name G Shn\<close>
    and sts: \<open>sts = pr0_states G Shn\<close> and gt: \<open>gt = pgtab G sts\<close>
    and rt: \<open>redtab = red_buckets G Shn (length sts)\<close>
    and V: \<open>V = mk_vtab G Shn (mk_stab G Shn gt sts redtab) sts gt redtab\<close>
    and run: \<open>vrun_u V ([v_av0 V], tcols w, w, []) = Some r\<close>
  shows \<open>dparse G Shn w = r\<close>
proof -
  have c: \<open>vctx_u G Shn gt sts redtab V\<close> using assms by (simp add: vctx_u_def)
  have tab: \<open>tables_ok G Shn sts gt (la_fix G Shn)\<close> using tables_ok_concrete[of G Shn] sts gt by simp
  have \<open>vst_rel G Shn sts gt (dinit G Shn sts w) ([v_av0 V], tcols w, w, [])\<close>
    using vinit_vrel[OF refl tab fn] imreach_init[of G Shn gt sts \<open>tcols w\<close>]
      dfollow_ok_dinit[of G Shn w]
    by (simp add: vst_rel_def dinit_def v_av0_mk[OF V] sts)
  with vrun_u_sound[OF run] c have \<open>drun_nh G Shn gt sts redtab (dinit G Shn sts w) = r\<close> by blast
  moreover have \<open>dparse G Shn w = drun_nh G Shn gt sts redtab (dinit G Shn sts w)\<close>
    using dparse_via_tables_nh[OF sts[symmetric] gt[symmetric] rt[symmetric] refl refl refl]
    by (simp add: dinit_def)
  ultimately show ?thesis by simp
qed

text \<open>The parser for the code generator: the checked vector run, and the sparse
  driver should it meet a conflict.\<close>

lemma dparse_via_tables_vu:
  assumes st: \<open>pr0_states G Shn = sts\<close>
    and gt: \<open>pgtab G sts = gtab\<close>
    and rt: \<open>red_buckets G Shn (length sts) = redtab\<close>
    and i0: \<open>st_find sts (lr0_start G Shn) = i\<^sub>0\<close>
    and fr: \<open>fresh_name G Shn\<close>
    and tb: \<open>mk_stab G Shn gtab sts redtab = stb\<close>
    and vt: \<open>mk_vtab G Shn stb sts gtab redtab = vtb\<close>
    and ki: \<open>sinit stb = kin\<close>
    and kc: \<open>sclosure stb kin = kcl\<close>
  shows \<open>dparse G Shn w = (case vrun_u vtb ([v_av0 vtb], tcols w, w, []) of
      Some r \<Rightarrow> r | None \<Rightarrow> sdrun stb (([kin], tcols w), [kcl], [i\<^sub>0], w, []))\<close>
proof (cases \<open>vrun_u vtb ([v_av0 vtb], tcols w, w, [])\<close>)
  case None
  then show ?thesis using dparse_via_tables_s[OF st gt rt i0 fr tb ki kc] by simp
next
  case (Some r)
  have \<open>dparse G Shn w = r\<close>
    by (rule vrun_u_dparse[OF fr st[symmetric] gt[symmetric] rt[symmetric] _ Some])
       (simp add: tb vt)
  with Some show ?thesis by simp
qed

section \<open>Faster code\<close>

text \<open>Code equations, and a copy of the checked driver, that the generated parser
  runs instead of the definitions above.  Each is proved equal to what it replaces
  (the copy: sound for it), so the simulation argument is untouched.\<close>

subsection \<open>Anchor-set operations\<close>

text \<open>The generated code rebuilds a list that an equation matches as \<open>x # xs\<close> and
  passes on whole; the equations here pass the list itself instead.\<close>

text \<open>A frame read by one walk down the list, without its length.\<close>

lemma getR_code [code]:
  \<open>getR [] k = FinRep []\<close>
  \<open>getR (R # av) k = (if k = 0 then R else getR av (k - 1))\<close>
  by (simp add: getR_def) (cases k, simp_all add: getR_def)

lemma merge_code [code]:
  \<open>merge xs ys = (case xs of [] \<Rightarrow> ys | x # xs' \<Rightarrow> (case ys of [] \<Rightarrow> xs | y # ys' \<Rightarrow>
     if x < y then x # merge xs' ys else if y < x then y # merge xs ys' else x # merge xs' ys'))\<close>
  by (cases xs; cases ys) simp_all

text \<open>Two sorted finite sets intersected by a merge.  The operations keep their
  sets sorted, but no lemma says so: the check at runtime keeps the equation
  unconditional.\<close>

fun slt :: \<open>nat list \<Rightarrow> bool\<close> where
  \<open>slt (x # y # ys) \<longleftrightarrow> x < y \<and> slt (y # ys)\<close>
| \<open>slt _ \<longleftrightarrow> True\<close>

lemma slt_sorted: \<open>slt xs \<longleftrightarrow> sorted_wrt (<) xs\<close>
  by (induction xs rule: slt.induct) (auto intro: less_trans)

fun inter_s :: \<open>nat list \<Rightarrow> nat list \<Rightarrow> nat list\<close> where
  \<open>inter_s [] ys = []\<close>
| \<open>inter_s xs [] = []\<close>
| \<open>inter_s (x # xs) (y # ys) =
    (if x < y then inter_s xs (y # ys) else if y < x then inter_s (x # xs) ys
     else x # inter_s xs ys)\<close>

lemma slt_code [code]:
  \<open>slt xs = (case xs of [] \<Rightarrow> True | x # xs' \<Rightarrow> (case xs' of [] \<Rightarrow> True | y # _ \<Rightarrow> x < y \<and> slt xs'))\<close>
  by (cases xs rule: slt.cases) simp_all

lemma inter_s_code [code]:
  \<open>inter_s xs ys = (case xs of [] \<Rightarrow> [] | x # xs' \<Rightarrow> (case ys of [] \<Rightarrow> [] | y # ys' \<Rightarrow>
     if x < y then inter_s xs' ys else if y < x then inter_s xs ys' else x # inter_s xs' ys'))\<close>
  by (cases xs; cases ys) simp_all

lemma inter_s_filter:
  \<open>sorted_wrt (<) xs \<Longrightarrow> sorted_wrt (<) ys \<Longrightarrow> inter_s xs ys = filter (\<lambda>i. i \<in> set ys) xs\<close>
proof (induction xs ys rule: inter_s.induct)
  case (3 x xs y ys)
  then show ?case
    by (auto intro!: filter_cong)
qed simp_all

text \<open>A union with an empty finite set, and an intersection with a singleton, give
  back an argument: no list is built.  The general cases are the equations above,
  under another name.\<close>

definition cunion_m :: \<open>indrep \<Rightarrow> indrep \<Rightarrow> indrep\<close> where
  \<open>cunion_m = cunion\<close>

lemma cunion_m_code [code]:
  \<open>cunion_m (FinRep xs) (FinRep ys) = FinRep (merge xs ys)\<close>
  \<open>cunion_m (FinRep xs) (UpRep ys n) = UpRep (filter (\<lambda>i. i < n) (merge xs ys)) n\<close>
  \<open>cunion_m (UpRep xs n) (FinRep ys) = UpRep (filter (\<lambda>i. i < n) (merge xs ys)) n\<close>
  \<open>cunion_m (UpRep xs n) (UpRep ys m) = UpRep (filter (\<lambda>i. i < min n m) (merge xs ys)) (min n m)\<close>
  by (simp_all add: cunion_m_def)

lemma cunion_code [code]:
  \<open>cunion R S = (case R of
     FinRep xs \<Rightarrow> (case xs of [] \<Rightarrow> (case S of FinRep _ \<Rightarrow> S | UpRep _ _ \<Rightarrow> cunion_m R S)
       | _ # _ \<Rightarrow> (case S of FinRep ys \<Rightarrow> (case ys of [] \<Rightarrow> R | _ # _ \<Rightarrow> cunion_m R S)
                  | UpRep _ _ \<Rightarrow> cunion_m R S))
   | UpRep _ _ \<Rightarrow> cunion_m R S)\<close>
  by (auto simp: cunion_m_def split: indrep.split list.split)

definition cinter_m :: \<open>indrep \<Rightarrow> indrep \<Rightarrow> indrep\<close> where
  \<open>cinter_m = cinter\<close>

lemma cinter_m_code [code]:
  \<open>cinter_m (FinRep xs) (FinRep ys) =
     FinRep (if slt xs \<and> slt ys then inter_s xs ys else filter (\<lambda>i. irep_mem i (FinRep ys)) xs)\<close>
  \<open>cinter_m (FinRep xs) (UpRep ys m) = FinRep (filter (\<lambda>i. irep_mem i (UpRep ys m)) xs)\<close>
  \<open>cinter_m (UpRep xs n) (FinRep ys) = FinRep (filter (\<lambda>i. irep_mem i (UpRep xs n)) ys)\<close>
  \<open>cinter_m (UpRep xs n) (UpRep ys m) =
     UpRep (filter (\<lambda>i. i < max n m)
       (merge (filter (\<lambda>i. irep_mem i (UpRep ys m)) xs) (filter (\<lambda>i. irep_mem i (UpRep xs n)) ys)))
       (max n m)\<close>
  by (simp_all add: cinter_m_def slt_sorted inter_s_filter del: irep_mem_correct)

lemma filter_eq_replicate: \<open>filter (\<lambda>i. i = y) xs = replicate (count_list xs y) y\<close>
  by (induction xs) auto

text \<open>A finite set may repeat an element, so the singleton on the right comes back
  only when it occurs once.\<close>

lemma cinter_code [code]:
  \<open>cinter R S = (case R of
     FinRep xs \<Rightarrow> (case xs of
         [] \<Rightarrow> FinRep []
       | x # xs' \<Rightarrow> (case xs' of
           [] \<Rightarrow> (if irep_mem x S then R else FinRep [])
         | _ # _ \<Rightarrow> (case S of
             FinRep ys \<Rightarrow> (case ys of
                 [] \<Rightarrow> cinter_m R S
               | y # ys' \<Rightarrow> (case ys' of
                   [] \<Rightarrow> (let k = count_list xs y in if k = 1 then S else FinRep (replicate k y))
                 | _ # _ \<Rightarrow> cinter_m R S))
           | UpRep _ _ \<Rightarrow> cinter_m R S)))
   | UpRep _ _ \<Rightarrow> (case S of
       FinRep ys \<Rightarrow> (case ys of
           [] \<Rightarrow> cinter_m R S
         | y # ys' \<Rightarrow> (case ys' of [] \<Rightarrow> (if irep_mem y R then S else FinRep []) | _ # _ \<Rightarrow> cinter_m R S))
     | UpRep _ _ \<Rightarrow> cinter_m R S))\<close>
  by (auto simp: cinter_m_def filter_eq_replicate Let_def split: indrep.split list.split)

text \<open>A frame filled in one pass, without the pairs of \<^const>\<open>zip\<close>; a dead kernel
  item adds nothing to a finite set.\<close>

fun vfill_row :: \<open>indrep list \<Rightarrow> (nat \<times> eff) list \<Rightarrow> indrep \<Rightarrow> indrep\<close> where
  \<open>vfill_row kav [] acc = acc\<close>
| \<open>vfill_row kav ((kk, e) # cs) acc = vfill_row kav cs (let R = getR kav kk in
     if irep_nonempty R then cunion acc (eapp e R)
     else (case acc of FinRep _ \<Rightarrow> acc | UpRep _ _ \<Rightarrow> cunion acc (FinRep [])))\<close>

fun vfill_go :: \<open>indrep list \<Rightarrow> indrep list \<Rightarrow> (nat \<times> eff) list list \<Rightarrow> indrep list\<close> where
  \<open>vfill_go kav (R # Rs) (cs # css) = vfill_row kav cs R # vfill_go kav Rs css\<close>
| \<open>vfill_go kav _ _ = []\<close>

lemma merge_Nil2 [simp]: \<open>merge xs [] = xs\<close>
  by (cases xs) simp_all

lemma eapp_dead: \<open>\<not> irep_nonempty R \<Longrightarrow> eapp e R = FinRep []\<close>
  by (simp add: eapp_def)

lemma vfill_row_fold:
  \<open>vfill_row kav cs R = fold (\<lambda>(kk, e) acc. cunion acc (eapp e (getR kav kk))) cs R\<close>
  by (induction kav cs R rule: vfill_row.induct) (simp add: Let_def eapp_dead split: indrep.split)+

lemma vfill_code [code]: \<open>vfill cts kav = vfill_go kav kav cts\<close>
proof -
  have \<open>vfill_go kav Rs cts =
      map (\<lambda>(R, cs). fold (\<lambda>(kk, e) acc. cunion acc (eapp e (getR kav kk))) cs R) (zip Rs cts)\<close> for Rs
    by (induction kav Rs cts rule: vfill_go.induct) (simp_all add: vfill_row_fold)
  then show ?thesis by (simp add: vfill_def)
qed

subsection \<open>Numbered lookahead\<close>

text \<open>The checked driver with the lookahead numbered once, before the run, where
  \<^const>\<open>vrun_u\<close> searches the token list at every shift and every licence.  A
  reduction finds its target frame by one \<^const>\<open>drop\<close>, without the length of the
  stack.\<close>

definition vnw :: \<open>('n, 't) vtab \<Rightarrow> ('t \<times> nat) list \<Rightarrow> (nat \<times> nat) list\<close> where
  \<open>vnw V w = map (\<lambda>(a, c). (vnum V a, c)) w\<close>

definition vmstep_n :: \<open>('n, 't) vtab \<Rightarrow> vframes \<times> (nat \<times> nat) list \<Rightarrow> ('n, 't) vact \<Rightarrow>
    (vframes \<times> (nat \<times> nat) list) option\<close> where
  \<open>vmstep_n V fw act = (case fw of (fs, w) \<Rightarrow> (case fs of [] \<Rightarrow> None | (j, av) # _ \<Rightarrow>
     (case act of
        VShift \<Rightarrow> (case w of [] \<Rightarrow> None | (a, c) # w' \<Rightarrow>
          (case iget (iget (v_sh V) j (IArray [])) a None of None \<Rightarrow> None
           | Some e \<Rightarrow> map_option (\<lambda>f. (f # fs, w')) (vgo V e av (FinRep [c]))))
      | VReduce s b pr \<Rightarrow> (let fs' = drop (length (snd pr)) fs in (case fs' of [] \<Rightarrow> None
          | (j\<^sub>0, av\<^sub>0) # _ \<Rightarrow>
            (case iget (iget (v_go V) j\<^sub>0 (IArray [])) b None of None \<Rightarrow> None
             | Some e \<Rightarrow> map_option (\<lambda>f. (f # fs', w)) (vgo V e av\<^sub>0 (getR av s))))))))\<close>

definition vlic_n :: \<open>('n, 't) vtab \<Rightarrow> nat \<Rightarrow> (nat \<times> nat) list \<Rightarrow> nat \<Rightarrow> indrep \<Rightarrow> bool\<close> where
  \<open>vlic_n V j w s RS = (case w of [] \<Rightarrow> s \<in> set (iget (v_ce V) j [])
     | (a, c) # _ \<Rightarrow> list_ex (\<lambda>(s', \<tau>). s' = s \<and> irep_ex_wsat \<tau> c RS)
         (iget (iget (v_cl V) j (IArray [])) a []))\<close>

definition vcands_n :: \<open>('n, 't) vtab \<Rightarrow> nat \<Rightarrow> indrep list \<Rightarrow> (nat \<times> nat) list \<Rightarrow> ('n, 't) vact list\<close> where
  \<open>vcands_n V j av w = (let reds = map (\<lambda>(s, b, pr). VReduce s b pr)
       (filter (\<lambda>(s, b, pr). let RS = getR av s in irep_nonempty RS \<and> vlic_n V j w s RS)
         (iget (v_cp V) j []))
     in (case w of [] \<Rightarrow> reds | _ \<Rightarrow> VShift # reds))\<close>

fun vchoose_n :: \<open>('n, 't) vtab \<Rightarrow> vframes \<times> (nat \<times> nat) list \<Rightarrow> ('n, 't) vact list \<Rightarrow>
    (('n, 't) vact \<times> vframes \<times> (nat \<times> nat) list) option option\<close> where
  \<open>vchoose_n V fw [] = Some None\<close>
| \<open>vchoose_n V fw (a # acts) = (case vmstep_n V fw a of
     None \<Rightarrow> vchoose_n V fw acts
   | Some r \<Rightarrow> if a = VShift \<or> \<not> list_ex (\<lambda>b. vmstep_n V fw b \<noteq> None) acts then Some (Some (a, r))
              else None)\<close>

type_synonym ('m, 'ch, 'n, 't) vst_n =
  \<open>vframes \<times> (nat \<times> nat) list \<times> ('m, 'ch, 't) tword \<times> ('m, 'ch, 'n, 't) ast list\<close>

definition vstep_un :: \<open>('n, 't) vtab \<Rightarrow> ('m, 'ch, 'n, 't) vst_n \<Rightarrow> ('m, 'ch, 'n, 't) vst_n option option\<close> where
  \<open>vstep_un V st = (case st of (fs, w, v, tstk) \<Rightarrow> (case fs of [] \<Rightarrow> Some None | (j, av) # _ \<Rightarrow>
     (case vchoose_n V (fs, w) (vcands_n V j av w) of None \<Rightarrow> None | Some None \<Rightarrow> Some None
      | Some (Some (act, fs', w')) \<Rightarrow>
          (case tstep (vdec act) (v, tstk) of (v', tstk') \<Rightarrow> Some (Some (fs', w', v', tstk'))))))\<close>

definition vfinal_n :: \<open>('n, 't) vtab \<Rightarrow> ('m, 'ch, 'n, 't) vst_n \<Rightarrow> bool\<close> where
  \<open>vfinal_n V st = (case st of (fs, w, v, tstk) \<Rightarrow> w = [] \<and> (case fs of [] \<Rightarrow> False
     | (j, av) # _ \<Rightarrow> irep_mem (v_ind0 V) (getR av (iget (v_fin V) j 0))))\<close>

partial_function (option) vrun_un ::
  \<open>('n, 't) vtab \<Rightarrow> ('m, 'ch, 'n, 't) vst_n \<Rightarrow> ('m, 'ch, 'n, 't) ast option option\<close>
  where
  \<open>vrun_un V st = (case st of (fs, w, v, tstk) \<Rightarrow>
     if vfinal_n V st then Some (case tstk of t # _ \<Rightarrow> Some t | [] \<Rightarrow> None)
     else (case vstep_un V st of None \<Rightarrow> None | Some None \<Rightarrow> Some None
       | Some (Some st') \<Rightarrow> vrun_un V st'))\<close>

lemmas vrun_un_simps [code] = vrun_un.simps

lemma vnw_simps [simp]: \<open>vnw V [] = []\<close> \<open>vnw V ((a, c) # w) = (vnum V a, c) # vnw V w\<close>
  by (simp_all add: vnw_def)

lemma vmstep_n_vnw:
  \<open>vmstep_n V (fs, vnw V w) act = map_option (\<lambda>(fs', w'). (fs', vnw V w')) (vmstep V (fs, w) act)\<close>
proof (cases act)
  case VShift
  then show ?thesis
    by (cases w) (auto simp: vmstep_n_def vmstep_def option.map_comp comp_def
        split: list.split option.split)
next
  case (VReduce s b pr)
  then show ?thesis
  proof (cases \<open>length (snd pr) < length fs\<close>)
    case True
    obtain j av fs\<^sub>1 where fs: \<open>fs = (j, av) # fs\<^sub>1\<close> using True by (cases fs) auto
    obtain j\<^sub>0 av\<^sub>0 where nth: \<open>fs ! length (snd pr) = (j\<^sub>0, av\<^sub>0)\<close> by (cases \<open>fs ! length (snd pr)\<close>)
    have dr: \<open>drop (length (snd pr)) fs = (j\<^sub>0, av\<^sub>0) # drop (Suc (length (snd pr))) fs\<close>
      using True nth by (metis Cons_nth_drop_Suc)
    show ?thesis using True nth dr unfolding VReduce fs
      by (auto simp: vmstep_n_def vmstep_def Let_def option.map_comp comp_def split: option.split)
  next
    case False
    then show ?thesis using VReduce
      by (auto simp: vmstep_n_def vmstep_def Let_def split: list.split)
  qed
qed

lemma vlic_n_vnw: \<open>vlic_n V j (vnw V w) s RS = vlic V j w s RS\<close>
  by (cases w) (auto simp: vlic_n_def vlic_def)

lemma vcands_n_vnw: \<open>vcands_n V j av (vnw V w) = vcands V j av w\<close>
  unfolding vcands_n_def vcands_def vlic_n_vnw by (cases w) auto

lemma vchoose_n_vnw:
  \<open>vchoose_n V (fs, vnw V w) acts =
     map_option (map_option (\<lambda>(a, fs', w'). (a, fs', vnw V w'))) (vchoose V (fs, w) acts)\<close>
proof (induction acts)
  case (Cons a acts)
  have ex: \<open>list_ex (\<lambda>b. vmstep_n V (fs, vnw V w) b \<noteq> None) acts \<longleftrightarrow>
      list_ex (\<lambda>b. vmstep V (fs, w) b \<noteq> None) acts\<close>
    by (simp add: vmstep_n_vnw)
  show ?case using Cons.IH by (auto simp: vmstep_n_vnw ex split: option.split)
qed simp

lemma vstep_un_vnw:
  \<open>vstep_un V (fs, vnw V w, v, tstk) =
     map_option (map_option (\<lambda>(fs', w', vt). (fs', vnw V w', vt))) (vstep_u V (fs, w, v, tstk))\<close>
  by (auto simp: vstep_un_def vstep_u_def vchoose_n_vnw vcands_n_vnw
      split: list.split option.split prod.split)

lemma vfinal_n_vnw: \<open>vfinal_n V (fs, vnw V w, v, tstk) = vfinal V (fs, w, v, tstk)\<close>
  by (simp add: vfinal_n_def vfinal_def vnw_def)

lemma vrun_un_sound:
  assumes run: \<open>vrun_un V vs = Some r\<close>
  shows \<open>\<forall>fs w v tstk. vs = (fs, vnw V w, v, tstk) \<longrightarrow> vrun_u V (fs, w, v, tstk) = Some r\<close>
proof (rule vrun_un.raw_induct[OF _ run], goal_cases)
  case (1 f V vs r)
  show ?case
  proof (intro allI impI)
    fix fs w v tstk
    assume vs: \<open>vs = (fs, vnw V w, v, tstk)\<close>
    note body = "1"(2)[unfolded vs, simplified vfinal_n_vnw vstep_un_vnw]
    show \<open>vrun_u V (fs, w, v, tstk) = Some r\<close>
    proof (cases \<open>vfinal V (fs, w, v, tstk)\<close>)
      case True
      with body show ?thesis by (subst vrun_u.simps) simp
    next
      case False
      show ?thesis
      proof (cases \<open>vstep_u V (fs, w, v, tstk)\<close>)
        case None
        with False body show ?thesis by simp
      next
        case (Some x)
        show ?thesis
        proof (cases x)
          case None
          with Some False body show ?thesis by (subst vrun_u.simps) simp
        next
          case (Some st\<^sub>1)
          obtain fs\<^sub>1 w\<^sub>1 v\<^sub>1 t\<^sub>1 where st1: \<open>st\<^sub>1 = (fs\<^sub>1, w\<^sub>1, v\<^sub>1, t\<^sub>1)\<close> by (cases st\<^sub>1)
          from \<open>vstep_u V (fs, w, v, tstk) = Some x\<close> Some st1 False body
          have \<open>f V (fs\<^sub>1, vnw V w\<^sub>1, v\<^sub>1, t\<^sub>1) = Some r\<close> by simp
          with "1"(1) have \<open>vrun_u V st\<^sub>1 = Some r\<close> unfolding st1 by blast
          with False \<open>vstep_u V (fs, w, v, tstk) = Some x\<close> Some show ?thesis
            by (subst vrun_u.simps) simp
        qed
      qed
    qed
  qed
qed

definition vtcols :: \<open>('n, 't) vtab \<Rightarrow> ('m, 'ch, 't) tword \<Rightarrow> (nat \<times> nat) list\<close> where
  \<open>vtcols V w = map (\<lambda>t. (vnum V (tok t), s_col (span t))) w\<close>

lemma vtcols_vnw: \<open>vtcols V w = vnw V (tcols w)\<close>
  by (simp add: vtcols_def vnw_def tcols_def)

text \<open>The parser for the code generator: \<^const>\<open>vrun_un\<close> on the numbered word, and
  the sparse driver should it meet a conflict.\<close>

lemma dparse_via_tables_vun:
  assumes st: \<open>pr0_states G Shn = sts\<close>
    and gt: \<open>pgtab G sts = gtab\<close>
    and rt: \<open>red_buckets G Shn (length sts) = redtab\<close>
    and i0: \<open>st_find sts (lr0_start G Shn) = i\<^sub>0\<close>
    and fr: \<open>fresh_name G Shn\<close>
    and tb: \<open>mk_stab G Shn gtab sts redtab = stb\<close>
    and vt: \<open>mk_vtab G Shn stb sts gtab redtab = vtb\<close>
    and ki: \<open>sinit stb = kin\<close>
    and kc: \<open>sclosure stb kin = kcl\<close>
  shows \<open>dparse G Shn w = (case vrun_un vtb ([v_av0 vtb], vtcols vtb w, w, []) of
      Some r \<Rightarrow> r | None \<Rightarrow> sdrun stb (([kin], tcols w), [kcl], [i\<^sub>0], w, []))\<close>
proof (cases \<open>vrun_un vtb ([v_av0 vtb], vtcols vtb w, w, [])\<close>)
  case None
  then show ?thesis using dparse_via_tables_s[OF st gt rt i0 fr tb ki kc] by simp
next
  case (Some r)
  have \<open>vrun_u vtb ([v_av0 vtb], tcols w, w, []) = Some r\<close>
    using vrun_un_sound[OF Some] by (simp add: vtcols_vnw)
  then have \<open>dparse G Shn w = r\<close>
    using dparse_via_tables_vu[OF st gt rt i0 fr tb vt ki kc, of w] by simp
  with Some show ?thesis by simp
qed

subsection \<open>Kernel-only frames\<close>

text \<open>An entry of the successor tables names the kernel items of the target
  state, and \<^const>\<open>vkav\<close> pads them with an empty set for every other item.  The
  entries here keep the kernel items alone, with a plan of the target's items:
  whether each is a kernel item, and its contributions, each from the rank of
  its kernel item.  The tables come from \<^const>\<open>mk_vtab\<close>'s by a map.\<close>

type_synonym kentry = \<open>nat \<times> (nat \<times> irel) list \<times> (bool \<times> (nat \<times> eff) list) list\<close>

datatype ('n, 't) vktab = VKTab
  (k_v: \<open>('n, 't) vtab\<close>)
  (k_sh: \<open>kentry option iarray iarray\<close>)
  (k_go: \<open>kentry option iarray iarray\<close>)

text \<open>The kernel items, and the rank of a kernel item among them; for any other
  item a rank past them all, where a frame reads the empty set.\<close>

fun ksome :: \<open>'a option list \<Rightarrow> 'a list\<close> where
  \<open>ksome [] = []\<close>
| \<open>ksome (None # xs) = ksome xs\<close>
| \<open>ksome (Some x # xs) = x # ksome xs\<close>

fun kidx :: \<open>'a option list \<Rightarrow> nat \<Rightarrow> nat option\<close> where
  \<open>kidx [] k = None\<close>
| \<open>kidx (x # xs) k = (case k of
     0 \<Rightarrow> (case x of None \<Rightarrow> None | Some _ \<Rightarrow> Some 0)
   | Suc k' \<Rightarrow> (case x of None \<Rightarrow> kidx xs k' | Some _ \<Rightarrow> map_option Suc (kidx xs k')))\<close>

definition krank :: \<open>'a option list \<Rightarrow> nat \<Rightarrow> nat\<close> where
  \<open>krank km kk = (case kidx km kk of None \<Rightarrow> length km | Some r \<Rightarrow> r)\<close>

definition kconv :: \<open>('n, 't) vtab \<Rightarrow> nat \<times> (nat \<times> irel) option list \<Rightarrow> kentry\<close> where
  \<open>kconv V e = (case e of (j', km) \<Rightarrow> (j', ksome km,
     map (\<lambda>(x, cs). (x \<noteq> None, map (\<lambda>(kk, e). (krank km kk, e)) cs)) (zip km (iget (v_ct V) j' []))))\<close>

definition kmap :: \<open>('n, 't) vtab \<Rightarrow> (nat \<times> (nat \<times> irel) option list) option iarray iarray \<Rightarrow>
    kentry option iarray iarray\<close> where
  \<open>kmap V T = IArray (map (\<lambda>r. IArray (map (map_option (kconv V)) (IArray.list_of r))) (IArray.list_of T))\<close>

definition mk_vktab :: \<open>('n, 't) vtab \<Rightarrow> ('n, 't) vktab\<close> where
  \<open>mk_vktab V = VKTab V (kmap V (v_sh V)) (kmap V (v_go V))\<close>

lemma iget_kmap:
  \<open>iget (iget (kmap V T) j (IArray [])) a None = map_option (kconv V) (iget (iget T j (IArray [])) a None)\<close>
  by (cases T) (auto simp: kmap_def iget_def)

fun vfill_p :: \<open>indrep list \<Rightarrow> (bool \<times> (nat \<times> eff) list) list \<Rightarrow> indrep list \<Rightarrow> indrep list\<close> where
  \<open>vfill_p kav [] Rs = []\<close>
| \<open>vfill_p kav ((b, cs) # pl) Rs = (if b
     then (case Rs of [] \<Rightarrow> vfill_row kav cs (FinRep []) # vfill_p kav pl []
           | R # Rs' \<Rightarrow> vfill_row kav cs R # vfill_p kav pl Rs')
     else vfill_row kav cs (FinRep []) # vfill_p kav pl Rs)\<close>

definition vgo_k :: \<open>kentry \<Rightarrow> indrep list \<Rightarrow> indrep \<Rightarrow> (nat \<times> indrep list) option\<close> where
  \<open>vgo_k e av RA = (case e of (j', ks, pl) \<Rightarrow> let kav = map (\<lambda>(ps, q). cpre q RA (getR av ps)) ks in
     if list_ex irep_nonempty kav then Some (j', vfill_p kav pl kav) else None)\<close>

lemma vfill_p_zip:
  \<open>vfill_p K (map (\<lambda>(x, cs). (x \<noteq> None, g cs)) (zip km cts)) (map f (ksome km)) =
     map (\<lambda>(x, cs). vfill_row K (g cs) (case_option (FinRep []) f x)) (zip km cts)\<close>
proof (induction km arbitrary: cts)
  case (Cons x km)
  then show ?case by (cases cts; cases x) auto
qed simp

lemma length_ksome: \<open>length (ksome xs) \<le> length xs\<close>
  by (induction xs rule: ksome.induct) auto

lemma krank_getR:
  \<open>getR (map (case_option (FinRep []) f) km) kk = getR (map f (ksome km)) (krank km kk)\<close>
proof (induction km arbitrary: kk)
  case Nil
  then show ?case by (simp add: getR_def krank_def)
next
  case (Cons x km)
  have l: \<open>length (ksome km) \<le> length km\<close> by (rule length_ksome)
  show ?case
  proof (cases kk)
    case 0
    with l show ?thesis by (cases x) (auto simp: getR_def krank_def)
  next
    case (Suc k)
    have ih: \<open>getR (map (case_option (FinRep []) f) km) k = getR (map f (ksome km)) (krank km k)\<close>
      by (rule Cons.IH)
    show ?thesis
      using ih l by (cases x; cases \<open>kidx km k\<close>) (auto simp: Suc krank_def getR_def)
  qed
qed

lemma vfill_row_cong:
  \<open>(\<And>kk. getR K kk = getR K' (r kk)) \<Longrightarrow> vfill_row K cs acc = vfill_row K' (map (\<lambda>(kk, e). (r kk, e)) cs) acc\<close>
  by (induction K cs acc rule: vfill_row.induct) (simp_all add: Let_def)

lemma vgo_k_kconv: \<open>vgo_k (kconv V e) av RA = vgo V e av RA\<close>
proof (cases e)
  case (Pair j' km)
  let ?f = \<open>\<lambda>(ps, q). cpre q RA (getR av ps)\<close>
  have kav: \<open>vkav km av RA = map (case_option (FinRep []) ?f) km\<close>
    by (simp add: vkav_def)
  have live: \<open>list_ex irep_nonempty (map ?f (ksome km)) =
      list_ex irep_nonempty (map (case_option (FinRep []) ?f) km)\<close>
    by (induction km rule: ksome.induct) auto
  have row: \<open>fold (\<lambda>(kk, e) acc. cunion acc (eapp e (getR (map (case_option (FinRep []) ?f) km) kk))) cs R =
      vfill_row (map ?f (ksome km)) (map (\<lambda>(kk, e). (krank km kk, e)) cs) R\<close> for cs R
    unfolding vfill_row_fold[symmetric] by (rule vfill_row_cong[OF krank_getR])
  have fill: \<open>vfill cts (map (case_option (FinRep []) ?f) km) =
      vfill_p (map ?f (ksome km))
        (map (\<lambda>(x, cs). (x \<noteq> None, map (\<lambda>(kk, e). (krank km kk, e)) cs)) (zip km cts))
        (map ?f (ksome km))\<close> for cts
    unfolding vfill_p_zip vfill_def zip_map1 map_map
    by (rule map_cong) (auto simp: row)
  show ?thesis
    unfolding Pair vgo_k_def vgo_def kconv_def kav Let_def prod.case live fill ..
qed
subsection \<open>The fused run\<close>

text \<open>\<^const>\<open>vrun_un\<close> with a step taken in place: the shift when it is live, else
  the reduce candidates scanned in table order, without the list of candidates,
  the choice and the next state built between them.\<close>

datatype ('n, 't) vsres = VSConf | VSRej | VSRed \<open>'n \<times> ('n, 't) rhs\<close> vframes

definition vlive_k :: \<open>('n, 't) vktab \<Rightarrow> nat \<Rightarrow> indrep list \<Rightarrow> (nat \<times> nat) list \<Rightarrow> nat \<Rightarrow> bool\<close> where
  \<open>vlive_k K j av w s = (let RS = getR av s in irep_nonempty RS \<and> vlic_n (k_v K) j w s RS)\<close>

definition vred_k :: \<open>('n, 't) vktab \<Rightarrow> vframes \<Rightarrow> indrep list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'n \<times> ('n, 't) rhs \<Rightarrow>
    vframes option\<close> where
  \<open>vred_k K fs av s b pr = (let fs' = drop (length (snd pr)) fs in (case fs' of [] \<Rightarrow> None
     | (j\<^sub>0, av\<^sub>0) # _ \<Rightarrow> (case iget (iget (k_go K) j\<^sub>0 (IArray [])) b None of None \<Rightarrow> None
        | Some e \<Rightarrow> map_option (\<lambda>f. f # fs') (vgo_k e av\<^sub>0 (getR av s)))))\<close>

fun vscan_k :: \<open>('n, 't) vktab \<Rightarrow> vframes \<Rightarrow> (nat \<times> nat) list \<Rightarrow> nat \<Rightarrow> indrep list \<Rightarrow>
    (nat \<times> nat \<times> ('n \<times> ('n, 't) rhs)) list \<Rightarrow> ('n, 't) vsres\<close> where
  \<open>vscan_k K fs w j av [] = VSRej\<close>
| \<open>vscan_k K fs w j av ((s, b, pr) # cs) = (if vlive_k K j av w s
     then (case vred_k K fs av s b pr of None \<Rightarrow> vscan_k K fs w j av cs
       | Some fs' \<Rightarrow> if list_ex (\<lambda>(s, b, pr). vlive_k K j av w s \<and> vred_k K fs av s b pr \<noteq> None) cs
                    then VSConf else VSRed pr fs')
     else vscan_k K fs w j av cs)\<close>

definition vshift_k :: \<open>('n, 't) vktab \<Rightarrow> nat \<Rightarrow> indrep list \<Rightarrow> (nat \<times> nat) list \<Rightarrow> (nat \<times> indrep list) option\<close> where
  \<open>vshift_k K j av w = (case w of [] \<Rightarrow> None | (a, c) # _ \<Rightarrow>
     (case iget (iget (k_sh K) j (IArray [])) a None of None \<Rightarrow> None | Some e \<Rightarrow> vgo_k e av (FinRep [c])))\<close>

partial_function (option) vrun_k ::
  \<open>('n, 't) vktab \<Rightarrow> vframes \<Rightarrow> (nat \<times> nat) list \<Rightarrow> ('m, 'ch, 't) tword \<Rightarrow> ('m, 'ch, 'n, 't) ast list \<Rightarrow>
    ('m, 'ch, 'n, 't) ast option option\<close>
  where
  \<open>vrun_k K fs w v tstk = (if w = [] \<and> (case fs of [] \<Rightarrow> False
       | (j, av) # _ \<Rightarrow> irep_mem (v_ind0 (k_v K)) (getR av (iget (v_fin (k_v K)) j 0)))
     then Some (case tstk of t # _ \<Rightarrow> Some t | [] \<Rightarrow> None)
     else (case fs of [] \<Rightarrow> Some None | (j, av) # _ \<Rightarrow>
       (case vshift_k K j av w of
          Some f \<Rightarrow> vrun_k K (f # fs) (tl w) (tl v) (Leaf (hd v) # tstk)
        | None \<Rightarrow> (case vscan_k K fs w j av (iget (v_cp (k_v K)) j []) of
            VSConf \<Rightarrow> None
          | VSRej \<Rightarrow> Some None
          | VSRed pr fs' \<Rightarrow> vrun_k K fs' w v
              (Node (fst pr) (rev (take (length (snd pr)) tstk)) # drop (length (snd pr)) tstk)))))\<close>

lemmas vrun_k_simps [code] = vrun_k.simps

lemma k_v_mk [simp]: \<open>k_v (mk_vktab V) = V\<close>
  by (simp add: mk_vktab_def)

lemma vshift_k_vmstep:
  \<open>vshift_k (mk_vktab V) j av w = Some f \<Longrightarrow> vmstep_n V ((j, av) # fs, w) VShift = Some (f # (j, av) # fs, tl w)\<close>
  \<open>vshift_k (mk_vktab V) j av w = None \<Longrightarrow> vmstep_n V ((j, av) # fs, w) VShift = None\<close>
  by (auto simp: vshift_k_def vmstep_n_def mk_vktab_def iget_kmap vgo_k_kconv split: list.splits option.splits)
    (metis surj_pair)

lemma vred_k_vmstep:
  \<open>vmstep_n V ((j, av) # fs, w) (VReduce s b pr) =
     map_option (\<lambda>fs'. (fs', w)) (vred_k (mk_vktab V) ((j, av) # fs) av s b pr)\<close>
  by (auto simp: vred_k_def vmstep_n_def mk_vktab_def iget_kmap vgo_k_kconv Let_def option.map_comp comp_def
      split: list.splits option.splits)

lemma vscan_k_vchoose:
  fixes V :: \<open>('n, 't) vtab\<close> and j :: nat and av :: \<open>indrep list\<close> and w :: \<open>(nat \<times> nat) list\<close>
  defines \<open>ok \<equiv> \<lambda>(s :: nat, b :: nat, pr :: 'n \<times> ('n, 't) rhs). let RS = getR av s in irep_nonempty RS \<and> vlic_n V j w s RS\<close>
  shows \<open>vscan_k (mk_vktab V) ((j, av) # fs) w j av cs = VSRej \<Longrightarrow>
      vchoose_n V ((j, av) # fs, w) (map (\<lambda>(s, b, pr). VReduce s b pr) (filter ok cs)) = Some None\<close>
    and \<open>vscan_k (mk_vktab V) ((j, av) # fs) w j av cs = VSRed pr fs' \<Longrightarrow> \<exists>s b.
      vchoose_n V ((j, av) # fs, w) (map (\<lambda>(s, b, pr). VReduce s b pr) (filter ok cs)) =
        Some (Some (VReduce s b pr, fs', w))\<close>
proof (induction cs)
  case (Cons c cs)
  obtain s b p where c: \<open>c = (s, b, p)\<close> by (cases c)
  have lv: \<open>vlive_k (mk_vktab V) j av w s \<longleftrightarrow> ok (s, b, p)\<close>
    by (simp add: ok_def vlive_k_def)
  have ex: \<open>list_ex (\<lambda>b. vmstep_n V ((j, av) # fs, w) b \<noteq> None) (map (\<lambda>(s, b, pr). VReduce s b pr) (filter ok cs)) \<longleftrightarrow>
      list_ex (\<lambda>(s, b, pr). vlive_k (mk_vktab V) j av w s \<and> vred_k (mk_vktab V) ((j, av) # fs) av s b pr \<noteq> None) cs\<close>
    by (induction cs) (auto simp: vred_k_vmstep ok_def vlive_k_def)
  { case 1
    then show ?case using Cons.IH(1) lv ex
      by (auto simp: c vred_k_vmstep split: if_splits option.splits) }
  { case 2
    then show ?case using Cons.IH(2) lv ex
      by (auto simp: c vred_k_vmstep split: if_splits option.splits) }
qed simp_all

lemma vstep_un_k:
  fixes V :: \<open>('n, 't) vtab\<close>
  shows \<open>vshift_k (mk_vktab V) j av w = Some f \<Longrightarrow>
      vstep_un V ((j, av) # fs, w, v, tstk) = Some (Some (f # (j, av) # fs, tl w, tl v, Leaf (hd v) # tstk))\<close>
    and \<open>vshift_k (mk_vktab V) j av w = None \<Longrightarrow>
      vscan_k (mk_vktab V) ((j, av) # fs) w j av (iget (v_cp V) j []) = VSRej \<Longrightarrow>
      vstep_un V ((j, av) # fs, w, v, tstk) = Some None\<close>
    and \<open>vshift_k (mk_vktab V) j av w = None \<Longrightarrow>
      vscan_k (mk_vktab V) ((j, av) # fs) w j av (iget (v_cp V) j []) = VSRed pr fs' \<Longrightarrow>
      vstep_un V ((j, av) # fs, w, v, tstk) =
        Some (Some (fs', w, v, Node (fst pr) (rev (take (length (snd pr)) tstk)) # drop (length (snd pr)) tstk))\<close>
proof -
  let ?reds = \<open>map (\<lambda>(s, b, pr). VReduce s b pr) (filter (\<lambda>(s :: nat, b :: nat, pr :: 'n \<times> ('n, 't) rhs).
      let RS = getR av s in irep_nonempty RS \<and> vlic_n V j w s RS) (iget (v_cp V) j []))\<close>
  have none: \<open>vchoose_n V ((j, av) # fs, w) (vcands_n V j av w) = vchoose_n V ((j, av) # fs, w) ?reds\<close>
    if \<open>vshift_k (mk_vktab V) j av w = None\<close>
    using vshift_k_vmstep(2)[OF that, of fs] by (cases w) (simp_all add: vcands_n_def)
  { assume sh: \<open>vshift_k (mk_vktab V) j av w = Some f\<close>
    then have \<open>w \<noteq> []\<close> by (auto simp: vshift_k_def)
    then show \<open>vstep_un V ((j, av) # fs, w, v, tstk) = Some (Some (f # (j, av) # fs, tl w, tl v, Leaf (hd v) # tstk))\<close>
      using vshift_k_vmstep(1)[OF sh, of fs] by (cases w) (auto simp: vstep_un_def vcands_n_def) }
  { assume sh: \<open>vshift_k (mk_vktab V) j av w = None\<close>
      and sc: \<open>vscan_k (mk_vktab V) ((j, av) # fs) w j av (iget (v_cp V) j []) = VSRej\<close>
    show \<open>vstep_un V ((j, av) # fs, w, v, tstk) = Some None\<close>
      using vscan_k_vchoose(1)[OF sc] none[OF sh] by (simp add: vstep_un_def) }
  { assume sh: \<open>vshift_k (mk_vktab V) j av w = None\<close>
      and sc: \<open>vscan_k (mk_vktab V) ((j, av) # fs) w j av (iget (v_cp V) j []) = VSRed pr fs'\<close>
    show \<open>vstep_un V ((j, av) # fs, w, v, tstk) =
        Some (Some (fs', w, v, Node (fst pr) (rev (take (length (snd pr)) tstk)) # drop (length (snd pr)) tstk))\<close>
      using vscan_k_vchoose(2)[OF sc] none[OF sh] by (auto simp: vstep_un_def) }
qed

lemma vrun_k_sound:
  assumes run: \<open>vrun_k K fs w v tstk = Some r\<close>
  shows \<open>K = mk_vktab V \<longrightarrow> vrun_un V (fs, w, v, tstk) = Some r\<close>
proof (rule vrun_k.raw_induct[where P = \<open>\<lambda>K fs w v tstk r. K = mk_vktab V \<longrightarrow> vrun_un V (fs, w, v, tstk) = Some r\<close>,
    OF _ run], goal_cases)
  case (1 f K fs w v tstk r)
  show ?case
  proof
    assume K: \<open>K = mk_vktab V\<close>
    note body = "1"(2)[unfolded K k_v_mk]
    have fin: \<open>vfinal_n V (fs, w, v, tstk) \<longleftrightarrow> w = [] \<and> (case fs of [] \<Rightarrow> False
        | (j, av) # _ \<Rightarrow> irep_mem (v_ind0 V) (getR av (iget (v_fin V) j 0)))\<close>
      by (simp add: vfinal_n_def)
    show \<open>vrun_un V (fs, w, v, tstk) = Some r\<close>
    proof (cases \<open>vfinal_n V (fs, w, v, tstk)\<close>)
      case True
      with body fin show ?thesis by (subst vrun_un.simps) simp
    next
      case nf: False
      show ?thesis
      proof (cases fs)
        case Nil
        with nf body fin show ?thesis by (subst vrun_un.simps) (simp add: vstep_un_def)
      next
        case (Cons fr fs\<^sub>1)
        obtain j av where fr: \<open>fr = (j, av)\<close> by (cases fr)
        note body = body[unfolded Cons fr]
        note nf' = nf[unfolded Cons fr]
        have nfin: \<open>\<not> (w = [] \<and> irep_mem (v_ind0 V) (getR av (iget (v_fin V) j 0)))\<close>
          using nf' fin[unfolded Cons fr] by simp
        show ?thesis
        proof (cases \<open>vshift_k (mk_vktab V) j av w\<close>)
          case (Some f')
          from nfin Some body have \<open>f K (f' # (j, av) # fs\<^sub>1) (tl w) (tl v) (Leaf (hd v) # tstk) = Some r\<close>
            by (cases w) (simp_all add: K)
          with "1"(1) K have \<open>vrun_un V (f' # (j, av) # fs\<^sub>1, tl w, tl v, Leaf (hd v) # tstk) = Some r\<close>
            by blast
          with nf' show ?thesis
            unfolding Cons fr by (subst vrun_un.simps) (simp add: vstep_un_k(1)[OF Some, of fs\<^sub>1 v tstk])
        next
          case sh: None
          show ?thesis
          proof (cases \<open>vscan_k (mk_vktab V) ((j, av) # fs\<^sub>1) w j av (iget (v_cp V) j [])\<close>)
            case VSConf
            from nfin sh VSConf body show ?thesis by (cases w) (simp_all add: K)
          next
            case VSRej
            from nfin sh VSRej body have \<open>r = None\<close> by (cases w) (simp_all add: K)
            with nf' show ?thesis
              unfolding Cons fr by (subst vrun_un.simps) (simp add: vstep_un_k(2)[OF sh VSRej, of v tstk])
          next
            case (VSRed pr fs')
            from nfin sh VSRed body have \<open>f K fs' w v
                (Node (fst pr) (rev (take (length (snd pr)) tstk)) # drop (length (snd pr)) tstk) = Some r\<close>
              by (cases w) (simp_all add: K)
            with "1"(1) K have \<open>vrun_un V (fs', w, v,
                Node (fst pr) (rev (take (length (snd pr)) tstk)) # drop (length (snd pr)) tstk) = Some r\<close>
              by blast
            with nf' show ?thesis
              unfolding Cons fr by (subst vrun_un.simps) (simp add: vstep_un_k(3)[OF sh VSRed, of v tstk])
          qed
        qed
      qed
    qed
  qed
qed

text \<open>The parser for the code generator: \<^const>\<open>vrun_k\<close> over the kernel-only tables,
  and the sparse driver should it meet a conflict.\<close>

lemma dparse_via_tables_vk:
  assumes st: \<open>pr0_states G Shn = sts\<close>
    and gt: \<open>pgtab G sts = gtab\<close>
    and rt: \<open>red_buckets G Shn (length sts) = redtab\<close>
    and i0: \<open>st_find sts (lr0_start G Shn) = i\<^sub>0\<close>
    and fr: \<open>fresh_name G Shn\<close>
    and tb: \<open>mk_stab G Shn gtab sts redtab = stb\<close>
    and vt: \<open>mk_vtab G Shn stb sts gtab redtab = vtb\<close>
    and kt: \<open>mk_vktab vtb = vktb\<close>
    and ki: \<open>sinit stb = kin\<close>
    and kc: \<open>sclosure stb kin = kcl\<close>
  shows \<open>dparse G Shn w = (case vrun_k vktb [v_av0 vtb] (vtcols vtb w) w [] of
      Some r \<Rightarrow> r | None \<Rightarrow> sdrun stb (([kin], tcols w), [kcl], [i\<^sub>0], w, []))\<close>
proof (cases \<open>vrun_k vktb [v_av0 vtb] (vtcols vtb w) w []\<close>)
  case None
  then show ?thesis using dparse_via_tables_s[OF st gt rt i0 fr tb ki kc] by simp
next
  case (Some r)
  have \<open>vrun_un vtb ([v_av0 vtb], vtcols vtb w, w, []) = Some r\<close>
    using vrun_k_sound[OF Some] kt by simp
  then show ?thesis
    using dparse_via_tables_vun[OF st gt rt i0 fr tb vt ki kc, of w] Some by simp
qed

text \<open>The numbers of some tokens, from the tokens of the tables alone: no table has
  to be built to know them. The backend evaluates them with its checks, so that a
  token type of constructors without arguments is numbered by a case distinction
  rather than a search through \<^const>\<open>v_lal\<close>.\<close>

definition vnums :: \<open>('n, 't) is_cfg \<Rightarrow> 'n \<Rightarrow> 't list \<Rightarrow> nat list\<close> where
  \<open>vnums G Shn ctrs =
     map (ntidx (vtoks G (red_buckets G Shn (length (pr0_states G Shn))))) ctrs\<close>

lemma vnums_map:
  assumes st: \<open>pr0_states G Shn = sts\<close>
    and rt: \<open>red_buckets G Shn (length sts) = redtab\<close>
    and vt: \<open>mk_vtab G Shn stb sts gtab redtab = vtb\<close>
    and ns: \<open>vnums G Shn ctrs = ns\<close>
  shows \<open>map (vnum vtb) ctrs = ns\<close>
proof -
  have \<open>vnum vtb = ntidx (vtoks G redtab)\<close>
    by (rule ext) (rule vnum_mk[OF vt[symmetric]])
  then show ?thesis unfolding ns[symmetric] vnums_def st rt by simp
qed

definition vtnum :: \<open>('t \<Rightarrow> nat) \<Rightarrow> ('m, 'ch, 't) tword \<Rightarrow> (nat \<times> nat) list\<close> where
  \<open>vtnum f w = map (\<lambda>t. (f (tok t), s_col (span t))) w\<close>

lemma vtcols_vtnum: \<open>vtcols V w = vtnum (vnum V) w\<close>
  by (simp add: vtcols_def vtnum_def)

lemma dparse_via_tables_vkn:
  assumes st: \<open>pr0_states G Shn = sts\<close>
    and gt: \<open>pgtab G sts = gtab\<close>
    and rt: \<open>red_buckets G Shn (length sts) = redtab\<close>
    and i0: \<open>st_find sts (lr0_start G Shn) = i\<^sub>0\<close>
    and fr: \<open>fresh_name G Shn\<close>
    and tb: \<open>mk_stab G Shn gtab sts redtab = stb\<close>
    and vt: \<open>mk_vtab G Shn stb sts gtab redtab = vtb\<close>
    and kt: \<open>mk_vktab vtb = vktb\<close>
    and ki: \<open>sinit stb = kin\<close>
    and kc: \<open>sclosure stb kin = kcl\<close>
    and tn: \<open>vnum vtb = f\<close>
  shows \<open>dparse G Shn w = (case vrun_k vktb [v_av0 vtb] (vtnum f w) w [] of
      Some r \<Rightarrow> r | None \<Rightarrow> sdrun stb (([kin], tcols w), [kcl], [i\<^sub>0], w, []))\<close>
  unfolding tn[symmetric] vtcols_vtnum[symmetric]
  by (rule dparse_via_tables_vk[OF st gt rt i0 fr tb vt kt ki kc])

section \<open>Building the tables once\<close>

text \<open>\<^const>\<open>mk_vtab\<close> states each entry on its own, which the proofs want and the
  code generator should not follow: \<^const>\<open>vits\<close> runs a closure per state, token and
  nonterminal, and \<^const>\<open>trow\<close> a fixpoint per contribution.  Its code equation
  computes the closures and the transfer rows once, and the edges of the transfer
  graph once for all rows.\<close>

definition tr_step_c :: \<open>('n, 't) stab \<Rightarrow> (nat \<times> irel) list iarray \<Rightarrow> eff list \<Rightarrow> eff list\<close> where
  \<open>tr_step_c T ti row = map (\<lambda>a. fold ejoin (map (\<lambda>(c, q). ecomp (of_rel q) (row ! c)) (ti !! a)) (row ! a))
     [0..<s_np T]\<close>

lemma tr_step_c: \<open>tr_step_c T (IArray (map (tin T) [0..<s_np T])) = tr_step T\<close>
  by (auto simp: fun_eq_iff tr_step_c_def tr_step_def)

definition trows :: \<open>('n, 't) stab \<Rightarrow> eff list iarray\<close> where
  \<open>trows T = (let ti = IArray (map (tin T) [0..<s_np T]) in
     IArray (map (\<lambda>b. the (while_option (\<lambda>row. tr_step_c T ti row \<noteq> row) (tr_step_c T ti)
       (tinit (s_np T) b))) [0..<s_np T]))\<close>

definition vrow :: \<open>eff list iarray \<Rightarrow> ('n, 't) stab \<Rightarrow> nat \<Rightarrow> eff list\<close> where
  \<open>vrow R T b = (if b < IArray.length R then R !! b else trow T b)\<close>

lemma vrow_trows: \<open>vrow (trows T) T b = trow T b\<close>
  by (simp add: vrow_def trows_def tr_step_c trow_def trow_loop_def)

definition vcontrib_c :: \<open>('n, 't) is_cfg \<Rightarrow> 'n \<Rightarrow> ('n, 't) stab \<Rightarrow> eff list iarray \<Rightarrow>
    ('n, 't) citem list \<Rightarrow> ('n, 't) citem \<Rightarrow> (nat \<times> eff) list\<close> where
  \<open>vcontrib_c G Shn T R its it = (if is_slot G it then
     List.map_filter (\<lambda>kk. if is_slot G (its ! kk) then None else
       (case vnext_nt G (its ! kk) of None \<Rightarrow> None
        | Some (B, q) \<Rightarrow> Some (kk, ecomp (vrow R T (nnum G Shn B) ! nnum G Shn (fst (fst it))) (of_rel q))))
       [0..<length its]
   else [])\<close>

lemma vcontrib_c: \<open>vcontrib_c G Shn T (trows T) = vcontrib G Shn T\<close>
  unfolding vcontrib_c_def[abs_def] vcontrib_def[abs_def] vrow_trows ..

definition vits_tab :: \<open>('n, 't) is_cfg \<Rightarrow> ('n, 't) citem list list \<Rightarrow> ('n, 't) citem list iarray\<close> where
  \<open>vits_tab G sts = IArray (map (vits G sts) [0..<length sts])\<close>

lemma vits_tab: \<open>iget (vits_tab G sts) j [] = vits G sts j\<close>
  by (simp add: iget_def vits_tab_def vits_def)

definition ventry_c :: \<open>(('n, 't) sym \<times> nat) list list \<Rightarrow> ('n, 't) citem list list \<Rightarrow>
    ('n, 't) citem list iarray \<Rightarrow> nat \<Rightarrow> ('n, 't) sym \<Rightarrow> (nat \<times> (nat \<times> irel) option list) option\<close> where
  \<open>ventry_c gt sts A j X = (let j' = dnext gt sts j X in
     if j' < length sts then Some (j', vkmap (iget A j []) X (iget A j' [])) else None)\<close>

lemma ventry_c: \<open>ventry_c gt sts (vits_tab G sts) = ventry G gt sts\<close>
  by (simp add: fun_eq_iff ventry_c_def ventry_def vits_tab Let_def)

definition vinit_frame_c :: \<open>('n, 't) is_cfg \<Rightarrow> 'n \<Rightarrow> ('n, 't) stab \<Rightarrow> eff list iarray \<Rightarrow>
    ('n, 't) citem list list \<Rightarrow> ('n, 't) citem list iarray \<Rightarrow> nat \<times> indrep list\<close> where
  \<open>vinit_frame_c G Shn T R sts A = (let i\<^sub>0 = st_find sts (lr0_start G Shn); its = iget A i\<^sub>0 [] in
     (i\<^sub>0, vfill (map (vcontrib_c G Shn T R its) its)
       (map (\<lambda>it. if it = (start_prod G Shn, 0) then FinRep [istart_ind G] else FinRep []) its)))\<close>

lemma vinit_frame_c: \<open>vinit_frame_c G Shn T (trows T) sts (vits_tab G sts) = vinit_frame G Shn T sts\<close>
  by (simp add: vinit_frame_c_def vinit_frame_def vits_tab vcontrib_c Let_def)

lemma mk_vtab_code [code]:
  \<open>mk_vtab G Shn T sts gt redtab = (let toks = vtoks G redtab; ns = [0..<length sts];
       ps = eprods G Shn; A = vits_tab G sts; R = trows T in
     VTab (zip toks [0..<length toks]) (length toks)
       (IArray (map (\<lambda>j. IArray (map (\<lambda>a. ventry_c gt sts A j (Tm a)) toks)) ns))
       (IArray (map (\<lambda>j. IArray (map (\<lambda>b. ventry_c gt sts A j (Nt (fst (ps ! b)))) [0..<length ps])) ns))
       (IArray (map (\<lambda>j. let its = iget A j [] in map (vcontrib_c G Shn T R its) its) ns))
       (IArray (map (\<lambda>j. vcomps G Shn (iget A j [])) ns))
       (IArray (map (\<lambda>j. let its = iget A j [] in
          IArray (map (\<lambda>a. vcells its j (redtab ! j) (Some a)) toks)) ns))
       (IArray (map (\<lambda>j. map fst (vcells (iget A j []) j (redtab ! j) None)) ns))
       (IArray (map (\<lambda>j. ntidx (iget A j []) (start_prod G Shn, 1)) ns))
       (vinit_frame_c G Shn T R sts A)
       (istart_ind G))\<close>
  by (simp add: mk_vtab_def Let_def ventry_c vcontrib_c vits_tab vinit_frame_c)

text \<open>The two names are too short to keep from later theories' variables.\<close>

hide_const (open) sh cn

end
