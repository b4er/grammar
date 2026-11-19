(* Author: Basil Fürer *)

theory LR_Lab
  imports LR_Arr
begin

section \<open>Integer labels\<close>

text \<open>The trees of a run carry the names of the nonterminals, and a decoder
  compares the name of every node with the name of its nonterminal. Names are
  strings or naturals, and in the code a string is a list of characters, so these
  comparisons cost more than the run itself. Here the arrays of LR_Arr carry
  integers instead, the position of each name in a list of names computed once,
  and the run builds trees over integers. A decoder over such trees compares
  integers. It is the decoder composed with the map back to names
  (\<^term>\<open>dec \<circ> relab (lnm ns)\<close>), so the code equation of a parser can run on the
  integer arrays and the integer decoders with the same result. The diagnostics
  keep the run on names.\<close>

subsection \<open>Relabelling\<close>

primrec relab :: \<open>('n \<Rightarrow> 'n') \<Rightarrow> ('m, 'ch, 'n, 't) ast \<Rightarrow> ('m, 'ch, 'n', 't) ast\<close> where
  \<open>relab h (Leaf t) = Leaf t\<close>
| \<open>relab h (Node n xs) = Node (h n) (map (relab h) xs)\<close>

lemma relab_relab: \<open>relab h (relab g t) = relab (h \<circ> g) t\<close>
  by (induction t) auto

lemma case_list_map:
  \<open>(case map f xs of [] \<Rightarrow> a | y # ys \<Rightarrow> g y ys) = (case xs of [] \<Rightarrow> a | y # ys \<Rightarrow> g (f y) (map f ys))\<close>
  by (cases xs) simp_all

lemma case_ast_relab:
  \<open>(case relab h c of Leaf t \<Rightarrow> f t | Node n ys \<Rightarrow> g n ys) =
    (case c of Leaf t \<Rightarrow> f t | Node n ys \<Rightarrow> g (h n) (map (relab h) ys))\<close>
  by (cases c) simp_all

definition rhs_lab :: \<open>('n \<Rightarrow> 'n') \<Rightarrow> ('n, 't) rhs \<Rightarrow> ('n', 't) rhs\<close> where
  \<open>rhs_lab h = map (\<lambda>(s, r). (map_sym h id s, r))\<close>

definition pr_lab :: \<open>('n \<Rightarrow> 'n') \<Rightarrow> 'n \<times> ('n, 't) rhs \<Rightarrow> 'n' \<times> ('n', 't) rhs\<close> where
  \<open>pr_lab h pr = (h (fst pr), rhs_lab h (snd pr))\<close>

lemma length_rhs_lab [simp]: \<open>length (rhs_lab h r) = length r\<close>
  by (simp add: rhs_lab_def)

lemma pr_lab_comp: \<open>pr_lab h (pr_lab g pr) = pr_lab (h \<circ> g) pr\<close>
  by (simp add: pr_lab_def rhs_lab_def sym.map_comp split_beta)

lemma pr_lab_id: \<open>pr_lab id pr = pr\<close>
  by (simp add: pr_lab_def rhs_lab_def sym.map_id split_beta)

primrec aact_lab :: \<open>('n \<Rightarrow> 'n') \<Rightarrow> ('n, 't) aact \<Rightarrow> ('n', 't) aact\<close> where
  \<open>aact_lab h (AShift k) = AShift k\<close>
| \<open>aact_lab h (AReduce pr B) = AReduce (pr_lab h pr) B\<close>

primrec dact_lab :: \<open>('n \<Rightarrow> 'n') \<Rightarrow> ('n, 't) dact \<Rightarrow> ('n', 't) dact\<close> where
  \<open>dact_lab h DShift = DShift\<close>
| \<open>dact_lab h (DReduce pr) = DReduce (pr_lab h pr)\<close>

lemma xtree_lab:
  \<open>xtree dec (dact_lab h a) v (map (relab h) ts) = map (relab h) (xtree dec a v ts)\<close>
  by (cases a) (simp_all add: xtree_def pr_lab_def take_as_eq drop_as_eq take_map drop_map rev_map)

lemma sresult_map: \<open>sresult (map f ts) = map_option f (sresult ts)\<close>
  by (simp add: sresult_def split: list.split)

subsection \<open>Relabelled arrays\<close>

lemma nat_of_integer_zi [simp]: \<open>nat_of_integer (zi k) = k\<close>
  by (metis nat_of_integer_integer_of_nat)

lemma zi_nat_of_integer: \<open>0 \<le> i \<Longrightarrow> zi (nat_of_integer i) = i\<close>
  by (simp add: integer_eq_iff integer_of_nat.rep_eq nat_of_integer.rep_eq less_eq_integer.rep_eq)

lemma less_zi: \<open>0 \<le> i \<Longrightarrow> i < zi n \<longleftrightarrow> nat_of_integer i < n\<close>
  by (simp add: less_integer.rep_eq less_eq_integer.rep_eq integer_of_nat.rep_eq
      nat_of_integer.rep_eq nat_less_iff)

definition amap :: \<open>('a \<Rightarrow> 'b) \<Rightarrow> 'a option iarray \<Rightarrow> 'b option iarray\<close> where
  \<open>amap f a = IArray (map (map_option f) (IArray.list_of a))\<close>

lemma aget_amap: \<open>aget (amap f a) i = map_option f (aget a i)\<close>
  by (auto simp: aget_def amap_def less_zi)

lemma amap_amap: \<open>amap f (amap g a) = amap (f \<circ> g) a\<close>
  by (simp add: amap_def option.map_comp comp_def)

lemma amap_comp_amap: \<open>amap f \<circ> amap g = amap (f \<circ> g)\<close>
  by (rule ext) (simp add: amap_amap)

lemma amap_id: \<open>amap id = id\<close>
  by (rule ext) (case_tac x; simp add: amap_def option.map_id0)

lemma aget2_amap: \<open>aget2 (amap (amap f) a) i j = map_option f (aget2 a i j)\<close>
  by (simp add: aget2_def aget_amap aget_amap split: option.split)

definition alab :: \<open>('n \<Rightarrow> 'n') \<Rightarrow> ('n, 't) atabs \<Rightarrow> ('n', 't) atabs\<close> where
  \<open>alab h A = ATabs (at_lal A) (at_miss A) (amap (amap (map (aact_lab h))) (at_A A))
     (amap (map (aact_lab h)) (at_E A)) (at_N A) (at_pf A)\<close>

text \<open>All actions of the arrays, and the names they reduce to.\<close>

definition oelems :: \<open>'a list option list \<Rightarrow> 'a list\<close> where
  \<open>oelems xs = concat (map (\<lambda>x. case x of None \<Rightarrow> [] | Some es \<Rightarrow> es) xs)\<close>

definition aacts :: \<open>('n, 't) atabs \<Rightarrow> ('n, 't) aact list\<close> where
  \<open>aacts A = concat (map (\<lambda>x. case x of None \<Rightarrow> [] | Some r \<Rightarrow> oelems (IArray.list_of r))
       (IArray.list_of (at_A A))) @ oelems (IArray.list_of (at_E A))\<close>

definition pr_names :: \<open>'n \<times> ('n, 't) rhs \<Rightarrow> 'n list\<close> where
  \<open>pr_names pr = fst pr # concat (map (\<lambda>(s, _). case s of Nt n \<Rightarrow> [n] | Tm _ \<Rightarrow> []) (snd pr))\<close>

definition addn :: \<open>'n \<Rightarrow> 'n list \<Rightarrow> 'n list\<close> where
  \<open>addn n acc = (if n \<in> set acc then acc else n # acc)\<close>

lemma set_fold_addn: \<open>set (fold addn ns acc) = set acc \<union> set ns\<close>
  by (induction ns arbitrary: acc) (auto simp: addn_def)

primrec alabel :: \<open>('n, 't) aact \<Rightarrow> 'n list \<Rightarrow> 'n list\<close> where
  \<open>alabel (AShift _) acc = acc\<close>
| \<open>alabel (AReduce pr _) acc = fold addn (pr_names pr) acc\<close>

lemma pr_lab_cong:
  \<open>(\<And>n. n \<in> set (pr_names pr) \<Longrightarrow> f n = g n) \<Longrightarrow> pr_lab f pr = pr_lab g pr\<close>
  apply (cases pr)
  apply (auto simp: pr_lab_def rhs_lab_def pr_names_def intro!: map_cong)
  subgoal for a b s r by (cases s) force+
  done

definition alabels :: \<open>('n, 't) atabs \<Rightarrow> 'n list\<close> where
  \<open>alabels A = fold alabel (aacts A) []\<close>

lemma set_fold_alabel:
  \<open>AReduce pr B \<in> set as \<Longrightarrow> n \<in> set (pr_names pr) \<Longrightarrow> n \<in> set (fold alabel as acc)\<close>
proof (induction as arbitrary: acc)
  case (Cons a as)
  have mono: \<open>set acc \<subseteq> set (alabel a acc)\<close> for acc
    by (cases a) (auto simp: set_fold_addn)
  have keep: \<open>set acc \<subseteq> set (fold alabel as acc)\<close> for acc as
  proof (induction as arbitrary: acc)
    case (Cons b bs)
    have \<open>set acc \<subseteq> set (alabel b acc)\<close> by (cases b) (auto simp: set_fold_addn)
    with Cons.IH[of \<open>alabel b acc\<close>] show ?case by simp
  qed simp
  show ?case
  proof (cases \<open>a = AReduce pr B\<close>)
    case True
    with Cons.prems keep[of \<open>alabel a acc\<close> as] show ?thesis by (auto simp: set_fold_addn)
  next
    case False
    with Cons show ?thesis by simp
  qed
qed simp

lemma alabels_mem: \<open>AReduce pr B \<in> set (aacts A) \<Longrightarrow> n \<in> set (pr_names pr) \<Longrightarrow> n \<in> set (alabels A)\<close>
  unfolding alabels_def by (rule set_fold_alabel)

lemma aacts_alab: \<open>aacts (alab h A) = map (aact_lab h) (aacts A)\<close>
  by (simp add: aacts_def alab_def amap_def oelems_def map_concat comp_def
      option.case_distrib[where h = \<open>map (aact_lab h)\<close>]
      option.case_distrib[where h = \<open>\<lambda>r. oelems (IArray.list_of r)\<close>]
      cong: option.case_cong)

lemma amap_cong:
  assumes \<open>\<And>x. Some x \<in> set (IArray.list_of a) \<Longrightarrow> f x = g x\<close>
  shows \<open>amap f a = amap g a\<close>
proof -
  have \<open>map_option f x = map_option g x\<close> if \<open>x \<in> set (IArray.list_of a)\<close> for x
  proof (cases x)
    case (Some y)
    then show ?thesis using that assms by simp
  qed simp
  then show ?thesis unfolding amap_def by (simp cong: map_cong)
qed

lemma alab_cong:
  assumes \<open>\<And>a. a \<in> set (aacts A) \<Longrightarrow> aact_lab f a = aact_lab g a\<close>
  shows \<open>alab f A = alab g A\<close>
proof -
  have e: \<open>map (aact_lab f) es = map (aact_lab g) es\<close> if \<open>\<And>a. a \<in> set es \<Longrightarrow> a \<in> set (aacts A)\<close> for es
    using assms that by (auto intro!: map_cong)
  have A: \<open>amap (amap (map (aact_lab f))) (at_A A) = amap (amap (map (aact_lab g))) (at_A A)\<close>
    by (rule amap_cong, rule amap_cong, rule e)
      (force simp: aacts_def oelems_def)
  have E: \<open>amap (map (aact_lab f)) (at_E A) = amap (map (aact_lab g)) (at_E A)\<close>
    by (rule amap_cong, rule e) (force simp: aacts_def oelems_def)
  show ?thesis unfolding alab_def A E ..
qed

lemma aact_lab_comp: \<open>aact_lab h (aact_lab g a) = aact_lab (h \<circ> g) a\<close>
  by (cases a) (simp_all add: pr_lab_comp)

lemma alab_alab: \<open>alab h (alab g A) = alab (h \<circ> g) A\<close>
proof -
  have c: \<open>aact_lab h \<circ> aact_lab g = aact_lab (h \<circ> g)\<close>
    by (rule ext) (simp add: aact_lab_comp)
  show ?thesis by (simp add: alab_def amap_amap amap_comp_amap map_comp_map c)
qed

lemma alab_id: \<open>alab id A = A\<close>
proof -
  have ai: \<open>aact_lab id x = x\<close> for x by (cases x) (simp_all add: pr_lab_id)
  have a1: \<open>map (aact_lab id) = id\<close> by (rule ext, induct_tac x) (simp_all add: ai ai[unfolded id_def])
  have a2: \<open>amap (map (aact_lab id)) = id\<close> by (simp add: a1 amap_id)
  have a3: \<open>amap (amap (map (aact_lab id))) = id\<close> by (simp add: a2 amap_id)
  show ?thesis by (cases A) (simp add: alab_def a2 a3 amap_id)
qed

lemma acands_alab: \<open>acands (alab h A) k l = map (aact_lab h) (acands A k l)\<close>
  by (simp add: acands_def alab_def aget2_amap split: option.split)

lemma aecands_alab: \<open>aecands (alab h A) k = map (aact_lab h) (aecands A k)\<close>
  by (simp add: aecands_def alab_def aget_amap split: option.split)

lemma atarget_alab:
  \<open>atarget (alab h A) kstk (aact_lab h a) = map_option (\<lambda>(d, s). (dact_lab h d, s)) (atarget A kstk a)\<close>
  by (cases a)
    (simp_all add: atarget_def pr_lab_def drop_as_eq alab_def option.map_comp comp_def
      split: list.split)

lemma sfind_atarget_alab:
  \<open>sfind (atarget (alab h A) kstk) (map (aact_lab h) xs) =
    map_option (\<lambda>(d, s). (dact_lab h d, s)) (sfind (atarget A kstk) xs)\<close>
  unfolding sfind_map o_def atarget_alab sfind_map_option ..

lemma actl_alab: \<open>actl (alab h A) c = map_option (\<lambda>(a, r). (dact_lab h a, r)) (actl A c)\<close>
  by (auto simp: actl_def acands_alab aecands_alab sfind_atarget_alab option.map_comp comp_def
      split_beta split: list.split prod.split dact.split
      intro!: option.map_cong0)

lemma afinal_alab: \<open>afinal (alab h A) = afinal A\<close>
  by (rule ext) (simp add: afinal_def alab_def split: prod.split list.split)

subsection \<open>The run over relabelled arrays\<close>

lemma nrun_map:
  assumes ctl: \<open>\<And>c. ctl2 c = map_option (\<lambda>(a, r). (H a, r)) (ctl1 c)\<close>
    and fin: \<open>\<And>c. fin2 c = fin1 c\<close>
    and xt: \<open>\<And>a v ts. xtree dec (H a) v (map R ts) = map R (xtree dec a v ts)\<close>
    and sr: \<open>\<And>ts. sresult (map R ts) = map_option R (sresult ts)\<close>
  shows \<open>nrun ctl2 fin2 dec (stk, v, map R ts) = map_option R (nrun ctl1 fin1 dec (stk, v, ts))\<close>
proof -
  have one: \<open>nrun ctl2 fin2 dec (fst st, fst (snd st), map R (snd (snd st))) = Some (R t)\<close>
    if h: \<open>nrun ctl1 fin1 dec st = Some t\<close> for st t
  proof -
    have \<open>ctl1 = ctl1 \<longrightarrow> fin1 = fin1 \<longrightarrow> dec = dec \<longrightarrow>
        nrun ctl2 fin2 dec (fst st, fst (snd st), map R (snd (snd st))) = Some (R t)\<close>
    proof (rule nrun.raw_induct[OF _ h, where P = \<open>\<lambda>c f d st t. c = ctl1 \<longrightarrow> f = fin1 \<longrightarrow> d = dec \<longrightarrow>
        nrun ctl2 fin2 dec (fst st, fst (snd st), map R (snd (snd st))) = Some (R t)\<close>], goal_cases)
      case (1 F c f d st t)
      obtain stk v ts where st: \<open>st = (stk, v, ts)\<close> by (cases st)
      show ?case
      proof (intro impI)
        assume c: \<open>c = ctl1\<close> and f: \<open>f = fin1\<close> and d: \<open>d = dec\<close>
        show \<open>nrun ctl2 fin2 dec (fst st, fst (snd st), map R (snd (snd st))) = Some (R t)\<close>
        proof (cases \<open>fin1 (stk, v)\<close>)
          case True
          with "1"(2) show ?thesis unfolding st c f
            by (subst nrun.simps) (auto simp: fin sr)
        next
          case False
          from False "1"(2) obtain a stk' v' where
              sc: \<open>ctl1 (stk, v) = Some (a, stk', v')\<close>
            and rec: \<open>F c f d (stk', v', xtree d a v ts) = Some t\<close>
            unfolding st c f by (auto simp: bind_eq_Some_conv)
          from "1"(1)[OF rec] c f d
          have \<open>nrun ctl2 fin2 dec (stk', v', map R (xtree dec a v ts)) = Some (R t)\<close> by simp
          then show ?thesis unfolding st using False sc
            by (subst nrun.simps) (simp add: fin ctl xt)
        qed
      qed
    qed
    then show ?thesis by blast
  qed
  have two: \<open>\<exists>t'. t = R t' \<and> nrun ctl1 fin1 dec (stk, v, ts) = Some t'\<close>
    if h: \<open>nrun ctl2 fin2 dec st2 = Some t\<close> and e: \<open>st2 = (stk, v, map R ts)\<close> for st2 t stk v ts
  proof -
    have \<open>ctl2 = ctl2 \<longrightarrow> fin2 = fin2 \<longrightarrow> dec = dec \<longrightarrow> (\<forall>stk v ts.
        st2 = (stk, v, map R ts) \<longrightarrow> (\<exists>t'. t = R t' \<and> nrun ctl1 fin1 dec (stk, v, ts) = Some t'))\<close>
    proof (rule nrun.raw_induct[OF _ h, where P = \<open>\<lambda>c f d st2 t. c = ctl2 \<longrightarrow> f = fin2 \<longrightarrow> d = dec \<longrightarrow>
        (\<forall>stk v ts. st2 = (stk, v, map R ts) \<longrightarrow>
          (\<exists>t'. t = R t' \<and> nrun ctl1 fin1 dec (stk, v, ts) = Some t'))\<close>], goal_cases)
      case (1 F c f d st2 t)
      show ?case
      proof (intro impI allI)
        fix stk v ts
        assume c: \<open>c = ctl2\<close> and f: \<open>f = fin2\<close> and d: \<open>d = dec\<close>
          and st: \<open>st2 = (stk, v, map R ts)\<close>
        show \<open>\<exists>t'. t = R t' \<and> nrun ctl1 fin1 dec (stk, v, ts) = Some t'\<close>
        proof (cases \<open>fin1 (stk, v)\<close>)
          case True
          with "1"(2) show ?thesis unfolding st c f
            by (subst nrun.simps) (auto simp: fin sr)
        next
          case False
          from False "1"(2) obtain a stk' v' where
              sc: \<open>ctl2 (stk, v) = Some (a, stk', v')\<close>
            and rec: \<open>F c f d (stk', v', xtree d a v (map R ts)) = Some t\<close>
            unfolding st c f by (auto simp: bind_eq_Some_conv fin)
          from sc obtain a1 where sc1: \<open>ctl1 (stk, v) = Some (a1, stk', v')\<close> and a: \<open>a = H a1\<close>
            unfolding ctl by (auto split: prod.splits)
          have \<open>\<exists>t'. t = R t' \<and> nrun ctl1 fin1 dec (stk', v', xtree dec a1 v ts) = Some t'\<close>
            using "1"(1)[OF rec] c f d a xt by simp
          then show ?thesis using False sc1 by (subst nrun.simps) simp
        qed
      qed
    qed
    then show ?thesis using e by blast
  qed
  show ?thesis
  proof (cases \<open>nrun ctl1 fin1 dec (stk, v, ts)\<close>)
    case None
    have \<open>nrun ctl2 fin2 dec (stk, v, map R ts) = None\<close>
    proof (rule ccontr)
      assume \<open>nrun ctl2 fin2 dec (stk, v, map R ts) \<noteq> None\<close>
      then obtain t where \<open>nrun ctl2 fin2 dec (stk, v, map R ts) = Some t\<close> by blast
      from two[OF this refl] None show False by auto
    qed
    with None show ?thesis by simp
  next
    case (Some t)
    then show ?thesis using one[OF Some] by simp
  qed
qed

lemma nrun_alab:
  \<open>nrun (actl (alab h A)) (afinal (alab h A)) dec (stk, v, map (relab h) ts) =
    map_option (relab h) (nrun (actl A) (afinal A) dec (stk, v, ts))\<close>
  by (rule nrun_map[OF _ _ xtree_lab sresult_map]) (simp_all add: actl_alab afinal_alab)

lemma nrun_alab_Nil:
  \<open>nrun (actl (alab h A)) (afinal (alab h A)) dec (stk, v, []) =
    map_option (relab h) (nrun (actl A) (afinal A) dec (stk, v, []))\<close>
  using nrun_alab[of h A dec stk v \<open>[]\<close>] by simp

subsection \<open>Names as integers\<close>

primrec nix :: \<open>'n list \<Rightarrow> 'n \<Rightarrow> nat\<close> where
  \<open>nix [] n = 0\<close>
| \<open>nix (x # xs) n = (if x = n then 0 else Suc (nix xs n))\<close>

definition lix :: \<open>'n list \<Rightarrow> 'n \<Rightarrow> integer\<close> where
  \<open>lix ns n = zi (nix ns n)\<close>

lemma lix_code [code]:
  \<open>lix [] n = 0\<close>
  \<open>lix (x # xs) n = (if x = n then 0 else lix xs n + 1)\<close>
  by (simp_all add: lix_def integer_of_nat_eq_of_nat)

text \<open>The name at a position, and outside the positions a name that is not in the
  list. It is never computed: only the proofs mention it.\<close>

definition lnm :: \<open>'n list \<Rightarrow> integer \<Rightarrow> 'n\<close> where
  \<open>lnm ns i = (if 0 \<le> i \<and> nat_of_integer i < length ns then ns ! nat_of_integer i
     else (SOME x. x \<notin> set ns))\<close>

lemma nix_less: \<open>n \<in> set ns \<Longrightarrow> nix ns n < length ns\<close>
  by (induction ns) auto

lemma nth_nix: \<open>n \<in> set ns \<Longrightarrow> ns ! nix ns n = n\<close>
  by (induction ns) auto

lemma nix_nth: \<open>distinct ns \<Longrightarrow> k < length ns \<Longrightarrow> nix ns (ns ! k) = k\<close>
proof (induction ns arbitrary: k)
  case (Cons x xs)
  then show ?case by (cases k) (auto simp: nth_mem)
qed simp

lemma lnm_lix: \<open>n \<in> set ns \<Longrightarrow> lnm ns (lix ns n) = n\<close>
  by (simp add: lnm_def lix_def nix_less nth_nix)

lemma lix_range: \<open>n \<in> set ns \<Longrightarrow> 0 \<le> lix ns n \<and> nat_of_integer (lix ns n) < length ns\<close>
  by (simp add: lix_def nix_less)

lemma lnm_eq_iff:
  fixes ns :: \<open>'n list\<close>
  assumes d: \<open>distinct ns\<close> and inf: \<open>infinite (UNIV :: 'n set)\<close> and s: \<open>s \<in> set ns\<close>
  shows \<open>lnm ns i = s \<longleftrightarrow> i = lix ns s\<close>
proof
  assume l: \<open>lnm ns i = s\<close>
  show \<open>i = lix ns s\<close>
  proof (cases \<open>0 \<le> i \<and> nat_of_integer i < length ns\<close>)
    case True
    with l have \<open>ns ! nat_of_integer i = s\<close> by (simp add: lnm_def)
    with True d have \<open>nix ns s = nat_of_integer i\<close> using nix_nth by blast
    with True show ?thesis by (simp add: lix_def zi_nat_of_integer)
  next
    case False
    have \<open>\<exists>x. x \<notin> set ns\<close> using ex_new_if_finite[OF inf, of \<open>set ns\<close>] by simp
    then have \<open>(SOME x. x \<notin> set ns) \<notin> set ns\<close> by (rule someI_ex)
    with False l s show ?thesis by (auto simp: lnm_def)
  qed
qed (simp add: lnm_lix s)

lemma lnm_inj:
  assumes d: \<open>distinct ns\<close> and i: \<open>0 \<le> i\<close> \<open>nat_of_integer i < length ns\<close>
    and j: \<open>0 \<le> j\<close> \<open>nat_of_integer j < length ns\<close>
  shows \<open>lnm ns i = lnm ns j \<longleftrightarrow> i = j\<close>
proof
  assume \<open>lnm ns i = lnm ns j\<close>
  with i j have \<open>ns ! nat_of_integer i = ns ! nat_of_integer j\<close> by (simp add: lnm_def)
  with d i j have \<open>nat_of_integer i = nat_of_integer j\<close> by (simp add: nth_eq_iff_index_eq)
  then show \<open>i = j\<close> using i j by (metis zi_nat_of_integer)
qed simp

lemma lnm_ds:
  fixes ns :: \<open>'n list\<close>
  assumes ns: \<open>remdups (zs @ ds) = ns\<close> and inf: \<open>infinite (UNIV :: 'n set)\<close>
    and ds: \<open>ds = xs @ s # ys\<close>
  shows \<open>lnm ns i = s \<longleftrightarrow> i = lix ns s\<close>
  by (rule lnm_eq_iff) (use ns ds inf in auto)

subsection \<open>The code equation\<close>

text \<open>The run on names, followed by a decoder, is the run on the integer arrays
  followed by the decoder over integer trees.\<close>

lemma alab_back:
  assumes ns: \<open>remdups (alabels A @ ds) = ns\<close>
  shows \<open>alab (lnm ns) (alab (lix ns) A) = A\<close>
proof -
  have \<open>alab (lnm ns) (alab (lix ns) A) = alab (lnm ns \<circ> lix ns) A\<close> by (rule alab_alab)
  also have \<open>\<dots> = alab id A\<close>
  proof (rule alab_cong)
    fix a assume a: \<open>a \<in> set (aacts A)\<close>
    show \<open>aact_lab (lnm ns \<circ> lix ns) a = aact_lab id a\<close>
    proof (cases a)
      case (AReduce pr B)
      have \<open>n \<in> set ns\<close> if \<open>n \<in> set (pr_names pr)\<close> for n
        using alabels_mem[of pr B A n] a AReduce ns that by auto
      then have \<open>pr_lab (lnm ns \<circ> lix ns) pr = pr_lab id pr\<close>
        by (intro pr_lab_cong) (simp add: lnm_lix)
      then show ?thesis using AReduce by simp
    qed simp
  qed
  finally show ?thesis by (simp add: alab_id)
qed

theorem bind_nrun_lab:
  assumes ns: \<open>remdups (alabels A @ ds) = ns\<close> and A': \<open>alab (lix ns) A = A'\<close>
    and nd: \<open>d \<circ> relab (lnm ns) = nd\<close>
  shows \<open>Option.bind (nrun (actl A) (afinal A) dec (stk, v, [])) d =
    Option.bind (nrun (actl A') (afinal A') dec (stk, v, [])) nd\<close>
proof -
  have \<open>nrun (actl A) (afinal A) dec (stk, v, []) =
      map_option (relab (lnm ns)) (nrun (actl A') (afinal A') dec (stk, v, []))\<close>
    using nrun_alab_Nil[of \<open>lnm ns\<close> A' dec stk v] alab_back[OF ns] A' by simp
  then show ?thesis using nd[symmetric]
    by (simp add: bind_map_option comp_def)
qed

end
