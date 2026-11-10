theory LR_Trie
  imports LR_Int
begin

section \<open>Tables as binary tries\<close>

text \<open>A table from naturals to values as a binary trie: the path to a key is
  the sequence of bits of its binary numeral, least significant first. With
  binary naturals (\<^verbatim>\<open>Code_Binary_Nat\<close>) a lookup follows the constructors of
  the numeral and involves no arithmetic, and a trie is static data.\<close>

datatype 'a ntrie = NTip | NNode \<open>'a option\<close> \<open>'a ntrie\<close> \<open>'a ntrie\<close>

fun lookup_num :: \<open>'a ntrie \<Rightarrow> num \<Rightarrow> 'a option\<close> where
  \<open>lookup_num NTip _ = None\<close>
| \<open>lookup_num (NNode x l r) num.One = x\<close>
| \<open>lookup_num (NNode x l r) (num.Bit0 k) = lookup_num l k\<close>
| \<open>lookup_num (NNode x l r) (num.Bit1 k) = lookup_num r k\<close>

datatype 'a ntab = NTab \<open>'a option\<close> \<open>'a ntrie\<close>

definition tlookup :: \<open>'a ntab \<Rightarrow> nat \<Rightarrow> 'a option\<close> where
  \<open>tlookup t n = (case t of NTab z tr \<Rightarrow> if n = 0 then z else lookup_num tr (num_of_nat n))\<close>

text \<open>Code equations for binary naturals, to be declared where
  \<^verbatim>\<open>Code_Binary_Nat\<close> is imported.\<close>

lemma tlookup_binary:
  \<open>tlookup t 0 = (case t of NTab z tr \<Rightarrow> z)\<close>
  \<open>tlookup t (nat_of_num k) = (case t of NTab z tr \<Rightarrow> lookup_num tr k)\<close>
  unfolding tlookup_def by (simp_all split: ntab.splits add: nat_of_num_numeral)

text \<open>The trie of the keys \<open>a * k + b\<close>, \<open>k \<ge> 1\<close>, up to the bound \<open>B\<close>.\<close>

primrec mk_trie :: \<open>(nat \<Rightarrow> 'a option) \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'a ntrie\<close> where
  \<open>mk_trie f B 0 a b = NTip\<close>
| \<open>mk_trie f B (Suc fu) a b = (if B < a + b then NTip
     else NNode (f (a + b)) (mk_trie f B fu (2 * a) b) (mk_trie f B fu (2 * a) (a + b)))\<close>

fun nbits :: \<open>num \<Rightarrow> nat\<close> where
  \<open>nbits num.One = 1\<close>
| \<open>nbits (num.Bit0 k) = Suc (nbits k)\<close>
| \<open>nbits (num.Bit1 k) = Suc (nbits k)\<close>

lemma nat_of_num_pos: \<open>0 < nat_of_num k\<close>
  by (induction k) auto

lemma nbits_le: \<open>nbits k \<le> nat_of_num k\<close>
proof (induction k)
  case (Bit0 k) then show ?case using nat_of_num_pos[of k] by simp
next
  case (Bit1 k) then show ?case using nat_of_num_pos[of k] by simp
qed simp

lemma lookup_mk_trie:
  assumes \<open>0 < a\<close> and \<open>a * nat_of_num k + b \<le> B \<longrightarrow> nbits k \<le> fu\<close>
  shows \<open>lookup_num (mk_trie f B fu a b) k =
    (if a * nat_of_num k + b \<le> B then f (a * nat_of_num k + b) else None)\<close>
  using assms
proof (induction k arbitrary: fu a b)
  case One
  then show ?case by (cases fu) auto
next
  case (Bit0 k)
  have eq: \<open>a * nat_of_num (num.Bit0 k) + b = 2 * a * nat_of_num k + b\<close> by simp
  have le: \<open>a + b \<le> 2 * a * nat_of_num k + b\<close> using nat_of_num_pos[of k] Bit0.prems(1) by simp
  show ?case
  proof (cases fu)
    case 0 then show ?thesis using Bit0.prems by simp
  next
    case (Suc fu')
    show ?thesis
    proof (cases \<open>B < a + b\<close>)
      case True
      then have \<open>\<not> a * nat_of_num (num.Bit0 k) + b \<le> B\<close> using le eq by linarith
      then show ?thesis using Suc True by simp
    next
      case False
      have ih: \<open>lookup_num (mk_trie f B fu' (2 * a) b) k =
          (if 2 * a * nat_of_num k + b \<le> B then f (2 * a * nat_of_num k + b) else None)\<close>
        by (rule Bit0.IH) (use Bit0.prems Suc in \<open>unfold eq, auto\<close>)
      then show ?thesis unfolding eq using Suc False by simp
    qed
  qed
next
  case (Bit1 k)
  have eq: \<open>a * nat_of_num (num.Bit1 k) + b = 2 * a * nat_of_num k + (a + b)\<close> by simp
  show ?case
  proof (cases fu)
    case 0 then show ?thesis using Bit1.prems by simp
  next
    case (Suc fu')
    show ?thesis
    proof (cases \<open>B < a + b\<close>)
      case True
      then have \<open>\<not> a * nat_of_num (num.Bit1 k) + b \<le> B\<close> using eq by linarith
      then show ?thesis using Suc True by simp
    next
      case False
      have ih: \<open>lookup_num (mk_trie f B fu' (2 * a) (a + b)) k =
          (if 2 * a * nat_of_num k + (a + b) \<le> B then f (2 * a * nat_of_num k + (a + b)) else None)\<close>
        by (rule Bit1.IH) (use Bit1.prems Suc in \<open>unfold eq, auto\<close>)
      then show ?thesis unfolding eq using Suc False by simp
    qed
  qed
qed

definition tab_of_fun :: \<open>(nat \<Rightarrow> 'a option) \<Rightarrow> nat \<Rightarrow> 'a ntab\<close> where
  \<open>tab_of_fun f B = NTab (f 0) (mk_trie f B (Suc B) 1 0)\<close>

lemma tlookup_tab_of_fun: \<open>tlookup (tab_of_fun f B) n = (if n \<le> B then f n else None)\<close>
proof (cases \<open>n = 0\<close>)
  case True
  then show ?thesis unfolding tab_of_fun_def tlookup_def by simp
next
  case False
  then have n: \<open>n = nat_of_num (num_of_nat n)\<close>
    using num_of_nat_inverse by simp
  have \<open>lookup_num (mk_trie f B (Suc B) 1 0) (num_of_nat n) =
      (if 1 * nat_of_num (num_of_nat n) + 0 \<le> B then f (1 * nat_of_num (num_of_nat n) + 0) else None)\<close>
    by (rule lookup_mk_trie) (use nbits_le[of \<open>num_of_nat n\<close>] in auto)
  then show ?thesis unfolding tab_of_fun_def tlookup_def using False n[symmetric] by simp
qed

definition tab_of_list :: \<open>'a list \<Rightarrow> 'a ntab\<close> where
  \<open>tab_of_list xs = tab_of_fun (\<lambda>n. if n < length xs then Some (xs ! n) else None) (length xs)\<close>

lemma tlookup_tab_of_list: \<open>tlookup (tab_of_list xs) n = (if n < length xs then Some (xs ! n) else None)\<close>
  unfolding tab_of_list_def tlookup_tab_of_fun by auto

definition tab_of_assoc :: \<open>(nat \<times> 'a) list \<Rightarrow> 'a ntab\<close> where
  \<open>tab_of_assoc kvs = tab_of_fun (map_of kvs) (fold max (map fst kvs) 0)\<close>

lemma fold_max_acc: \<open>(m :: nat) \<le> fold max xs m\<close>
  by (induction xs arbitrary: m) (auto intro: le_trans[OF max.cobounded2])

lemma fold_max_ge: \<open>(x :: nat) \<in> set xs \<Longrightarrow> x \<le> fold max xs m\<close>
  by (induction xs arbitrary: m) (auto intro: le_trans[OF max.cobounded1 fold_max_acc])

lemma tlookup_tab_of_assoc: \<open>tlookup (tab_of_assoc kvs) k = map_of kvs k\<close>
proof -
  have \<open>map_of kvs k = None\<close> if \<open>\<not> k \<le> fold max (map fst kvs) 0\<close>
  proof (rule ccontr)
    assume \<open>map_of kvs k \<noteq> None\<close>
    then have \<open>k \<in> set (map fst kvs)\<close> by (auto dest: map_of_SomeD intro: rev_image_eqI)
    then show False using that fold_max_ge by blast
  qed
  then show ?thesis unfolding tab_of_assoc_def tlookup_tab_of_fun by auto
qed

definition tab_opt :: \<open>(nat \<times> 'a) list \<Rightarrow> ('a \<Rightarrow> 'b option) \<Rightarrow> 'b ntab\<close> where
  \<open>tab_opt kvs g = tab_of_fun (\<lambda>k. Option.bind (map_of kvs k) g) (fold max (map fst kvs) 0)\<close>

lemma tlookup_tab_opt: \<open>tlookup (tab_opt kvs g) k = Option.bind (map_of kvs k) g\<close>
proof -
  have \<open>map_of kvs k = None\<close> if \<open>\<not> k \<le> fold max (map fst kvs) 0\<close>
  proof (rule ccontr)
    assume \<open>map_of kvs k \<noteq> None\<close>
    then have \<open>k \<in> set (map fst kvs)\<close> by (auto dest: map_of_SomeD intro: rev_image_eqI)
    then show False using that fold_max_ge by blast
  qed
  then show ?thesis unfolding tab_opt_def tlookup_tab_of_fun by auto
qed

text \<open>Structural drop, without arithmetic on the length.\<close>

fun drop_as :: \<open>'a list \<Rightarrow> 'b list \<Rightarrow> 'b list\<close> where
  \<open>drop_as [] ys = ys\<close>
| \<open>drop_as (_ # xs) [] = []\<close>
| \<open>drop_as (_ # xs) (_ # ys) = drop_as xs ys\<close>

lemma drop_as_eq: \<open>drop_as xs ys = drop (length xs) ys\<close>
  by (induction xs ys rule: drop_as.induct) auto

subsection \<open>Trie tables and the trie step\<close>

datatype ('n, 't) jtabs = JTabs
  (jt_lal: \<open>('t \<times> nat) list\<close>) (jt_miss: nat)
  (jt_gT: \<open>nat ntab ntab\<close>) (jt_gN: \<open>nat ntab ntab\<close>)
  (jt_lic: \<open>unit ntab ntab ntab\<close>) (jt_pc: \<open>nat list ntab\<close>)
  (jt_prs: \<open>(('n \<times> ('n, 't) rhs) \<times> nat) ntab\<close>) (jt_pf: \<open>bool ntab\<close>)

text \<open>The lookahead as a number: \<open>0\<close> for the end of the input, \<open>Suc i\<close> for the
  \<open>i\<close>-th token of the tables, \<open>jt_miss\<close> for any other token.\<close>

definition jla :: \<open>('n, 't) jtabs \<Rightarrow> ('m, 'ch, 't) tword \<Rightarrow> nat\<close> where
  \<open>jla J v = (case v of [] \<Rightarrow> 0 | x # _ \<Rightarrow>
     (case map_of (jt_lal J) (tok x) of Some l \<Rightarrow> l | None \<Rightarrow> jt_miss J))\<close>

definition jget :: \<open>'a ntab ntab \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'a option\<close> where
  \<open>jget tab i k = (case tlookup tab i of None \<Rightarrow> None | Some r \<Rightarrow> tlookup r k)\<close>

definition jlicd :: \<open>unit ntab option \<Rightarrow> nat \<Rightarrow> bool\<close> where
  \<open>jlicd lics j = (case lics of None \<Rightarrow> False | Some t \<Rightarrow> tlookup t j \<noteq> None)\<close>

definition jtarget :: \<open>('n, 't) jtabs \<Rightarrow> nat list \<Rightarrow> nat \<Rightarrow> iact \<Rightarrow> nat option\<close> where
  \<open>jtarget J stk l act = (case act of
      IShift \<Rightarrow> jget (jt_gT J) (hd stk) l
    | IReduce j \<Rightarrow> (case tlookup (jt_prs J) j of None \<Rightarrow> None | Some (pr, A) \<Rightarrow>
        (case drop_as (snd pr) stk of [] \<Rightarrow> None | i' # _ \<Rightarrow> jget (jt_gN J) i' A)))\<close>

definition jctl :: \<open>('n, 't) jtabs \<Rightarrow> ('m, 'ch, 't) sctl_t \<Rightarrow>
    (('n, 't) dact \<times> ('m, 'ch, 't) sctl_t) option\<close> where
  \<open>jctl J c = (case c of (stk, v) \<Rightarrow>
     (case stk of [] \<Rightarrow> None | i # _ \<Rightarrow>
       let l = jla J v;
           lics = jget (jt_lic J) i l;
           comps = (case tlookup (jt_pc J) i of None \<Rightarrow> [] | Some cs \<Rightarrow> cs);
           cands = (case v of [] \<Rightarrow> [] | _ \<Rightarrow> [IShift]) @ map IReduce (filter (jlicd lics) comps)
       in (case spick (jtarget J stk l) cands of
            None \<Rightarrow> None
          | Some (IShift, q) \<Rightarrow> Some (DShift, q # stk, tl v)
          | Some (IReduce j, q) \<Rightarrow> (case tlookup (jt_prs J) j of None \<Rightarrow> None | Some (pr, A) \<Rightarrow>
              Some (DReduce pr, q # drop_as (snd pr) stk, v)))))\<close>

definition jfinal :: \<open>('n, 't) jtabs \<Rightarrow> ('m, 'ch, 't) sctl_t \<Rightarrow> bool\<close> where
  \<open>jfinal J c \<longleftrightarrow> (case c of (stk, v) \<Rightarrow> v = [] \<and>
     (case stk of [] \<Rightarrow> False | i # _ \<Rightarrow> tlookup (jt_pf J) i = Some True))\<close>

subsection \<open>The trie tables of the list tables\<close>

fun jtabs_of :: \<open>('n, 't) ltabs \<Rightarrow> ('n, 't) jtabs\<close> where
  \<open>jtabs_of (LTabs ns gT gN cs pc prs pl ph pf) = (let
     toks = remdups (concat (map (map fst) gT) @ concat (map (List.map_filter snd) cs));
     lal = map (\<lambda>a. (a, Suc (la_tindex toks a))) toks;
     miss = Suc (length toks);
     li = (\<lambda>a. case map_of lal a of Some l \<Rightarrow> l | None \<Rightarrow> miss);
     lt = (\<lambda>t. case t of None \<Rightarrow> 0 | Some a \<Rightarrow> li a)
   in JTabs lal miss
     (tab_of_list (map (\<lambda>row. tab_opt (map (\<lambda>(a, j). (li a, j)) row)
        (\<lambda>j. if min j ns < ns then Some (min j ns) else None)) gT))
     (tab_of_list (map (\<lambda>row. tab_opt row
        (\<lambda>j. if min j ns < ns then Some (min j ns) else None)) gN))
     (tab_of_list (map (\<lambda>cells. tab_of_fun (\<lambda>l. let js = map fst (filter (\<lambda>(j, t). lt t = l) cells) in
        if js = [] then None else Some (tab_of_assoc (map (\<lambda>j. (j, ())) js))) miss) cs))
     (tab_of_list pc)
     (tab_of_list (zip prs ph))
     (tab_of_list pf))\<close>

subsection \<open>Correctness of the trie step\<close>

text \<open>The trie tables need the facts that \<^const>\<open>mk_ltabs\<close> guarantees about the
  productions offered as reduces.\<close>

fun lwf2 :: \<open>('n, 't) ltabs \<Rightarrow> bool\<close> where
  \<open>lwf2 (LTabs ns gT gN cs pc prs pl ph pf) \<longleftrightarrow> (\<forall>row \<in> set pc. \<forall>j \<in> set row.
     j < length prs \<and> j < length ph \<and> j < length pl \<and> pl ! j = length (snd (prs ! j)))\<close>

lemma lwf2_mk_ltabs: \<open>lwf2 (mk_ltabs gt sts redtab pc pf)\<close>
proof -
  have \<open>la_tindex (remdups (concat pc)) pr < length (remdups (concat pc))\<close>
    if \<open>row \<in> set pc\<close> \<open>pr \<in> set row\<close> for row pr
    using la_tindex_nth[of pr \<open>remdups (concat pc)\<close>] that by auto
  then show ?thesis unfolding mk_ltabs_def Let_def by auto
qed

text \<open>Token numbers.\<close>

lemma map_of_lal:
  \<open>map_of (map (\<lambda>a. (a, f a)) xs) b = (if b \<in> set xs then Some (f b) else None)\<close>
  by (induction xs) auto

lemma li_inj:
  assumes \<open>a \<in> set toks\<close>
  shows \<open>(case map_of (map (\<lambda>a. (a, Suc (la_tindex toks a))) toks) a of Some l \<Rightarrow> l | None \<Rightarrow> Suc (length toks)) =
      (case map_of (map (\<lambda>a. (a, Suc (la_tindex toks a))) toks) b of Some l \<Rightarrow> l | None \<Rightarrow> Suc (length toks))
    \<longleftrightarrow> a = b\<close>
  using assms la_tindex_nth[of a toks] la_tindex_inj[of a toks b] by (auto simp: map_of_lal)

lemma map_of_li_row:
  assumes li_eq: \<open>\<And>a b. a \<in> set toks \<Longrightarrow> li a = li b \<longleftrightarrow> a = b\<close>
    and keys: \<open>set (map fst row) \<subseteq> set toks\<close>
  shows \<open>map_of (map (\<lambda>(a, j). (li a, j)) row) (li b) = map_of row b\<close>
  using keys
proof (induction row)
  case (Cons x row)
  obtain a j where x: \<open>x = (a, j)\<close> by (cases x)
  have a: \<open>a \<in> set toks\<close> using Cons.prems x by simp
  show ?case using Cons li_eq[OF a, of b] unfolding x by auto
qed simp

lemma map_of_li_row_0:
  fixes li :: \<open>'a \<Rightarrow> nat\<close>
  assumes \<open>\<And>a. 0 < li a\<close>
  shows \<open>map_of (map (\<lambda>(a, j). (li a, j)) row) 0 = None\<close>
proof (induction row)
  case (Cons x row)
  obtain a j where x: \<open>x = (a, j)\<close> by (cases x)
  show ?case using Cons assms[of a] unfolding x by auto
qed simp

theorem jctl_eq:
  assumes wf: \<open>lwf2 L\<close>
  shows \<open>jctl (jtabs_of L) (stk, v) = isctl (itabs_of L) (stk, v)\<close>
proof -
  obtain ns gT gN cs pc prs pl ph pf where L: \<open>L = LTabs ns gT gN cs pc prs pl ph pf\<close>
    by (cases L)
  define toks where \<open>toks = remdups (concat (map (map fst) gT) @
     concat (map (List.map_filter snd) cs))\<close>
  define li where \<open>li = (\<lambda>a. case map_of (map (\<lambda>a. (a, Suc (la_tindex toks a))) toks) a of
     Some l \<Rightarrow> l | None \<Rightarrow> Suc (length toks))\<close>
  define lt where \<open>lt = (\<lambda>t. case t of None \<Rightarrow> 0 | Some a \<Rightarrow> li a)\<close>
  define J where \<open>J = jtabs_of L\<close>
  define T where \<open>T = itabs_of L\<close>
  have Jf: \<open>jt_lal J = map (\<lambda>a. (a, Suc (la_tindex toks a))) toks\<close> \<open>jt_miss J = Suc (length toks)\<close>
    \<open>jt_gT J = tab_of_list (map (\<lambda>row. tab_opt (map (\<lambda>(a, j). (li a, j)) row)
        (\<lambda>j. if min j ns < ns then Some (min j ns) else None)) gT)\<close>
    \<open>jt_gN J = tab_of_list (map (\<lambda>row. tab_opt row
        (\<lambda>j. if min j ns < ns then Some (min j ns) else None)) gN)\<close>
    \<open>jt_lic J = tab_of_list (map (\<lambda>cells. tab_of_fun
        (\<lambda>l. let js = map fst (filter (\<lambda>(j, t). lt t = l) cells) in
          if js = [] then None else Some (tab_of_assoc (map (\<lambda>j. (j, ())) js)))
        (Suc (length toks))) cs)\<close>
    \<open>jt_pc J = tab_of_list pc\<close> \<open>jt_prs J = tab_of_list (zip prs ph)\<close> \<open>jt_pf J = tab_of_list pf\<close>
    unfolding J_def L toks_def li_def lt_def by (simp_all add: Let_def)
  have li_val: \<open>li a = (if a \<in> set toks then Suc (la_tindex toks a) else Suc (length toks))\<close> for a
    unfolding li_def by (simp add: map_of_lal)
  have li_pos: \<open>0 < li a\<close> for a using li_val[of a] by simp
  have li_le: \<open>li a \<le> Suc (length toks)\<close> for a
    using li_val[of a] la_tindex_nth[of a toks] by (auto split: if_splits)
  have li_eq: \<open>a \<in> set toks \<Longrightarrow> li a = li b \<longleftrightarrow> a = b\<close> for a b
    unfolding li_def by (rule li_inj)
  have jla: \<open>jla J v = (case v of [] \<Rightarrow> 0 | x # _ \<Rightarrow> li (tok x))\<close>
    unfolding jla_def Jf li_def by (simp split: list.splits)
  have gT_keys: \<open>set (map fst row) \<subseteq> set toks\<close> if \<open>row \<in> set gT\<close> for row
    using that unfolding toks_def by auto
  have cs_toks: \<open>a \<in> set toks\<close> if \<open>row \<in> set cs\<close> \<open>(j, Some a) \<in> set row\<close> for row j a
    using that unfolding toks_def by (force simp: List.map_filter_def)
  have matchv: \<open>lt t = jla J v \<longleftrightarrow> (case v of [] \<Rightarrow> t = None | x # _ \<Rightarrow> t = Some (tok x))\<close>
    if \<open>t = None \<or> (\<exists>a. t = Some a \<and> a \<in> set toks)\<close> for t
    using that li_pos li_eq unfolding lt_def jla by (auto split: list.splits option.splits)
  show ?thesis
  proof (cases stk)
    case Nil
    then show ?thesis unfolding J_def[symmetric] T_def[symmetric] jctl_def isctl_def by simp
  next
    case (Cons i rest)
    define cells where \<open>cells = (if i < length cs then cs ! i else [])\<close>
    define comps where \<open>comps = (if i < length pc then pc ! i else [])\<close>
    define I where \<open>I = icands comps cells v\<close>
    have jc: \<open>j < length prs \<and> j < length ph \<and> j < length pl \<and> pl ! j = length (snd (prs ! j))\<close>
      if \<open>j \<in> set comps\<close> for j
      using that wf unfolding L comps_def by (auto split: if_splits)
    have jI: \<open>j \<in> set comps\<close> if \<open>IReduce j \<in> set I\<close> for j
      using that unfolding I_def icands_def Let_def by (cases v) auto
    have sI: \<open>v \<noteq> []\<close> if \<open>IShift \<in> set I\<close>
      using that unfolding I_def icands_def Let_def by (cases v) auto
    have lic: \<open>jlicd (jget (jt_lic J) i (jla J v)) j = ilic cells v j\<close> for j
    proof (cases \<open>i < length cs\<close>)
      case False
      then show ?thesis unfolding jlicd_def jget_def Jf cells_def ilic_def
        by (simp add: tlookup_tab_of_list)
    next
      case True
      define row where \<open>row = cs ! i\<close>
      have row_in: \<open>row \<in> set cs\<close> using True unfolding row_def by simp
      have la_le: \<open>jla J v \<le> Suc (length toks)\<close> using li_le unfolding jla by (simp split: list.splits)
      define js where \<open>js = map fst (filter (\<lambda>(j, t). lt t = jla J v) row)\<close>
      have g: \<open>jget (jt_lic J) i (jla J v) =
          (if js = [] then None else Some (tab_of_assoc (map (\<lambda>j. (j, ())) js)))\<close>
        unfolding jget_def Jf using True la_le
        by (simp add: tlookup_tab_of_list tlookup_tab_of_fun row_def[symmetric] js_def Let_def)
      have mem: \<open>jlicd (jget (jt_lic J) i (jla J v)) j \<longleftrightarrow> j \<in> set js\<close>
        unfolding g jlicd_def by (auto simp: tlookup_tab_of_assoc map_of_lal)
      have tv: \<open>t = None \<or> (\<exists>a. t = Some a \<and> a \<in> set toks)\<close> if \<open>(j', t) \<in> set row\<close> for j' t
        using that cs_toks[OF row_in] by (cases t) auto
      have e1: \<open>j \<in> set js \<longleftrightarrow> (\<exists>t. (j, t) \<in> set row \<and> lt t = jla J v)\<close>
        unfolding js_def by force
      have e2: \<open>ilic cells v j \<longleftrightarrow>
          (\<exists>t. (j, t) \<in> set row \<and> (case v of [] \<Rightarrow> t = None | x # _ \<Rightarrow> t = Some (tok x)))\<close>
        unfolding ilic_def list_ex_iff cells_def row_def using True by force
      show ?thesis unfolding mem e1 e2 using matchv tv by blast
    qed
    have cj: \<open>(case tlookup (jt_pc J) i of None \<Rightarrow> [] | Some cs \<Rightarrow> cs) = comps\<close>
      unfolding Jf comps_def by (simp add: tlookup_tab_of_list)
    have cand: \<open>(case v of [] \<Rightarrow> [] | _ \<Rightarrow> [IShift]) @
        map IReduce (filter (jlicd (jget (jt_lic J) i (jla J v))) comps) = I\<close>
    proof -
      have \<open>filter (jlicd (jget (jt_lic J) i (jla J v))) comps = filter (ilic cells v) comps\<close>
        by (rule filter_cong) (simp_all add: lic)
      then show ?thesis unfolding I_def icands_def Let_def by (cases v) simp_all
    qed
    have hd_i: \<open>hd stk = i\<close> using Cons by simp
    have pg: \<open>jget (jt_gT J) i' (li a) = (let q = inext (it_gtT T) (it_ns T) i' a in
        if q < it_ns T then Some q else None)\<close> for i' a
    proof (cases \<open>i' < length gT\<close>)
      case True
      have k: \<open>set (map fst (gT ! i')) \<subseteq> set toks\<close> using gT_keys True by simp
      show ?thesis unfolding jget_def Jf T_def L using True
        by (simp add: tlookup_tab_of_list tlookup_tab_opt map_of_li_row[OF li_eq k] inext_def Let_def
            split: option.splits)
    next
      case False
      then show ?thesis unfolding jget_def Jf T_def L by (simp add: tlookup_tab_of_list inext_def)
    qed
    have pg0: \<open>jget (jt_gT J) i' 0 = None\<close> for i'
      unfolding jget_def Jf
      by (simp add: tlookup_tab_of_list tlookup_tab_opt map_of_li_row_0[OF li_pos] split: option.splits)
    have pn: \<open>jget (jt_gN J) i' A = (let q = inext (it_gtN T) (it_ns T) i' A in
        if q < it_ns T then Some q else None)\<close> for i' A
      unfolding jget_def Jf T_def L
      by (simp add: tlookup_tab_of_list tlookup_tab_opt inext_def Let_def split: option.splits)
    have pj: \<open>tlookup (jt_prs J) j = Some (prs ! j, ph ! j)\<close>
      \<open>it_prs T !! j = prs ! j\<close> \<open>it_plhs T !! j = ph ! j\<close>
      \<open>drop_as (snd (prs ! j)) stk = drop (it_plen T !! j) stk\<close> if \<open>j \<in> set comps\<close> for j
      using jc[OF that] unfolding Jf T_def L by (simp_all add: tlookup_tab_of_list drop_as_eq)
    have tg: \<open>jtarget J stk (jla J v) a = itarget T stk v a\<close> if \<open>a \<in> set I\<close> for a
    proof (cases a)
      case IShift
      show ?thesis
      proof (cases v)
        case Nil
        then show ?thesis unfolding IShift jtarget_def itarget_def jla by (simp add: pg0)
      next
        case (Cons x v')
        then show ?thesis unfolding IShift jtarget_def itarget_def jla by (simp add: pg)
      qed
    next
      case (IReduce j)
      have j: \<open>j \<in> set comps\<close> using jI that IReduce by blast
      show ?thesis unfolding IReduce jtarget_def itarget_def iact.case
        unfolding pj(1,3)[OF j] pj(4)[OF j, symmetric] option.case prod.case
        by (simp add: pn split: list.splits)
    qed
    have sp: \<open>spick (jtarget J stk (jla J v)) I = spick (itarget T stk v) I\<close>
      by (rule spick_cong) (rule tg)
    have ci: \<open>(if i < IArray.length (it_cells T) then it_cells T !! i else []) = cells\<close>
      unfolding T_def L cells_def by simp
    have pi: \<open>(if i < IArray.length (it_pc T) then it_pc T !! i else []) = comps\<close>
      unfolding T_def L comps_def by simp
    have JE: \<open>jctl J (stk, v) = (case spick (jtarget J stk (jla J v)) I of
          None \<Rightarrow> None
        | Some (IShift, q) \<Rightarrow> Some (DShift, q # stk, tl v)
        | Some (IReduce j, q) \<Rightarrow> (case tlookup (jt_prs J) j of None \<Rightarrow> None | Some (pr, A) \<Rightarrow>
            Some (DReduce pr, q # drop_as (snd pr) stk, v)))\<close>
      unfolding jctl_def prod.case using Cons by (simp only: list.case prod.case Let_def cj cand)
    have IE: \<open>isctl T (stk, v) = (case spick (itarget T stk v) I of
          None \<Rightarrow> None
        | Some (IShift, q) \<Rightarrow> Some (DShift, q # stk, tl v)
        | Some (IReduce j, q) \<Rightarrow>
            Some (DReduce (it_prs T !! j), q # drop (it_plen T !! j) stk, v))\<close>
      unfolding isctl_def prod.case using Cons
      by (simp only: list.case prod.case Let_def ci pi I_def)
    have \<open>jctl J (stk, v) = isctl T (stk, v)\<close>
    proof (cases \<open>spick (itarget T stk v) I\<close>)
      case None
      then show ?thesis unfolding JE IE sp by simp
    next
      case (Some r)
      obtain a q where r: \<open>r = (a, q)\<close> by (cases r)
      from spick_SomeD[OF Some[unfolded r]] have aI: \<open>a \<in> set I\<close> by blast
      show ?thesis
      proof (cases a)
        case IShift
        then show ?thesis unfolding JE IE sp Some r by simp
      next
        case (IReduce j)
        have j: \<open>j \<in> set comps\<close> using jI aI IReduce by blast
        show ?thesis unfolding JE IE sp Some r IReduce option.case prod.case iact.case
          unfolding pj(1,2)[OF j] pj(4)[OF j, symmetric] option.case prod.case ..
      qed
    qed
    then show ?thesis unfolding J_def T_def .
  qed
qed

theorem jfinal_eq: \<open>jfinal (jtabs_of L) c = isfinal (itabs_of L) c\<close>
  by (cases L; cases c) (auto simp: jfinal_def isfinal_def Let_def tlookup_tab_of_list split: list.splits)


subsection \<open>Table inlining\<close>

lemma dparse_via_trie_tables:
  assumes static: \<open>sstatic G Shn\<close>
    and st: \<open>pr0_states G Shn = sts\<close> and gt: \<open>pgtab G sts = gtab\<close>
    and rt: \<open>red_buckets G Shn (length sts) = redtab\<close>
    and pcs: \<open>pcomps G sts = pc\<close> and pfs: \<open>pfins Shn sts = pf\<close>
    and i0: \<open>st_find sts (lr0_start G Shn) = i\<^sub>0\<close>
    and lt: \<open>mk_ltabs gtab sts redtab pc pf = L\<close>
    and jt: \<open>jtabs_of L = J\<close>
  shows \<open>dparse G Shn w = srun_hist (jctl J) (jfinal J) [] ([i\<^sub>0], w, [])\<close>
proof -
  have wf: \<open>lwf2 L\<close> using lwf2_mk_ltabs lt by blast
  have c: \<open>jctl (jtabs_of L) = isctl (itabs_of L)\<close>
    by (rule ext) (case_tac x, simp only: jctl_eq[OF wf])
  have f: \<open>jfinal (jtabs_of L) = isfinal (itabs_of L)\<close> by (rule ext) (rule jfinal_eq)
  show ?thesis
    unfolding dparse_via_index_tables[OF static st gt rt pcs pfs i0 lt refl] jt[symmetric] c f ..
qed

text \<open>Tree building without arithmetic on the length of the right-hand side.\<close>

fun take_as :: \<open>'a list \<Rightarrow> 'b list \<Rightarrow> 'b list\<close> where
  \<open>take_as [] _ = []\<close>
| \<open>take_as (_ # xs) [] = []\<close>
| \<open>take_as (_ # xs) (y # ys) = y # take_as xs ys\<close>

lemma take_as_eq: \<open>take_as xs ys = take (length xs) ys\<close>
  by (induction xs ys rule: take_as.induct) auto

lemma stree_code [code]:
  \<open>stree act v tstk = (case act of
      DShift \<Rightarrow> Leaf (hd v) # tstk
    | DReduce pr \<Rightarrow> Node (fst pr) (rev (take_as (snd pr) tstk)) # drop_as (snd pr) tstk)\<close>
  by (simp add: stree_def take_as_eq drop_as_eq split: dact.split)

end
