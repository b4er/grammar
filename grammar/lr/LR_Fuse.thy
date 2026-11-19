(* Author: Basil Fürer *)

theory LR_Fuse
  imports LR_Lab
begin

section \<open>Fused semantic actions\<close>

text \<open>A parser's code runs the driver, which builds a tree, and then the decoders,
  which walk the tree again and compute the value of each node from the values of its
  children. Here the driver computes the values directly: its stack holds values
  instead of trees, and a reduction applies the action of the nonterminal to the
  values of the children. A value (\<open>fv\<close>) is a token for a leaf,
  and for a node its label and the result of its action, \<open>None\<close> when the action
  fails. The run on values is the run on trees followed by a fold over the tree
  (\<open>afold\<close>), for any actions (\<open>frun_map\<close>).

  The decoders are such a fold: a decoder looks at the children of a node only
  through their own decoders and through their tokens, so the decoder of a node is a
  function of the values of its children. A parser states this as one equation per
  nonterminal, between its decoder and its action on values (\<open>fuse_tree\<close>); then its
  run on trees followed by its decoder is its run on values (\<open>bind_frun\<close>). The
  diagnostics keep the run on trees.\<close>

subsection \<open>Values and the fold\<close>

datatype ('m, 'ch, 't, 'v) fv = FLeaf \<open>('t, 'ch, 'm) token_scheme\<close> | FNode integer \<open>'v option\<close>

text \<open>The values of the nonterminals, one type per carrier: a wide sum, so that a value
  is one constructor away from its carrier, not one per level of a binary sum. A parser
  with more than 16 carriers nests the rest in the last alternative.\<close>

datatype ('a, 'b, 'c, 'd, 'e, 'f, 'g, 'h, 'i, 'j, 'k, 'l, 'm, 'n, 'o, 'p) vs =
  V0 'a | V1 'b | V2 'c | V3 'd | V4 'e | V5 'f | V6 'g | V7 'h
| V8 'i | V9 'j | V10 'k | V11 'l | V12 'm | V13 'n | V14 'o | V15 'p

primrec afold :: \<open>(integer \<Rightarrow> ('m, 'ch, 't, 'v) fv list \<Rightarrow> 'v option) \<Rightarrow>
    ('m, 'ch, integer, 't) ast \<Rightarrow> ('m, 'ch, 't, 'v) fv\<close> where
  \<open>afold K (Leaf w) = FLeaf w\<close>
| \<open>afold K (Node i cs) = FNode i (K i (map (afold K) cs))\<close>

text \<open>The value of a tree when the decoder of each label is given (\<open>dl\<close>): not
  recursive. If the decoders are functions of the values of the children, it is the
  fold.\<close>

definition vof :: \<open>(integer \<Rightarrow> ('m, 'ch, integer, 't) ast \<Rightarrow> 'v option) \<Rightarrow>
    ('m, 'ch, integer, 't) ast \<Rightarrow> ('m, 'ch, 't, 'v) fv\<close> where
  \<open>vof dl t = (case t of Leaf w \<Rightarrow> FLeaf w | Node i cs \<Rightarrow> FNode i (dl i t))\<close>

lemma vof_afold:
  assumes \<open>\<And>i cs. dl i (Node i cs) = K i (map (vof dl) cs)\<close>
  shows \<open>vof dl t = afold K t\<close>
proof (induction t)
  case (Node i cs)
  then have m: \<open>map (vof dl) cs = map (afold K) cs\<close> by simp
  have \<open>vof dl (Node i cs) = FNode i (K i (map (afold K) cs))\<close>
    by (simp only: vof_def ast.case assms m)
  then show ?case by simp
qed (simp add: vof_def)

text \<open>The value of a nonterminal's carrier, from the value of a node: its label
  must be the nonterminal's.\<close>

definition fproj :: \<open>integer \<Rightarrow> ('v \<Rightarrow> 'a option) \<Rightarrow> ('m, 'ch, 't, 'v) fv \<Rightarrow> 'a option\<close> where
  \<open>fproj ix pj u = (case u of FLeaf _ \<Rightarrow> None | FNode i x \<Rightarrow> if i = ix then Option.bind x pj else None)\<close>

lemma fproj_vof:
  assumes dl: \<open>\<And>t. dl ix t = map_option ij (nd t)\<close>
    and pj: \<open>\<And>x. Option.bind (map_option ij x) pj = x\<close>
    and node: \<open>\<And>i cs. i \<noteq> ix \<Longrightarrow> nd (Node i cs) = None\<close>
    and leaf: \<open>\<And>w. nd (Leaf w) = None\<close>
  shows \<open>fproj ix pj (vof dl c) = nd c\<close>
  by (cases c) (auto simp: fproj_def vof_def dl pj node leaf)

lemma case_fv_vof:
  \<open>(case vof dl c of FLeaf x \<Rightarrow> f x | FNode i y \<Rightarrow> None) = (case c of Leaf x \<Rightarrow> f x | Node n ys \<Rightarrow> None)\<close>
  by (cases c) (simp_all add: vof_def)

subsection \<open>The actions of the labels\<close>

text \<open>A list of triples: a label, its decoder (proofs only) and its action
  (code). \<open>kof\<close> looks up a label.\<close>

definition kof :: \<open>('k \<times> ('a \<Rightarrow> 'b option)) list \<Rightarrow> 'k \<Rightarrow> 'a \<Rightarrow> 'b option\<close> where
  \<open>kof ps i x = (case map_of ps i of None \<Rightarrow> None | Some f \<Rightarrow> f x)\<close>

definition hpart :: \<open>'k \<times> 'h \<times> 'c \<Rightarrow> 'k \<times> 'h\<close> where
  \<open>hpart x = (fst x, fst (snd x))\<close>

definition kpart :: \<open>'k \<times> 'h \<times> 'c \<Rightarrow> 'k \<times> 'c\<close> where
  \<open>kpart x = (fst x, snd (snd x))\<close>

lemma fst_hpart [simp]: \<open>fst (hpart x) = fst x\<close> and fst_comp_hpart [simp]: \<open>fst \<circ> hpart = fst\<close>
  by (auto simp: hpart_def)

lemma fst_kpart [simp]: \<open>fst (kpart x) = fst x\<close> and fst_comp_kpart [simp]: \<open>fst \<circ> kpart = fst\<close>
  by (auto simp: kpart_def)

lemma kof_in:
  \<open>distinct (map fst ps) \<Longrightarrow> (i, f) \<in> set ps \<Longrightarrow> kof ps i x = f x\<close>
  by (simp add: kof_def map_of_is_SomeI)

lemma kof_notin:
  assumes \<open>i \<notin> set (map fst ps)\<close> shows \<open>kof ps i x = None\<close>
proof -
  from assms have \<open>map_of ps i = None\<close> by (simp add: map_of_eq_None_iff)
  then show ?thesis by (simp add: kof_def)
qed

text \<open>A property of all triples, by a recursion the backend can unfold one
  triple at a time.\<close>

fun tall :: \<open>('k \<Rightarrow> 'h \<Rightarrow> 'c \<Rightarrow> bool) \<Rightarrow> ('k \<times> 'h \<times> 'c) list \<Rightarrow> bool\<close> where
  \<open>tall P [] = True\<close>
| \<open>tall P ((i, h, k) # xs) = (P i h k \<and> tall P xs)\<close>

lemma tall_iff: \<open>tall P xs \<longleftrightarrow> (\<forall>(i, h, k) \<in> set xs. P i h k)\<close>
  by (induction P xs rule: tall.induct) auto

lemma tallD1: \<open>tall P ((i, h, k) # xs) \<Longrightarrow> P i h k\<close>
  and tallD2: \<open>tall P ((i, h, k) # xs) \<Longrightarrow> tall P xs\<close>
  and tallI: \<open>P i h k \<Longrightarrow> tall P xs \<Longrightarrow> tall P ((i, h, k) # xs)\<close>
  and tallNil: \<open>tall P []\<close>
  by simp_all

lemma kof_tr:
  assumes \<open>distinct (map fst tr)\<close>
  shows \<open>tall (\<lambda>i h k. (\<forall>x. kof (map hpart tr) i x = h x) \<and>
      (\<forall>y. kof (map kpart tr) i y = k y)) tr\<close>
  unfolding tall_iff
proof (intro ballI, clarify)
  fix i h k assume m: \<open>(i, h, k) \<in> set tr\<close>
  have m1: \<open>(i, h) \<in> set (map hpart tr)\<close> and m2: \<open>(i, k) \<in> set (map kpart tr)\<close>
    using m by (force simp: hpart_def kpart_def)+
  have d1: \<open>distinct (map fst (map hpart tr))\<close> and d2: \<open>distinct (map fst (map kpart tr))\<close>
    using assms by simp_all
  show \<open>(\<forall>x. kof (map hpart tr) i x = h x) \<and> (\<forall>y. kof (map kpart tr) i y = k y)\<close>
    using kof_in[OF d1 m1] kof_in[OF d2 m2] by simp
qed

theorem fuse_tree:
  assumes d: \<open>distinct (map fst tr)\<close>
    and H: \<open>tall (\<lambda>i h k. \<forall>cs. h (Node i cs) = k (map (vof (kof (map hpart tr))) cs)) tr\<close>
  shows \<open>vof (kof (map hpart tr)) t = afold (kof (map kpart tr)) t\<close>
proof (rule vof_afold)
  fix i cs
  show \<open>kof (map hpart tr) i (Node i cs) = kof (map kpart tr) i (map (vof (kof (map hpart tr))) cs)\<close>
  proof (cases \<open>i \<in> set (map fst tr)\<close>)
    case True
    then obtain h k where m: \<open>(i, h, k) \<in> set tr\<close> by auto
    from kof_tr[OF d] m have \<open>\<forall>x. kof (map hpart tr) i x = h x\<close> \<open>\<forall>y. kof (map kpart tr) i y = k y\<close>
      by (auto simp: tall_iff)
    moreover from H m have \<open>h (Node i cs) = k (map (vof (kof (map hpart tr))) cs)\<close>
      by (auto simp: tall_iff)
    ultimately show ?thesis by simp
  next
    case False
    then show ?thesis using kof_notin[of i \<open>map hpart tr\<close>] kof_notin[of i \<open>map kpart tr\<close>] by simp
  qed
qed

lemma distinct_lix:
  assumes \<open>distinct ds\<close> \<open>set ds \<subseteq> set ns\<close>
  shows \<open>distinct (map (lix ns) ds)\<close>
proof -
  have \<open>inj_on (lix ns) (set ds)\<close>
    by (rule inj_onI) (metis assms(2) lnm_lix subsetD)
  then show ?thesis using assms(1) by (simp add: distinct_map)
qed

lemma names_sub: \<open>remdups (zs @ ds) = ns \<Longrightarrow> set ds \<subseteq> set ns\<close>
  by auto

lemma lix_keys_range:
  assumes \<open>map fst tr = map (lix ns) ds\<close> \<open>set ds \<subseteq> set ns\<close>
  shows \<open>\<forall>i \<in> set (map fst tr). 0 \<le> i \<and> i < zi (length ns)\<close>
proof
  fix i assume \<open>i \<in> set (map fst tr)\<close>
  then obtain A where A: \<open>A \<in> set ds\<close> \<open>i = lix ns A\<close> using assms(1) by auto
  with assms(2) have \<open>0 \<le> i \<and> nat_of_integer i < length ns\<close> using lix_range[of A ns] by auto
  then show \<open>0 \<le> i \<and> i < zi (length ns)\<close> by (simp add: less_zi)
qed

lemma map_fst_lix:
  \<open>map fst ((i, h, k) # xs) = i # map fst xs\<close> \<open>map fst [] = []\<close>
  \<open>map (lix ns) (A # ds) = lix ns A # map (lix ns) ds\<close> \<open>map (lix ns) [] = []\<close>
  \<open>map kpart ((i, h, k) # xs) = (i, k) # map kpart xs\<close> \<open>map kpart [] = []\<close>
  by (simp_all add: kpart_def)

lemma nd_other:
  assumes \<open>\<And>i cs. nd (Node i cs) = (if i = ix then b cs else None)\<close>
  shows \<open>i \<noteq> ix \<Longrightarrow> nd (Node i cs) = None\<close>
  using assms by simp

subsection \<open>The actions as an array\<close>

definition ftab :: \<open>nat \<Rightarrow> (integer \<times> 'f) list \<Rightarrow> 'f option iarray\<close> where
  \<open>ftab n ps = IArray (map (\<lambda>j. map_of ps (zi j)) [0..<n])\<close>

definition kget :: \<open>('a \<Rightarrow> 'b option) option iarray \<Rightarrow> integer \<Rightarrow> 'a \<Rightarrow> 'b option\<close> where
  \<open>kget a i x = (case aget a i of None \<Rightarrow> None | Some f \<Rightarrow> f x)\<close>

lemma kget_ftab:
  assumes \<open>\<forall>i \<in> set (map fst ps). 0 \<le> i \<and> i < zi n\<close>
  shows \<open>kget (ftab n ps) i x = kof ps i x\<close>
proof (cases \<open>0 \<le> i \<and> i < zi n\<close>)
  case True
  then have \<open>nat_of_integer i < n\<close> using less_zi by blast
  with True show ?thesis
    by (simp add: kget_def kof_def aget_def ftab_def zi_nat_of_integer)
next
  case False
  then have \<open>map_of ps i = None\<close> using assms by (auto simp: map_of_eq_None_iff)
  with False show ?thesis
    by (auto simp: kget_def kof_def aget_def ftab_def less_zi)
qed

definition fnode :: \<open>(('m, 'ch, 't, 'v) fv list \<Rightarrow> 'v option) option iarray \<Rightarrow>
    integer \<Rightarrow> ('m, 'ch, 't, 'v) fv list \<Rightarrow> ('m, 'ch, 't, 'v) fv\<close> where
  \<open>fnode a i us = FNode i (kget a i us)\<close>

subsection \<open>The run on values\<close>

definition ftree :: \<open>('w \<Rightarrow> ('t, 'ch, 'm) token_scheme) \<Rightarrow>
    (integer \<Rightarrow> ('m, 'ch, 't, 'v) fv list \<Rightarrow> ('m, 'ch, 't, 'v) fv) \<Rightarrow> (integer, 't) dact \<Rightarrow>
    'w list \<Rightarrow> ('m, 'ch, 't, 'v) fv list \<Rightarrow> ('m, 'ch, 't, 'v) fv list\<close> where
  \<open>ftree dec N act v us = (case act of
      DShift \<Rightarrow> FLeaf (dec (hd v)) # us
    | DReduce pr \<Rightarrow> N (fst pr) (rev (take_as (snd pr) us)) # drop_as (snd pr) us)\<close>

definition fresult :: \<open>('m, 'ch, 't, 'v) fv list \<Rightarrow> ('m, 'ch, 't, 'v) fv option\<close> where
  \<open>fresult us = (case us of u # _ \<Rightarrow> Some u | [] \<Rightarrow> None)\<close>

partial_function (option) frun ::
  \<open>('k list \<times> 'w list \<Rightarrow> ((integer, 't) dact \<times> 'k list \<times> 'w list) option) \<Rightarrow>
    ('k list \<times> 'w list \<Rightarrow> bool) \<Rightarrow>
    (integer \<Rightarrow> ('m, 'ch, 't, 'v) fv list \<Rightarrow> ('m, 'ch, 't, 'v) fv) \<Rightarrow>
    ('w \<Rightarrow> ('t, 'ch, 'm) token_scheme) \<Rightarrow>
    'k list \<times> 'w list \<times> ('m, 'ch, 't, 'v) fv list \<Rightarrow> ('m, 'ch, 't, 'v) fv option\<close>
  where
  \<open>frun ctl fin N dec st = (case st of (stk, v, us) \<Rightarrow>
     if fin (stk, v) then fresult us
     else Option.bind (ctl (stk, v)) (\<lambda>(act, stk', v').
       frun ctl fin N dec (stk', v', ftree dec N act v us)))\<close>

lemmas frun_simps [code] = frun.simps

context
  fixes U :: \<open>('m, 'ch, integer, 't) ast \<Rightarrow> ('m, 'ch, 't, 'v) fv\<close>
    and N :: \<open>integer \<Rightarrow> ('m, 'ch, 't, 'v) fv list \<Rightarrow> ('m, 'ch, 't, 'v) fv\<close>
  assumes U_leaf: \<open>\<And>w. U (Leaf w) = FLeaf w\<close>
    and U_node: \<open>\<And>i cs. U (Node i cs) = N i (map U cs)\<close>
begin

lemma ftree_map: \<open>ftree dec N a v (map U ts) = map U (xtree dec a v ts)\<close>
  by (cases a) (simp_all add: ftree_def xtree_def U_leaf U_node take_as_eq drop_as_eq
      take_map drop_map rev_map)

lemma fresult_map: \<open>fresult (map U ts) = map_option U (sresult ts)\<close>
  by (simp add: fresult_def sresult_def split: list.split)

theorem frun_map:
  \<open>frun ctl fin N dec (stk, v, map U ts) = map_option U (nrun ctl fin dec (stk, v, ts))\<close>
proof -
  have one: \<open>frun ctl fin N dec (fst st, fst (snd st), map U (snd (snd st))) = Some (U t)\<close>
    if h: \<open>nrun ctl fin dec st = Some t\<close> for st t
  proof -
    have \<open>ctl = ctl \<longrightarrow> fin = fin \<longrightarrow> dec = dec \<longrightarrow>
        frun ctl fin N dec (fst st, fst (snd st), map U (snd (snd st))) = Some (U t)\<close>
    proof (rule nrun.raw_induct[OF _ h, where P = \<open>\<lambda>c f d st t. c = ctl \<longrightarrow> f = fin \<longrightarrow> d = dec \<longrightarrow>
        frun ctl fin N dec (fst st, fst (snd st), map U (snd (snd st))) = Some (U t)\<close>], goal_cases)
      case (1 F c f d st t)
      obtain stk v ts where st: \<open>st = (stk, v, ts)\<close> by (cases st)
      show ?case
      proof (intro impI)
        assume c: \<open>c = ctl\<close> and f: \<open>f = fin\<close> and d: \<open>d = dec\<close>
        show \<open>frun ctl fin N dec (fst st, fst (snd st), map U (snd (snd st))) = Some (U t)\<close>
        proof (cases \<open>fin (stk, v)\<close>)
          case True
          with "1"(2) show ?thesis unfolding st c f
            by (subst frun.simps) (auto simp: fresult_map)
        next
          case False
          from False "1"(2) obtain a stk' v' where
              sc: \<open>ctl (stk, v) = Some (a, stk', v')\<close>
            and rec: \<open>F c f d (stk', v', xtree d a v ts) = Some t\<close>
            unfolding st c f by (auto simp: bind_eq_Some_conv)
          from "1"(1)[OF rec] c f d
          have \<open>frun ctl fin N dec (stk', v', map U (xtree dec a v ts)) = Some (U t)\<close> by simp
          then show ?thesis unfolding st using False sc
            by (subst frun.simps) (simp add: ftree_map)
        qed
      qed
    qed
    then show ?thesis by blast
  qed
  have two: \<open>\<exists>t'. t = U t' \<and> nrun ctl fin dec (stk, v, ts) = Some t'\<close>
    if h: \<open>frun ctl fin N dec st2 = Some t\<close> and e: \<open>st2 = (stk, v, map U ts)\<close> for st2 t stk v ts
  proof -
    have \<open>ctl = ctl \<longrightarrow> fin = fin \<longrightarrow> N = N \<longrightarrow> dec = dec \<longrightarrow> (\<forall>stk v ts.
        st2 = (stk, v, map U ts) \<longrightarrow> (\<exists>t'. t = U t' \<and> nrun ctl fin dec (stk, v, ts) = Some t'))\<close>
    proof (rule frun.raw_induct[OF _ h, where P = \<open>\<lambda>c f n d st2 t. c = ctl \<longrightarrow> f = fin \<longrightarrow> n = N \<longrightarrow>
        d = dec \<longrightarrow> (\<forall>stk v ts. st2 = (stk, v, map U ts) \<longrightarrow>
          (\<exists>t'. t = U t' \<and> nrun ctl fin dec (stk, v, ts) = Some t'))\<close>], goal_cases)
      case (1 F c f n d st2 t)
      show ?case
      proof (intro impI allI)
        fix stk v ts
        assume c: \<open>c = ctl\<close> and f: \<open>f = fin\<close> and n: \<open>n = N\<close> and d: \<open>d = dec\<close>
          and st: \<open>st2 = (stk, v, map U ts)\<close>
        show \<open>\<exists>t'. t = U t' \<and> nrun ctl fin dec (stk, v, ts) = Some t'\<close>
        proof (cases \<open>fin (stk, v)\<close>)
          case True
          with "1"(2) show ?thesis unfolding st c f
            by (subst nrun.simps) (auto simp: fresult_map)
        next
          case False
          from False "1"(2) obtain a stk' v' where
              sc: \<open>ctl (stk, v) = Some (a, stk', v')\<close>
            and rec: \<open>F c f n d (stk', v', ftree d n a v (map U ts)) = Some t\<close>
            unfolding st c f by (auto simp: bind_eq_Some_conv)
          have \<open>\<exists>t'. t = U t' \<and> nrun ctl fin dec (stk', v', xtree dec a v ts) = Some t'\<close>
            using "1"(1)[OF rec] c f n d by (simp add: ftree_map)
          then show ?thesis using False sc by (subst nrun.simps) simp
        qed
      qed
    qed
    then show ?thesis using e by blast
  qed
  show ?thesis
  proof (cases \<open>nrun ctl fin dec (stk, v, ts)\<close>)
    case None
    have \<open>frun ctl fin N dec (stk, v, map U ts) = None\<close>
    proof (rule ccontr)
      assume \<open>frun ctl fin N dec (stk, v, map U ts) \<noteq> None\<close>
      then obtain t where \<open>frun ctl fin N dec (stk, v, map U ts) = Some t\<close> by blast
      from two[OF this refl] None show False by auto
    qed
    with None show ?thesis by simp
  next
    case (Some t)
    then show ?thesis using one[OF Some] by simp
  qed
qed

end

subsection \<open>The code equation\<close>

text \<open>The run on trees followed by the decoder of the start, over the run on values
  followed by the projection to the start's carrier: \<open>V\<close> from \<open>fuse_tree\<close>, \<open>L\<close>
  from \<open>fproj_vof\<close>, and the array of the actions.\<close>

theorem bind_frun:
  assumes V: \<open>\<And>t. vof dl t = afold K t\<close> and L: \<open>\<And>c. fproj ix pj (vof dl c) = nd c\<close>
    and N: \<open>\<And>i us. N i us = FNode i (K i us)\<close>
  shows \<open>Option.bind (nrun ctl fin dec (stk, v, [])) nd =
    Option.bind (frun ctl fin N dec (stk, v, [])) (fproj ix pj)\<close>
proof -
  have \<open>frun ctl fin N dec (stk, v, map (afold K) []) = map_option (afold K) (nrun ctl fin dec (stk, v, []))\<close>
    by (rule frun_map) (simp_all add: N)
  moreover have \<open>fproj ix pj (afold K t) = nd t\<close> for t using L[of t] V[of t] by simp
  ultimately show ?thesis by (simp add: bind_map_option comp_def)
qed

lemma fnode_kof:
  assumes \<open>ftab n (map kpart tr) = a\<close> \<open>\<forall>i \<in> set (map fst tr). 0 \<le> i \<and> i < zi n\<close>
  shows \<open>fnode a i us = FNode i (kof (map kpart tr) i us)\<close>
proof -
  have \<open>\<forall>i \<in> set (map fst (map kpart tr)). 0 \<le> i \<and> i < zi n\<close> using assms(2) by simp
  from kget_ftab[OF this, of i us] assms(1) show ?thesis by (simp add: fnode_def)
qed

end
