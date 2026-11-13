(* Author: Basil Fürer, Claude *)

theory LR_Prec_Parse
  imports LR_Parser TIGER_Grammar.LR_Prec
begin

text \<open>The parser of the restricted grammar, stated against the grammar the user
  wrote.  All of it is inherited from the driver theorems on
  \<^term>\<open>restrict G d\<close>; \<^const>\<open>plain_ast\<close> drops the unit nodes of the chains and
  restores the original nonterminal names.

  In the terms of Klint and Visser, \<^const>\<open>prec_ok\<close> generates a filter, and the
  restricted grammar with \<open>plain orig_name\<close> as translation shows it context-free
  \<^cite>\<open>\<open>Def.~4.8\<close> in "klint1994-disambiguation-filters"\<close> once the checks pass;
  \<open>prec_ok_unique\<close> says the filter is completely disambiguating
  \<^cite>\<open>\<open>Def.~4.2\<close> in "klint1994-disambiguation-filters"\<close>, up to \<^const>\<open>erase\<close>.
  The informal counterparts are \<^cite>\<open>\<open>Thms.~6.1, 6.4\<close> in "adams2017-tree-automata"\<close>:
  intersection with a bottom-up deterministic automaton adds no ambiguity and no
  LR(k) conflicts.  Here nothing is inferred from the automaton: determinism and
  the conflict check are premises on the restricted grammar.\<close>

section \<open>Freshness of the shift name\<close>

lemma sub_nts: \<open>(X, i) \<in> set (sub nm r ks) \<Longrightarrow> X = Nt y \<Longrightarrow> \<exists>c. y = nm c\<close>
  by (auto simp: sub_def split: sym.splits)

lemma cprods_names:
  assumes \<open>(m, r) \<in> set (cprods P as key C nm L)\<close>
  shows \<open>\<exists>c. m = nm c\<close> and \<open>(X, i) \<in> set r \<Longrightarrow> X = Nt y \<Longrightarrow> \<exists>c. y = nm c\<close>
  using assms by (auto simp: cprods_def Let_def dest: sub_nts[OF _ refl])

lemma restrict_names:
  \<open>CHR ''#'' \<in> set (istart (restrict G d))\<close>
  \<open>(m, r) \<in> set (iprods (restrict G d)) \<Longrightarrow> CHR ''#'' \<in> set m\<close>
  \<open>(m, r) \<in> set (iprods (restrict G d)) \<Longrightarrow> (Nt y, i) \<in> set r \<Longrightarrow> CHR ''#'' \<in> set y\<close>
  by (auto simp: restrict_alt restrict_gen_def Let_def dest: cprods_names(1) cprods_names(2)[OF _ _ refl])

theorem fresh_name_restrict:
  assumes \<open>CHR ''#'' \<notin> set Shn\<close>
  shows \<open>fresh_name (restrict G d) Shn\<close>
  using assms restrict_names[where G = G and d = d] unfolding fresh_name_def by fastforce

section \<open>Unit chains on grammars without layout\<close>

text \<open>\<^const>\<open>restrict\<close> writes its unit chains with \<^const>\<open>Eq\<close>. If that is the only
  relation of the grammar besides \<^const>\<open>Any\<close>, and it stands on nonterminals only, the
  indices of the nodes are not observable: a tree of the grammar with all relations
  \<^const>\<open>Any\<close> is a tree of the original one with one index everywhere (\<open>rind\<close>).
  So the parser is built from \<open>restricted\<close>, which then passes \<^const>\<open>ii\<close> and gets
  the simple driver. The check is a computation on the restricted grammar, nothing about
  \<^const>\<open>restrict\<close> is needed.\<close>

definition rany :: \<open>('n, 't) is_cfg \<Rightarrow> ('n, 't) is_cfg\<close> where
  \<open>rany H = H\<lparr>iprods := map (\<lambda>(n, r). (n, map (\<lambda>(X, _). (X, Any)) r)) (iprods H)\<rparr>\<close>

definition rels_free :: \<open>('n, 't) is_cfg \<Rightarrow> bool\<close> where
  \<open>rels_free H \<longleftrightarrow> list_all (\<lambda>(m, r). list_all (\<lambda>(X, a). a = Any \<or> a = Eq \<and>
     (case X of Nt _ \<Rightarrow> True | Tm _ \<Rightarrow> False)) r) (iprods H)\<close>

definition relax :: \<open>('n, 't) is_cfg \<Rightarrow> ('n, 't) is_cfg\<close> where
  \<open>relax H = (if rels_free H then rany H else H)\<close>

definition restricted :: \<open>(string, 't) is_cfg \<Rightarrow> (string, 't) prec_decl \<Rightarrow> (string, 't) is_cfg\<close> where
  \<open>restricted G d = relax (restrict G d)\<close>

lemma relax_sel[simp]: \<open>istart (relax H) = istart H\<close> \<open>istart_ind (relax H) = istart_ind H\<close>
  by (simp_all add: relax_def rany_def)

fun rind :: \<open>nat \<Rightarrow> ('m, 'ch, 'n, 't) ptree \<Rightarrow> ('m, 'ch, 'n, 't) ptree\<close> where
  \<open>rind c (PLeaf t) = PLeaf t\<close>
| \<open>rind c (PNode n i ts) = PNode n c (map (rind c) ts)\<close>

lemma pyield_rind[simp]: \<open>pyield (rind c t) = pyield t\<close>
  by (induction c t rule: rind.induct) (auto intro!: arg_cong[of _ _ concat])

lemma erase_rind[simp]: \<open>erase (rind c t) = erase t\<close>
  by (induction c t rule: rind.induct) auto

lemma fst_proot_rind[simp]: \<open>fst (proot (rind c t)) = fst (proot t)\<close>
  by (cases t) auto

lemma wf_rany: \<open>wf_ptree H t \<Longrightarrow> wf_ptree (rany H) t\<close>
proof (induction rule: wf_ptree.induct)
  case (wf_leaf t)
  show ?case by (rule wf_ptree.wf_leaf)
next
  case (wf_node A rhs i pts)
  have \<open>(A, map (\<lambda>(X, _). (X, Any)) rhs) \<in> set (iprods (rany H))\<close>
    using wf_node.hyps by (force simp: rany_def)
  then show ?case
    by (rule wf_ptree.wf_node)
      (use wf_node.IH in \<open>auto simp: list_all2_conv_all_nth case_prod_beta\<close>)
qed

lemma wf_rind:
  assumes \<open>wf_ptree (rany H) t\<close>
    and rels: \<open>\<And>m r X a. (m, r) \<in> set (iprods H) \<Longrightarrow> (X, a) \<in> set r \<Longrightarrow> a = Any \<or> a = Eq \<and> (\<exists>y. X = Nt y)\<close>
  shows \<open>wf_ptree H (rind c t)\<close>
  using assms(1)
proof (induction rule: wf_ptree.induct)
  case (wf_leaf t)
  show ?case by (auto intro: wf_ptree.wf_leaf)
next
  case (wf_node A rhs i pts)
  from wf_node.hyps obtain r where r: \<open>(A, r) \<in> set (iprods H)\<close>
    \<open>rhs = map (\<lambda>(X, _). (X, Any)) r\<close> by (auto simp: rany_def)
  have len: \<open>length pts = length r\<close> using list_all2_lengthD[OF wf_node.IH] r(2) by simp
  have \<open>list_all2 (\<lambda>Xr pt. fst (proot pt) = fst Xr \<and> irel_sat (snd Xr) (snd (proot pt)) c \<and>
      wf_ptree H pt) r (map (rind c) pts)\<close>
  proof (rule list_all2_all_nthI)
    show \<open>length r = length (map (rind c) pts)\<close> using len by simp
  next
    fix k assume k: \<open>k < length r\<close>
    obtain X a where ra: \<open>r ! k = (X, a)\<close> by fastforce
    have m: \<open>(X, a) \<in> set r\<close> using k ra by (metis nth_mem)
    have ih: \<open>fst (proot (pts ! k)) = X\<close> \<open>wf_ptree H (rind c (pts ! k))\<close>
      using list_all2_nthD[OF wf_node.IH, of k] k r(2) ra by (auto simp: case_prod_beta)
    have \<open>irel_sat a (snd (proot (rind c (pts ! k)))) c\<close>
      using rels[OF r(1) m] ih(1) by (cases \<open>pts ! k\<close>) auto
    then show \<open>fst (proot (map (rind c) pts ! k)) = fst (r ! k) \<and>
        irel_sat (snd (r ! k)) (snd (proot (map (rind c) pts ! k))) c \<and>
        wf_ptree H (map (rind c) pts ! k)\<close>
      using k len ra ih by simp
  qed
  with r(1) show ?case by (auto intro: wf_ptree.wf_node)
qed

lemma wf_relax: \<open>wf_ptree H t \<Longrightarrow> wf_ptree (relax H) t\<close>
  by (simp add: relax_def wf_rany)

lemma relax_tree:
  assumes wf: \<open>wf_ptree (relax H) t\<close> and rt: \<open>proot t = (Nt n, i)\<close>
  shows \<open>\<exists>t'. wf_ptree H t' \<and> proot t' = (Nt n, i) \<and> pyield t' = pyield t \<and> erase t' = erase t\<close>
proof (cases \<open>rels_free H\<close>)
  case False
  with assms show ?thesis by (auto simp: relax_def)
next
  case True
  have rels: \<open>a = Any \<or> a = Eq \<and> (\<exists>y. X = Nt y)\<close>
    if \<open>(m, r) \<in> set (iprods H)\<close> \<open>(X, a) \<in> set r\<close> for m r X a
    using True that unfolding rels_free_def list_all_iff by (cases X) fastforce+
  have \<open>wf_ptree H (rind i t)\<close>
    using wf_rind[of H t, OF _ rels] wf True by (simp add: relax_def)
  moreover have \<open>proot (rind i t) = (Nt n, i)\<close> using rt by (cases t) auto
  ultimately show ?thesis by (intro exI[of _ \<open>rind i t\<close>]) simp
qed

lemma ii_relax: \<open>rels_free H \<Longrightarrow> ii (relax H)\<close>
  by (auto simp: ii_def relax_def rany_def list_all_iff)

lemma fresh_name_relax: \<open>fresh_name H Shn \<Longrightarrow> fresh_name (relax H) Shn\<close>
  unfolding fresh_name_def relax_def rany_def by (auto split: if_splits) (force+)

theorem fresh_name_restricted:
  assumes \<open>CHR ''#'' \<notin> set Shn\<close>
  shows \<open>fresh_name (restricted G d) Shn\<close>
  unfolding restricted_def by (rule fresh_name_relax[OF fresh_name_restrict[OF assms]])

section \<open>Between the two grammars\<close>

lemma accepts_root:
  fixes t :: \<open>('m, 'ch, 'n, 't) ptree\<close>
  assumes \<open>proot t = (Nt (istart G), j)\<close>
  shows \<open>prec_run G (compile G d) (pq0 G) t \<longleftrightarrow> prec_ok G d t\<close>
  by (rule accepts_iff_prec_ok) (use assms in simp)

context
  fixes G :: \<open>(string, 't) is_cfg\<close> and d :: \<open>(string, 't) prec_decl\<close>
  assumes ns: \<open>no_self_unit G\<close>
begin

lemma restrict_ptree_sound:
  fixes pt' :: \<open>('m, 'ch, string, 't) ptree\<close>
  assumes wf: \<open>wf_ptree (restrict G d) pt'\<close>
    and rt: \<open>proot pt' = (Nt (istart (restrict G d)), istart_ind (restrict G d))\<close>
  shows \<open>wf_ptree G (plain orig_name pt') \<and> proot (plain orig_name pt') = (Nt (istart G), istart_ind G) \<and>
    prec_ok G d (plain orig_name pt')\<close>
proof -
  obtain Q and cls :: \<open>_ \<Rightarrow> string\<close> where r: \<open>restrict_ok G (compile G d) (pq0 G) Q cls (restrict G d) orig_name\<close>
    using restrict_correct[OF ns] by blast
  interpret r: restrict_ok G \<open>compile G d\<close> \<open>pq0 G\<close> Q cls \<open>restrict G d\<close> orig_name by (fact r)
  have \<open>prec_run G (compile G d) (pq0 G) (plain orig_name pt') \<and>
      proot (plain orig_name pt') = (Nt (orig_name (istart (restrict G d))), snd (proot pt'))\<close>
    by (rule r.restrict_sound[OF wf]) (use rt r.start in auto)
  then have run: \<open>prec_run G (compile G d) (pq0 G) (plain orig_name pt')\<close>
    and root: \<open>proot (plain orig_name pt') = (Nt (istart G), istart_ind G)\<close>
    using r.start rt by auto
  have \<open>prec_ok G d (plain orig_name pt')\<close>
    using accepts_root[OF root] run by blast
  with run root prec_run_wf[OF run] show ?thesis by blast
qed

lemma restrict_ptree_complete:
  fixes pt :: \<open>('m, 'ch, string, 't) ptree\<close>
  assumes wf: \<open>wf_ptree G pt\<close> and rt: \<open>proot pt = (Nt (istart G), istart_ind G)\<close>
    and ok: \<open>prec_ok G d pt\<close>
  shows \<open>\<exists>pt'. wf_ptree (restrict G d) pt' \<and>
    proot pt' = (Nt (istart (restrict G d)), istart_ind (restrict G d)) \<and> plain orig_name pt' = pt\<close>
proof -
  obtain Q and cls :: \<open>_ \<Rightarrow> string\<close> where r: \<open>restrict_ok G (compile G d) (pq0 G) Q cls (restrict G d) orig_name\<close>
    using restrict_correct[OF ns] by blast
  interpret r: restrict_ok G \<open>compile G d\<close> \<open>pq0 G\<close> Q cls \<open>restrict G d\<close> orig_name by (fact r)
  have \<open>prec_run G (compile G d) (pq0 G) pt\<close>
    using accepts_root[OF rt] ok by blast
  from r.restrict_complete[OF this r.start(1)] rt r.start show ?thesis by auto
qed

lemma restricted_ptree_sound:
  fixes pt' :: \<open>('m, 'ch, string, 't) ptree\<close>
  assumes wf: \<open>wf_ptree (restricted G d) pt'\<close>
    and rt: \<open>proot pt' = (Nt (istart (restricted G d)), istart_ind (restricted G d))\<close>
  shows \<open>\<exists>pt. wf_ptree G pt \<and> proot pt = (Nt (istart G), istart_ind G) \<and>
    pyield pt = pyield pt' \<and> erase pt = plain_ast orig_name (erase pt') \<and> prec_ok G d pt\<close>
proof -
  from relax_tree[OF wf[unfolded restricted_def] rt[unfolded restricted_def relax_sel]]
  obtain s :: \<open>('m, 'ch, string, 't) ptree\<close> where s: \<open>wf_ptree (restrict G d) s\<close>
    \<open>proot s = (Nt (istart (restrict G d)), istart_ind (restrict G d))\<close>
    \<open>pyield s = pyield pt'\<close> \<open>erase s = erase pt'\<close> by blast
  from restrict_ptree_sound[OF s(1,2)] s(3,4) erase_plain[of orig_name s]
  show ?thesis by (intro exI[of _ \<open>plain orig_name s\<close>]) simp
qed

lemma restricted_ptree_complete:
  fixes pt :: \<open>('m, 'ch, string, 't) ptree\<close>
  assumes \<open>wf_ptree G pt\<close> \<open>proot pt = (Nt (istart G), istart_ind G)\<close> \<open>prec_ok G d pt\<close>
  shows \<open>\<exists>pt'. wf_ptree (restricted G d) pt' \<and>
    proot pt' = (Nt (istart (restricted G d)), istart_ind (restricted G d)) \<and>
    plain orig_name pt' = pt\<close>
  using restrict_ptree_complete[OF assms] wf_relax unfolding restricted_def relax_sel by blast

section \<open>The driver\<close>

theorem dparse_restrict_sound:
  assumes fn: \<open>fresh_name (restricted G d) Shn\<close>
    and p: \<open>dparse (restricted G d) Shn w = Some t\<close>
  shows \<open>\<exists>pt. wf_ptree G pt \<and> proot pt = (Nt (istart G), istart_ind G) \<and> pyield pt = w \<and>
    erase pt = plain_ast orig_name t \<and> prec_ok G d pt\<close>
proof -
  from dparse_sound_ast[OF fn p] obtain pt' where wf: \<open>wf_ptree (restricted G d) pt'\<close>
    and rt: \<open>proot pt' = (Nt (istart (restricted G d)), istart_ind (restricted G d))\<close>
    and e: \<open>erase pt' = t\<close> and y: \<open>pyield pt' = w\<close>
    unfolding ast_of_def by blast
  from restricted_ptree_sound[OF wf rt] e y show ?thesis by blast
qed

corollary dparse_restrict_ast:
  assumes \<open>fresh_name (restricted G d) Shn\<close> and \<open>dparse (restricted G d) Shn w = Some t\<close>
  shows \<open>ast_of G (Nt (istart G)) (istart_ind G) (plain_ast orig_name t) w\<close>
  using dparse_restrict_sound[OF assms] unfolding ast_of_def by metis

theorem dparse_restrict_complete:
  fixes pt :: \<open>('m, 'ch, string, 't) ptree\<close>
  assumes fn: \<open>fresh_name (restricted G d) Shn\<close> and det: \<open>mdet (restricted G d) Shn\<close>
    and wf: \<open>wf_ptree G pt\<close> and rt: \<open>proot pt = (Nt (istart G), istart_ind G)\<close>
    and ok: \<open>prec_ok G d pt\<close>
  shows \<open>\<exists>t. dparse (restricted G d) Shn (pyield pt) = Some t\<close>
proof -
  from restricted_ptree_complete[OF wf rt ok] obtain pt' where
    \<open>wf_ptree (restricted G d) pt'\<close>
    \<open>proot pt' = (Nt (istart (restricted G d)), istart_ind (restricted G d))\<close>
    \<open>plain orig_name pt' = pt\<close> by blast
  from dparse_complete[OF fn det this(1,2)] this(3) show ?thesis by auto
qed

theorem dparse_restrict_exact:
  fixes pt :: \<open>('m, 'ch, string, 't) ptree\<close>
  assumes fn: \<open>fresh_name (restricted G d) Shn\<close> and det: \<open>mdet (restricted G d) Shn\<close>
    and chk: \<open>acc_conflicts (restricted G d) Shn = []\<close>
    and wf: \<open>wf_ptree G pt\<close> and rt: \<open>proot pt = (Nt (istart G), istart_ind G)\<close>
    and ok: \<open>prec_ok G d pt\<close>
  shows \<open>\<exists>t. dparse (restricted G d) Shn (pyield pt) = Some t \<and> plain_ast orig_name t = erase pt\<close>
proof -
  from restricted_ptree_complete[OF wf rt ok] obtain pt' where
    w: \<open>wf_ptree (restricted G d) pt'\<close>
    and r: \<open>proot pt' = (Nt (istart (restricted G d)), istart_ind (restricted G d))\<close>
    and p: \<open>plain orig_name pt' = pt\<close> by blast
  have \<open>dparse (restricted G d) Shn (pyield pt') = Some (erase pt')\<close>
    using dparse_complete_exact[OF fn det chk w r] by simp
  then show ?thesis using p erase_plain[of orig_name pt'] by auto
qed

text \<open>Uniqueness: two trees that satisfy the declaration and read the same word
  have the same ast.\<close>

corollary prec_ok_unique:
  fixes pt pt2 :: \<open>('m, 'ch, string, 't) ptree\<close>
  assumes fn: \<open>fresh_name (restricted G d) Shn\<close> and det: \<open>mdet (restricted G d) Shn\<close>
    and chk: \<open>acc_conflicts (restricted G d) Shn = []\<close>
    and a: \<open>wf_ptree G pt\<close> \<open>proot pt = (Nt (istart G), istart_ind G)\<close> \<open>prec_ok G d pt\<close>
    and b: \<open>wf_ptree G pt2\<close> \<open>proot pt2 = (Nt (istart G), istart_ind G)\<close> \<open>prec_ok G d pt2\<close>
    and y: \<open>pyield pt = pyield pt2\<close>
  shows \<open>erase pt = erase pt2\<close>
  using dparse_restrict_exact[OF fn det chk a] dparse_restrict_exact[OF fn det chk b] y by force

end

section \<open>Schematic forms for the backend\<close>

text \<open>A parser of a grammar with declarations is
  \<open>\<lambda>w. Option.bind (dparse Gr Shn w) (dec \<circ> plain_ast orig_name)\<close>, with \<open>Gr\<close> a constant
  defined as \<^term>\<open>restricted G d\<close> and \<open>dec\<close> a decoder of \<open>G\<close>, so that the premises about
  \<open>dec\<close> are the ones of a grammar without declarations.\<close>

definition prec_lang :: \<open>(string, 't) is_cfg \<Rightarrow> (string, 't) prec_decl \<Rightarrow> ('m, 'ch, 't) tword set\<close> where
  \<open>prec_lang G d = {w. \<exists>pt :: ('m, 'ch, string, 't) ptree. wf_ptree G pt \<and>
     proot pt = (Nt (istart G), istart_ind G) \<and> pyield pt = w \<and> prec_ok G d pt}\<close>

lemma no_self_unitI:
  assumes \<open>list_all (\<lambda>p. case snd p of [(Nt m, r)] \<Rightarrow> m \<noteq> fst p | _ \<Rightarrow> True) (iprods G)\<close>
  shows \<open>no_self_unit G\<close>
  using assms by (fastforce simp: no_self_unit_def list_all_iff)

context
  fixes G Gr :: \<open>(string, 't) is_cfg\<close> and d :: \<open>(string, 't) prec_decl\<close>
    and parse_fn and dec :: \<open>('m, 'ch, string, 't) ast \<Rightarrow> 'x option\<close> and Shn
  assumes body: \<open>parse_fn = (\<lambda>w. Option.bind (dparse Gr Shn w) (dec \<circ> plain_ast orig_name))\<close>
    and gr: \<open>Gr = restricted G d\<close>
    and ns: \<open>no_self_unit G\<close>
    and fn: \<open>fresh_name Gr Shn\<close>
begin

lemma parse_fn_tree:
  assumes rec: \<open>parse_fn w = Some x\<close>
  shows \<open>\<exists>pt :: ('m, 'ch, string, 't) ptree. wf_ptree G pt \<and>
    proot pt = (Nt (istart G), istart_ind G) \<and> pyield pt = w \<and> prec_ok G d pt \<and>
    dec (erase pt) = Some x\<close>
proof -
  from rec obtain t where p: \<open>dparse Gr Shn w = Some t\<close> and de: \<open>dec (plain_ast orig_name t) = Some x\<close>
    by (auto simp: body bind_eq_Some_conv)
  from dparse_restrict_sound[OF ns fn[unfolded gr] p[unfolded gr]] show ?thesis
    using de by metis
qed

lemma parse_fn_lang: \<open>parse_fn w = Some x \<Longrightarrow> w \<in> prec_lang G d\<close>
  using parse_fn_tree unfolding prec_lang_def by blast

lemma parse_fn_complete_lang:
  assumes det: \<open>mdet Gr Shn\<close> and mem: \<open>w \<in> prec_lang G d\<close>
    and dec_total: \<open>\<And>t. ast_of G (Nt (istart G)) (istart_ind G) t w \<Longrightarrow> \<exists>x. dec t = Some x\<close>
  shows \<open>\<exists>x. parse_fn w = Some x\<close>
proof -
  from mem obtain pt :: \<open>('m, 'ch, string, 't) ptree\<close> where wf: \<open>wf_ptree G pt\<close>
    and rt: \<open>proot pt = (Nt (istart G), istart_ind G)\<close> and y: \<open>pyield pt = w\<close>
    and ok: \<open>prec_ok G d pt\<close>
    unfolding prec_lang_def by blast
  from dparse_restrict_complete[OF ns fn[unfolded gr] det[unfolded gr] wf rt ok] y
  obtain t where p: \<open>dparse (restricted G d) Shn w = Some t\<close> by blast
  have \<open>ast_of G (Nt (istart G)) (istart_ind G) (plain_ast orig_name t) w\<close>
    by (rule dparse_restrict_ast[OF ns fn[unfolded gr] p])
  from dec_total[OF this] show ?thesis using p by (auto simp: body gr)
qed

lemma parse_fn_complete:
  fixes pt :: \<open>('m, 'ch, string, 't) ptree\<close>
  assumes det: \<open>mdet Gr Shn\<close> and chk: \<open>acc_conflicts Gr Shn = []\<close>
    and wf: \<open>wf_ptree G pt\<close> and rt: \<open>proot pt = (Nt (istart G), istart_ind G)\<close>
    and ok: \<open>prec_ok G d pt\<close> and de: \<open>dec (erase pt) = Some x\<close>
  shows \<open>parse_fn (pyield pt) = Some x\<close>
  using dparse_restrict_exact[OF ns fn[unfolded gr] det[unfolded gr] chk[unfolded gr] wf rt ok] de
  by (auto simp: body gr)

lemma parse_fn_no_error:
  assumes rec: \<open>parse_fn w = Some x\<close> and none: \<open>\<forall>y \<in> set w. tok y \<noteq> e\<close>
  shows \<open>\<exists>t. dec t = Some x \<and> ast_of G (Nt (istart G)) (istart_ind G) t w \<and> e \<notin> set (atoks t)\<close>
proof -
  from parse_fn_tree[OF rec] obtain pt :: \<open>('m, 'ch, string, 't) ptree\<close> where
    \<open>wf_ptree G pt\<close> \<open>proot pt = (Nt (istart G), istart_ind G)\<close> \<open>pyield pt = w\<close>
    \<open>dec (erase pt) = Some x\<close> by blast
  note pt = this
  have ne: \<open>e \<notin> set (atoks (erase pt))\<close> using atoks_erase[of pt] none pt(3) by auto
  have \<open>ast_of G (Nt (istart G)) (istart_ind G) (erase pt) w\<close>
    unfolding ast_of_def using pt by blast
  with pt(4) ne show ?thesis by blast
qed

end

text \<open>For \<^theory_text>\<open>parser (ast)\<close>: the decoder is \<^const>\<open>Some\<close>, the parser returns the tree
  of \<open>G\<close>'s names.\<close>

context
  fixes G Gr :: \<open>(string, 't) is_cfg\<close> and d :: \<open>(string, 't) prec_decl\<close> and Shn
    and parse_fn :: \<open>('m, 'ch, 't) tword \<Rightarrow> ('m, 'ch, string, 't) ast option\<close>
  assumes body: \<open>parse_fn = (\<lambda>w. Option.bind (dparse Gr Shn w) (Some \<circ> plain_ast orig_name))\<close>
    and gr: \<open>Gr = restricted G d\<close>
    and ns: \<open>no_self_unit G\<close>
    and fn: \<open>fresh_name Gr Shn\<close>
begin

lemma parse_fn_ast_tree:
  assumes rec: \<open>parse_fn w = Some t\<close>
  shows \<open>\<exists>pt :: ('m, 'ch, string, 't) ptree. wf_ptree G pt \<and>
    proot pt = (Nt (istart G), istart_ind G) \<and> pyield pt = w \<and> prec_ok G d pt \<and> erase pt = t\<close>
  using parse_fn_tree[OF body gr ns fn rec] by simp

lemma parse_fn_ast_complete_lang:
  assumes det: \<open>mdet Gr Shn\<close> and mem: \<open>w \<in> prec_lang G d\<close>
  shows \<open>\<exists>t. parse_fn w = Some t\<close>
  by (rule parse_fn_complete_lang[OF body gr ns fn det mem]) simp

lemma parse_fn_ast_complete:
  fixes pt :: \<open>('m, 'ch, string, 't) ptree\<close>
  assumes det: \<open>mdet Gr Shn\<close> and chk: \<open>acc_conflicts Gr Shn = []\<close>
    and wf: \<open>wf_ptree G pt\<close> and rt: \<open>proot pt = (Nt (istart G), istart_ind G)\<close>
    and ok: \<open>prec_ok G d pt\<close>
  shows \<open>parse_fn (pyield pt) = Some (erase pt)\<close>
  by (rule parse_fn_complete[OF body gr ns fn det chk wf rt ok]) simp

lemma parse_fn_ast_no_error:
  assumes rec: \<open>parse_fn w = Some t\<close> and none: \<open>\<forall>y \<in> set w. tok y \<noteq> e\<close>
  shows \<open>ast_of G (Nt (istart G)) (istart_ind G) t w \<and> e \<notin> set (atoks t)\<close>
  using parse_fn_no_error[OF body gr ns fn rec none] by simp

end

ML_file \<open>lr_prec.ML\<close>

end
