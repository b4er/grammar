theory LR
  imports Grammar_Command.Indentation_Sensitive "HOL-Library.While_Combinator"
begin

section \<open>Fuel-free GLR steps\<close>

text \<open>
  The table layer: the LR(0) automaton over the cores of the \<open>k = 0\<close>
  frames, the column-relative first table, and per-item LALR(1) lookahead
  cells relating the token's column to the item's anchor.  The cells stand
  in for the paper's Sect. 5.6 lookahead tuples: the parser of
  \<^text>\<open>LR_Driver\<close> is LALR(1)-style, not the canonical LR(1) instance of
  Algorithm 8; \<^text>\<open>LR_Det\<close> shows that the cells cover its lookahead.

  The GLR machine of \<^text>\<open>Indentation_Sensitive\<close> section 5 is a
  checker whose steps carry explicit closure fuel.  This section removes the
  fuel by searching for the least sufficient one, which exists by
  \<^text>\<open>xcls_stable_ex\<close>.
\<close>

subsection \<open>The least satisfying number, executably\<close>

text \<open>The least \<open>n\<close> with \<open>P n\<close>, by \<^const>\<open>while_option\<close>; defined
  whenever a witness exists.  Every fuelled fixpoint of this theory uses it.\<close>

definition nat_search :: \<open>(nat \<Rightarrow> bool) \<Rightarrow> nat\<close> where
  \<open>nat_search P = the (while_option (\<lambda>n. \<not> P n) Suc 0)\<close>

lemma nat_search_sat:
  assumes \<open>P k\<close>
  shows \<open>P (nat_search P)\<close>
proof -
  have \<open>n \<le> k \<Longrightarrow> \<not> P n \<Longrightarrow> Suc n \<le> k \<and> k - Suc n < k - n\<close> for n
    using assms by (cases \<open>n = k\<close>) auto
  then obtain t where t: \<open>while_option (\<lambda>n. \<not> P n) Suc 0 = Some t\<close>
    using measure_while_option_Some[of \<open>\<lambda>n. n \<le> k\<close> \<open>\<lambda>n. \<not> P n\<close> Suc \<open>\<lambda>n. k - n\<close> 0]
    by auto
  with while_option_stop[OF t] show ?thesis
    by (simp add: nat_search_def)
qed

subsection \<open>Fuel-free closure\<close>

definition xfuel :: \<open>('n, 't) is_cfg \<Rightarrow> ('n, 't) xitem list \<Rightarrow> nat\<close> where
  \<open>xfuel G xs = nat_search (\<lambda>t. xstable G xs (xiter G xs t))\<close>

definition xclosure_auto :: \<open>('n, 't) is_cfg \<Rightarrow> ('n, 't) xitem list \<Rightarrow> ('n, 't) xitem list\<close> where
  \<open>xclosure_auto G xs = xclosure G (xfuel G xs) xs\<close>

lemma xfuel_stable: \<open>xstable G xs (xiter G xs (xfuel G xs))\<close>
proof -
  obtain fuel where \<open>xstable G xs (xiter G xs fuel)\<close>
    using xcls_stable_ex by blast
  from nat_search_sat[of \<open>\<lambda>t. xstable G xs (xiter G xs t)\<close>, OF this]
  show ?thesis by (simp add: xfuel_def)
qed

lemma xclosure_chk_xfuel:
  \<open>xclosure_chk G (xfuel G xs) xs = Some (xclosure_auto G xs)\<close>
  using xfuel_stable unfolding xclosure_chk_def xclosure_auto_def by simp

text \<open>The fuel-free closure concretises to the abstract factored closure,
  without a fuel hypothesis.\<close>

theorem xclosure_auto_correct:
  \<open>fconcs (xset (xclosure_auto G xs)) = fconcs (fclosure G 0 (xset xs))\<close>
  using xclosure_chk_correct[OF xclosure_chk_xfuel] .

subsection \<open>Acceptance\<close>

text \<open>Acceptance condition on a configuration: the post-\<^const>\<open>grun\<close>
  condition of \<^const>\<open>gaccepts\<close>; the driver of \<^text>\<open>LR_Driver\<close>
  uses it.\<close>

definition gfinal :: \<open>('n, 't) is_cfg \<Rightarrow> 'n \<Rightarrow> ('n, 't) gconfig \<Rightarrow> bool\<close> where
  \<open>gfinal G Shn gc \<longleftrightarrow> (case gc of (Ys, v) \<Rightarrow> v = [] \<and> Ys \<noteq> [] \<and>
      list_ex (\<lambda>(pr, m, R). fst pr = Shn \<and> m = Suc 0 \<and>
                irep_mem (istart_ind G) R) (hd Ys))\<close>

section \<open>LR(0) core tabulation\<close>

text \<open>
  The indentation sets of items are input-dependent; their
  \<^emph>\<open>cores\<close> (production and dot) are not: \<^const>\<open>xgoto\<close> advances dots
  regardless of the goto label, and \<^const>\<open>xclosure\<close> adds one
  dot-\<^text>\<open>0\<close> slot per production unconditionally.  So the finitely many
  reachable cores can be tabulated at grammar-declaration time, giving the
  state skeleton for LR(k) tables and conflict reporting; the runtime
  indentation sets refine it per input.
\<close>


text \<open>After Knuth (1965, Sect. II step 3: the state sets), DeRemer and
  Pennello (1982, Sect. 2.2: the LR(0) automaton \<open>(K, Next, Reduce)\<close>) and
  Barthwal (2010, Sect. 5.3 and Def. 5.5.4: the worklist \<open>visit\<close>, with the
  unseen part of the finite universe as measure).\<close>
subsection \<open>Cores of frames\<close>

type_synonym ('n, 't) citem = \<open>('n \<times> ('n, 't) rhs) \<times> nat\<close>

definition ccore :: \<open>('n, 't) xitem list \<Rightarrow> ('n, 't) citem list\<close> where
  \<open>ccore xs = remdups (map (\<lambda>(pr, m, R). (pr, m)) xs)\<close>

definition cgoto :: \<open>('n, 't) citem list \<Rightarrow> ('n, 't) sym \<Rightarrow> ('n, 't) citem list\<close> where
  \<open>cgoto cs X = remdups (map (\<lambda>(pr, m). (pr, Suc m))
     (filter (\<lambda>(pr, m). m < length (snd pr) \<and> fst (snd pr ! m) = X) cs))\<close>

definition cclosure :: \<open>('n, 't) is_cfg \<Rightarrow> ('n, 't) citem list \<Rightarrow> ('n, 't) citem list\<close> where
  \<open>cclosure G cs = remdups (cs @ map (\<lambda>pr. (pr, 0)) (iprods G))\<close>

lemma set_ccore_xgoto:
  \<open>set (ccore (xgoto xs X l)) = set (cgoto (ccore xs) X)\<close>
  unfolding ccore_def cgoto_def xgoto_def by force

lemma set_ccore_xclosure:
  \<open>set (ccore (xclosure G fuel xs)) = set (cclosure G (ccore xs))\<close>
proof -
  have len: \<open>length (xiter G xs fuel) = length (iprods G)\<close> by simp
  show ?thesis
    unfolding ccore_def cclosure_def xclosure_def xslots_def
    by (force simp: set_zip in_set_conv_nth len intro: rev_image_eqI)
qed

lemma set_ccore_xclosure_auto:
  \<open>set (ccore (xclosure_auto G xs)) = set (cclosure G (ccore xs))\<close>
  unfolding xclosure_auto_def by (rule set_ccore_xclosure)

subsection \<open>The finite universe of cores\<close>

definition start_prod :: \<open>('n, 't) is_cfg \<Rightarrow> 'n \<Rightarrow> 'n \<times> ('n, 't) rhs\<close> where
  \<open>start_prod G Shn = (Shn, [(Nt (istart G), Eq)])\<close>

definition cuniv :: \<open>('n, 't) is_cfg \<Rightarrow> 'n \<Rightarrow> ('n, 't) citem set\<close> where
  \<open>cuniv G Shn = (SIGMA pr : insert (start_prod G Shn) (set (iprods G)).
     {..length (snd pr)})\<close>

lemma finite_cuniv: \<open>finite (cuniv G Shn)\<close>
  unfolding cuniv_def by (intro finite_SigmaI) auto

lemma cgoto_cclosure_univ:
  assumes \<open>set s \<subseteq> cuniv G Shn\<close>
  shows \<open>set (cgoto (cclosure G s) X) \<subseteq> cuniv G Shn\<close>
proof
  fix c assume \<open>c \<in> set (cgoto (cclosure G s) X)\<close>
  then obtain pr m where c: \<open>c = (pr, Suc m)\<close> and m: \<open>m < length (snd pr)\<close>
    and mem: \<open>(pr, m) \<in> set s \<union> (\<lambda>pr. (pr, 0)) ` set (iprods G)\<close>
    unfolding cgoto_def cclosure_def by auto
  have \<open>pr \<in> insert (start_prod G Shn) (set (iprods G))\<close>
    using mem assms unfolding cuniv_def by auto
  then show \<open>c \<in> cuniv G Shn\<close>
    using m unfolding c cuniv_def by auto
qed

definition gram_syms :: \<open>('n, 't) is_cfg \<Rightarrow> ('n, 't) syms\<close> where
  \<open>gram_syms G =
     remdups (Nt (istart G) # concat (map (\<lambda>(A, rhs). map fst rhs) (iprods G)))\<close>

subsection \<open>Worklist subset construction\<close>

text \<open>States are core lists, compared up to their sets; \<^text>\<open>cinserts\<close> adds
  the successors not yet seen.\<close>

fun cinserts :: \<open>('n, 't) citem list list \<Rightarrow> ('n, 't) citem list list \<Rightarrow>
    ('n, 't) citem list list \<Rightarrow> ('n, 't) citem list list\<close> where
  \<open>cinserts seen [] acc = acc\<close>
| \<open>cinserts seen (t # ts) acc =
     (if list_ex (\<lambda>u. set u = set t) (seen @ acc)
      then cinserts seen ts acc
      else cinserts seen ts (t # acc))\<close>

lemma cinserts_superset: \<open>set acc \<subseteq> set (cinserts seen ts acc)\<close>
  by (induction seen ts acc rule: cinserts.induct) auto

lemma cinserts_elems:
  \<open>set (cinserts seen ts acc) \<subseteq> set ts \<union> set acc\<close>
  by (induction seen ts acc rule: cinserts.induct) auto

lemma cinserts_covers:
  \<open>t \<in> set ts \<Longrightarrow> \<exists>u \<in> set (seen @ cinserts seen ts acc). set u = set t\<close>
proof (induction seen ts acc rule: cinserts.induct)
  case (2 seen t' ts acc)
  show ?case
  proof (cases \<open>t = t'\<close>)
    case True
    show ?thesis
    proof (cases \<open>list_ex (\<lambda>u. set u = set t') (seen @ acc)\<close>)
      case True
      then obtain u where u: \<open>u \<in> set (seen @ acc)\<close> and \<open>set u = set t'\<close>
        by (auto simp: list_ex_iff)
      then have \<open>u \<in> set (seen @ cinserts seen ts acc)\<close>
        using cinserts_superset by fastforce
      then show ?thesis using \<open>set u = set t'\<close> \<open>t = t'\<close> True by auto
    next
      case False
      have \<open>t' \<in> set (cinserts seen ts (t' # acc))\<close>
        using cinserts_superset by fastforce
      then show ?thesis using False \<open>t = t'\<close> by auto
    qed
  next
    case False
    with "2.prems" have t: \<open>t \<in> set ts\<close> by simp
    show ?thesis
    proof (cases \<open>list_ex (\<lambda>u. set u = set t') (seen @ acc)\<close>)
      case True
      from "2.IH"(1)[OF True t] show ?thesis using True by simp
    next
      case False
      from "2.IH"(2)[OF False t] show ?thesis using False by simp
    qed
  qed
qed simp

lemma cinserts_distinct:
  \<open>distinct (map set (seen @ acc)) \<Longrightarrow>
   distinct (map set (seen @ cinserts seen ts acc))\<close>
proof (induction seen ts acc rule: cinserts.induct)
  case (2 seen t ts acc)
  show ?case
  proof (cases \<open>list_ex (\<lambda>u. set u = set t) (seen @ acc)\<close>)
    case True
    then show ?thesis using "2.IH"(1) "2.prems" by simp
  next
    case False
    have \<open>distinct (map set (seen @ t # acc))\<close>
      using "2.prems" False by (auto simp: list_ex_iff image_iff)
    then show ?thesis using "2.IH"(2) False by simp
  qed
qed simp

subsection \<open>The worklist subset construction, generic in the closure\<close>

text \<open>The subset construction as a worklist over states (lists of cores),
  parametrised by the closure \<open>cl\<close> taken before each goto:
  \<^const>\<open>cclosure\<close> for the LR(0) automaton \<^text>\<open>lr0_states\<close>,
  \<^text>\<open>creach\<close> for the precise automaton \<^text>\<open>pr0_states\<close> of
  \<^text>\<open>LR_Det\<close>.  The invariant and the termination measure only need
  that a goto through the closure stays inside \<^const>\<open>cuniv\<close>.  The
  \<^const>\<open>while_option\<close> scaffold is shared with the cell saturation below.\<close>

lemma while_option_the_inv:
  fixes f :: \<open>'s \<Rightarrow> nat\<close>
  assumes init: \<open>P s\<^sub>0\<close>
    and step: \<open>\<And>s. P s \<Longrightarrow> b s \<Longrightarrow> P (c s) \<and> f (c s) < f s\<close>
  shows \<open>P (the (while_option b c s\<^sub>0)) \<and> \<not> b (the (while_option b c s\<^sub>0))\<close>
proof -
  obtain t where t: \<open>while_option b c s\<^sub>0 = Some t\<close>
    using measure_while_option_Some[where P = P and b = b and c = c and s = s\<^sub>0 and f = f]
      init step by blast
  have \<open>P t\<close>
    by (rule while_option_rule[where P = P, OF _ t init]) (use step in blast)
  with while_option_stop[OF t] show ?thesis by (simp add: t)
qed

definition wl_step :: \<open>('n, 't) is_cfg \<Rightarrow> (('n, 't) citem list \<Rightarrow> ('n, 't) citem list) \<Rightarrow>
    ('n, 't) citem list list \<times> ('n, 't) citem list list \<Rightarrow>
    ('n, 't) citem list list \<times> ('n, 't) citem list list\<close> where
  \<open>wl_step G cl = (\<lambda>(visited, work). case work of
      [] \<Rightarrow> (visited, [])
    | s # ws \<Rightarrow> (s # visited,
        cinserts (s # visited) (map (cgoto (cl s)) (gram_syms G)) ws))\<close>

definition wl_inv :: \<open>('n, 't) is_cfg \<Rightarrow> 'n \<Rightarrow> (('n, 't) citem list \<Rightarrow> ('n, 't) citem list) \<Rightarrow>
    ('n, 't) citem set set \<Rightarrow>
    ('n, 't) citem list list \<times> ('n, 't) citem list list \<Rightarrow> bool\<close> where
  \<open>wl_inv G Shn cl S\<^sub>0 = (\<lambda>(visited, work).
     distinct (map set (visited @ work)) \<and>
     (\<forall>s \<in> set (visited @ work). set s \<subseteq> cuniv G Shn) \<and>
     S\<^sub>0 \<subseteq> set ` set (visited @ work) \<and>
     (\<forall>s \<in> set visited. \<forall>X \<in> set (gram_syms G).
        \<exists>t \<in> set (visited @ work). set t = set (cgoto (cl s) X)))\<close>

lemma wl_step_inv:
  assumes univ: \<open>\<And>s X. set s \<subseteq> cuniv G Shn \<Longrightarrow> set (cgoto (cl s) X) \<subseteq> cuniv G Shn\<close>
    and inv: \<open>wl_inv G Shn cl S\<^sub>0 (visited, work)\<close> and ne: \<open>work \<noteq> []\<close>
  shows \<open>wl_inv G Shn cl S\<^sub>0 (wl_step G cl (visited, work))\<close>
proof -
  obtain s ws where work: \<open>work = s # ws\<close> using ne by (cases work) auto
  define succs where \<open>succs = map (cgoto (cl s)) (gram_syms G)\<close>
  define nw where \<open>nw = cinserts (s # visited) succs ws\<close>
  have res: \<open>wl_step G cl (visited, work) = (s # visited, nw)\<close>
    unfolding wl_step_def work succs_def nw_def by simp
  have dst: \<open>distinct (map set (visited @ work))\<close>
    and unv: \<open>\<forall>u \<in> set (visited @ work). set u \<subseteq> cuniv G Shn\<close>
    and s\<^sub>0: \<open>S\<^sub>0 \<subseteq> set ` set (visited @ work)\<close>
    and cov: \<open>\<forall>u \<in> set visited. \<forall>X \<in> set (gram_syms G).
        \<exists>t \<in> set (visited @ work). set t = set (cgoto (cl u) X)\<close>
    using inv unfolding wl_inv_def by auto
  have dst': \<open>distinct (map set ((s # visited) @ nw))\<close>
    unfolding nw_def
    by (rule cinserts_distinct) (use dst work in auto)
  have sub: \<open>set (visited @ work) \<subseteq> set ((s # visited) @ nw)\<close>
    using cinserts_superset[of ws \<open>s # visited\<close> succs]
    unfolding nw_def work by auto
  have unv': \<open>\<forall>u \<in> set ((s # visited) @ nw). set u \<subseteq> cuniv G Shn\<close>
  proof
    fix u assume \<open>u \<in> set ((s # visited) @ nw)\<close>
    then consider \<open>u \<in> set (visited @ work)\<close> | \<open>u \<in> set succs\<close>
      using cinserts_elems[of \<open>s # visited\<close> succs ws] work
      unfolding nw_def by auto
    then show \<open>set u \<subseteq> cuniv G Shn\<close>
    proof cases
      case 1 then show ?thesis using unv by blast
    next
      case 2
      then obtain X where \<open>u = cgoto (cl s) X\<close>
        unfolding succs_def by auto
      then show ?thesis
        using univ unv work by fastforce
    qed
  qed
  have s\<^sub>0': \<open>S\<^sub>0 \<subseteq> set ` set ((s # visited) @ nw)\<close>
    by (rule subset_trans[OF s\<^sub>0 image_mono[OF sub]])
  have cov': \<open>\<forall>u \<in> set (s # visited). \<forall>X \<in> set (gram_syms G).
      \<exists>t \<in> set ((s # visited) @ nw). set t = set (cgoto (cl u) X)\<close>
  proof (intro ballI)
    fix u X assume u: \<open>u \<in> set (s # visited)\<close> and X: \<open>X \<in> set (gram_syms G)\<close>
    show \<open>\<exists>t \<in> set ((s # visited) @ nw). set t = set (cgoto (cl u) X)\<close>
    proof (cases \<open>u = s\<close>)
      case True
      have \<open>cgoto (cl s) X \<in> set succs\<close>
        using X unfolding succs_def by auto
      from cinserts_covers[OF this, of \<open>s # visited\<close> ws]
      show ?thesis unfolding nw_def True by auto
    next
      case False
      with u have \<open>u \<in> set visited\<close> by simp
      from cov[rule_format, OF this X] obtain t where
        \<open>t \<in> set (visited @ work)\<close> and \<open>set t = set (cgoto (cl u) X)\<close>
        by blast
      then show ?thesis using sub by blast
    qed
  qed
  show ?thesis unfolding res wl_inv_def
    using dst' unv' s\<^sub>0' cov' by simp
qed

lemma wl_step_card:
  assumes inv: \<open>wl_inv G Shn cl S\<^sub>0 (visited, work)\<close> and ne: \<open>work \<noteq> []\<close>
  shows \<open>card (set ` set (fst (wl_step G cl (visited, work))))
       = Suc (card (set ` set visited))\<close>
proof -
  obtain s ws where work: \<open>work = s # ws\<close> using ne by (cases work) auto
  have \<open>set s \<notin> set ` set visited\<close>
    using inv unfolding wl_inv_def work by (auto simp: image_iff)
  moreover have \<open>finite (set ` set visited)\<close> by simp
  ultimately show ?thesis
    unfolding wl_step_def work by (simp add: Let_def)
qed

definition lr0_start :: \<open>('n, 't) is_cfg \<Rightarrow> 'n \<Rightarrow> ('n, 't) citem list\<close> where
  \<open>lr0_start G Shn = [(start_prod G Shn, 0)]\<close>

definition lr0_init :: \<open>('n, 't) is_cfg \<Rightarrow> 'n \<Rightarrow>
    ('n, 't) citem list list \<times> ('n, 't) citem list list\<close> where
  \<open>lr0_init G Shn = ([], [lr0_start G Shn, []])\<close>

lemma wl_inv_init:
  \<open>wl_inv G Shn cl {set (lr0_start G Shn), {}} (lr0_init G Shn)\<close>
  unfolding wl_inv_def lr0_init_def lr0_start_def cuniv_def start_prod_def
  by auto

definition wl_states :: \<open>('n, 't) is_cfg \<Rightarrow> 'n \<Rightarrow> (('n, 't) citem list \<Rightarrow> ('n, 't) citem list) \<Rightarrow>
    ('n, 't) citem list list\<close> where
  \<open>wl_states G Shn cl =
     fst (the (while_option (\<lambda>(v, w). w \<noteq> []) (wl_step G cl) (lr0_init G Shn)))\<close>

lemma wl_states_inv:
  assumes univ: \<open>\<And>s X. set s \<subseteq> cuniv G Shn \<Longrightarrow> set (cgoto (cl s) X) \<subseteq> cuniv G Shn\<close>
  shows \<open>wl_inv G Shn cl {set (lr0_start G Shn), {}} (wl_states G Shn cl, [])\<close>
proof -
  let ?P = \<open>wl_inv G Shn cl {set (lr0_start G Shn), {}}\<close>
  let ?t = \<open>the (while_option (\<lambda>(v, w). w \<noteq> []) (wl_step G cl) (lr0_init G Shn))\<close>
  have \<open>?P ?t \<and> \<not> (case ?t of (v, w) \<Rightarrow> w \<noteq> [])\<close>
  proof (rule while_option_the_inv[where P = ?P and b = \<open>\<lambda>(v, w). w \<noteq> []\<close>
        and c = \<open>wl_step G cl\<close> and f = \<open>\<lambda>(v, w). card (Pow (cuniv G Shn)) - card (set ` set v)\<close>])
    show \<open>?P (lr0_init G Shn)\<close> by (rule wl_inv_init)
  next
    fix st assume inv: \<open>?P st\<close> and b: \<open>case st of (v, w) \<Rightarrow> w \<noteq> []\<close>
    obtain v w where st: \<open>st = (v, w)\<close> by (cases st)
    have card_lt: \<open>card (set ` set v) < card (Pow (cuniv G Shn))\<close>
    proof -
      have \<open>set ` set (fst (wl_step G cl (v, w))) \<subseteq> Pow (cuniv G Shn)\<close>
        using wl_step_inv[OF univ inv[unfolded st] b[unfolded st, simplified]]
        unfolding wl_inv_def by (cases \<open>wl_step G cl (v, w)\<close>) auto
      then have \<open>card (set ` set (fst (wl_step G cl (v, w)))) \<le> card (Pow (cuniv G Shn))\<close>
        by (intro card_mono) (simp add: finite_cuniv)
      then show ?thesis
        using wl_step_card[OF inv[unfolded st] b[unfolded st, simplified]] by simp
    qed
    show \<open>?P (wl_step G cl st) \<and>
        (case wl_step G cl st of (v, w) \<Rightarrow> card (Pow (cuniv G Shn)) - card (set ` set v))
        < (case st of (v, w) \<Rightarrow> card (Pow (cuniv G Shn)) - card (set ` set v))\<close>
      using wl_step_inv[OF univ inv[unfolded st]] wl_step_card[OF inv[unfolded st]] b card_lt
      unfolding st by (cases \<open>wl_step G cl (v, w)\<close>) auto
  qed
  then show ?thesis unfolding wl_states_def by (cases ?t) auto
qed

subsection \<open>The LR(0) automaton\<close>

definition lr0_states :: \<open>('n, 't) is_cfg \<Rightarrow> 'n \<Rightarrow> ('n, 't) citem list list\<close> where
  \<open>lr0_states G Shn = wl_states G Shn (cclosure G)\<close>

lemma lr0_states_inv:
  \<open>wl_inv G Shn (cclosure G) {set (lr0_start G Shn), {}} (lr0_states G Shn, [])\<close>
  unfolding lr0_states_def by (rule wl_states_inv[OF cgoto_cclosure_univ])

theorem lr0_states_closed:
  assumes \<open>s \<in> set (lr0_states G Shn)\<close> and \<open>X \<in> set (gram_syms G)\<close>
  shows \<open>\<exists>t \<in> set (lr0_states G Shn). set t = set (cgoto (cclosure G s) X)\<close>
  using lr0_states_inv assms unfolding wl_inv_def by fastforce

lemma ccore_xinit: \<open>set (ccore (xinit G Shn)) = set (lr0_start G Shn)\<close>
  unfolding ccore_def xinit_def lr0_start_def start_prod_def by simp

theorem lr0_states_start:
  \<open>\<exists>t \<in> set (lr0_states G Shn). set t = set (ccore (xinit G Shn))\<close>
proof -
  have \<open>set (lr0_start G Shn) \<in> set ` set (lr0_states G Shn)\<close>
    using lr0_states_inv[of G Shn] unfolding wl_inv_def by auto
  moreover have \<open>set (ccore (xinit G Shn)) = set (lr0_start G Shn)\<close> by (rule ccore_xinit)
  ultimately show ?thesis by auto
qed

theorem lr0_states_empty: \<open>\<exists>t \<in> set (lr0_states G Shn). set t = {}\<close>
proof -
  have \<open>{} \<in> set ` set (lr0_states G Shn)\<close>
    using lr0_states_inv[of G Shn] unfolding wl_inv_def by auto
  then show ?thesis by auto
qed

subsection \<open>Reachable closure and conflict reporting\<close>

text \<open>\<^const>\<open>cclosure\<close> adds a dot-\<^text>\<open>0\<close> slot for every production
  (dead slots carry empty \<^typ>\<open>indrep\<close>s at runtime), so at core level an
  \<^text>\<open>\<epsilon>\<close>-production looks completed in every state.  Conflict diagnostics
  need the classic \<^emph>\<open>reachable\<close> closure: only productions of nonterminals
  that occur after a dot.  One production can be added per round, so
  \<^term>\<open>length (iprods G)\<close> rounds saturate.\<close>

definition creach_step :: \<open>('n, 't) is_cfg \<Rightarrow> ('n, 't) citem list \<Rightarrow> ('n, 't) citem list\<close> where
  \<open>creach_step G cs = remdups (cs @ concat (map (\<lambda>pr.
       if list_ex (\<lambda>(pr', m). m < length (snd pr') \<and> fst (snd pr' ! m) = Nt (fst pr)) cs
       then [(pr, 0)] else []) (iprods G)))\<close>

definition creach :: \<open>('n, 't) is_cfg \<Rightarrow> ('n, 't) citem list \<Rightarrow> ('n, 't) citem list\<close> where
  \<open>creach G cs = (creach_step G ^^ Suc (length (iprods G))) cs\<close>

lemma creach_step_mono: \<open>set cs \<subseteq> set (creach_step G cs)\<close>
  unfolding creach_step_def by auto

lemma creach_funpow_mono: \<open>set cs \<subseteq> set ((creach_step G ^^ k) cs)\<close>
proof (induction k arbitrary: cs)
  case (Suc k)
  have \<open>set cs \<subseteq> set (creach_step G cs)\<close> by (rule creach_step_mono)
  also have \<open>\<dots> \<subseteq> set ((creach_step G ^^ k) (creach_step G cs))\<close> by (rule Suc.IH)
  finally show ?case by (simp add: funpow_swap1)
qed simp

lemma creach_superset: \<open>set cs \<subseteq> set (creach G cs)\<close>
  unfolding creach_def by (rule creach_funpow_mono)

lemma creach_step_sound:
  \<open>set (creach_step G cs) \<subseteq> set cs \<union> (\<lambda>pr. (pr, 0)) ` set (iprods G)\<close>
  unfolding creach_step_def by (auto split: if_splits)

lemma creach_funpow_sound:
  \<open>set ((creach_step G ^^ k) cs) \<subseteq> set cs \<union> (\<lambda>pr. (pr, 0)) ` set (iprods G)\<close>
proof (induction k arbitrary: cs)
  case (Suc k)
  have \<open>set ((creach_step G ^^ Suc k) cs)
      = set ((creach_step G ^^ k) (creach_step G cs))\<close>
    by (simp add: funpow_swap1)
  also have \<open>\<dots> \<subseteq> set (creach_step G cs) \<union> (\<lambda>pr. (pr, 0)) ` set (iprods G)\<close>
    by (rule Suc.IH)
  also have \<open>\<dots> \<subseteq> set cs \<union> (\<lambda>pr. (pr, 0)) ` set (iprods G)\<close>
    using creach_step_sound by fastforce
  finally show ?case .
qed simp

lemma creach_sound:
  \<open>set (creach G cs) \<subseteq> set (cclosure G cs)\<close>
proof -
  have \<open>set (creach G cs) \<subseteq> set cs \<union> (\<lambda>pr. (pr, 0)) ` set (iprods G)\<close>
    unfolding creach_def by (rule creach_funpow_sound)
  also have \<open>\<dots> = set (cclosure G cs)\<close>
    unfolding cclosure_def by auto
  finally show ?thesis .
qed

subsection \<open>The automaton covers every machine run\<close>

text \<open>The core of every frame either machine builds is a tabulated state:
  goto through a tabulated symbol stays tabulated by
  \<^text>\<open>lr0_states_closed\<close>, and goto through any other symbol is
  the (tabulated) empty state, since all next symbols of cores in
  \<^const>\<open>cuniv\<close> are in \<^const>\<open>gram_syms\<close>.\<close>

lemma set_cgoto_cong:
  \<open>set cs = set cs' \<Longrightarrow> set (cgoto cs X) = set (cgoto cs' X)\<close>
  unfolding cgoto_def by auto

lemma cgoto_memI:
  \<open>(pr, m) \<in> set cs \<Longrightarrow> m < length (snd pr) \<Longrightarrow> fst (snd pr ! m) = X \<Longrightarrow> (pr, Suc m) \<in> set (cgoto cs X)\<close>
  unfolding cgoto_def by force

lemma cgoto_set_mono: \<open>set cs \<subseteq> set cs' \<Longrightarrow> set (cgoto cs X) \<subseteq> set (cgoto cs' X)\<close>
  unfolding cgoto_def by auto

lemma set_cclosure_cong:
  \<open>set cs = set cs' \<Longrightarrow> set (cclosure G cs) = set (cclosure G cs')\<close>
  unfolding cclosure_def by auto

lemma lr0_states_univ:
  \<open>s \<in> set (lr0_states G Shn) \<Longrightarrow> set s \<subseteq> cuniv G Shn\<close>
  using lr0_states_inv[of G Shn] unfolding wl_inv_def by auto

lemma lr0_states_distinct: \<open>distinct (map set (lr0_states G Shn))\<close>
  using lr0_states_inv[of G Shn] unfolding wl_inv_def by auto

lemma cclosure_univ:
  \<open>set cs \<subseteq> cuniv G Shn \<Longrightarrow> set (cclosure G cs) \<subseteq> cuniv G Shn\<close>
  unfolding cclosure_def cuniv_def by auto

lemma creach_univ:
  assumes \<open>set s \<subseteq> cuniv G Shn\<close>
  shows \<open>set (creach G s) \<subseteq> cuniv G Shn\<close>
  using creach_sound[of G s] cclosure_univ[OF assms] by blast

lemma gram_syms_iprods:
  \<open>(A, rhs) \<in> set (iprods G) \<Longrightarrow> m < length rhs \<Longrightarrow> fst (rhs ! m) \<in> set (gram_syms G)\<close>
  unfolding gram_syms_def by force

lemma cuniv_next_gram_syms:
  assumes \<open>(pr, m) \<in> cuniv G Shn\<close> and \<open>m < length (snd pr)\<close>
  shows \<open>fst (snd pr ! m) \<in> set (gram_syms G)\<close>
proof -
  from assms(1) consider \<open>pr = start_prod G Shn\<close> | \<open>pr \<in> set (iprods G)\<close>
    unfolding cuniv_def by auto
  then show ?thesis
  proof cases
    case 1
    then show ?thesis using assms(2) unfolding start_prod_def gram_syms_def by simp
  next
    case 2
    then show ?thesis using gram_syms_iprods[of \<open>fst pr\<close> \<open>snd pr\<close> G m] assms(2) by simp
  qed
qed

lemma cgoto_nosym:
  assumes univ: \<open>set cs \<subseteq> cuniv G Shn\<close> and X: \<open>X \<notin> set (gram_syms G)\<close>
  shows \<open>set (cgoto cs X) = {}\<close>
proof -
  have nsym: \<open>fst (snd pr ! m) \<in> set (gram_syms G)\<close>
    if mem: \<open>(pr, m) \<in> set cs\<close> and m: \<open>m < length (snd pr)\<close> for pr m
    using cuniv_next_gram_syms[OF _ m] univ mem by blast
  show ?thesis
    using nsym X unfolding cgoto_def by (fastforce simp: filter_empty_conv)
qed

definition cores_ok :: \<open>('n, 't) is_cfg \<Rightarrow> 'n \<Rightarrow> ('n, 't) xitem list \<Rightarrow> bool\<close> where
  \<open>cores_ok G Shn f \<longleftrightarrow> (\<exists>s \<in> set (lr0_states G Shn). set (ccore f) = set s)\<close>

lemma cores_ok_goto:
  assumes ok: \<open>cores_ok G Shn f\<close>
    and CL: \<open>set (ccore CL) = set (cclosure G (ccore f))\<close>
    and new: \<open>set (ccore f') = set (cgoto (ccore CL) X)\<close>
  shows \<open>cores_ok G Shn f'\<close>
proof -
  from ok obtain s where s: \<open>s \<in> set (lr0_states G Shn)\<close>
    and eq: \<open>set (ccore f) = set s\<close>
    unfolding cores_ok_def by blast
  have red: \<open>set (ccore f') = set (cgoto (cclosure G s) X)\<close>
    using new set_cgoto_cong[OF CL]
      set_cgoto_cong[OF set_cclosure_cong[OF eq]] by simp
  show ?thesis
  proof (cases \<open>X \<in> set (gram_syms G)\<close>)
    case True
    from lr0_states_closed[OF s True] obtain t where
      \<open>t \<in> set (lr0_states G Shn)\<close> and \<open>set t = set (cgoto (cclosure G s) X)\<close>
      by blast
    then show ?thesis using red unfolding cores_ok_def by auto
  next
    case False
    have \<open>set (cclosure G s) \<subseteq> cuniv G Shn\<close>
      by (rule cclosure_univ[OF lr0_states_univ[OF s]])
    from cgoto_nosym[OF this False] red have \<open>set (ccore f') = {}\<close> by simp
    then show ?thesis
      using lr0_states_empty unfolding cores_ok_def by auto
  qed
qed

lemma gstep_cores:
  assumes step: \<open>gstep G (Xs, w) act = Some (Xs', w')\<close>
    and ok: \<open>\<forall>f \<in> set Xs. cores_ok G Shn f\<close>
  shows \<open>\<forall>f \<in> set Xs'. cores_ok G Shn f\<close>
proof (cases act)
  case (GShift fuel)
  obtain a l w\<^sub>0 where w: \<open>w = (a, l) # w\<^sub>0\<close>
    using step GShift by (cases w) auto
  obtain CL where ne: \<open>Xs \<noteq> []\<close>
    and chk: \<open>xclosure_chk G fuel (hd Xs) = Some CL\<close>
    and Xs': \<open>Xs' = xgoto CL (Tm a) l # Xs\<close>
    using step unfolding GShift w
    by (auto split: if_splits option.splits)
  have CL: \<open>CL = xclosure G fuel (hd Xs)\<close>
    using chk unfolding xclosure_chk_def by (auto split: if_splits)
  have hd_ok: \<open>cores_ok G Shn (hd Xs)\<close> using ok ne by auto
  have \<open>cores_ok G Shn (xgoto CL (Tm a) l)\<close>
    by (rule cores_ok_goto[OF hd_ok _ set_ccore_xgoto])
       (simp add: CL set_ccore_xclosure)
  then show ?thesis using ok unfolding Xs' by auto
next
  case (GReduce f\<^sub>1 f\<^sub>2 pr i)
  obtain CL\<^sub>2 where ne: \<open>Xs \<noteq> []\<close>
    and len: \<open>length (snd pr) < length Xs\<close>
    and chk\<^sub>2: \<open>xclosure_chk G f\<^sub>2 (Xs ! length (snd pr)) = Some CL\<^sub>2\<close>
    and Xs': \<open>Xs' = xgoto CL\<^sub>2 (Nt (fst pr)) i # drop (length (snd pr)) Xs\<close>
    using step unfolding GReduce
    by (auto split: if_splits option.splits)
  have CL\<^sub>2: \<open>CL\<^sub>2 = xclosure G f\<^sub>2 (Xs ! length (snd pr))\<close>
    using chk\<^sub>2 unfolding xclosure_chk_def by (auto split: if_splits)
  have nth_ok: \<open>cores_ok G Shn (Xs ! length (snd pr))\<close> using ok len by auto
  have \<open>cores_ok G Shn (xgoto CL\<^sub>2 (Nt (fst pr)) i)\<close>
    by (rule cores_ok_goto[OF nth_ok _ set_ccore_xgoto])
       (simp add: CL\<^sub>2 set_ccore_xclosure)
  then show ?thesis using ok unfolding Xs' by (auto dest: in_set_dropD)
qed

theorem grun_cores:
  assumes run: \<open>grun G as ([xinit G Shn], w) = Some (Ys, v)\<close>
    and f: \<open>f \<in> set Ys\<close>
  shows \<open>\<exists>s \<in> set (lr0_states G Shn). set (ccore f) = set s\<close>
proof -
  have init: \<open>\<forall>f \<in> set [xinit G Shn]. cores_ok G Shn f\<close>
  proof -
    obtain t where \<open>t \<in> set (lr0_states G Shn)\<close>
      and \<open>set t = set (ccore (xinit G Shn))\<close>
      using lr0_states_start[of G Shn] by blast
    then show ?thesis unfolding cores_ok_def
      by (intro ballI bexI[of _ t]) auto
  qed
  have \<open>grun G as (Xs, w') = Some (Ys, v) \<Longrightarrow> \<forall>f \<in> set Xs. cores_ok G Shn f \<Longrightarrow>
      \<forall>f \<in> set Ys. cores_ok G Shn f\<close> for Xs w'
  proof (induction as arbitrary: Xs w')
    case Nil
    then show ?case by simp
  next
    case (Cons a as)
    obtain gc\<^sub>1 where step: \<open>gstep G (Xs, w') a = Some gc\<^sub>1\<close>
      and rest: \<open>grun G as gc\<^sub>1 = Some (Ys, v)\<close>
      using Cons.prems(1) by (auto split: option.splits)
    obtain Xs\<^sub>1 w\<^sub>1 where gc\<^sub>1: \<open>gc\<^sub>1 = (Xs\<^sub>1, w\<^sub>1)\<close> by (cases gc\<^sub>1)
    have \<open>\<forall>f \<in> set Xs\<^sub>1. cores_ok G Shn f\<close>
      using gstep_cores[OF step[unfolded gc\<^sub>1] Cons.prems(2)] .
    from Cons.IH[OF rest[unfolded gc\<^sub>1] this] show ?case .
  qed
  from this[OF run init] f show ?thesis
    unfolding cores_ok_def by auto
qed

section \<open>Column-relative first sets: LR(k) lookahead, phase 1\<close>

text \<open>
  Deterministic LR parsing of an II-CFG needs \<^emph>\<open>column-relative\<close>
  lookahead: a spine ends where the next token's column says so, not where
  its class does. A lookahead entry is a token class paired with a
  \<^typ>\<open>cirel\<close> relating the token's column to the indentation of the item
  that carries it. The executable first-set layer:

    \<^item> \<^text>\<open>cwiden\<close>: composed relations widened into a four-element class
      universe, keeping the fixpoints finite. Over-approximating is the safe
      direction throughout: lookahead only prunes reduce actions;
    \<^item> \<^text>\<open>nullables\<close>: executable nullability, complete against the
      derivations of the infinite grammar \<^const>\<open>infG\<close>;
    \<^item> \<^text>\<open>ffix\<close>: the first-token table, one saturation fixpoint,
      complete for \<^term>\<open>fHk G 1\<close>.
\<close>

subsection \<open>Widening composed relations\<close>

fun cwiden :: \<open>cirel \<Rightarrow> cirel\<close> where
  \<open>cwiden (CGt n) = (if n = 0 then CGe else CGt 1)\<close>
| \<open>cwiden (CGtAny n) = CAny\<close>
| \<open>cwiden c = c\<close>

lemma csat_cwiden: \<open>csat c k i \<Longrightarrow> csat (cwiden c) k i\<close>
  by (cases c) auto

lemma cwiden_range: \<open>cwiden c \<in> {CEq, CGe, CGt 1, CAny}\<close>
  by (cases c) auto

subsection \<open>Bounded saturation of monotone list fixpoints\<close>

text \<open>A set-extensional, monotone step that stays inside a finite universe
  saturates within \<^term>\<open>card U\<close> rounds.\<close>

lemma funpow_saturates:
  fixes f :: \<open>'a list \<Rightarrow> 'a list\<close> and U :: \<open>'a set\<close>
  assumes ext: \<open>\<And>xs ys. set xs = set ys \<Longrightarrow> set (f xs) = set (f ys)\<close>
    and mono: \<open>\<And>xs. set xs \<subseteq> set (f xs)\<close>
    and inU: \<open>\<And>xs. set xs \<subseteq> U \<Longrightarrow> set (f xs) \<subseteq> U\<close>
    and fin: \<open>finite U\<close>
    and istart: \<open>set xs\<^sub>0 \<subseteq> U\<close>
    and N: \<open>card U \<le> N\<close>
  shows \<open>set (f ((f ^^ N) xs\<^sub>0)) = set ((f ^^ N) xs\<^sub>0)\<close>
proof -
  have iterU: \<open>set ((f ^^ k) xs\<^sub>0) \<subseteq> U\<close> for k
    by (induction k) (use istart inU in auto)
  show ?thesis
  proof (cases \<open>\<exists>k < N. set (f ((f ^^ k) xs\<^sub>0)) = set ((f ^^ k) xs\<^sub>0)\<close>)
    case True
    then obtain k where k: \<open>k < N\<close>
      and st: \<open>set (f ((f ^^ k) xs\<^sub>0)) = set ((f ^^ k) xs\<^sub>0)\<close> by blast
    have stab: \<open>set ((f ^^ (k + d)) xs\<^sub>0) = set ((f ^^ k) xs\<^sub>0)\<close> for d
    proof (induction d)
      case (Suc d)
      have \<open>set ((f ^^ (k + Suc d)) xs\<^sub>0) = set (f ((f ^^ (k + d)) xs\<^sub>0))\<close>
        by simp
      also have \<open>\<dots> = set (f ((f ^^ k) xs\<^sub>0))\<close>
        by (rule ext[OF Suc.IH])
      finally show ?case using st by simp
    qed simp
    have NN: \<open>set ((f ^^ N) xs\<^sub>0) = set ((f ^^ k) xs\<^sub>0)\<close>
      using stab[of \<open>N - k\<close>] k by simp
    then show ?thesis using ext[OF NN] st by simp
  next
    case False
    have grow: \<open>k \<le> N \<Longrightarrow> k \<le> card (set ((f ^^ k) xs\<^sub>0))\<close> for k
    proof (induction k)
      case (Suc k)
      have ne: \<open>set (f ((f ^^ k) xs\<^sub>0)) \<noteq> set ((f ^^ k) xs\<^sub>0)\<close>
        using False Suc.prems by auto
      have \<open>set ((f ^^ k) xs\<^sub>0) \<subset> set (f ((f ^^ k) xs\<^sub>0))\<close>
        using mono ne by blast
      then have \<open>card (set ((f ^^ k) xs\<^sub>0)) < card (set (f ((f ^^ k) xs\<^sub>0)))\<close>
        by (intro psubset_card_mono)
           (use inU[OF iterU[of k]] fin finite_subset in auto)
      then show ?case using Suc by simp
    qed simp
    have \<open>N \<le> card (set ((f ^^ N) xs\<^sub>0))\<close> using grow by simp
    moreover have \<open>card (set ((f ^^ N) xs\<^sub>0)) \<le> card U\<close>
      by (intro card_mono fin iterU)
    ultimately have \<open>card (set ((f ^^ N) xs\<^sub>0)) = card U\<close> using N by simp
    then have full: \<open>set ((f ^^ N) xs\<^sub>0) = U\<close>
      by (intro card_subset_eq fin iterU)
    have \<open>set (f ((f ^^ N) xs\<^sub>0)) \<subseteq> U\<close>
      by (rule inU[OF iterU])
    then show ?thesis using full mono[of \<open>(f ^^ N) xs\<^sub>0\<close>] by auto
  qed
qed

subsection \<open>Executable nullability\<close>

definition nsym :: \<open>'n list \<Rightarrow> ('n, 't) sym \<Rightarrow> bool\<close> where
  \<open>nsym ns X = (case X of Nt B \<Rightarrow> B \<in> set ns | Tm _ \<Rightarrow> False)\<close>

definition nstep :: \<open>('n, 't) is_cfg \<Rightarrow> 'n list \<Rightarrow> 'n list\<close> where
  \<open>nstep G ns = remdups (map fst (filter (\<lambda>(A, rhs).
      list_all (\<lambda>(X, r). nsym ns X) rhs) (iprods G)) @ ns)\<close>

definition nullables :: \<open>('n, 't) is_cfg \<Rightarrow> 'n list\<close> where
  \<open>nullables G = (nstep G ^^ Suc (length (remdups (map fst (iprods G))))) []\<close>

lemma nsym_ext: \<open>set ns = set ns' \<Longrightarrow> nsym ns X = nsym ns' X\<close>
  unfolding nsym_def by (cases X) auto

lemma nstep_ext:
  \<open>set ns = set ns' \<Longrightarrow> set (nstep G ns) = set (nstep G ns')\<close>
  unfolding nstep_def using nsym_ext[of ns ns']
  by (auto simp: list_all_iff case_prod_beta)

lemma nstep_mono: \<open>set ns \<subseteq> set (nstep G ns)\<close>
  unfolding nstep_def by auto

lemma nstep_inU:
  \<open>set ns \<subseteq> fst ` set (iprods G) \<Longrightarrow> set (nstep G ns) \<subseteq> fst ` set (iprods G)\<close>
  unfolding nstep_def by force

lemma nullables_stable:
  \<open>set (nstep G (nullables G)) = set (nullables G)\<close>
  unfolding nullables_def
proof (rule funpow_saturates[where U = \<open>fst ` set (iprods G)\<close>])
  show \<open>\<And>xs ys. set xs = set ys \<Longrightarrow> set (nstep G xs) = set (nstep G ys)\<close>
    by (rule nstep_ext)
  show \<open>\<And>xs. set xs \<subseteq> set (nstep G xs)\<close>
    by (rule nstep_mono)
  show \<open>\<And>xs. set xs \<subseteq> fst ` set (iprods G) \<Longrightarrow>
      set (nstep G xs) \<subseteq> fst ` set (iprods G)\<close>
    by (rule nstep_inU)
  show \<open>finite (fst ` set (iprods G))\<close> by simp
  show \<open>set [] \<subseteq> fst ` set (iprods G)\<close> by simp
  show \<open>card (fst ` set (iprods G)) \<le> Suc (length (remdups (map fst (iprods G))))\<close>
    by (metis card_set eq_imp_le le_SucI set_map)
qed

lemma nullables_closed:
  assumes \<open>(A, rhs) \<in> set (iprods G)\<close>
    and \<open>list_all (\<lambda>(X, r). nsym (nullables G) X) rhs\<close>
  shows \<open>A \<in> set (nullables G)\<close>
proof -
  have \<open>A \<in> set (nstep G (nullables G))\<close>
    unfolding nstep_def using assms by force
  then show ?thesis using nullables_stable by fastforce
qed

text \<open>
  Completeness against \<^const>\<open>infG\<close>, through the erased grammar: a
  derivation of \<^text>\<open>eps\<close> erases to one of
  \<^term>\<open>set (derel (iprods G))\<close>, where nullability is the library's
  \<^const>\<open>Nullable\<close>, and the fixpoint above is closed under its introduction
  rule.
\<close>

lemma nsym_nullables:
  assumes \<open>Nullable (set (derel (iprods G))) X\<close>
  shows \<open>nsym (nullables G) X\<close>
  using assms
proof (induction rule: Nullable.induct)
  case (NullableSym A w)
  from NullableSym.hyps obtain rhs where p: \<open>(A, rhs) \<in> set (iprods G)\<close>
    and w: \<open>w = map fst rhs\<close> unfolding derel_def by auto
  have \<open>list_all (\<lambda>(X, r). nsym (nullables G) X) rhs\<close>
    using NullableSym.IH unfolding w by (auto simp: list_all_iff case_prod_beta)
  from nullables_closed[OF p this] show ?case by (simp add: nsym_def)
qed

lemma nullables_complete:
  assumes \<open>(infG G) \<turnstile> [Nt (B, j)] \<Rightarrow>(n) []\<close>
  shows \<open>B \<in> set (nullables G)\<close>
proof -
  have \<open>set (derel (iprods G)) \<turnstile> [Nt B] \<Rightarrow>* []\<close>
    using derives_unann[OF relpowp_imp_rtranclp[OF assms]] by simp
  from nsym_nullables[OF nullable_if[OF this]] show ?thesis
    by (simp add: nsym_def)
qed

lemma annotated_null:
  assumes \<open>(infG G) \<turnstile> arhs \<Rightarrow>(m) []\<close> and \<open>annotates j rhs arhs\<close>
  shows \<open>list_all (\<lambda>(X, r). nsym (nullables G) X) rhs\<close>
proof -
  have d: \<open>set (derel (iprods G)) \<turnstile> map fst rhs \<Rightarrow>* []\<close>
    using derives_unann[OF relpowp_imp_rtranclp[OF assms(1)]]
      annotates_unann[OF assms(2)] by simp
  have \<open>nsym (nullables G) (fst Xr)\<close> if \<open>Xr \<in> set rhs\<close> for Xr
    using derives_NilD[OF d, of \<open>fst Xr\<close>] that
    by (auto intro: nsym_nullables nullable_if)
  then show ?thesis by (auto simp: list_all_iff case_prod_beta)
qed

subsection \<open>The first-token table\<close>

text \<open>A flat table of triples: nonterminal, token class, and the widened
  relation of the token's column to the nonterminal's own indentation.\<close>

type_synonym ('n, 't) ftab = \<open>('n \<times> 't \<times> cirel) list\<close>

definition flook :: \<open>('n, 't) ftab \<Rightarrow> 'n \<Rightarrow> ('t \<times> cirel) list\<close> where
  \<open>flook tab B = map (\<lambda>(_, a, \<rho>). (a, \<rho>)) (filter (\<lambda>(B', _, _). B' = B) tab)\<close>

lemma flookI: \<open>(B, a, \<rho>) \<in> set tab \<Longrightarrow> (a, \<rho>) \<in> set (flook tab B)\<close>
  unfolding flook_def by force

lemma flookD: \<open>(a, \<rho>) \<in> set (flook tab B) \<Longrightarrow> (B, a, \<rho>) \<in> set tab\<close>
  unfolding flook_def by auto

fun fscan :: \<open>('n, 't) ftab \<Rightarrow> 'n list \<Rightarrow> ('n, 't) rhs \<Rightarrow> ('t \<times> cirel) list\<close> where
  \<open>fscan tab ns [] = []\<close>
| \<open>fscan tab ns ((X, r) # rest) =
     (case X of
        Tm a \<Rightarrow> [(a, cwiden (cirel_of r))]
      | Nt B \<Rightarrow> map (\<lambda>(a, \<rho>). (a, cwiden (ccomp (cirel_of r) \<rho>))) (flook tab B))
     @ (if nsym ns X then fscan tab ns rest else [])\<close>

definition fstep :: \<open>('n, 't) is_cfg \<Rightarrow> ('n, 't) ftab \<Rightarrow> ('n, 't) ftab\<close> where
  \<open>fstep G tab = remdups (tab @ concat (map (\<lambda>(B, rhs).
      map (\<lambda>(a, \<sigma>). (B, a, \<sigma>)) (fscan tab (nullables G) rhs)) (iprods G)))\<close>

definition ffix :: \<open>('n, 't) is_cfg \<Rightarrow> ('n, 't) ftab\<close> where
  \<open>ffix G = the (while_option (\<lambda>tab. length (fstep G tab) \<noteq> length tab)
      (fstep G) [])\<close>

definition funiv :: \<open>('n, 't) is_cfg \<Rightarrow> ('n \<times> 't \<times> cirel) set\<close> where
  \<open>funiv G = fst ` set (iprods G) \<times> set (gram_terms G) \<times> {CEq, CGe, CGt 1, CAny}\<close>

lemma finite_funiv: \<open>finite (funiv G)\<close>
  unfolding funiv_def by auto

lemma fscan_inU:
  assumes tab: \<open>set tab \<subseteq> funiv G\<close>
    and terms: \<open>\<And>a r. (Tm a, r) \<in> set rhs \<Longrightarrow> a \<in> set (gram_terms G)\<close>
    and mem: \<open>(a, \<sigma>) \<in> set (fscan tab ns rhs)\<close>
  shows \<open>a \<in> set (gram_terms G) \<and> \<sigma> \<in> {CEq, CGe, CGt 1, CAny}\<close>
  using terms mem
proof (induction rhs)
  case Nil
  then show ?case by simp
next
  case (Cons Xr rest)
  obtain X r where Xr: \<open>Xr = (X, r)\<close> by (cases Xr)
  from Cons.prems(2) consider
      (head) \<open>(a, \<sigma>) \<in> set (case X of
          Tm b \<Rightarrow> [(b, cwiden (cirel_of r))]
        | Nt B \<Rightarrow> map (\<lambda>(b, \<rho>). (b, cwiden (ccomp (cirel_of r) \<rho>))) (flook tab B))\<close>
    | (tail) \<open>(a, \<sigma>) \<in> set (fscan tab ns rest)\<close>
    unfolding Xr by (auto split: if_splits)
  then show ?case
  proof cases
    case head
    show ?thesis
    proof (cases X)
      case (Tm b)
      then show ?thesis
        using head Cons.prems(1)[of b r] cwiden_range Xr by auto
    next
      case (Nt B)
      from head obtain \<rho> where \<open>(a, \<rho>) \<in> set (flook tab B)\<close>
        and \<sigma>: \<open>\<sigma> = cwiden (ccomp (cirel_of r) \<rho>)\<close>
        unfolding Nt by auto
      from flookD[OF this(1)] have \<open>(B, a, \<rho>) \<in> set tab\<close> .
      then have \<open>a \<in> set (gram_terms G)\<close>
        using tab unfolding funiv_def by auto
      then show ?thesis using cwiden_range \<sigma> by auto
    qed
  next
    case tail
    then show ?thesis using Cons.IH Cons.prems(1) by fastforce
  qed
qed

lemma fstep_mono: \<open>set tab \<subseteq> set (fstep G tab)\<close>
  unfolding fstep_def by auto

lemma fstep_inU:
  assumes \<open>set tab \<subseteq> funiv G\<close>
  shows \<open>set (fstep G tab) \<subseteq> funiv G\<close>
proof
  fix x assume \<open>x \<in> set (fstep G tab)\<close>
  then consider \<open>x \<in> set tab\<close>
    | B rhs a \<sigma> where \<open>(B, rhs) \<in> set (iprods G)\<close>
        and \<open>(a, \<sigma>) \<in> set (fscan tab (nullables G) rhs)\<close> and \<open>x = (B, a, \<sigma>)\<close>
    unfolding fstep_def by fastforce
  then show \<open>x \<in> funiv G\<close>
  proof cases
    case 1
    then show ?thesis using assms by blast
  next
    case 2
    have \<open>a \<in> set (gram_terms G) \<and> \<sigma> \<in> {CEq, CGe, CGt 1, CAny}\<close>
      using fscan_inU[OF assms _ 2(2)] gram_termsI[OF 2(1)] by blast
    then show ?thesis
      using 2 unfolding funiv_def by force
  qed
qed

lemma fstep_distinct: \<open>distinct (fstep G tab)\<close>
  unfolding fstep_def by simp

text \<open>Saturation loops: iterate until the (always distinct) table stops
  growing.\<close>

lemma while_table_saturates_from:
  fixes step :: \<open>'x list \<Rightarrow> 'x list\<close> and U :: \<open>'x set\<close>
  assumes mono: \<open>\<And>tab. set tab \<subseteq> set (step tab)\<close>
    and dst: \<open>\<And>tab. distinct (step tab)\<close>
    and inU: \<open>\<And>tab. set tab \<subseteq> U \<Longrightarrow> set (step tab) \<subseteq> U\<close>
    and fin: \<open>finite U\<close>
    and istart: \<open>set tab\<^sub>0 \<subseteq> U\<close> and dst\<^sub>0: \<open>distinct tab\<^sub>0\<close>
  shows \<open>\<exists>t. while_option (\<lambda>tab. length (step tab) \<noteq> length tab) step tab\<^sub>0 = Some t \<and>
         set (step t) = set t \<and> set t \<subseteq> U\<close>
proof -
  define P where \<open>P = (\<lambda>tab :: 'x list. set tab \<subseteq> U \<and> distinct tab)\<close>
  define f where \<open>f = (\<lambda>tab :: 'x list. card U - card (set tab))\<close>
  have stepP: \<open>P (step tab) \<and> f (step tab) < f tab\<close>
    if Ptab: \<open>P tab\<close> and b: \<open>length (step tab) \<noteq> length tab\<close> for tab
  proof -
    have PU: \<open>set (step tab) \<subseteq> U\<close>
      using Ptab inU unfolding P_def by blast
    have cs: \<open>card (set (step tab)) = length (step tab)\<close>
      using dst by (simp add: distinct_card)
    have ct: \<open>card (set tab) = length tab\<close>
      using Ptab unfolding P_def by (simp add: distinct_card)
    have le: \<open>card (set tab) \<le> card (set (step tab))\<close>
      by (intro card_mono) (auto simp: mono)
    have lt: \<open>card (set tab) < card (set (step tab))\<close>
      using le b cs ct by simp
    have ltU: \<open>card (set tab) < card U\<close>
      using lt card_mono[OF fin PU] by simp
    have \<open>f (step tab) < f tab\<close>
      unfolding f_def using lt ltU by (simp add: diff_less_mono2)
    then show ?thesis using PU dst unfolding P_def by simp
  qed
  have P\<^sub>0: \<open>P tab\<^sub>0\<close> using istart dst\<^sub>0 unfolding P_def by simp
  have Some: \<open>\<exists>t. while_option (\<lambda>tab. length (step tab) \<noteq> length tab) step tab\<^sub>0 = Some t\<close>
    by (rule measure_while_option_Some[where P = P and f = f])
       (use stepP P\<^sub>0 in \<open>auto simp: P_def\<close>)
  then obtain t where t:
    \<open>while_option (\<lambda>tab. length (step tab) \<noteq> length tab) step tab\<^sub>0 = Some t\<close> by blast
  have Pt: \<open>P t\<close>
    by (rule while_option_rule[OF _ t]) (use stepP P\<^sub>0 in \<open>auto simp: P_def\<close>)
  have stop: \<open>length (step t) = length t\<close>
    using while_option_stop[OF t] by simp
  have \<open>card (set t) = card (set (step t))\<close>
    using stop Pt dst unfolding P_def by (simp add: distinct_card)
  then have \<open>set t = set (step t)\<close>
    by (intro card_subset_eq) (auto simp: mono)
  then show ?thesis using t Pt unfolding P_def by auto
qed

lemma while_table_saturates:
  fixes step :: \<open>'x list \<Rightarrow> 'x list\<close> and U :: \<open>'x set\<close>
  assumes \<open>\<And>tab. set tab \<subseteq> set (step tab)\<close>
    and \<open>\<And>tab. distinct (step tab)\<close>
    and \<open>\<And>tab. set tab \<subseteq> U \<Longrightarrow> set (step tab) \<subseteq> U\<close>
    and \<open>finite U\<close>
  shows \<open>\<exists>t. while_option (\<lambda>tab. length (step tab) \<noteq> length tab) step [] = Some t \<and>
         set (step t) = set t \<and> set t \<subseteq> U\<close>
  by (rule while_table_saturates_from[OF assms]) simp_all

lemma ffix_while:
  \<open>\<exists>t. while_option (\<lambda>tab. length (fstep G tab) \<noteq> length tab) (fstep G) [] = Some t \<and>
   set (fstep G t) = set t \<and> set t \<subseteq> funiv G\<close>
  by (rule while_table_saturates[OF fstep_mono fstep_distinct fstep_inU finite_funiv])

lemma ffix_stable: \<open>set (fstep G (ffix G)) = set (ffix G)\<close>
proof -
  obtain t where t: \<open>while_option (\<lambda>tab. length (fstep G tab) \<noteq> length tab)
      (fstep G) [] = Some t\<close>
    and st: \<open>set (fstep G t) = set t\<close>
    using ffix_while by blast
  show ?thesis unfolding ffix_def t by (simp add: st)
qed

lemma ffix_inU: \<open>set (ffix G) \<subseteq> funiv G\<close>
proof -
  obtain t where t: \<open>while_option (\<lambda>tab. length (fstep G tab) \<noteq> length tab)
      (fstep G) [] = Some t\<close>
    and U: \<open>set t \<subseteq> funiv G\<close>
    using ffix_while by blast
  show ?thesis unfolding ffix_def t by (simp add: U)
qed

lemma ffix_closed:
  assumes \<open>(B, rhs) \<in> set (iprods G)\<close>
    and \<open>(a, \<sigma>) \<in> set (fscan (ffix G) (nullables G) rhs)\<close>
  shows \<open>(B, a, \<sigma>) \<in> set (ffix G)\<close>
proof -
  have \<open>(B, a, \<sigma>) \<in> set (fstep G (ffix G))\<close>
    unfolding fstep_def using assms by force
  then show ?thesis using ffix_stable by blast
qed

subsection \<open>Completeness of the first-token table\<close>

lemma fscan_complete:
  assumes \<open>(infG G) \<turnstile> arhs \<Rightarrow>(n) Tm (a, c) # V\<close>
    and \<open>annotates j rhs arhs\<close>
  shows \<open>\<exists>\<sigma>. (a, \<sigma>) \<in> set (fscan (ffix G) (nullables G) rhs) \<and> csat \<sigma> c j\<close>
  using assms
proof (induction n arbitrary: rhs arhs j V rule: less_induct)
  case (less n)
  have \<open>arhs \<noteq> []\<close>
    using less.prems(1) deriven_from_empty by fastforce
  then obtain Xr rest where rhs: \<open>rhs = Xr # rest\<close>
    using less.prems(2) unfolding annotates_def
    by (cases rhs) auto
  obtain X r where Xr: \<open>Xr = (X, r)\<close> by (cases Xr)
  from less.prems(2) obtain Y arest where arhs: \<open>arhs = Y # arest\<close>
    and Y: \<open>\<exists>j\<^sub>1. Y = annsym (X, j\<^sub>1) \<and> irel_sat r j\<^sub>1 j\<close>
    and annrest: \<open>annotates j rest arest\<close>
    unfolding rhs Xr by (cases arhs) (auto simp: annotates_def)
  have \<open>(infG G) \<turnstile> [Y] @ arest \<Rightarrow>(n) Tm (a, c) # V\<close>
    using less.prems(1) unfolding arhs by simp
  from iffD1[OF deriven_append_decomp this]
  obtain n\<^sub>1 n\<^sub>2 w\<^sub>1 w\<^sub>2 where n: \<open>n = n\<^sub>1 + n\<^sub>2\<close> and w: \<open>Tm (a, c) # V = w\<^sub>1 @ w\<^sub>2\<close>
    and d\<^sub>1: \<open>(infG G) \<turnstile> [Y] \<Rightarrow>(n\<^sub>1) w\<^sub>1\<close>
    and d\<^sub>2: \<open>(infG G) \<turnstile> arest \<Rightarrow>(n\<^sub>2) w\<^sub>2\<close>
    by blast
  obtain j\<^sub>1 where Yj: \<open>Y = annsym (X, j\<^sub>1)\<close> and sat: \<open>irel_sat r j\<^sub>1 j\<close>
    using Y by blast
  show ?case
  proof (cases w\<^sub>1)
    case Nil
    have XN: \<open>nsym (nullables G) X\<close>
    proof (cases X)
      case (Tm b)
      then show ?thesis using d\<^sub>1 Nil Yj by (fastforce simp: deriven_Tm_Cons)
    next
      case (Nt C)
      have \<open>(infG G) \<turnstile> [Nt (C, j\<^sub>1)] \<Rightarrow>(n\<^sub>1) []\<close>
        using d\<^sub>1 Yj Nt unfolding Nil by simp
      from nullables_complete[OF this] show ?thesis
        using Nt unfolding nsym_def by simp
    qed
    have n\<^sub>1: \<open>n\<^sub>1 \<noteq> 0\<close> using d\<^sub>1 Nil Yj by (cases n\<^sub>1) auto
    then have n\<^sub>2: \<open>n\<^sub>2 < n\<close> using n by simp
    have d\<^sub>2': \<open>(infG G) \<turnstile> arest \<Rightarrow>(n\<^sub>2) Tm (a, c) # V\<close>
      using d\<^sub>2 w unfolding Nil by simp
    from less.IH[OF n\<^sub>2 d\<^sub>2' annrest]
    obtain \<sigma> where \<open>(a, \<sigma>) \<in> set (fscan (ffix G) (nullables G) rest)\<close>
      and \<open>csat \<sigma> c j\<close> by blast
    then show ?thesis
      unfolding rhs Xr using XN by auto
  next
    case (Cons y w\<^sub>1')
    have y: \<open>y = Tm (a, c)\<close> and V: \<open>V = w\<^sub>1' @ w\<^sub>2\<close>
      using w unfolding Cons by auto
    show ?thesis
    proof (cases X)
      case (Tm b)
      have YT: \<open>Y = Tm (b, j\<^sub>1)\<close> using Yj Tm by simp
      have \<open>w\<^sub>1 = [Tm (b, j\<^sub>1)]\<close>
        using d\<^sub>1[unfolded YT] by (simp add: deriven_Tm_Cons)
      then have ab: \<open>a = b\<close> and cj: \<open>c = j\<^sub>1\<close>
        using Cons y by auto
      have \<open>csat (cirel_of r) c j\<close> using sat cj by simp
      then have \<open>csat (cwiden (cirel_of r)) c j\<close> by (rule csat_cwiden)
      then show ?thesis
        unfolding rhs Xr using Tm ab by auto
    next
      case (Nt C)
      have YN: \<open>Y = Nt (C, j\<^sub>1)\<close> using Yj Nt by simp
      obtain m\<^sub>1 where n\<^sub>1: \<open>n\<^sub>1 = Suc m\<^sub>1\<close>
        using d\<^sub>1 Cons y YN by (cases n\<^sub>1) auto
      from relpowp_Suc_D2[OF d\<^sub>1[unfolded n\<^sub>1 YN]] obtain v where
        st: \<open>infG G \<turnstile> [Nt (C, j\<^sub>1)] \<Rightarrow> v\<close>
        and dv: \<open>(infG G) \<turnstile> v \<Rightarrow>(m\<^sub>1) Tm (a, c) # w\<^sub>1'\<close>
        unfolding Cons y by blast
      from st obtain brhs' where
        pr: \<open>((C, j\<^sub>1), brhs') \<in> infG G\<close> and v: \<open>v = brhs'\<close>
        by (auto simp: derive_singleton)
      from pr[unfolded infG_alt] obtain brhs where
        brhs: \<open>(C, brhs) \<in> set (iprods G)\<close> and annb: \<open>annotates j\<^sub>1 brhs brhs'\<close>
        by blast
      have \<open>m\<^sub>1 < n\<close> using n n\<^sub>1 by simp
      from less.IH[OF this dv[unfolded v] annb]
      obtain \<rho> where mem: \<open>(a, \<rho>) \<in> set (fscan (ffix G) (nullables G) brhs)\<close>
        and sat\<rho>: \<open>csat \<rho> c j\<^sub>1\<close> by blast
      have inffix: \<open>(C, a, \<rho>) \<in> set (ffix G)\<close>
        by (rule ffix_closed[OF brhs mem])
      have \<open>csat (cwiden (ccomp (cirel_of r) \<rho>)) c j\<close>
      proof -
        have \<open>csat (ccomp (cirel_of r) \<rho>) c j\<close>
          unfolding csat_ccomp using sat\<rho> sat by auto
        then show ?thesis by (rule csat_cwiden)
      qed
      then show ?thesis
        unfolding rhs Xr using Nt flookI[OF inffix] by force
    qed
  qed
qed

text \<open>The phase-1 theorem: the executable table covers \<^term>\<open>fHk G 1\<close>.
  Every token that can begin the yield of an (annotated) production rest
  is covered by a computed \<^text>\<open>(token, cirel)\<close> cell; the only other
  possibility is a fully nullable rest exposing the follow-up lookahead.\<close>

theorem first1_complete:
  assumes \<open>v \<in> fHk G (Suc 0) rest i u\<close>
  shows \<open>(\<exists>a c \<sigma>. v = [(a, c)] \<and>
            (a, \<sigma>) \<in> set (fscan (ffix G) (nullables G) rest) \<and> csat \<sigma> c i)
       \<or> (list_all (\<lambda>(X, r). nsym (nullables G) X) rest \<and> v = take (Suc 0) u)\<close>
proof -
  from fHkE[OF assms] obtain arest where
    ann: \<open>annotates i rest arest\<close>
    and vHk: \<open>v \<in> Hk (infG G) (Suc 0) (arest @ map Tm u)\<close> by metis
  from vHk[unfolded Hk_def] obtain V where
    len: \<open>length v = Suc 0\<close>
    and der: \<open>infG G \<turnstile> arest @ map Tm u \<Rightarrow>* map Tm v @ V\<close>
    by auto
  obtain t where veq: \<open>v = [t]\<close> using len by (cases v) auto
  obtain a c where t: \<open>t = (a, c)\<close> by (cases t)
  from der obtain n where dern: \<open>(infG G) \<turnstile> arest @ map Tm u \<Rightarrow>(n) Tm (a, c) # V\<close>
    unfolding veq t by (auto simp: rtranclp_power)
  from iffD1[OF deriven_append_decomp dern]
  obtain n\<^sub>1 n\<^sub>2 w\<^sub>1 w\<^sub>2 where w: \<open>Tm (a, c) # V = w\<^sub>1 @ w\<^sub>2\<close>
    and d\<^sub>1: \<open>(infG G) \<turnstile> arest \<Rightarrow>(n\<^sub>1) w\<^sub>1\<close>
    and d\<^sub>2: \<open>(infG G) \<turnstile> map Tm u \<Rightarrow>(n\<^sub>2) w\<^sub>2\<close>
    by blast
  show ?thesis
  proof (cases w\<^sub>1)
    case Nil
    have nul: \<open>list_all (\<lambda>(X, r). nsym (nullables G) X) rest\<close>
      by (rule annotated_null[OF d\<^sub>1[unfolded Nil] ann])
    have w2eq: \<open>w\<^sub>2 = map Tm u\<close>
      using relpowp_imp_rtranclp[OF d\<^sub>2] by (simp add: derives_from_Tms_iff)
    have \<open>map Tm u = Tm (a, c) # V\<close> using w w2eq unfolding Nil by simp
    then obtain u' where \<open>u = (a, c) # u'\<close> by (cases u) auto
    then show ?thesis using nul veq t by simp
  next
    case (Cons y w\<^sub>1')
    have \<open>y = Tm (a, c)\<close> using w unfolding Cons by simp
    from fscan_complete[OF d\<^sub>1[unfolded Cons this] ann]
    show ?thesis using veq t by auto
  qed
qed

section \<open>LR tables and conflict reports\<close>

text \<open>
  The layers on top of the LR(0) automaton and the lookahead tables: the
  canonical per-item LALR cells and the conflict report over them; the
  driver that parses with the cells at runtime follows in
  \<^text>\<open>LR_Driver\<close>.
\<close>

subsection \<open>Live frames\<close>

definition live :: \<open>('n, 't) xitem list \<Rightarrow> bool\<close> where
  \<open>live xs = list_ex (\<lambda>(pr, m, R). irep_nonempty R) xs\<close>

section \<open>Column-aware conflict analysis\<close>

text \<open>
  Follow cells relate token columns to the indentations of different
  items, which are pairwise incomparable, so a token-level report could
  compare token classes only. For a sharper check every item
  is related to a \<^emph>\<open>common anchor\<close>, the indentation label of the goto
  that built the state. Composing these paths needs inverse relations,
  which \<^typ>\<open>cirel\<close> lacks, so the analysis runs in a small
  two-directional class algebra \<^text>\<open>wrel\<close>. That algebra is the verified
  core: embedding, inversion and composition only weaken, and
  \<^text>\<open>wdisjoint\<close> detects only disjoint pairs, so pruning a conflict
  pair is justified.
\<close>

subsection \<open>The two-directional class algebra\<close>

datatype wrel = WEq | WGe | WGt | WLe | WLt | WAny

fun wsat :: \<open>wrel \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool\<close> where
  \<open>wsat WEq k i \<longleftrightarrow> k = i\<close>
| \<open>wsat WGe k i \<longleftrightarrow> k \<ge> i\<close>
| \<open>wsat WGt k i \<longleftrightarrow> k > i\<close>
| \<open>wsat WLe k i \<longleftrightarrow> k \<le> i\<close>
| \<open>wsat WLt k i \<longleftrightarrow> k < i\<close>
| \<open>wsat WAny k i \<longleftrightarrow> True\<close>

fun w_of :: \<open>irel \<Rightarrow> wrel\<close> where
  \<open>w_of Eq = WEq\<close> | \<open>w_of Gt = WGt\<close> | \<open>w_of Ge = WGe\<close> | \<open>w_of Any = WAny\<close>

lemma w_of_sound: \<open>irel_sat r k i \<Longrightarrow> wsat (w_of r) k i\<close>
  by (cases r) auto

fun wemb :: \<open>cirel \<Rightarrow> wrel\<close> where
  \<open>wemb CEq = WEq\<close>
| \<open>wemb CGe = WGe\<close>
| \<open>wemb (CGt n) = (if n = 0 then WGe else WGt)\<close>
| \<open>wemb CAny = WAny\<close>
| \<open>wemb (CGtAny n) = WAny\<close>

lemma wemb_sound: \<open>csat \<sigma> k i \<Longrightarrow> wsat (wemb \<sigma>) k i\<close>
  by (cases \<sigma>) auto

fun winv :: \<open>wrel \<Rightarrow> wrel\<close> where
  \<open>winv WEq = WEq\<close> | \<open>winv WGe = WLe\<close> | \<open>winv WGt = WLt\<close>
| \<open>winv WLe = WGe\<close> | \<open>winv WLt = WGt\<close> | \<open>winv WAny = WAny\<close>

lemma winv_sound: \<open>wsat \<tau> k i \<Longrightarrow> wsat (winv \<tau>) i k\<close>
  by (cases \<tau>) auto

fun wcomp :: \<open>wrel \<Rightarrow> wrel \<Rightarrow> wrel\<close> where
  \<open>wcomp WEq \<tau> = \<tau>\<close>
| \<open>wcomp \<tau> WEq = \<tau>\<close>
| \<open>wcomp WGe WGe = WGe\<close>
| \<open>wcomp WGe WGt = WGt\<close>
| \<open>wcomp WGt WGe = WGt\<close>
| \<open>wcomp WGt WGt = WGt\<close>
| \<open>wcomp WLe WLe = WLe\<close>
| \<open>wcomp WLe WLt = WLt\<close>
| \<open>wcomp WLt WLe = WLt\<close>
| \<open>wcomp WLt WLt = WLt\<close>
| \<open>wcomp \<tau>\<^sub>1 \<tau>\<^sub>2 = WAny\<close>

lemma wcomp_sound:
  \<open>wsat \<tau>\<^sub>2 k j \<Longrightarrow> wsat \<tau>\<^sub>1 j i \<Longrightarrow> wsat (wcomp \<tau>\<^sub>1 \<tau>\<^sub>2) k i\<close>
  by (cases \<tau>\<^sub>1; cases \<tau>\<^sub>2) auto

fun wdisjoint :: \<open>wrel \<Rightarrow> wrel \<Rightarrow> bool\<close> where
  \<open>wdisjoint WEq WGt = True\<close> | \<open>wdisjoint WGt WEq = True\<close>
| \<open>wdisjoint WEq WLt = True\<close> | \<open>wdisjoint WLt WEq = True\<close>
| \<open>wdisjoint WGt WLt = True\<close> | \<open>wdisjoint WLt WGt = True\<close>
| \<open>wdisjoint WGt WLe = True\<close> | \<open>wdisjoint WLe WGt = True\<close>
| \<open>wdisjoint WGe WLt = True\<close> | \<open>wdisjoint WLt WGe = True\<close>
| \<open>wdisjoint \<tau>\<^sub>1 \<tau>\<^sub>2 = False\<close>

lemma wdisjoint_sound:
  \<open>wsat \<tau>\<^sub>1 c l \<Longrightarrow> wsat \<tau>\<^sub>2 c l \<Longrightarrow> \<not> wdisjoint \<tau>\<^sub>1 \<tau>\<^sub>2\<close>
  by (cases \<tau>\<^sub>1; cases \<tau>\<^sub>2) auto

subsection \<open>Anchored reachable closures\<close>

text \<open>Items with a \<^typ>\<open>wrel\<close> relating the state's incoming goto label to
  the item's left-hand-side indentation.  Kernel items read it off their
  just-dotted symbol; closure children compose through the position's
  relation.  Like \<^const>\<open>creach\<close>, a diagnostic computation.\<close>

type_synonym ('n, 't) witem = \<open>('n \<times> ('n, 't) rhs) \<times> nat \<times> wrel\<close>

definition wkernel :: \<open>('n, 't) citem list \<Rightarrow> ('n, 't) witem list\<close> where
  \<open>wkernel s = map (\<lambda>(pr, m). (pr, m,
      if m = 0 then WAny else w_of (snd (snd pr ! (m - 1))))) s\<close>

definition wreach_step :: \<open>('n, 't) is_cfg \<Rightarrow> ('n, 't) witem list \<Rightarrow> ('n, 't) witem list\<close> where
  \<open>wreach_step G ws = remdups (ws @ concat (map (\<lambda>(pr, m, \<rho>).
      if m < length (snd pr)
      then (case fst (snd pr ! m) of
             Nt B \<Rightarrow> map (\<lambda>br. (br, 0,
                       wcomp (winv (w_of (snd (snd pr ! m)))) \<rho>))
                     (filter (\<lambda>br. fst br = B) (iprods G))
           | Tm _ \<Rightarrow> [])
      else []) ws))\<close>

definition wreach :: \<open>('n, 't) is_cfg \<Rightarrow> ('n, 't) citem list \<Rightarrow> ('n, 't) witem list\<close> where
  \<open>wreach G s = (wreach_step G ^^ Suc (length (iprods G) * 6)) (wkernel s)\<close>

subsection \<open>Anchored shift cells\<close>

text \<open>A shift cell relates the token's column to the state's common anchor
  through the dotted terminal's own relation.\<close>

definition shift_cells :: \<open>('n, 't) witem list \<Rightarrow> ('t \<times> wrel) list\<close> where
  \<open>shift_cells ws = concat (map (\<lambda>(pr, m, \<rho>).
      if m < length (snd pr)
      then (case fst (snd pr ! m) of
             Tm a \<Rightarrow> [(a, wcomp (winv \<rho>) (w_of (snd (snd pr ! m))))]
           | Nt _ \<Rightarrow> [])
      else []) ws)\<close>

section \<open>Canonical per-item lookahead (LALR over the LR(0) automaton)\<close>

text \<open>
  A global FOLLOW table would lose the column information at every
  occurrence whose relation is not equality; lookahead is therefore
  computed per item, along the automaton:
  a cell \<^text>\<open>(state, item, token-or-end, \<tau>)\<close> says the token's column
  relates by \<^text>\<open>\<tau>\<close> to that item's own left-hand-side indentation.
  Cells are seeded at the start item, flow through closures (re-anchored
  through the occurrence's relation) and through gotos unchanged, in one
  saturation over the automaton, LALR-style.
\<close>

definition anch :: \<open>'n \<times> ('n, 't) rhs \<Rightarrow> nat \<Rightarrow> wrel\<close> where
  \<open>anch pr m = (if m = 0 then WAny else w_of (snd (snd pr ! (m - 1))))\<close>

definition st_find :: \<open>('n, 't) citem list list \<Rightarrow> ('n, 't) citem list \<Rightarrow> nat\<close> where
  \<open>st_find sts t = (case filter (\<lambda>j. set (sts ! j) = set t) [0..<length sts]
     of [] \<Rightarrow> length sts | j # _ \<Rightarrow> j)\<close>

lemma st_find_le: \<open>st_find sts t \<le> length sts\<close>
proof (cases \<open>filter (\<lambda>j. set (sts ! j) = set t) [0..<length sts]\<close>)
  case Nil
  then show ?thesis unfolding st_find_def by simp
next
  case (Cons j rest)
  have \<open>j \<in> set (filter (\<lambda>j. set (sts ! j) = set t) [0..<length sts])\<close>
    unfolding Cons by simp
  then have \<open>j < length sts\<close> by simp
  then show ?thesis unfolding st_find_def Cons by simp
qed

lemma st_find_found:
  assumes \<open>t \<in> set sts\<close> and \<open>set t = set s\<close>
  shows \<open>st_find sts s < length sts \<and> set (sts ! st_find sts s) = set s\<close>
proof -
  obtain j where j: \<open>j < length sts\<close> and tj: \<open>sts ! j = t\<close> using assms(1) by (metis in_set_conv_nth)
  have \<open>j \<in> set (filter (\<lambda>j. set (sts ! j) = set s) [0..<length sts])\<close> using j tj assms(2) by simp
  then obtain j' rest where f: \<open>filter (\<lambda>j. set (sts ! j) = set s) [0..<length sts] = j' # rest\<close>
    by (cases \<open>filter (\<lambda>j. set (sts ! j) = set s) [0..<length sts]\<close>) auto
  have \<open>j' \<in> set (filter (\<lambda>j. set (sts ! j) = set s) [0..<length sts])\<close> unfolding f by simp
  then have j'_ok: \<open>j' < length sts \<and> set (sts ! j') = set s\<close> by simp
  show ?thesis unfolding st_find_def f using j'_ok by simp
qed

lemma st_find_cong: \<open>set t = set t' \<Longrightarrow> st_find sts t = st_find sts t'\<close>
  unfolding st_find_def by simp

lemma st_find_unique:
  assumes dst: \<open>distinct (map set sts)\<close> and i: \<open>i < length sts\<close>
    and eq: \<open>set (sts ! i) = set t\<close>
  shows \<open>st_find sts t = i\<close>
proof -
  have uniq: \<open>j = i\<close> if \<open>j \<in> set (filter (\<lambda>j. set (sts ! j) = set t) [0..<length sts])\<close> for j
  proof -
    have j: \<open>j < length sts\<close> and ej: \<open>set (sts ! j) = set t\<close> using that by auto
    have \<open>map set sts ! j = map set sts ! i\<close> using j i ej eq by simp
    then show \<open>j = i\<close>
      using dst j i nth_eq_iff_index_eq[of \<open>map set sts\<close> j i] by simp
  qed
  have imem: \<open>i \<in> set (filter (\<lambda>j. set (sts ! j) = set t) [0..<length sts])\<close>
    using i eq by simp
  then obtain j rest where f:
    \<open>filter (\<lambda>j. set (sts ! j) = set t) [0..<length sts] = j # rest\<close>
    by (cases \<open>filter (\<lambda>j. set (sts ! j) = set t) [0..<length sts]\<close>) auto
  have \<open>j = i\<close> using uniq f by (metis list.set_intros(1))
  then show ?thesis unfolding st_find_def f by simp
qed

type_synonym ('n, 't) lacell = \<open>nat \<times> ('n, 't) citem \<times> 't option \<times> wrel\<close>

text \<open>The FIRST table, the nullable set and a per-state goto table are
  computed once and passed as parameters.  The \<^const>\<open>min\<close> in
  \<^text>\<open>la_next\<close> makes the state bound hold by construction, so the
  saturation-universe proof does not depend on the goto table's contents.\<close>

definition la_next :: \<open>(('n, 't) sym \<times> nat) list list \<Rightarrow> ('n, 't) citem list list \<Rightarrow>
    nat \<Rightarrow> ('n, 't) sym \<Rightarrow> nat\<close> where
  \<open>la_next gt sts i X =
     min (case map_of (gt ! i) X of Some j \<Rightarrow> j | None \<Rightarrow> length sts) (length sts)\<close>

lemma la_next_le: \<open>la_next gt sts i X \<le> length sts\<close>
  unfolding la_next_def by simp

definition la_gtab :: \<open>('n, 't) is_cfg \<Rightarrow> ('n, 't) citem list list \<Rightarrow>
    (('n, 't) sym \<times> nat) list list\<close> where
  \<open>la_gtab G sts = map (\<lambda>s. let cl = cclosure G s in
      map (\<lambda>X. (X, st_find sts (cgoto cl X)))
        (remdups (concat (map (\<lambda>(pr, m).
           if m < length (snd pr) then [fst (snd pr ! m)] else []) cl)))) sts\<close>

definition la_start :: \<open>('n, 't) is_cfg \<Rightarrow> 'n \<Rightarrow> ('n, 't) citem list list \<Rightarrow>
    ('n, 't) lacell list\<close> where
  \<open>la_start G Shn sts =
     [(st_find sts (lr0_start G Shn), (start_prod G Shn, 0), None, WAny)]\<close>

fun la_cell :: \<open>('n, 't) is_cfg \<Rightarrow> ('n, 't) ftab \<Rightarrow> 'n list \<Rightarrow>
    (('n, 't) sym \<times> nat) list list \<Rightarrow> ('n, 't) citem list list \<Rightarrow>
    ('n, 't) lacell \<Rightarrow> ('n, 't) lacell list\<close> where
  \<open>la_cell G ft ns gt sts (i, (pr, m), t, \<tau>) = (
      if m < length (snd pr)
      then (la_next gt sts i (fst (snd pr ! m)), (pr, Suc m), t, \<tau>)
        # (case fst (snd pr ! m) of
             Nt B \<Rightarrow> (let back = winv (w_of (snd (snd pr ! m)));
                         la = map (\<lambda>(a, \<sigma>). (Some a, wcomp back (wemb \<sigma>)))
                                (fscan ft ns (drop (Suc m) (snd pr)))
                              @ (if list_all (\<lambda>(X, r). nsym ns X)
                                       (drop (Suc m) (snd pr))
                                 then [(t, wcomp back \<tau>)] else [])
                     in concat (map (\<lambda>br.
                          if fst br = B
                          then map (\<lambda>(u, \<rho>). (i, (br, 0), u, \<rho>)) la
                          else []) (iprods G)))
           | Tm _ \<Rightarrow> [])
      else [])\<close>

definition la_step :: \<open>('n, 't) is_cfg \<Rightarrow> ('n, 't) ftab \<Rightarrow> 'n list \<Rightarrow>
    (('n, 't) sym \<times> nat) list list \<Rightarrow> ('n, 't) citem list list \<Rightarrow>
    ('n, 't) lacell list \<Rightarrow> ('n, 't) lacell list\<close> where
  \<open>la_step G ft ns gt sts L = remdups (L @ concat (map (la_cell G ft ns gt sts) L))\<close>

lemma la_cell_cases:
  assumes \<open>x \<in> set (la_cell G ft ns gt sts (i, (pr, m), t, \<tau>))\<close>
  obtains
    (goto) \<open>m < length (snd pr)\<close>
      and \<open>x = (la_next gt sts i (fst (snd pr ! m)), (pr, Suc m), t, \<tau>)\<close>
  | (first) br a \<sigma> where \<open>m < length (snd pr)\<close> and \<open>br \<in> set (iprods G)\<close>
      and \<open>(a, \<sigma>) \<in> set (fscan ft ns (drop (Suc m) (snd pr)))\<close>
      and \<open>x = (i, (br, 0), Some a, wcomp (winv (w_of (snd (snd pr ! m)))) (wemb \<sigma>))\<close>
  | (inherit) br where \<open>m < length (snd pr)\<close> and \<open>br \<in> set (iprods G)\<close>
      and \<open>x = (i, (br, 0), t, wcomp (winv (w_of (snd (snd pr ! m)))) \<tau>)\<close>
  using assms by (auto simp: Let_def split: sym.splits if_splits)

definition la_univ :: \<open>('n, 't) is_cfg \<Rightarrow> 'n \<Rightarrow> nat \<Rightarrow> ('n, 't) lacell set\<close> where
  \<open>la_univ G Shn n =
     {0..n} \<times> cuniv G Shn \<times> (Some ` set (gram_terms G) \<union> {None}) \<times> (UNIV :: wrel set)\<close>

lemma UNIV_wrel: \<open>(UNIV :: wrel set) = {WEq, WGe, WGt, WLe, WLt, WAny}\<close>
  by (auto intro: wrel.exhaust)

lemma finite_la_univ: \<open>finite (la_univ G Shn n)\<close>
  unfolding la_univ_def UNIV_wrel by (intro finite_cartesian_product) (auto simp: finite_cuniv)

lemma la_step_mono: \<open>set L \<subseteq> set (la_step G ft ns gt sts L)\<close>
  unfolding la_step_def by auto

lemma cuniv_terms:
  assumes \<open>(pr, m) \<in> cuniv G Shn\<close>
    and \<open>(Tm a, r) \<in> set (drop (Suc m) (snd pr))\<close>
  shows \<open>a \<in> set (gram_terms G)\<close>
proof -
  have mem: \<open>(Tm a, r) \<in> set (snd pr)\<close>
    using assms(2) by (rule in_set_dropD)
  from assms(1) consider \<open>pr = start_prod G Shn\<close> | \<open>pr \<in> set (iprods G)\<close>
    unfolding cuniv_def by auto
  then show ?thesis
  proof cases
    case 1
    then show ?thesis using mem unfolding start_prod_def by auto
  next
    case 2
    then show ?thesis
      using gram_termsI[of \<open>fst pr\<close> \<open>snd pr\<close> G a r] mem by auto
  qed
qed

lemma la_cell_inU:
  assumes ft: \<open>set ft \<subseteq> funiv G\<close>
    and cin: \<open>c \<in> la_univ G Shn (length sts)\<close>
  shows \<open>set (la_cell G ft ns gt sts c) \<subseteq> la_univ G Shn (length sts)\<close>
proof
  fix x assume xc: \<open>x \<in> set (la_cell G ft ns gt sts c)\<close>
  obtain i q t \<tau> where c\<^sub>4: \<open>c = (i, q, t, \<tau>)\<close> using prod_cases4 by blast
  obtain pr m where q: \<open>q = (pr, m)\<close> by (cases q)
  have iu: \<open>i \<le> length sts\<close> and pru: \<open>(pr, m) \<in> cuniv G Shn\<close>
    and tu: \<open>t \<in> Some ` set (gram_terms G) \<union> {None}\<close>
    using cin unfolding c\<^sub>4 q la_univ_def by auto
  from xc[unfolded c\<^sub>4 q] show \<open>x \<in> la_univ G Shn (length sts)\<close>
  proof (cases rule: la_cell_cases)
    case goto
    have \<open>(pr, Suc m) \<in> cuniv G Shn\<close>
      using pru goto(1) unfolding cuniv_def by auto
    then show ?thesis
      using la_next_le tu goto(2)
      unfolding la_univ_def by auto
  next
    case (first br a \<sigma>)
    have a: \<open>a \<in> set (gram_terms G)\<close>
      using fscan_inU[OF ft _ first(3)] cuniv_terms[OF pru] by blast
    show ?thesis
      using iu first(2,4) a unfolding la_univ_def cuniv_def by auto
  next
    case (inherit br)
    show ?thesis
      using iu tu inherit(2,3) unfolding la_univ_def cuniv_def by auto
  qed
qed

text \<open>The saturation runs as a worklist: every cell is expanded once, and
  only new cells enter the queue, where a fixpoint of \<^const>\<open>la_step\<close>
  would re-expand the table each round.  Termination and the closure
  property follow the invariant-plus-measure scheme of the
  \<^const>\<open>lr0_states\<close> worklist.\<close>

definition la_wl :: \<open>('n, 't) is_cfg \<Rightarrow> ('n, 't) ftab \<Rightarrow> 'n list \<Rightarrow>
    (('n, 't) sym \<times> nat) list list \<Rightarrow> ('n, 't) citem list list \<Rightarrow>
    ('n, 't) lacell list \<times> ('n, 't) lacell list \<Rightarrow>
    ('n, 't) lacell list \<times> ('n, 't) lacell list\<close> where
  \<open>la_wl G ft ns gt sts = (\<lambda>(dn, wk). case wk of
      [] \<Rightarrow> (dn, [])
    | c # ws \<Rightarrow> (c # dn,
        ws @ filter (\<lambda>x. x \<notin> set (c # dn) \<and> x \<notin> set ws)
               (remdups (la_cell G ft ns gt sts c))))\<close>

definition la_inv :: \<open>('n, 't) is_cfg \<Rightarrow> 'n \<Rightarrow> ('n, 't) ftab \<Rightarrow> 'n list \<Rightarrow>
    (('n, 't) sym \<times> nat) list list \<Rightarrow> ('n, 't) citem list list \<Rightarrow>
    ('n, 't) lacell list \<times> ('n, 't) lacell list \<Rightarrow> bool\<close> where
  \<open>la_inv G Shn ft ns gt sts = (\<lambda>(dn, wk).
     distinct (dn @ wk) \<and>
     set (dn @ wk) \<subseteq> la_univ G Shn (length sts) \<and>
     set (la_start G Shn sts) \<subseteq> set (dn @ wk) \<and>
     (\<forall>c \<in> set dn. set (la_cell G ft ns gt sts c) \<subseteq> set (dn @ wk)))\<close>

lemma la_wl_inv:
  assumes ft: \<open>set ft \<subseteq> funiv G\<close>
    and inv: \<open>la_inv G Shn ft ns gt sts (dn, wk)\<close> and ne: \<open>wk \<noteq> []\<close>
  shows \<open>la_inv G Shn ft ns gt sts (la_wl G ft ns gt sts (dn, wk))\<close>
proof -
  obtain c ws where wk: \<open>wk = c # ws\<close> using ne by (cases wk) auto
  define fresh where \<open>fresh = filter (\<lambda>x. x \<notin> set (c # dn) \<and> x \<notin> set ws)
      (remdups (la_cell G ft ns gt sts c))\<close>
  have res: \<open>la_wl G ft ns gt sts (dn, wk) = (c # dn, ws @ fresh)\<close>
    unfolding la_wl_def wk fresh_def by simp
  have dst: \<open>distinct (dn @ wk)\<close>
    and unv: \<open>set (dn @ wk) \<subseteq> la_univ G Shn (length sts)\<close>
    and st: \<open>set (la_start G Shn sts) \<subseteq> set (dn @ wk)\<close>
    and cls: \<open>\<forall>c' \<in> set dn. set (la_cell G ft ns gt sts c') \<subseteq> set (dn @ wk)\<close>
    using inv unfolding la_inv_def by auto
  have cinU: \<open>c \<in> la_univ G Shn (length sts)\<close> using unv wk by auto
  have dst': \<open>distinct ((c # dn) @ ws @ fresh)\<close>
    using dst unfolding wk fresh_def by auto
  have unv': \<open>set ((c # dn) @ ws @ fresh) \<subseteq> la_univ G Shn (length sts)\<close>
    using unv la_cell_inU[OF ft cinU] unfolding wk fresh_def by auto
  have sub: \<open>set (dn @ wk) \<subseteq> set ((c # dn) @ ws @ fresh)\<close>
    unfolding wk by auto
  have st': \<open>set (la_start G Shn sts) \<subseteq> set ((c # dn) @ ws @ fresh)\<close>
    using st sub by blast
  have cls': \<open>\<forall>c' \<in> set (c # dn).
      set (la_cell G ft ns gt sts c') \<subseteq> set ((c # dn) @ ws @ fresh)\<close>
  proof
    fix c' assume \<open>c' \<in> set (c # dn)\<close>
    then consider \<open>c' = c\<close> | \<open>c' \<in> set dn\<close> by auto
    then show \<open>set (la_cell G ft ns gt sts c') \<subseteq> set ((c # dn) @ ws @ fresh)\<close>
    proof cases
      case 1
      show ?thesis
      proof
        fix x assume x: \<open>x \<in> set (la_cell G ft ns gt sts c')\<close>
        show \<open>x \<in> set ((c # dn) @ ws @ fresh)\<close>
        proof (cases \<open>x \<in> set (c # dn) \<or> x \<in> set ws\<close>)
          case True then show ?thesis by auto
        next
          case False
          then have \<open>x \<in> set fresh\<close> using x unfolding fresh_def 1 by auto
          then show ?thesis by auto
        qed
      qed
    next
      case 2
      then show ?thesis using cls sub by blast
    qed
  qed
  show ?thesis unfolding res la_inv_def using dst' unv' st' cls' by simp
qed

lemma la_inv_init:
  \<open>la_inv G Shn ft ns gt sts ([], la_start G Shn sts)\<close>
  unfolding la_inv_def la_start_def la_univ_def cuniv_def
  using st_find_le by auto

text \<open>The saturated table over an arbitrary automaton \<open>(gt, sts)\<close>;
  \<^text>\<open>la_fix\<close> is its instance at the coarse tables, and the
  context-precise analysis of \<^text>\<open>LR_Det\<close> instantiates it at the
  precise ones.\<close>

definition la_fix_gen :: \<open>('n, 't) is_cfg \<Rightarrow> 'n \<Rightarrow> (('n, 't) sym \<times> nat) list list \<Rightarrow>
    ('n, 't) citem list list \<Rightarrow> ('n, 't) lacell list\<close> where
  \<open>la_fix_gen G Shn gt sts =
     fst (the (while_option (\<lambda>(dn, wk). wk \<noteq> []) (la_wl G (ffix G) (nullables G) gt sts)
       ([], la_start G Shn sts)))\<close>

lemma la_fix_gen_inv:
  \<open>la_inv G Shn (ffix G) (nullables G) gt sts (la_fix_gen G Shn gt sts, [])\<close>
proof -
  let ?P = \<open>la_inv G Shn (ffix G) (nullables G) gt sts\<close>
  let ?c = \<open>la_wl G (ffix G) (nullables G) gt sts\<close>
  let ?t = \<open>the (while_option (\<lambda>(dn, wk). wk \<noteq> []) ?c ([], la_start G Shn sts))\<close>
  have \<open>?P ?t \<and> \<not> (case ?t of (dn, wk) \<Rightarrow> wk \<noteq> [])\<close>
  proof (rule while_option_the_inv[where P = ?P and b = \<open>\<lambda>(dn, wk). wk \<noteq> []\<close>
        and c = ?c and f = \<open>\<lambda>(dn, wk). card (la_univ G Shn (length sts)) - length dn\<close>])
    show \<open>?P ([], la_start G Shn sts)\<close> by (rule la_inv_init)
  next
    fix st assume inv: \<open>?P st\<close>
      and b: \<open>case st of (dn, wk) \<Rightarrow> wk \<noteq> []\<close>
    obtain dn wk where st: \<open>st = (dn, wk)\<close> by (cases st)
    obtain c ws where wk: \<open>wk = c # ws\<close> using b st by (cases wk) auto
    have inv': \<open>?P (?c (dn, wk))\<close>
      using la_wl_inv[OF ffix_inU inv[unfolded st]] b st by simp
    have fst_res: \<open>fst (?c (dn, wk)) = c # dn\<close>
      unfolding la_wl_def wk by simp
    have \<open>distinct (c # dn)\<close> and \<open>set (c # dn) \<subseteq> la_univ G Shn (length sts)\<close>
      using inv unfolding st wk la_inv_def by auto
    then have \<open>length (c # dn) \<le> card (la_univ G Shn (length sts))\<close>
      by (metis distinct_card card_mono finite_la_univ)
    then have dec: \<open>card (la_univ G Shn (length sts)) - length (c # dn)
        < card (la_univ G Shn (length sts)) - length dn\<close>
      by simp
    show \<open>?P (?c st) \<and>
        (case ?c st of
           (dn, wk) \<Rightarrow> card (la_univ G Shn (length sts)) - length dn)
        < (case st of (dn, wk) \<Rightarrow> card (la_univ G Shn (length sts)) - length dn)\<close>
      using inv' dec fst_res unfolding st
      by (cases \<open>?c (dn, wk)\<close>) auto
  qed
  then show ?thesis unfolding la_fix_gen_def by (cases ?t) auto
qed

lemma la_fix_gen_stable:
  \<open>set (la_step G (ffix G) (nullables G) gt sts (la_fix_gen G Shn gt sts))
   = set (la_fix_gen G Shn gt sts)\<close>
proof -
  have cls: \<open>\<forall>c \<in> set (la_fix_gen G Shn gt sts).
      set (la_cell G (ffix G) (nullables G) gt sts c) \<subseteq> set (la_fix_gen G Shn gt sts)\<close>
    using la_fix_gen_inv[of G Shn gt sts] unfolding la_inv_def by auto
  have \<open>set (la_step G (ffix G) (nullables G) gt sts (la_fix_gen G Shn gt sts))
      \<subseteq> set (la_fix_gen G Shn gt sts)\<close>
    unfolding la_step_def using cls by auto
  then show ?thesis using la_step_mono by blast
qed

lemma la_fix_gen_start: \<open>set (la_start G Shn sts) \<subseteq> set (la_fix_gen G Shn gt sts)\<close>
  using la_fix_gen_inv[of G Shn gt sts] unfolding la_inv_def by auto

definition la_fix :: \<open>('n, 't) is_cfg \<Rightarrow> 'n \<Rightarrow> ('n, 't) lacell list\<close> where
  \<open>la_fix G Shn = la_fix_gen G Shn (la_gtab G (lr0_states G Shn)) (lr0_states G Shn)\<close>

text \<open>The automaton is the expensive part of every table, so the code
  equation binds it once rather than building it for the goto table and
  again for the state list.\<close>

lemma la_fix_code [code]:
  \<open>la_fix G Shn = (let sts = lr0_states G Shn in la_fix_gen G Shn (la_gtab G sts) sts)\<close>
  by (simp add: la_fix_def Let_def)

abbreviation la_step0 :: \<open>('n, 't) is_cfg \<Rightarrow> 'n \<Rightarrow> ('n, 't) lacell list \<Rightarrow>
    ('n, 't) lacell list\<close> where
  \<open>la_step0 G Shn \<equiv> la_step G (ffix G) (nullables G)
     (la_gtab G (lr0_states G Shn)) (lr0_states G Shn)\<close>

theorem la_fix_stable:
  \<open>set (la_step0 G Shn (la_fix G Shn)) = set (la_fix G Shn)\<close>
  unfolding la_fix_def by (rule la_fix_gen_stable)

lemma la_fix_start: \<open>set (la_start G Shn (lr0_states G Shn)) \<subseteq> set (la_fix G Shn)\<close>
  unfolding la_fix_def by (rule la_fix_gen_start)

subsection \<open>The canonical conflict report\<close>

text \<open>Reduce lookahead comes from the canonical cells, the anchoring to the
  state's common reference column from \<^const>\<open>wreach\<close>, which carries the
  anchor relation through closure chains. \<^const>\<open>anch\<close> alone would widen
  every dot-0 item to \<^const>\<open>WAny\<close>, and \<^const>\<open>wdisjoint\<close> could never
  separate them. A completed cell whose item has several \<^const>\<open>wreach\<close>
  instances is tested against each; an item without one falls back to
  \<^const>\<open>anch\<close>.\<close>

text \<open>The test itself takes the state collection and its cell table as
  parameters, since it runs over two automata: the coarse one the machine
  builds, and the context-precise one of the next subsection.\<close>

text \<open>A report entry names the pair that fired: the completed item, the
  token both sides claim, and the two anchor relations \<^const>\<open>wdisjoint\<close>
  failed to separate.\<close>

datatype ('n, 't) lconf =
    ConfSR \<open>'n \<times> ('n, 't) rhs\<close> 't wrel wrel
  | ConfRR \<open>'n \<times> ('n, 't) rhs\<close> \<open>'n \<times> ('n, 't) rhs\<close> \<open>'t option\<close> wrel wrel

text \<open>Order of appearance in \<^const>\<open>iprods\<close>. A reduce/reduce pair is
  reported in one direction only, by dropping the one whose mirror the test
  keeps. Two productions the grammar does not list keep both directions
  rather than neither, so the reported pairs change but the report is empty
  iff the underlying pairwise test finds nothing.\<close>

definition pr_before :: \<open>('n, 't) is_cfg \<Rightarrow> 'n \<times> ('n, 't) rhs \<Rightarrow>
    'n \<times> ('n, 't) rhs \<Rightarrow> bool\<close> where
  \<open>pr_before G pr pr' = (pr \<in> set (takeWhile (\<lambda>q. q \<noteq> pr') (iprods G)))\<close>

text \<open>Which candidate \<^text>\<open>dcands\<close> lists first, hence the one the
  driver takes whenever both successors are live. The shift comes
  first as long as input remains, and a reported shift/reduce pair always
  carries a token, so \<^text>\<open>SideShift\<close> is exact. Reduce order follows the
  frame closure, and \<^const>\<open>xslots\<close> lists the kernel ahead of the dot-0
  slots: a completed item beats an \<^text>\<open>\<epsilon>\<close>-production, and two
  \<^text>\<open>\<epsilon>\<close>-productions go by their position in \<^const>\<open>iprods\<close>. Two
  completed kernel items are ordered by the frame the run built, which a
  static report cannot know.\<close>

datatype ('n, 't) lside =
    SideShift | SideReduce \<open>'n \<times> ('n, 't) rhs\<close> | SideFrame

fun conf_first :: \<open>('n, 't) is_cfg \<Rightarrow> ('n, 't) lconf \<Rightarrow> ('n, 't) lside\<close> where
  \<open>conf_first G (ConfSR pr a \<tau> \<tau>') = SideShift\<close>
| \<open>conf_first G (ConfRR pr pr' t \<tau> \<tau>') =
     (if snd pr \<noteq> [] \<and> snd pr' \<noteq> [] then SideFrame
      else if snd pr' = [] \<and> snd pr \<noteq> [] then SideReduce pr
      else if snd pr = [] \<and> snd pr' \<noteq> [] then SideReduce pr'
      else if pr_before G pr pr' then SideReduce pr
      else SideReduce pr')\<close>

definition lalr_confs_at :: \<open>('n, 't) is_cfg \<Rightarrow> 'n \<Rightarrow> ('n, 't) citem list list \<Rightarrow>
    ('n, 't) lacell list \<Rightarrow> nat \<Rightarrow> ('n, 't) lconf list\<close> where
  \<open>lalr_confs_at G Shn sts L i =
     (let ws = wreach G (sts ! i);
          reds = concat (map (\<lambda>(i', (pr, m), t, \<tau>).
              if i' = i \<and> m = length (snd pr) \<and> fst pr \<noteq> Shn
              then (case filter (\<lambda>(pr', m', \<rho>). pr' = pr \<and> m' = m) ws of
                      [] \<Rightarrow> [(pr, t, wcomp (winv (anch pr m)) \<tau>)]
                    | insts \<Rightarrow> map (\<lambda>(pr', m', \<rho>).
                        (pr, t, wcomp (winv \<rho>) \<tau>)) insts)
              else []) L);
          shifts = shift_cells ws
      in remdups
          (concat (map (\<lambda>(pr, t, \<tau>). case t of
              Some a \<Rightarrow> map (\<lambda>(a', \<tau>'). ConfSR pr a \<tau> \<tau>')
                (filter (\<lambda>(a', \<tau>'). a' = a \<and> \<not> wdisjoint \<tau> \<tau>') shifts)
            | None \<Rightarrow> []) reds)
         @ concat (map (\<lambda>(pr, t, \<tau>). map (\<lambda>(pr', t', \<tau>'). ConfRR pr pr' t \<tau> \<tau>')
              (filter (\<lambda>(pr', t', \<tau>'). pr' \<noteq> pr \<and> \<not> pr_before G pr' pr \<and> t' = t \<and>
                 (case t of Some _ \<Rightarrow> \<not> wdisjoint \<tau> \<tau>' | None \<Rightarrow> True)) reds))
              reds)))\<close>

definition lalr_conflict_at :: \<open>('n, 't) is_cfg \<Rightarrow> 'n \<Rightarrow> ('n, 't) citem list list \<Rightarrow>
    ('n, 't) lacell list \<Rightarrow> nat \<Rightarrow> bool\<close> where
  \<open>lalr_conflict_at G Shn sts L i = (lalr_confs_at G Shn sts L i \<noteq> [])\<close>

definition lalr_conflicts :: \<open>('n, 't) is_cfg \<Rightarrow> 'n \<Rightarrow> nat list\<close> where
  \<open>lalr_conflicts G Shn = (let sts = lr0_states G Shn in
     filter (lalr_conflict_at G Shn sts (la_fix G Shn)) [0..<length sts])\<close>

subsection \<open>The precise automaton\<close>

text \<open>\<^const>\<open>cclosure\<close> predicts every production in every state, so a
  goto carries, besides the advanced kernel, one item per production whose
  right-hand side starts with the goto symbol.  Two states then agree as soon
  as their kernels do, and the cell propagation pools contexts that no viable
  prefix shares.  The items of a declaration, a specification and a
  refinement meet in the state after a name, and the report cannot tell such
  a meeting from a conflict.

  The precise automaton rebuilds the states with \<^const>\<open>creach\<close> in place
  of \<^const>\<open>cclosure\<close>, giving the classical viable-prefix states;
  \<^text>\<open>LR_Det\<close> runs its rigid-point conflict analysis over them.
  Nothing on the parsing path changes: the machine keeps the coarse frames,
  whose \<^typ>\<open>indrep\<close>s prune per input what the precise automaton
  separates statically.  A pair the precise automaton keeps apart is one
  \<^text>\<open>dcands\<close> never offers together.\<close>

definition pr0_states :: \<open>('n, 't) is_cfg \<Rightarrow> 'n \<Rightarrow> ('n, 't) citem list list\<close> where
  \<open>pr0_states G Shn = wl_states G Shn (creach G)\<close>

definition pgtab :: \<open>('n, 't) is_cfg \<Rightarrow> ('n, 't) citem list list \<Rightarrow>
    (('n, 't) sym \<times> nat) list list\<close> where
  \<open>pgtab G sts = map (\<lambda>s. let cl = creach G s in
      map (\<lambda>X. (X, st_find sts (cgoto cl X)))
        (remdups (concat (map (\<lambda>(pr, m).
           if m < length (snd pr) then [fst (snd pr ! m)] else []) cl)))) sts\<close>

end
