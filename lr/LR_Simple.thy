theory LR_Simple
  imports LR_Det
begin

section \<open>A table-driven driver for grammars without layout annotations\<close>

text \<open>
  For a grammar whose relations are all \<^const>\<open>Any\<close> (\<^const>\<open>ii\<close>), the
  indentation sets of the set-anchored driver carry no information beyond
  whether they are empty: every set is empty or contains the start
  indentation. The live items of a frame are then those of a state of the
  precise automaton \<^const>\<open>pr0_states\<close>, and the driver's choices are read off
  the indices of the coarse and the precise state. This theory defines a
  driver over these two index stacks alone and proves that it computes the
  same result as \<^const>\<open>dparse\<close>.
\<close>

subsection \<open>Anchor sets are empty or contain the start indentation\<close>

definition anch_set :: \<open>nat \<Rightarrow> indrep \<Rightarrow> bool\<close> where
  \<open>anch_set i0 R \<longleftrightarrow> irep_set R = {} \<or> i0 \<in> irep_set R\<close>

definition anch_items :: \<open>nat \<Rightarrow> ('n, 't) xitem list \<Rightarrow> bool\<close> where
  \<open>anch_items i0 xs \<longleftrightarrow> (\<forall>(pr, m, R) \<in> set xs. anch_set i0 R)\<close>

text \<open>The relations in the productions of the items: \<^const>\<open>Any\<close>, or
  \<^const>\<open>Eq\<close> on a nonterminal (the start production).\<close>

definition rel_ok :: \<open>irel \<Rightarrow> ('n, 't) sym \<Rightarrow> bool\<close> where
  \<open>rel_ok r X \<longleftrightarrow> r = Any \<or> (r = Eq \<and> (\<exists>B. X = Nt B))\<close>

definition anns_ok :: \<open>('n, 't) xitem list \<Rightarrow> bool\<close> where
  \<open>anns_ok xs \<longleftrightarrow> (\<forall>(pr, m, R) \<in> set xs. \<forall>k < length (snd pr).
     rel_ok (snd (snd pr ! k)) (fst (snd pr ! k)))\<close>

lemma rel_okD: \<open>rel_ok r X \<Longrightarrow> r = Any \<or> r = Eq\<close>
  unfolding rel_ok_def by blast

lemma ii_rels:
  assumes \<open>ii G\<close> and \<open>pr \<in> set (iprods G)\<close> and \<open>k < length (snd pr)\<close>
  shows \<open>snd (snd pr ! k) = Any\<close>
  using assms unfolding ii_def by (cases pr) (auto simp: list_all_iff)

lemma anch_set_union:
  \<open>anch_set i0 R\<^sub>1 \<Longrightarrow> anch_set i0 R\<^sub>2 \<Longrightarrow> anch_set i0 (irep_union R\<^sub>1 R\<^sub>2)\<close>
  unfolding anch_set_def by auto

lemma anch_set_img:
  \<open>anch_set i0 R \<Longrightarrow> r = Any \<or> r = Eq \<Longrightarrow> anch_set i0 (irep_img r R)\<close>
  unfolding anch_set_def by (auto simp: irel_sat.simps)

lemma anch_set_fold_xcontrib:
  assumes \<open>anch_set i0 acc\<close>
    and \<open>\<And>A rhs m R. ((A, rhs), m, R) \<in> set items \<Longrightarrow>
            anch_set i0 R \<and> (\<forall>k < length rhs. snd (rhs ! k) = Any \<or> snd (rhs ! k) = Eq)\<close>
  shows \<open>anch_set i0 (fold (xcontrib pr) items acc)\<close>
  using assms
proof (induction items arbitrary: acc)
  case (Cons it items)
  obtain A rhs m R where it: \<open>it = ((A, rhs), m, R)\<close> by (cases it) auto
  have ok: \<open>anch_set i0 R\<close> \<open>\<forall>k < length rhs. snd (rhs ! k) = Any \<or> snd (rhs ! k) = Eq\<close>
    using Cons.prems(2)[of A rhs m R] it by auto
  have c: \<open>anch_set i0 (xcontrib pr it acc)\<close>
    using ok Cons.prems(1) unfolding it
    by (auto intro!: anch_set_union anch_set_img)
  have h: \<open>anch_set i0 R \<and> (\<forall>k < length rhs. snd (rhs ! k) = Any \<or> snd (rhs ! k) = Eq)\<close>
    if \<open>((A, rhs), m, R) \<in> set items\<close> for A rhs m R
    using Cons.prems(2)[of A rhs m R] that by simp
  show ?case using Cons.IH[OF c h] by simp
qed simp

lemma xiter_anch:
  assumes ii: \<open>ii G\<close> and kern: \<open>anch_items i0 xs\<close> and anns: \<open>anns_ok xs\<close>
  shows \<open>p < length (iprods G) \<Longrightarrow> anch_set i0 (xiter G xs t ! p)\<close>
proof (induction t arbitrary: p)
  case 0
  then show ?case by (simp add: anch_set_def)
next
  case (Suc t)
  have len: \<open>length (xiter G xs t) = length (iprods G)\<close> by simp
  show ?case
    unfolding xiter.simps xround_nth[OF len Suc.prems]
  proof (rule anch_set_fold_xcontrib)
    show \<open>anch_set i0 (xiter G xs t ! p)\<close> by (rule Suc.IH[OF Suc.prems])
  next
    fix A rhs m R assume mem: \<open>((A, rhs), m, R) \<in> set (xslots G xs (xiter G xs t))\<close>
    show \<open>anch_set i0 R \<and> (\<forall>k < length rhs. snd (rhs ! k) = Any \<or> snd (rhs ! k) = Eq)\<close>
      using mem
    proof (rule xslots_memE)
      assume mem: \<open>((A, rhs), m, R) \<in> set xs\<close>
      have \<open>anch_set i0 R\<close> using kern mem unfolding anch_items_def by fastforce
      moreover have \<open>\<forall>k < length rhs. snd (rhs ! k) = Any \<or> snd (rhs ! k) = Eq\<close>
        using anns mem rel_okD unfolding anns_ok_def by fastforce
      ultimately show ?thesis by blast
    next
      fix q assume q: \<open>q < length (iprods G)\<close> and \<open>q < length (xiter G xs t)\<close>
        and eq: \<open>((A, rhs), m, R) = (iprods G ! q, 0, xiter G xs t ! q)\<close>
      have pr: \<open>(A, rhs) \<in> set (iprods G)\<close> using q eq by (metis nth_mem prod.inject)
      have \<open>R = xiter G xs t ! q\<close> using eq by simp
      then have \<open>anch_set i0 R\<close> using Suc.IH[OF q] by simp
      moreover have \<open>\<forall>k < length rhs. snd (rhs ! k) = Any\<close>
        using ii_rels[OF ii pr] by simp
      ultimately show ?thesis by simp
    qed
  qed
qed

lemma xclosure_auto_anch:
  assumes ii: \<open>ii G\<close> and kern: \<open>anch_items i0 xs\<close> and anns: \<open>anns_ok xs\<close>
  shows \<open>anch_items i0 (xclosure_auto G xs)\<close>
  unfolding anch_items_def
proof (intro ballI, clarify)
  fix pr m R assume mem: \<open>(pr, m, R) \<in> set (xclosure_auto G xs)\<close>
  then have \<open>(pr, m, R) \<in> set (xslots G xs (xiter G xs (xfuel G xs)))\<close>
    unfolding xclosure_auto_def xclosure_def .
  then show \<open>anch_set i0 R\<close>
  proof (rule xslots_memE)
    assume \<open>(pr, m, R) \<in> set xs\<close>
    then show ?thesis using kern unfolding anch_items_def by fastforce
  next
    fix q assume q: \<open>q < length (iprods G)\<close> and \<open>q < length (xiter G xs (xfuel G xs))\<close>
      and \<open>(pr, m, R) = (iprods G ! q, 0, xiter G xs (xfuel G xs) ! q)\<close>
    then show ?thesis using xiter_anch[OF ii kern anns q] by simp
  qed
qed

lemma xclosure_auto_anns_mem:
  assumes ii: \<open>ii G\<close> and anns: \<open>anns_ok xs\<close>
    and mem: \<open>(pr, m, R) \<in> set (xclosure_auto G xs)\<close> and k: \<open>k < length (snd pr)\<close>
  shows \<open>rel_ok (snd (snd pr ! k)) (fst (snd pr ! k))\<close>
proof -
  have mem': \<open>(pr, m, R) \<in> set (xslots G xs (xiter G xs (xfuel G xs)))\<close>
    using mem unfolding xclosure_auto_def xclosure_def .
  show ?thesis
    using mem'
  proof (rule xslots_memE)
    assume \<open>(pr, m, R) \<in> set xs\<close>
    then show ?thesis using anns k unfolding anns_ok_def by fastforce
  next
    fix q assume q: \<open>q < length (iprods G)\<close> and \<open>q < length (xiter G xs (xfuel G xs))\<close>
      and eq: \<open>(pr, m, R) = (iprods G ! q, 0, xiter G xs (xfuel G xs) ! q)\<close>
    have \<open>pr \<in> set (iprods G)\<close> using q eq by simp
    then show ?thesis using ii_rels[OF ii _ k] by (simp add: rel_ok_def)
  qed
qed

lemma xclosure_auto_anns:
  assumes ii: \<open>ii G\<close> and anns: \<open>anns_ok xs\<close>
  shows \<open>anns_ok (xclosure_auto G xs)\<close>
  unfolding anns_ok_def using xclosure_auto_anns_mem[OF ii anns] by fast

subsection \<open>The live part of a closure is the reachable closure\<close>

lemma irep_img_nonempty: \<open>irep_set R \<noteq> {} \<Longrightarrow> irep_set (irep_img r R) \<noteq> {}\<close>
proof -
  assume \<open>irep_set R \<noteq> {}\<close>
  then obtain i where i: \<open>i \<in> irep_set R\<close> by blast
  have \<open>\<exists>j. irel_sat r j i\<close> by (cases r) (auto intro: exI[of _ \<open>Suc i\<close>] exI[of _ i])
  then show ?thesis using i by auto
qed

lemma creach_funpow_live:
  assumes stable: \<open>xstable G xs cls\<close> and len: \<open>length cls = length (iprods G)\<close>
    and kern: \<open>set s \<subseteq> lcore xs\<close>
  shows \<open>set ((creach_step G ^^ k) s) \<subseteq> lcore (xslots G xs cls)\<close>
proof (induction k)
  case 0
  have \<open>lcore xs \<subseteq> lcore (xslots G xs cls)\<close>
    unfolding lcore_def using xslots_kernel by fast
  then show ?case using kern by simp
next
  case (Suc k)
  let ?cs = \<open>(creach_step G ^^ k) s\<close>
  show ?case
  proof
    fix c assume \<open>c \<in> set ((creach_step G ^^ Suc k) s)\<close>
    then have \<open>c \<in> set (creach_step G ?cs)\<close> by simp
    then consider \<open>c \<in> set ?cs\<close>
      | pr pr' m' where \<open>c = (pr, 0)\<close> \<open>pr \<in> set (iprods G)\<close> \<open>(pr', m') \<in> set ?cs\<close>
          \<open>m' < length (snd pr')\<close> \<open>fst (snd pr' ! m') = Nt (fst pr)\<close>
      unfolding creach_step_set by blast
    then show \<open>c \<in> lcore (xslots G xs cls)\<close>
    proof cases
      case 1 then show ?thesis using Suc.IH by blast
    next
      case (2 pr pr' m')
      from 2(3) Suc.IH have \<open>(pr', m') \<in> lcore (xslots G xs cls)\<close> by blast
      then obtain R' where mem': \<open>(pr', m', R') \<in> set (xslots G xs cls)\<close>
        and ne: \<open>irep_nonempty R'\<close> unfolding lcore_def by blast
      from 2(2) obtain q where q: \<open>q < length (iprods G)\<close> and pq: \<open>iprods G ! q = pr\<close>
        by (metis in_set_conv_nth)
      obtain A rhs where pr': \<open>pr' = (A, rhs)\<close> by (cases pr')
      have img: \<open>ximg pr (pr', m', R') \<noteq> {}\<close>
        using 2(4,5) ne irep_img_nonempty[of R' \<open>snd (rhs ! m')\<close>]
        unfolding pr' by auto
      have \<open>ximg (iprods G ! q) (pr', m', R') \<subseteq> irep_set (xround G xs cls ! q)\<close>
        unfolding xround_nth[OF len q] fold_xcontrib_set using mem' by blast
      also have \<open>\<dots> \<subseteq> irep_set (cls ! q)\<close> by (rule xstableD[OF stable len q])
      finally have \<open>irep_nonempty (cls ! q)\<close> using img pq by auto
      moreover have \<open>(iprods G ! q, 0, cls ! q) \<in> set (xslots G xs cls)\<close>
        using xslots_slot[OF q] len q by simp
      ultimately show ?thesis unfolding 2(1) lcore_def pq[symmetric] by blast
    qed
  qed
qed

theorem lcore_xclosure_auto:
  assumes kern: \<open>lcore xs = set s\<close>
  shows \<open>lcore (xclosure_auto G xs) = set (creach G s)\<close>
proof
  show \<open>lcore (xclosure_auto G xs) \<subseteq> set (creach G s)\<close>
  proof
    fix c assume \<open>c \<in> lcore (xclosure_auto G xs)\<close>
    then obtain pr m R where c: \<open>c = (pr, m)\<close> and mem: \<open>(pr, m, R) \<in> set (xclosure_auto G xs)\<close>
      and ne: \<open>irep_nonempty R\<close> unfolding lcore_def by blast
    from ne obtain j where \<open>j \<in> irep_set R\<close> by auto
    have k: \<open>\<And>pr m R. (pr, m, R) \<in> set xs \<Longrightarrow> irep_nonempty R \<Longrightarrow> (pr, m) \<in> set s\<close>
      using kern unfolding lcore_def by blast
    from xclosure_auto_live_creach[OF k mem \<open>j \<in> _\<close>] show \<open>c \<in> set (creach G s)\<close> using c by simp
  qed
next
  show \<open>set (creach G s) \<subseteq> lcore (xclosure_auto G xs)\<close>
    unfolding creach_def xclosure_auto_def xclosure_def
    by (rule creach_funpow_live[OF xfuel_stable]) (use kern in simp_all)
qed


subsection \<open>The set-valued goto on live cores\<close>

text \<open>Through a position with relation \<^const>\<open>Any\<close> an item keeps its set; through
  \<^const>\<open>Eq\<close> (only the start production has it) it is intersected with the
  goto's set, which contains the start indentation.\<close>

definition goto_ok :: \<open>nat \<Rightarrow> ('n, 't) xitem list \<Rightarrow> ('n, 't) sym \<Rightarrow> indrep \<Rightarrow> bool\<close> where
  \<open>goto_ok i0 CL X RA \<longleftrightarrow> irep_nonempty RA \<and>
     (\<forall>(pr, m, R) \<in> set CL. m < length (snd pr) \<longrightarrow> fst (snd pr ! m) = X \<longrightarrow>
        snd (snd pr ! m) = Any \<or> (snd (snd pr ! m) = Eq \<and> i0 \<in> irep_set RA))\<close>

lemma goto_set:
  assumes ok: \<open>goto_ok i0 CL X RA\<close> and anch: \<open>anch_set i0 R\<close>
    and mem: \<open>(pr, m, R) \<in> set CL\<close> and m: \<open>m < length (snd pr)\<close> and X: \<open>fst (snd pr ! m) = X\<close>
  shows \<open>irep_set (irep_inter R (irep_pre (snd (snd pr ! m)) RA)) = {} \<longleftrightarrow> irep_set R = {}\<close>
    and \<open>anch_set i0 (irep_inter R (irep_pre (snd (snd pr ! m)) RA))\<close>
proof -
  have ne: \<open>irep_set RA \<noteq> {}\<close> using ok unfolding goto_ok_def by simp
  have r: \<open>snd (snd pr ! m) = Any \<or> (snd (snd pr ! m) = Eq \<and> i0 \<in> irep_set RA)\<close>
    using ok mem m X unfolding goto_ok_def by fastforce
  have pa: \<open>irep_set (irep_pre Any RA) = UNIV\<close> using ne by auto
  have pe: \<open>irep_set (irep_pre Eq RA) = irep_set RA\<close> by simp
  from r consider \<open>snd (snd pr ! m) = Any\<close> | \<open>snd (snd pr ! m) = Eq\<close> \<open>i0 \<in> irep_set RA\<close> by blast
  then have \<open>(irep_set (irep_inter R (irep_pre (snd (snd pr ! m)) RA)) = {} \<longleftrightarrow> irep_set R = {}) \<and>
      anch_set i0 (irep_inter R (irep_pre (snd (snd pr ! m)) RA))\<close>
  proof cases
    case 1 then show ?thesis using pa anch by (simp add: anch_set_def)
  next
    case 2 then show ?thesis using pe anch unfolding anch_set_def by auto
  qed
  then show \<open>irep_set (irep_inter R (irep_pre (snd (snd pr ! m)) RA)) = {} \<longleftrightarrow> irep_set R = {}\<close>
    and \<open>anch_set i0 (irep_inter R (irep_pre (snd (snd pr ! m)) RA))\<close> by blast+
qed

lemma set_cgoto:
  \<open>set (cgoto cs X) = {(pr, Suc m) | pr m. (pr, m) \<in> set cs \<and> m < length (snd pr) \<and> fst (snd pr ! m) = X}\<close>
  unfolding cgoto_def by force

theorem lcore_lgoto:
  assumes ok: \<open>goto_ok i0 CL X RA\<close> and anch: \<open>anch_items i0 CL\<close> and cs: \<open>lcore CL = set cs\<close>
  shows \<open>lcore (lgoto CL X RA) = set (cgoto cs X)\<close>
proof -
  have a: \<open>anch_set i0 R\<close> if \<open>(pr, m, R) \<in> set CL\<close> for pr m R
    using anch that unfolding anch_items_def by fastforce
  have \<open>lcore (lgoto CL X RA) =
      {(pr, Suc m) | pr m. (pr, m) \<in> lcore CL \<and> m < length (snd pr) \<and> fst (snd pr ! m) = X}\<close>
  proof (intro equalityI subsetI)
    fix c assume \<open>c \<in> lcore (lgoto CL X RA)\<close>
    then obtain pr m' R' where c: \<open>c = (pr, m')\<close> and mem: \<open>(pr, m', R') \<in> set (lgoto CL X RA)\<close>
      and ne: \<open>irep_nonempty R'\<close> unfolding lcore_def by blast
    from mem obtain m R where m': \<open>m' = Suc m\<close> and memCL: \<open>(pr, m, R) \<in> set CL\<close>
      and m: \<open>m < length (snd pr)\<close> and X: \<open>fst (snd pr ! m) = X\<close>
      and R': \<open>R' = irep_inter R (irep_pre (snd (snd pr ! m)) RA)\<close>
      unfolding lgoto_def by auto
    have \<open>irep_nonempty R\<close> using goto_set(1)[OF ok a[OF memCL] memCL m X] ne R' by auto
    then have \<open>(pr, m) \<in> lcore CL\<close> using memCL unfolding lcore_def by blast
    then show \<open>c \<in> {(pr, Suc m) | pr m. (pr, m) \<in> lcore CL \<and> m < length (snd pr) \<and> fst (snd pr ! m) = X}\<close>
      using c m' m X by blast
  next
    fix c assume \<open>c \<in> {(pr, Suc m) | pr m. (pr, m) \<in> lcore CL \<and> m < length (snd pr) \<and> fst (snd pr ! m) = X}\<close>
    then obtain pr m where c: \<open>c = (pr, Suc m)\<close> and l: \<open>(pr, m) \<in> lcore CL\<close>
      and m: \<open>m < length (snd pr)\<close> and X: \<open>fst (snd pr ! m) = X\<close> by blast
    from l obtain R where memCL: \<open>(pr, m, R) \<in> set CL\<close> and ne: \<open>irep_nonempty R\<close>
      unfolding lcore_def by blast
    have mem: \<open>(pr, Suc m, irep_inter R (irep_pre (snd (snd pr ! m)) RA)) \<in> set (lgoto CL X RA)\<close>
      by (rule lgoto_memI[OF memCL m X])
    have \<open>irep_nonempty (irep_inter R (irep_pre (snd (snd pr ! m)) RA))\<close>
      using goto_set(1)[OF ok a[OF memCL] memCL m X] ne by auto
    then show \<open>c \<in> lcore (lgoto CL X RA)\<close> using mem c unfolding lcore_def by blast
  qed
  also have \<open>\<dots> = set (cgoto cs X)\<close> unfolding set_cgoto cs by blast
  finally show ?thesis .
qed

lemma lgoto_anch:
  assumes ok: \<open>goto_ok i0 CL X RA\<close> and anch: \<open>anch_items i0 CL\<close>
  shows \<open>anch_items i0 (lgoto CL X RA)\<close>
  unfolding anch_items_def
proof (intro ballI, clarify)
  fix pr m' R' assume mem: \<open>(pr, m', R') \<in> set (lgoto CL X RA)\<close>
  from mem obtain m R where memCL: \<open>(pr, m, R) \<in> set CL\<close>
    and m: \<open>m < length (snd pr)\<close> and X: \<open>fst (snd pr ! m) = X\<close>
    and R': \<open>R' = irep_inter R (irep_pre (snd (snd pr ! m)) RA)\<close>
    unfolding lgoto_def by auto
  have \<open>anch_set i0 R\<close> using anch memCL unfolding anch_items_def by fastforce
  from goto_set(2)[OF ok this memCL m X] show \<open>anch_set i0 R'\<close> using R' by simp
qed

lemma lgoto_anns: \<open>anns_ok CL \<Longrightarrow> anns_ok (lgoto CL X RA)\<close>
  unfolding anns_ok_def lgoto_def by fastforce

text \<open>The two gotos of the driver meet \<^const>\<open>goto_ok\<close>: a terminal has
  relation \<^const>\<open>Any\<close> everywhere, and the set of a reduce contains the start
  indentation when it is not empty.\<close>

lemma goto_ok_Tm:
  \<open>anns_ok CL \<Longrightarrow> irep_nonempty RA \<Longrightarrow> goto_ok i0 CL (Tm a) RA\<close>
  unfolding goto_ok_def anns_ok_def rel_ok_def by fastforce

lemma goto_ok_Nt:
  \<open>anns_ok CL \<Longrightarrow> irep_nonempty RA \<Longrightarrow> i0 \<in> irep_set RA \<Longrightarrow> goto_ok i0 CL (Nt A) RA\<close>
  unfolding goto_ok_def anns_ok_def rel_ok_def by fastforce

lemma red_set_anch:
  assumes \<open>anch_items i0 CL\<close> and \<open>irep_nonempty (red_set CL pr)\<close>
  shows \<open>i0 \<in> irep_set (red_set CL pr)\<close>
proof -
  from assms(2) obtain R where mem: \<open>(pr, length (snd pr), R) \<in> set CL\<close> and ne: \<open>irep_nonempty R\<close>
    unfolding red_set_nonempty_iff by blast
  have \<open>anch_set i0 R\<close> using assms(1) mem unfolding anch_items_def by fastforce
  then have \<open>i0 \<in> irep_set R\<close> using ne unfolding anch_set_def by auto
  then show ?thesis unfolding red_set_correct using mem by blast
qed

subsection \<open>The precise goto table\<close>

lemma pgtab_lookup:
  assumes \<open>i < length sts\<close> and \<open>(pr, m) \<in> set (creach G (sts ! i))\<close> and \<open>m < length (snd pr)\<close>
  shows \<open>map_of (pgtab G sts ! i) (fst (snd pr ! m)) =
           Some (st_find sts (cgoto (creach G (sts ! i)) (fst (snd pr ! m))))\<close>
proof -
  let ?f = \<open>\<lambda>(pr, m). if m < length (snd pr) then [fst (snd pr ! m)] else []\<close>
  have h1: \<open>fst (snd pr ! m) \<in> set (?f (pr, m))\<close> using assms(3) by simp
  have mem: \<open>fst (snd pr ! m) \<in> set (concat (map ?f (creach G (sts ! i))))\<close>
    unfolding set_concat set_map using h1 assms(2) by blast
  show ?thesis unfolding pgtab_def using assms(1) mem
    by (simp add: Let_def map_of_map_pair)
qed

lemma pgtab_none:
  assumes \<open>i < length sts\<close>
    and \<open>\<And>pr m. (pr, m) \<in> set (creach G (sts ! i)) \<Longrightarrow> m < length (snd pr) \<Longrightarrow> fst (snd pr ! m) \<noteq> X\<close>
  shows \<open>map_of (pgtab G sts ! i) X = None\<close>
proof -
  let ?f = \<open>\<lambda>(pr, m). if m < length (snd pr) then [fst (snd pr ! m)] else []\<close>
  have \<open>X \<notin> set (concat (map ?f (creach G (sts ! i))))\<close>
  proof
    assume \<open>X \<in> set (concat (map ?f (creach G (sts ! i))))\<close>
    then obtain pr m where \<open>(pr, m) \<in> set (creach G (sts ! i))\<close> \<open>m < length (snd pr)\<close>
      \<open>fst (snd pr ! m) = X\<close> by (auto split: if_splits)
    with assms(2) show False by blast
  qed
  then show ?thesis unfolding pgtab_def using assms(1)
    by (simp add: Let_def map_of_map_pair)
qed

text \<open>The successor in the precise automaton, with the sentinel
  \<^term>\<open>length psts\<close> for a dead successor.\<close>

theorem pnext_resolve:
  assumes psts: \<open>psts = pr0_states G Shn\<close> and p: \<open>p < length psts\<close>
  shows \<open>dnext (pgtab G psts) psts p X < length psts \<longleftrightarrow> cgoto (creach G (psts ! p)) X \<noteq> []\<close>
    and \<open>dnext (pgtab G psts) psts p X < length psts \<Longrightarrow>
           set (psts ! dnext (pgtab G psts) psts p X) = set (cgoto (creach G (psts ! p)) X)\<close>
proof -
  let ?s = \<open>psts ! p\<close> and ?pgt = \<open>pgtab G psts\<close>
  have len: \<open>length ?pgt = length psts\<close> unfolding pgtab_def by simp
  have dn: \<open>dnext ?pgt psts p X = la_next ?pgt psts p X\<close> unfolding dnext_def using p len by simp
  have s_in: \<open>?s \<in> set psts\<close> using p by simp
  have univ: \<open>set ?s \<subseteq> cuniv G Shn\<close>
    by (rule pr0_states_univ) (use s_in psts in simp)
  have \<open>(dnext ?pgt psts p X < length psts \<longleftrightarrow> cgoto (creach G ?s) X \<noteq> []) \<and>
      (dnext ?pgt psts p X < length psts \<longrightarrow>
         set (psts ! dnext ?pgt psts p X) = set (cgoto (creach G ?s) X))\<close>
  proof (cases \<open>\<exists>pr m. (pr, m) \<in> set (creach G ?s) \<and> m < length (snd pr) \<and> fst (snd pr ! m) = X\<close>)
    case True
    then obtain pr m where mem: \<open>(pr, m) \<in> set (creach G ?s)\<close> and m: \<open>m < length (snd pr)\<close>
      and X: \<open>fst (snd pr ! m) = X\<close> by blast
    have \<open>(pr, m) \<in> cuniv G Shn\<close> using creach_univ[OF univ] mem by blast
    from cuniv_next_gram_syms[OF this m] have X_sym: \<open>X \<in> set (gram_syms G)\<close> using X by simp
    obtain t where t: \<open>t \<in> set psts\<close> and te: \<open>set t = set (cgoto (creach G ?s) X)\<close>
      using pr0_states_closed[OF s_in[unfolded psts] X_sym] unfolding psts by blast
    from st_find_found[OF t te] have
        sf_lt: \<open>st_find psts (cgoto (creach G ?s) X) < length psts\<close>
      and sf_set: \<open>set (psts ! st_find psts (cgoto (creach G ?s) X)) = set (cgoto (creach G ?s) X)\<close>
      by auto
    have look: \<open>map_of (?pgt ! p) X = Some (st_find psts (cgoto (creach G ?s) X))\<close>
      using pgtab_lookup[OF p mem m] X by simp
    have eq: \<open>dnext ?pgt psts p X = st_find psts (cgoto (creach G ?s) X)\<close>
      unfolding dn la_next_def look using sf_lt by simp
    have \<open>cgoto (creach G ?s) X \<noteq> []\<close>
      using cgoto_memI[OF mem m X] by auto
    then show ?thesis using eq sf_lt sf_set by simp
  next
    case False
    have none: \<open>map_of (?pgt ! p) X = None\<close>
      by (rule pgtab_none[OF p]) (use False in blast)
    have eq: \<open>dnext ?pgt psts p X = length psts\<close> unfolding dn la_next_def none by simp
    have f: \<open>filter (\<lambda>(pr, m). m < length (snd pr) \<and> fst (snd pr ! m) = X) (creach G ?s) = []\<close>
      unfolding filter_empty_conv using False by fast
    have \<open>cgoto (creach G ?s) X = []\<close> unfolding cgoto_def f by simp
    then show ?thesis using eq by simp
  qed
  then show \<open>dnext ?pgt psts p X < length psts \<longleftrightarrow> cgoto (creach G ?s) X \<noteq> []\<close>
    and \<open>dnext ?pgt psts p X < length psts \<Longrightarrow>
           set (psts ! dnext ?pgt psts p X) = set (cgoto (creach G ?s) X)\<close> by blast+
qed


subsection \<open>The simple driver\<close>

text \<open>Per precise state: the productions it completes, and whether it
  completes the start production.\<close>

definition pcomps :: \<open>('n, 't) is_cfg \<Rightarrow> ('n, 't) citem list list \<Rightarrow> ('n \<times> ('n, 't) rhs) list list\<close> where
  \<open>pcomps G psts = map (\<lambda>s. remdups (map fst (filter (\<lambda>(pr, m). m = length (snd pr)) (creach G s)))) psts\<close>

definition pfins :: \<open>'n \<Rightarrow> ('n, 't) citem list list \<Rightarrow> bool list\<close> where
  \<open>pfins Shn psts = map (\<lambda>s. list_ex (\<lambda>(pr, m). fst pr = Shn \<and> m = Suc 0) s) psts\<close>

text \<open>A reduce cell licenses the reduce by naming the next token (or the end of
  the input); the width relation is not consulted.\<close>

definition slic :: \<open>nat \<Rightarrow> ('n, 't) lacell list \<Rightarrow> ('m, 'ch, 't) tword \<Rightarrow> 'n \<times> ('n, 't) rhs \<Rightarrow> bool\<close> where
  \<open>slic i cells v pr \<longleftrightarrow> list_ex (\<lambda>(i', itm, t, \<tau>).
       i' = i \<and> itm = (pr, length (snd pr)) \<and>
       (case v of [] \<Rightarrow> t = None | x # _ \<Rightarrow> t = Some (tok x))) cells\<close>

definition scands :: \<open>('n \<times> ('n, 't) rhs) list \<Rightarrow> nat \<Rightarrow> ('n, 't) lacell list \<Rightarrow>
    ('m, 'ch, 't) tword \<Rightarrow> ('n, 't) dact list\<close> where
  \<open>scands comps i cells v = (let reds = map DReduce (filter (slic i cells v) comps)
     in (case v of [] \<Rightarrow> reds | _ \<Rightarrow> DShift # reds))\<close>

text \<open>The precise successor of an action, if it is live.\<close>

definition starget :: \<open>(('n, 't) sym \<times> nat) list list \<Rightarrow> ('n, 't) citem list list \<Rightarrow>
    (nat \<times> nat) list \<Rightarrow> ('m, 'ch, 't) tword \<Rightarrow> ('n, 't) dact \<Rightarrow> nat option\<close> where
  \<open>starget pgt psts stk v act = (case act of
      DShift \<Rightarrow> (case v of [] \<Rightarrow> None | x # _ \<Rightarrow>
        let q = dnext pgt psts (snd (hd stk)) (Tm (tok x)) in
        if q < length psts then Some q else None)
    | DReduce pr \<Rightarrow> (if length (snd pr) < length stk then
        let q = dnext pgt psts (snd (stk ! length (snd pr))) (Nt (fst pr)) in
        if q < length psts then Some q else None
      else None))\<close>

fun spick :: \<open>('a \<Rightarrow> 'b option) \<Rightarrow> 'a list \<Rightarrow> ('a \<times> 'b) option\<close> where
  \<open>spick f [] = None\<close>
| \<open>spick f (a # as) = (case f a of Some b \<Rightarrow> Some (a, b) | None \<Rightarrow> spick f as)\<close>

type_synonym ('m, 'ch, 't) sctl_t = \<open>(nat \<times> nat) list \<times> ('m, 'ch, 't) tword\<close>

type_synonym ('m, 'ch, 'n, 't) sst = \<open>(nat \<times> nat) list \<times> ('m, 'ch, 't) tword \<times> ('m, 'ch, 'n, 't) ast list\<close>

text \<open>The step on the control part (the stack of index pairs and the input).\<close>

definition sctl :: \<open>(('n, 't) sym \<times> nat) list list \<Rightarrow> ('n, 't) citem list list \<Rightarrow>
    ('n, 't) lacell list list \<Rightarrow> (('n, 't) sym \<times> nat) list list \<Rightarrow> ('n, 't) citem list list \<Rightarrow>
    ('n \<times> ('n, 't) rhs) list list \<Rightarrow> ('m, 'ch, 't) sctl_t \<Rightarrow>
    (('n, 't) dact \<times> ('m, 'ch, 't) sctl_t) option\<close> where
  \<open>sctl gt sts redtab pgt psts pc c = (case c of (stk, v) \<Rightarrow>
     (case stk of [] \<Rightarrow> None | (i, p) # _ \<Rightarrow>
       let cells = (if i < length redtab then redtab ! i else []);
           comps = (if p < length pc then pc ! p else [])
       in (case spick (starget pgt psts stk v) (scands comps i cells v) of
            None \<Rightarrow> None
          | Some (act, q) \<Rightarrow> Some (act, case act of
              DShift \<Rightarrow> ((dnext gt sts i (Tm (tok (hd v))), q) # stk, tl v)
            | DReduce pr \<Rightarrow> ((dnext gt sts (fst (stk ! length (snd pr))) (Nt (fst pr)), q)
                 # drop (length (snd pr)) stk, v)))))\<close>

definition stree :: \<open>('n, 't) dact \<Rightarrow> ('m, 'ch, 't) tword \<Rightarrow> ('m, 'ch, 'n, 't) ast list \<Rightarrow>
    ('m, 'ch, 'n, 't) ast list\<close> where
  \<open>stree act v tstk = (case act of
      DShift \<Rightarrow> Leaf (hd v) # tstk
    | DReduce pr \<Rightarrow> Node (fst pr) (rev (take (length (snd pr)) tstk)) # drop (length (snd pr)) tstk)\<close>

definition sstep :: \<open>(('n, 't) sym \<times> nat) list list \<Rightarrow> ('n, 't) citem list list \<Rightarrow>
    ('n, 't) lacell list list \<Rightarrow> (('n, 't) sym \<times> nat) list list \<Rightarrow> ('n, 't) citem list list \<Rightarrow>
    ('n \<times> ('n, 't) rhs) list list \<Rightarrow> ('m, 'ch, 'n, 't) sst \<Rightarrow> ('m, 'ch, 'n, 't) sst option\<close> where
  \<open>sstep gt sts redtab pgt psts pc st = (case st of (stk, v, tstk) \<Rightarrow>
     map_option (\<lambda>(act, stk', v'). (stk', v', stree act v tstk))
       (sctl gt sts redtab pgt psts pc (stk, v)))\<close>

definition sfinal :: \<open>bool list \<Rightarrow> ('m, 'ch, 't) sctl_t \<Rightarrow> bool\<close> where
  \<open>sfinal pf c \<longleftrightarrow> (case c of (stk, v) \<Rightarrow> v = [] \<and> stk \<noteq> [] \<and>
     snd (hd stk) < length pf \<and> pf ! snd (hd stk))\<close>

definition sresult :: \<open>('m, 'ch, 'n, 't) ast list \<Rightarrow> ('m, 'ch, 'n, 't) ast option\<close> where
  \<open>sresult tstk = (case tstk of t # _ \<Rightarrow> Some t | [] \<Rightarrow> None)\<close>

fun srun :: \<open>(('n, 't) sym \<times> nat) list list \<Rightarrow> ('n, 't) citem list list \<Rightarrow>
    ('n, 't) lacell list list \<Rightarrow> (('n, 't) sym \<times> nat) list list \<Rightarrow> ('n, 't) citem list list \<Rightarrow>
    ('n \<times> ('n, 't) rhs) list list \<Rightarrow> bool list \<Rightarrow> nat \<Rightarrow> ('m, 'ch, 'n, 't) sst \<Rightarrow>
    ('m, 'ch, 'n, 't) ast option\<close> where
  \<open>srun gt sts redtab pgt psts pc pf 0 st = (case st of (stk, v, tstk) \<Rightarrow>
     if sfinal pf (stk, v) then sresult tstk else None)\<close>
| \<open>srun gt sts redtab pgt psts pc pf (Suc n) st = (case st of (stk, v, tstk) \<Rightarrow>
     if sfinal pf (stk, v) then sresult tstk
     else (case sstep gt sts redtab pgt psts pc st of
             None \<Rightarrow> None
           | Some st' \<Rightarrow> srun gt sts redtab pgt psts pc pf n st'))\<close>

partial_function (option) srun\<^sub>w\<^sub>f ::
  \<open>(('n, 't) sym \<times> nat) list list \<Rightarrow> ('n, 't) citem list list \<Rightarrow>
    ('n, 't) lacell list list \<Rightarrow> (('n, 't) sym \<times> nat) list list \<Rightarrow> ('n, 't) citem list list \<Rightarrow>
    ('n \<times> ('n, 't) rhs) list list \<Rightarrow> bool list \<Rightarrow> ('m, 'ch, 'n, 't) sst \<Rightarrow>
    ('m, 'ch, 'n, 't) ast option\<close>
  where
  \<open>srun\<^sub>w\<^sub>f gt sts redtab pgt psts pc pf st = (case st of (stk, v, tstk) \<Rightarrow>
     if sfinal pf (stk, v) then sresult tstk
     else Option.bind (sstep gt sts redtab pgt psts pc st) (srun\<^sub>w\<^sub>f gt sts redtab pgt psts pc pf))\<close>

text \<open>The run with a history of the stacks since the last shift.\<close>

partial_function (option) srun_hist ::
  \<open>(('n, 't) sym \<times> nat) list list \<Rightarrow> ('n, 't) citem list list \<Rightarrow>
    ('n, 't) lacell list list \<Rightarrow> (('n, 't) sym \<times> nat) list list \<Rightarrow> ('n, 't) citem list list \<Rightarrow>
    ('n \<times> ('n, 't) rhs) list list \<Rightarrow> bool list \<Rightarrow> (nat \<times> nat) list list \<Rightarrow>
    ('m, 'ch, 'n, 't) sst \<Rightarrow> ('m, 'ch, 'n, 't) ast option\<close>
  where
  \<open>srun_hist gt sts redtab pgt psts pc pf seen st = (case st of (stk, v, tstk) \<Rightarrow>
     if sfinal pf (stk, v) then sresult tstk
     else if stk \<in> set seen then None
     else Option.bind (sctl gt sts redtab pgt psts pc (stk, v)) (\<lambda>(act, stk', v').
       srun_hist gt sts redtab pgt psts pc pf (if act = DShift then [] else stk # seen)
         (stk', v', stree act v tstk)))\<close>

lemmas srun_hist_simps [code] = srun_hist.simps

definition sinit :: \<open>('n, 't) is_cfg \<Rightarrow> 'n \<Rightarrow> ('n, 't) citem list list \<Rightarrow> ('n, 't) citem list list \<Rightarrow>
    ('m, 'ch, 't) tword \<Rightarrow> ('m, 'ch, 'n, 't) sst\<close> where
  \<open>sinit G Shn sts psts w = ([(st_find sts (lr0_start G Shn), st_find psts (lr0_start G Shn))], w, [])\<close>

definition sparse :: \<open>('n, 't) is_cfg \<Rightarrow> 'n \<Rightarrow> ('m, 'ch, 't) tword \<Rightarrow> ('m, 'ch, 'n, 't) ast option\<close> where
  \<open>sparse G Shn w = (let sts = lr0_states G Shn; gt = la_gtab G sts;
       redtab = red_buckets G Shn (length sts); psts = pr0_states G Shn; pgt = pgtab G psts
     in srun\<^sub>w\<^sub>f gt sts redtab pgt psts (pcomps G psts) (pfins Shn psts) (sinit G Shn sts psts w))\<close>


subsection \<open>The simulation relation\<close>

text \<open>The static conditions: no layout annotations, operational determinism,
  and reduce cells naming a token carry no width constraint.\<close>

definition wany_ok :: \<open>('n, 't) lacell list list \<Rightarrow> bool\<close> where
  \<open>wany_ok redtab \<longleftrightarrow> list_all (list_all (\<lambda>(i, itm, t, \<tau>). t = None \<or> \<tau> = WAny)) redtab\<close>

definition sstatic :: \<open>('n, 't) is_cfg \<Rightarrow> 'n \<Rightarrow> bool\<close> where
  \<open>sstatic G Shn \<longleftrightarrow> ii G \<and> mdet G Shn \<and>
     wany_ok (red_buckets G Shn (length (lr0_states G Shn)))\<close>

lemma sstaticI:
  \<open>ii G \<Longrightarrow> rlalr_conflicts G Shn = [] \<Longrightarrow> fresh_name G Shn \<Longrightarrow>
     wany_ok (red_buckets G Shn (length (lr0_states G Shn))) \<Longrightarrow> sstatic G Shn\<close>
  unfolding sstatic_def using rlalr_sufficient[of G Shn] by (intro conjI) simp_all

lemma wany_okD:
  \<open>wany_ok redtab \<Longrightarrow> i < length redtab \<Longrightarrow> (i', itm, t, \<tau>) \<in> set (redtab ! i) \<Longrightarrow>
     t \<noteq> None \<Longrightarrow> \<tau> = WAny\<close>
  unfolding wany_ok_def list_all_iff by (fastforce dest: nth_mem)

definition sctrl :: \<open>('m, 'ch, 'n, 't) sst \<Rightarrow> ('m, 'ch, 't) sctl_t\<close> where
  \<open>sctrl ss = (case ss of (stk, v, tstk) \<Rightarrow> (stk, v))\<close>

definition ssim :: \<open>('n, 't) is_cfg \<Rightarrow> 'n \<Rightarrow> ('n, 't) citem list list \<Rightarrow>
    ('m, 'ch, 'n, 't) dst \<Rightarrow> ('m, 'ch, 'n, 't) sst \<Rightarrow> bool\<close> where
  \<open>ssim G Shn psts st ss \<longleftrightarrow> (case st of ((Xs, w), cstk, istk, v, tstk) \<Rightarrow>
     case ss of (stk, v', tstk') \<Rightarrow>
       v' = v \<and> tstk' = tstk \<and> w = tcols v \<and> Xs \<noteq> [] \<and> istk = map fst stk \<and>
       cstk_ok G Xs cstk \<and> didx_ok G (lr0_states G Shn) Xs istk \<and>
       (\<forall>k < length Xs. snd (stk ! k) < length psts \<and> set (psts ! snd (stk ! k)) = lcore (Xs ! k)) \<and>
       (\<forall>X \<in> set Xs. anch_items (istart_ind G) X \<and> anns_ok X) \<and>
       mreach G Shn (Xs, w))\<close>

lemma live_lcore: \<open>live xs \<longleftrightarrow> lcore xs \<noteq> {}\<close>
  unfolding live_def lcore_def list_ex_iff by fastforce

lemma dlive_lcore: \<open>dlive (X # Xs, w) \<longleftrightarrow> lcore X \<noteq> {}\<close>
  unfolding dlive_def by (simp add: live_lcore)

lemma lcore_xinit: \<open>lcore (xinit G Shn) = set (lr0_start G Shn)\<close>
  unfolding lcore_def xinit_def lr0_start_def start_prod_def by auto

lemma ssim_init:
  assumes psts: \<open>psts = pr0_states G Shn\<close>
  shows \<open>ssim G Shn psts (dinit G Shn (lr0_states G Shn) w) (sinit G Shn (lr0_states G Shn) psts w)\<close>
proof -
  obtain t where t: \<open>t \<in> set psts\<close> and te: \<open>set t = set (ccore (xinit G Shn))\<close>
    using pr0_states_start[of G Shn] psts by blast
  from st_find_found[OF t te[unfolded ccore_xinit]]
  have lt: \<open>st_find psts (lr0_start G Shn) < length psts\<close>
    and eq: \<open>set (psts ! st_find psts (lr0_start G Shn)) = set (lr0_start G Shn)\<close> by auto
  have anch: \<open>anch_items (istart_ind G) (xinit G Shn)\<close>
    unfolding anch_items_def anch_set_def xinit_def by simp
  have anns: \<open>anns_ok (xinit G Shn)\<close>
    unfolding anns_ok_def rel_ok_def xinit_def by simp
  show ?thesis
    unfolding ssim_def dinit_def sinit_def
    using lt eq anch anns didx_ok_init[of G Shn] mreach_init[of G Shn]
    by (simp add: cstk_ok_def lcore_xinit)
qed

lemma ssim_len:
  \<open>ssim G Shn psts ((Xs, w), cstk, istk, v, tstk) (stk, v', tstk') \<Longrightarrow> length stk = length Xs\<close>
  unfolding ssim_def using didx_ok_len by fastforce

lemma ssim_final:
  assumes sim: \<open>ssim G Shn psts ((Xs, w), cstk, istk, v, tstk) (stk, v', tstk')\<close>
  shows \<open>gfinal G Shn (Xs, w) \<longleftrightarrow> sfinal (pfins Shn psts) (stk, v')\<close>
proof -
  from sim have v: \<open>v' = v\<close> \<open>w = tcols v\<close> and ne: \<open>Xs \<noteq> []\<close>
    and p: \<open>snd (stk ! 0) < length psts\<close> \<open>set (psts ! snd (stk ! 0)) = lcore (Xs ! 0)\<close>
    and anch: \<open>anch_items (istart_ind G) (hd Xs)\<close>
    unfolding ssim_def by auto
  have len: \<open>length stk = length Xs\<close> using ssim_len[OF sim] .
  then have stk_ne: \<open>stk \<noteq> []\<close> using ne by auto
  then have hd: \<open>hd stk = stk ! 0\<close> by (simp add: hd_conv_nth)
  have hdX: \<open>hd Xs = Xs ! 0\<close> using ne by (simp add: hd_conv_nth)
  have i0: \<open>\<And>pr m R. (pr, m, R) \<in> set (hd Xs) \<Longrightarrow> irep_mem (istart_ind G) R \<longleftrightarrow> irep_nonempty R\<close>
    using anch unfolding anch_items_def anch_set_def by fastforce
  have \<open>list_ex (\<lambda>(pr, m, R). fst pr = Shn \<and> m = Suc 0 \<and> irep_mem (istart_ind G) R) (hd Xs) \<longleftrightarrow>
        (\<exists>(pr, m) \<in> lcore (hd Xs). fst pr = Shn \<and> m = Suc 0)\<close>
    unfolding list_ex_iff lcore_def using i0 by fastforce
  also have \<open>\<dots> \<longleftrightarrow> pfins Shn psts ! snd (hd stk)\<close>
    unfolding pfins_def using p hd hdX by (auto simp: list_ex_iff)
  moreover have \<open>w = [] \<longleftrightarrow> v' = []\<close> using v by (simp add: tcols_def)
  ultimately show ?thesis
    unfolding gfinal_def sfinal_def using ne stk_ne p hd by (auto simp: pfins_def)
qed

lemma pcomps_mem:
  \<open>p < length psts \<Longrightarrow>
     pr \<in> set (pcomps G psts ! p) \<longleftrightarrow> (pr, length (snd pr)) \<in> set (creach G (psts ! p))\<close>
  unfolding pcomps_def by force

lemma slic_dlic:
  assumes c: \<open>\<And>i' itm t \<tau>. (i', itm, t, \<tau>) \<in> set cells \<Longrightarrow> t \<noteq> None \<Longrightarrow> \<tau> = WAny\<close>
    and ne: \<open>irep_nonempty RS\<close>
  shows \<open>dlic i cells (tcols v) pr RS \<longleftrightarrow> slic i cells v pr\<close>
proof -
  show ?thesis
  proof (cases v)
    case Nil
    then show ?thesis unfolding dlic_def slic_def by simp
  next
    case (Cons x v')
    have \<open>\<And>i' itm t \<tau>. (i', itm, t, \<tau>) \<in> set cells \<Longrightarrow> t = Some (tok x) \<Longrightarrow>
        irep_ex_wsat \<tau> (s_col (span x)) RS\<close>
      using c ne by fastforce
    then show ?thesis unfolding dlic_def slic_def Cons list_ex_iff by fastforce
  qed
qed


subsection \<open>Candidates and picks\<close>

lemma cstk_ok_map: \<open>cstk_ok G Xs cstk \<longleftrightarrow> cstk = map (xclosure_auto G) Xs\<close>
  unfolding cstk_ok_def by (induction Xs arbitrary: cstk) (auto simp: list_all2_Cons1)

lemma dpick_NoneD:
  \<open>dpick G cstk gc acts = None \<Longrightarrow> a \<in> set acts \<Longrightarrow> mstep_cached G cstk gc a = Some gc' \<Longrightarrow>
     \<not> dlive gc'\<close>
  by (induction acts) (auto split: option.splits if_splits)

lemma spick_SomeD: \<open>spick f xs = Some (a, b) \<Longrightarrow> a \<in> set xs \<and> f a = Some b\<close>
  by (induction xs) (auto split: option.splits)

lemma spick_None_iff: \<open>spick f xs = None \<longleftrightarrow> (\<forall>a \<in> set xs. f a = None)\<close>
  by (induction xs) (auto split: option.splits)

lemma dcands_mem:
  assumes \<open>Xs \<noteq> []\<close>
  shows \<open>act \<in> set (dcands G i cells CL (Xs, w)) \<longleftrightarrow> (case act of
      DShift \<Rightarrow> w \<noteq> []
    | DReduce pr \<Rightarrow> irep_nonempty (red_set CL pr) \<and> dlic i cells w pr (red_set CL pr))\<close>
proof -
  have comp: \<open>pr \<in> set (remdups (map fst (filter (\<lambda>(pr, m, R). m = length (snd pr)) CL)))\<close>
    if \<open>irep_nonempty (red_set CL pr)\<close> for pr
  proof -
    from that obtain R where \<open>(pr, length (snd pr), R) \<in> set CL\<close>
      unfolding red_set_nonempty_iff by blast
    then show ?thesis by force
  qed
  show ?thesis
    using assms comp unfolding dcands_def
    by (cases act; cases w) (auto simp: Let_def)
qed

lemma scands_mem:
  \<open>act \<in> set (scands comps i cells v) \<longleftrightarrow> (case act of
      DShift \<Rightarrow> v \<noteq> []
    | DReduce pr \<Rightarrow> pr \<in> set comps \<and> slic i cells v pr)\<close>
  unfolding scands_def by (cases act; cases v) auto


subsection \<open>One step\<close>

context
  fixes G :: \<open>('n, 't) is_cfg\<close> and Shn :: 'n
    and sts :: \<open>('n, 't) citem list list\<close> and gt :: \<open>(('n, 't) sym \<times> nat) list list\<close>
    and redtab :: \<open>('n, 't) lacell list list\<close> and psts :: \<open>('n, 't) citem list list\<close>
    and pgt :: \<open>(('n, 't) sym \<times> nat) list list\<close> and pc :: \<open>('n \<times> ('n, 't) rhs) list list\<close>
  assumes static: \<open>sstatic G Shn\<close>
    and sts: \<open>sts = lr0_states G Shn\<close> and gt: \<open>gt = la_gtab G sts\<close>
    and redtab: \<open>redtab = red_buckets G Shn (length sts)\<close>
    and psts: \<open>psts = pr0_states G Shn\<close> and pgt: \<open>pgt = pgtab G psts\<close>
    and pc: \<open>pc = pcomps G psts\<close>
begin

lemma tabs: \<open>tables_ok G Shn sts gt (la_fix G Shn)\<close>
  using tables_ok_concrete[of G Shn] unfolding sts gt .

lemma ii: \<open>ii G\<close> and det: \<open>mdet G Shn\<close>
  and wany: \<open>wany_ok (red_buckets G Shn (length sts))\<close>
  using static unfolding sstatic_def sts by blast+

context
  fixes Xs :: \<open>('n, 't) xitem list list\<close> and w cstk istk
    and v :: \<open>('m, 'ch, 't) tword\<close> and tstk :: \<open>('m, 'ch, 'n, 't) ast list\<close> and stk i p
  assumes sim: \<open>ssim G Shn psts ((Xs, w), cstk, istk, v, tstk) (stk, v, tstk)\<close>
    and hd_stk: \<open>hd stk = (i, p)\<close>
begin

lemma c_ne: \<open>Xs \<noteq> []\<close> and c_w: \<open>w = tcols v\<close> and c_istk: \<open>istk = map fst stk\<close>
  and c_cstk: \<open>cstk = map (xclosure_auto G) Xs\<close>
  and c_didx: \<open>didx_ok G sts Xs istk\<close>
  and c_reach: \<open>mreach G Shn (Xs, w)\<close>
  using sim unfolding ssim_def sts cstk_ok_map by auto

lemma c_prec: \<open>k < length Xs \<Longrightarrow> snd (stk ! k) < length psts \<and> set (psts ! snd (stk ! k)) = lcore (Xs ! k)\<close>
  using sim unfolding ssim_def by auto

lemma c_frames: \<open>X \<in> set Xs \<Longrightarrow> anch_items (istart_ind G) X \<and> anns_ok X\<close>
  using sim unfolding ssim_def by auto

lemma c_len: \<open>length stk = length Xs\<close>
  using ssim_len[OF sim] .

lemma c_hd0: \<open>stk ! 0 = (i, p)\<close> and c_hdX: \<open>hd Xs = Xs ! 0\<close>
  using c_len c_ne hd_stk by (cases stk; cases Xs; simp)+

lemma c_istk_case: \<open>(case istk of [] \<Rightarrow> length sts | j # _ \<Rightarrow> j) = i\<close>
  using c_istk c_len c_ne hd_stk by (cases stk) auto

lemma c_cstk_case: \<open>(case cstk of [] \<Rightarrow> [] | c # _ \<Rightarrow> c) = xclosure_auto G (hd Xs)\<close>
  using c_cstk c_ne by (cases Xs) auto

lemma c_istk0: \<open>istk ! 0 = i\<close>
  using c_istk c_len c_ne c_hd0 by simp

lemma c_i_lt: \<open>i < length sts\<close>
  using didx_okD[OF c_didx, of 0] c_ne c_istk0 by simp

lemma c_p_lt: \<open>p < length psts\<close>
  using c_prec[of 0] c_ne c_hd0 by simp

lemma c_cells: \<open>(if i < length redtab then redtab ! i else []) = red_buckets G Shn (length sts) ! i\<close>
  using c_i_lt unfolding redtab by simp

lemma c_comps: \<open>(if p < length pc then pc ! p else []) = pcomps G psts ! p\<close>
  using c_p_lt unfolding pc pcomps_def by simp

lemma c_frame_cl:
  assumes \<open>k < length Xs\<close>
  shows \<open>lcore (xclosure_auto G (Xs ! k)) = set (creach G (psts ! snd (stk ! k)))\<close>
    and \<open>anch_items (istart_ind G) (xclosure_auto G (Xs ! k))\<close>
    and \<open>anns_ok (xclosure_auto G (Xs ! k))\<close>
proof -
  have f: \<open>anch_items (istart_ind G) (Xs ! k) \<and> anns_ok (Xs ! k)\<close>
    using c_frames assms by simp
  show \<open>lcore (xclosure_auto G (Xs ! k)) = set (creach G (psts ! snd (stk ! k)))\<close>
    by (rule lcore_xclosure_auto) (use c_prec[OF assms] in simp)
  show \<open>anch_items (istart_ind G) (xclosure_auto G (Xs ! k))\<close>
    using xclosure_auto_anch[OF ii] f by blast
  show \<open>anns_ok (xclosure_auto G (Xs ! k))\<close>
    using xclosure_auto_anns[OF ii] f by blast
qed

lemma c_CL:
  \<open>lcore (xclosure_auto G (hd Xs)) = set (creach G (psts ! p))\<close>
  \<open>anch_items (istart_ind G) (xclosure_auto G (hd Xs))\<close>
  \<open>anns_ok (xclosure_auto G (hd Xs))\<close>
  using c_frame_cl[of 0] c_ne c_hd0 c_hdX by simp_all

lemma c_red_comps:
  \<open>irep_nonempty (red_set (xclosure_auto G (hd Xs)) pr) \<longleftrightarrow> pr \<in> set (pcomps G psts ! p)\<close>
  unfolding pcomps_mem[OF c_p_lt] c_CL(1)[symmetric] red_set_nonempty_iff lcore_def by blast

lemma c_shift:
  assumes v: \<open>v = x # v'\<close>
  shows \<open>mstep G (Xs, w) DShift =
      Some (lgoto (xclosure_auto G (hd Xs)) (Tm (tok x)) (FinRep [s_col (span x)]) # Xs, tcols v')\<close>
    and \<open>lcore (lgoto (xclosure_auto G (hd Xs)) (Tm (tok x)) (FinRep [s_col (span x)])) =
      set (cgoto (creach G (psts ! p)) (Tm (tok x)))\<close>
proof -
  show \<open>mstep G (Xs, w) DShift =
      Some (lgoto (xclosure_auto G (hd Xs)) (Tm (tok x)) (FinRep [s_col (span x)]) # Xs, tcols v')\<close>
    unfolding mstep_def mstep_cached_def using c_ne by (simp add: c_w v hd_map)
  show \<open>lcore (lgoto (xclosure_auto G (hd Xs)) (Tm (tok x)) (FinRep [s_col (span x)])) =
      set (cgoto (creach G (psts ! p)) (Tm (tok x)))\<close>
    by (rule lcore_lgoto[OF goto_ok_Tm[OF c_CL(3)] c_CL(2) c_CL(1)]) simp
qed

lemma c_reduce:
  assumes n: \<open>length (snd pr) < length Xs\<close>
    and RS: \<open>irep_nonempty (red_set (xclosure_auto G (hd Xs)) pr)\<close>
  shows \<open>mstep G (Xs, w) (DReduce pr) =
      Some (lgoto (xclosure_auto G (Xs ! length (snd pr))) (Nt (fst pr))
              (red_set (xclosure_auto G (hd Xs)) pr) # drop (length (snd pr)) Xs, w)\<close>
    and \<open>lcore (lgoto (xclosure_auto G (Xs ! length (snd pr))) (Nt (fst pr))
              (red_set (xclosure_auto G (hd Xs)) pr)) =
      set (cgoto (creach G (psts ! snd (stk ! length (snd pr)))) (Nt (fst pr)))\<close>
proof -
  show \<open>mstep G (Xs, w) (DReduce pr) =
      Some (lgoto (xclosure_auto G (Xs ! length (snd pr))) (Nt (fst pr))
              (red_set (xclosure_auto G (hd Xs)) pr) # drop (length (snd pr)) Xs, w)\<close>
    unfolding mstep_def mstep_cached_def using c_ne n RS by (simp add: Let_def hd_map)
  have ok: \<open>goto_ok (istart_ind G) (xclosure_auto G (Xs ! length (snd pr))) (Nt (fst pr))
      (red_set (xclosure_auto G (hd Xs)) pr)\<close>
    by (rule goto_ok_Nt[OF c_frame_cl(3)[OF n] RS red_set_anch[OF c_CL(2) RS]])
  show \<open>lcore (lgoto (xclosure_auto G (Xs ! length (snd pr))) (Nt (fst pr))
              (red_set (xclosure_auto G (hd Xs)) pr)) =
      set (cgoto (creach G (psts ! snd (stk ! length (snd pr)))) (Nt (fst pr)))\<close>
    by (rule lcore_lgoto[OF ok c_frame_cl(2)[OF n] c_frame_cl(1)[OF n]])
qed

lemma c_act_iff:
  \<open>(act \<in> set (dcands G i (red_buckets G Shn (length sts) ! i) (xclosure_auto G (hd Xs)) (Xs, w)) \<and>
     (\<exists>gc'. mstep G (Xs, w) act = Some gc' \<and> dlive gc')) \<longleftrightarrow>
   (act \<in> set (scands (pcomps G psts ! p) i (red_buckets G Shn (length sts) ! i) v) \<and>
     starget pgt psts stk v act \<noteq> None)\<close>
proof (cases act)
  case DShift
  show ?thesis
  proof (cases v)
    case Nil
    then show ?thesis unfolding DShift dcands_mem[OF c_ne] scands_mem using c_w by simp
  next
    case (Cons x v')
    have pr: \<open>dnext pgt psts p (Tm (tok x)) < length psts \<longleftrightarrow>
        cgoto (creach G (psts ! p)) (Tm (tok x)) \<noteq> []\<close>
      using pnext_resolve(1)[OF psts c_p_lt] unfolding pgt .
    show ?thesis unfolding DShift dcands_mem[OF c_ne] scands_mem c_shift(1)[OF Cons]
      using pr c_shift(2)[OF Cons] c_w Cons hd_stk by (simp add: dlive_lcore starget_def Let_def)
  qed
next
  case (DReduce pr)
  show ?thesis
  proof (cases \<open>irep_nonempty (red_set (xclosure_auto G (hd Xs)) pr)\<close>)
    case False
    then show ?thesis unfolding DReduce dcands_mem[OF c_ne] scands_mem c_red_comps by simp
  next
    case RS: True
    have lic: \<open>dlic i (red_buckets G Shn (length sts) ! i) w pr (red_set (xclosure_auto G (hd Xs)) pr)
        \<longleftrightarrow> slic i (red_buckets G Shn (length sts) ! i) v pr\<close>
      unfolding c_w
      by (rule slic_dlic[OF wany_okD[OF wany] RS]) (use c_i_lt in simp_all)
    show ?thesis
    proof (cases \<open>length (snd pr) < length Xs\<close>)
      case False
      then have \<open>mstep G (Xs, w) (DReduce pr) = None\<close>
        unfolding mstep_def mstep_cached_def by simp
      moreover have \<open>starget pgt psts stk v (DReduce pr) = None\<close>
        using False c_len unfolding starget_def by simp
      ultimately show ?thesis unfolding DReduce by simp
    next
      case n: True
      have q_lt: \<open>snd (stk ! length (snd pr)) < length psts\<close> using c_prec[OF n] by simp
      have pr': \<open>dnext pgt psts (snd (stk ! length (snd pr))) (Nt (fst pr)) < length psts \<longleftrightarrow>
          cgoto (creach G (psts ! snd (stk ! length (snd pr)))) (Nt (fst pr)) \<noteq> []\<close>
        using pnext_resolve(1)[OF psts q_lt] unfolding pgt .
      show ?thesis unfolding DReduce dcands_mem[OF c_ne] scands_mem c_reduce(1)[OF n RS]
        using RS lic pr' c_reduce(2)[OF n RS] n c_len c_red_comps
        by (simp add: dlive_lcore starget_def Let_def)
    qed
  qed
qed

lemma lcore_Nil_ne: \<open>lcore xs \<noteq> {} \<Longrightarrow> xs \<noteq> []\<close>
  unfolding lcore_def by auto

lemma c_shift_post:
  assumes v: \<open>v = x # v'\<close> and q: \<open>q = dnext pgt psts p (Tm (tok x))\<close> and q_lt: \<open>q < length psts\<close>
  shows \<open>ssim G Shn psts
     ((lgoto (xclosure_auto G (hd Xs)) (Tm (tok x)) (FinRep [s_col (span x)]) # Xs, tcols v'),
      xclosure_auto G (lgoto (xclosure_auto G (hd Xs)) (Tm (tok x)) (FinRep [s_col (span x)])) # cstk,
      dnext gt sts i (Tm (tok x)) # istk, v', ts)
     ((dnext gt sts i (Tm (tok x)), q) # stk, v', ts)\<close>
proof -
  let ?F = \<open>lgoto (xclosure_auto G (hd Xs)) (Tm (tok x)) (FinRep [s_col (span x)])\<close>
  have ne: \<open>cgoto (creach G (psts ! p)) (Tm (tok x)) \<noteq> []\<close>
    using pnext_resolve(1)[OF psts c_p_lt, of \<open>Tm (tok x)\<close>] q q_lt unfolding pgt by simp
  have Fl: \<open>lcore ?F = set (psts ! q)\<close>
    using c_shift(2)[OF v] pnext_resolve(2)[OF psts c_p_lt, of \<open>Tm (tok x)\<close>] q q_lt
    unfolding pgt by simp
  have Fne: \<open>?F \<noteq> []\<close> using c_shift(2)[OF v] ne by (intro lcore_Nil_ne) simp
  have ok: \<open>goto_ok (istart_ind G) (xclosure_auto G (hd Xs)) (Tm (tok x)) (FinRep [s_col (span x)])\<close>
    by (rule goto_ok_Tm[OF c_CL(3)]) simp
  have Fa: \<open>anch_items (istart_ind G) ?F\<close> using lgoto_anch[OF ok c_CL(2)] .
  have Fn: \<open>anns_ok ?F\<close> using lgoto_anns[OF c_CL(3)] .
  have didx: \<open>didx_ok G sts (?F # Xs) (dnext gt sts i (Tm (tok x)) # istk)\<close>
    using didx_ok_push[OF tabs c_didx, of 0 \<open>Tm (tok x)\<close> \<open>FinRep [s_col (span x)]\<close>]
      c_ne Fne c_hdX c_istk0 by simp
  have reach: \<open>mreach G Shn (?F # Xs, tcols v')\<close> using mreach_step[OF c_reach c_shift(1)[OF v]] .
  have prec: \<open>\<forall>k < length (?F # Xs). snd (((dnext gt sts i (Tm (tok x)), q) # stk) ! k) < length psts \<and>
      set (psts ! snd (((dnext gt sts i (Tm (tok x)), q) # stk) ! k)) = lcore ((?F # Xs) ! k)\<close>
  proof (intro allI impI)
    fix k assume k: \<open>k < length (?F # Xs)\<close>
    show \<open>snd (((dnext gt sts i (Tm (tok x)), q) # stk) ! k) < length psts \<and>
      set (psts ! snd (((dnext gt sts i (Tm (tok x)), q) # stk) ! k)) = lcore ((?F # Xs) ! k)\<close>
    proof (cases k)
      case 0 then show ?thesis using q_lt Fl by simp
    next
      case (Suc k') then show ?thesis using c_prec[of k'] k by simp
    qed
  qed
  have fr: \<open>\<forall>X \<in> set (?F # Xs). anch_items (istart_ind G) X \<and> anns_ok X\<close>
    unfolding list.set(2) ball_simps(7) using Fa Fn c_frames by blast
  have cs: \<open>cstk_ok G (?F # Xs) (xclosure_auto G ?F # cstk)\<close>
    using c_cstk by (simp add: cstk_ok_map)
  have ist: \<open>dnext gt sts i (Tm (tok x)) # istk = map fst ((dnext gt sts i (Tm (tok x)), q) # stk)\<close>
    using c_istk by simp
  have sts': \<open>didx_ok G (lr0_states G Shn) (?F # Xs) (dnext gt sts i (Tm (tok x)) # istk)\<close>
    using didx unfolding sts .
  show ?thesis unfolding ssim_def prod.case
    by (intro conjI refl list.distinct(2) ist cs sts' prec fr reach)
qed

lemma c_reduce_post:
  assumes n: \<open>length (snd pr) < length Xs\<close>
    and RS: \<open>irep_nonempty (red_set (xclosure_auto G (hd Xs)) pr)\<close>
    and q: \<open>q = dnext pgt psts (snd (stk ! length (snd pr))) (Nt (fst pr))\<close> and q_lt: \<open>q < length psts\<close>
  shows \<open>ssim G Shn psts
     ((lgoto (xclosure_auto G (Xs ! length (snd pr))) (Nt (fst pr))
         (red_set (xclosure_auto G (hd Xs)) pr) # drop (length (snd pr)) Xs, w),
      xclosure_auto G (lgoto (xclosure_auto G (Xs ! length (snd pr))) (Nt (fst pr))
         (red_set (xclosure_auto G (hd Xs)) pr)) # drop (length (snd pr)) cstk,
      dnext gt sts (istk ! length (snd pr)) (Nt (fst pr)) # drop (length (snd pr)) istk, v, ts)
     ((dnext gt sts (fst (stk ! length (snd pr))) (Nt (fst pr)), q) # drop (length (snd pr)) stk, v, ts)\<close>
proof -
  let ?n = \<open>length (snd pr)\<close>
  let ?F = \<open>lgoto (xclosure_auto G (Xs ! ?n)) (Nt (fst pr)) (red_set (xclosure_auto G (hd Xs)) pr)\<close>
  have sn: \<open>snd (stk ! ?n) < length psts\<close> using c_prec[OF n] by simp
  have ne: \<open>cgoto (creach G (psts ! snd (stk ! ?n))) (Nt (fst pr)) \<noteq> []\<close>
    using pnext_resolve(1)[OF psts sn, of \<open>Nt (fst pr)\<close>] q q_lt unfolding pgt by simp
  have Fl: \<open>lcore ?F = set (psts ! q)\<close>
    using c_reduce(2)[OF n RS] pnext_resolve(2)[OF psts sn, of \<open>Nt (fst pr)\<close>] q q_lt
    unfolding pgt by simp
  have Fne: \<open>?F \<noteq> []\<close> using c_reduce(2)[OF n RS] ne by (intro lcore_Nil_ne) simp
  have ok: \<open>goto_ok (istart_ind G) (xclosure_auto G (Xs ! ?n)) (Nt (fst pr))
      (red_set (xclosure_auto G (hd Xs)) pr)\<close>
    by (rule goto_ok_Nt[OF c_frame_cl(3)[OF n] RS red_set_anch[OF c_CL(2) RS]])
  have Fa: \<open>anch_items (istart_ind G) ?F\<close> using lgoto_anch[OF ok c_frame_cl(2)[OF n]] .
  have Fn: \<open>anns_ok ?F\<close> using lgoto_anns[OF c_frame_cl(3)[OF n]] .
  have didx: \<open>didx_ok G sts (?F # drop ?n Xs) (dnext gt sts (istk ! ?n) (Nt (fst pr)) # drop ?n istk)\<close>
    using didx_ok_push[OF tabs c_didx n Fne] .
  have reach: \<open>mreach G Shn (?F # drop ?n Xs, w)\<close> using mreach_step[OF c_reach c_reduce(1)[OF n RS]] .
  have ist: \<open>istk ! ?n = fst (stk ! ?n)\<close> using c_istk c_len n by simp
  have prec: \<open>\<forall>k < length (?F # drop ?n Xs).
      snd (((dnext gt sts (fst (stk ! ?n)) (Nt (fst pr)), q) # drop ?n stk) ! k) < length psts \<and>
      set (psts ! snd (((dnext gt sts (fst (stk ! ?n)) (Nt (fst pr)), q) # drop ?n stk) ! k)) =
        lcore ((?F # drop ?n Xs) ! k)\<close>
  proof (intro allI impI)
    fix k assume k: \<open>k < length (?F # drop ?n Xs)\<close>
    show \<open>snd (((dnext gt sts (fst (stk ! ?n)) (Nt (fst pr)), q) # drop ?n stk) ! k) < length psts \<and>
      set (psts ! snd (((dnext gt sts (fst (stk ! ?n)) (Nt (fst pr)), q) # drop ?n stk) ! k)) =
        lcore ((?F # drop ?n Xs) ! k)\<close>
    proof (cases k)
      case 0 then show ?thesis using q_lt Fl by simp
    next
      case (Suc k')
      have kk: \<open>?n + k' < length Xs\<close> using k Suc n by simp
      have e1: \<open>drop ?n stk ! k' = stk ! (?n + k')\<close>
        by (rule nth_drop) (use n c_len in \<open>metis less_imp_le\<close>)
      have e2: \<open>drop ?n Xs ! k' = Xs ! (?n + k')\<close>
        by (rule nth_drop) (rule less_imp_le[OF n])
      show ?thesis unfolding Suc nth_Cons_Suc e1 e2 by (rule c_prec[OF kk])
    qed
  qed
  have fr: \<open>\<forall>X \<in> set (drop ?n Xs). anch_items (istart_ind G) X \<and> anns_ok X\<close>
  proof
    fix X assume \<open>X \<in> set (drop ?n Xs)\<close>
    then have \<open>X \<in> set Xs\<close> by (rule in_set_dropD)
    then show \<open>anch_items (istart_ind G) X \<and> anns_ok X\<close> by (rule c_frames)
  qed
  have fr': \<open>\<forall>X \<in> set (?F # drop ?n Xs). anch_items (istart_ind G) X \<and> anns_ok X\<close>
    unfolding list.set(2) ball_simps(7) using Fa Fn fr by blast
  have cs: \<open>cstk_ok G (?F # drop ?n Xs) (xclosure_auto G ?F # drop ?n cstk)\<close>
    using c_cstk by (simp add: cstk_ok_map drop_map)
  have ist': \<open>dnext gt sts (istk ! ?n) (Nt (fst pr)) # drop ?n istk =
      map fst ((dnext gt sts (fst (stk ! ?n)) (Nt (fst pr)), q) # drop ?n stk)\<close>
    using c_istk ist by (simp add: drop_map)
  have sts': \<open>didx_ok G (lr0_states G Shn) (?F # drop ?n Xs)
      (dnext gt sts (istk ! ?n) (Nt (fst pr)) # drop ?n istk)\<close>
    using didx unfolding sts .
  show ?thesis unfolding ssim_def prod.case
    by (intro conjI refl list.distinct(2) ist' cs sts' prec fr' reach c_w)
qed

end

lemma ssim_step:
  assumes sim: \<open>ssim G Shn psts st ss\<close> and nf: \<open>\<not> gfinal G Shn (fst st)\<close>
  shows \<open>rel_option (ssim G Shn psts) (dstep G gt sts redtab st) (sstep gt sts redtab pgt psts pc ss)\<close>
proof -
  obtain Xs w cstk istk v tstk where st: \<open>st = ((Xs, w), cstk, istk, v, tstk)\<close>
    by (cases st) auto
  obtain stk v' tstk' where ss: \<open>ss = (stk, v', tstk')\<close> by (cases ss) auto
  have v': \<open>v' = v\<close> and t': \<open>tstk' = tstk\<close> using sim unfolding st ss ssim_def by auto
  have sim': \<open>ssim G Shn psts ((Xs, w), cstk, istk, v, tstk) (stk, v, tstk)\<close>
    using sim unfolding st ss v' t' .
  obtain i p where hd: \<open>hd stk = (i, p)\<close> by (cases \<open>hd stk\<close>) auto
  have ne: \<open>Xs \<noteq> []\<close> using c_ne[OF sim' hd] .
  have stk_ne: \<open>stk \<noteq> []\<close> using c_len[OF sim' hd] ne by auto
  then obtain rest where stk_eq: \<open>stk = (i, p) # rest\<close> using hd by (cases stk) auto
  let ?cells = \<open>red_buckets G Shn (length sts) ! i\<close>
  let ?CL = \<open>xclosure_auto G (hd Xs)\<close>
  let ?D = \<open>dcands G i ?cells ?CL (Xs, w)\<close>
  let ?S = \<open>scands (pcomps G psts ! p) i ?cells v\<close>
  let ?f = \<open>starget pgt psts stk v\<close>
  have dstep_eq: \<open>dstep G gt sts redtab st = (case dpick G cstk (Xs, w) ?D of
        None \<Rightarrow> None
      | Some (act, gc') \<Rightarrow> Some (case act of
          DShift \<Rightarrow> (gc', xclosure_auto G (hd (fst gc')) # cstk,
              dnext gt sts i (Tm (tok (hd v))) # istk, tl v, Leaf (hd v) # tstk)
        | DReduce pr \<Rightarrow> (gc', xclosure_auto G (hd (fst gc')) # drop (length (snd pr)) cstk,
              dnext gt sts (istk ! length (snd pr)) (Nt (fst pr)) # drop (length (snd pr)) istk, v,
              Node (fst pr) (rev (take (length (snd pr)) tstk)) # drop (length (snd pr)) tstk)))\<close>
    unfolding st dstep_def Let_def prod.case c_istk_case[OF sim' hd] c_cstk_case[OF sim' hd]
      c_cells[OF sim' hd] ..
  have sctl_eq: \<open>sctl gt sts redtab pgt psts pc (stk, v) = (case spick ?f ?S of
        None \<Rightarrow> None
      | Some (act, q) \<Rightarrow> Some (act, case act of
          DShift \<Rightarrow> ((dnext gt sts i (Tm (tok (hd v))), q) # stk, tl v)
        | DReduce pr \<Rightarrow> ((dnext gt sts (fst (stk ! length (snd pr))) (Nt (fst pr)), q)
             # drop (length (snd pr)) stk, v)))\<close>
    using c_cells[OF sim' hd] c_comps[OF sim' hd]
    by (simp only: sctl_def stk_eq list.case prod.case Let_def)
  have iff: \<open>\<And>a. (a \<in> set ?D \<and> (\<exists>gc'. mstep G (Xs, w) a = Some gc' \<and> dlive gc')) \<longleftrightarrow>
      (a \<in> set ?S \<and> ?f a \<noteq> None)\<close>
    by (rule c_act_iff[OF sim' hd])
  have mc: \<open>\<And>a. mstep_cached G cstk (Xs, w) a = mstep G (Xs, w) a\<close>
    by (simp add: mstep_def c_cstk[OF sim' hd])
  have hdi: \<open>i = hd istk\<close> using c_istk[OF sim' hd] stk_eq by simp
  have didx': \<open>didx_ok G (lr0_states G Shn) Xs istk\<close> using c_didx[OF sim' hd] unfolding sts .
  have uniq: \<open>a\<^sub>1 = a\<^sub>2\<close>
    if \<open>a\<^sub>1 \<in> set ?D\<close> \<open>a\<^sub>2 \<in> set ?D\<close> \<open>mstep G (Xs, w) a\<^sub>1 = Some gc\<^sub>1\<close> \<open>mstep G (Xs, w) a\<^sub>2 = Some gc\<^sub>2\<close>
      \<open>dlive gc\<^sub>1\<close> \<open>dlive gc\<^sub>2\<close> for a\<^sub>1 a\<^sub>2 gc\<^sub>1 gc\<^sub>2
  proof (rule ccontr)
    assume \<open>a\<^sub>1 \<noteq> a\<^sub>2\<close>
    from det[unfolded mdet_def, rule_format, of \<open>(Xs, w)\<close> istk i \<open>?cells\<close> ?CL a\<^sub>1 a\<^sub>2 gc\<^sub>1 gc\<^sub>2]
    show False using c_reach[OF sim' hd] ne didx' hdi that \<open>a\<^sub>1 \<noteq> a\<^sub>2\<close> unfolding sts by simp
  qed
  show ?thesis
  proof (cases \<open>dpick G cstk (Xs, w) ?D\<close>)
    case None
    have \<open>\<forall>a \<in> set ?S. ?f a = None\<close>
    proof (intro ballI)
      fix a assume a: \<open>a \<in> set ?S\<close>
      show \<open>?f a = None\<close>
      proof (rule ccontr)
        assume \<open>?f a \<noteq> None\<close>
        with a iff obtain gc' where \<open>a \<in> set ?D\<close> \<open>mstep G (Xs, w) a = Some gc'\<close> \<open>dlive gc'\<close> by blast
        with dpick_NoneD[OF None] mc show False by metis
      qed
    qed
    then have \<open>spick ?f ?S = None\<close> by (simp add: spick_None_iff)
    then show ?thesis unfolding dstep_eq ss sstep_def v' t' prod.case sctl_eq None by simp
  next
    case (Some r)
    obtain a gc' where r: \<open>r = (a, gc')\<close> by (cases r)
    from dpick_sound[OF Some[unfolded r]] mc have aD: \<open>a \<in> set ?D\<close>
      and ms: \<open>mstep G (Xs, w) a = Some gc'\<close> and lv: \<open>dlive gc'\<close> by auto
    from iff[of a] aD ms lv obtain q where fq: \<open>?f a = Some q\<close> by auto
    have aS: \<open>a \<in> set ?S\<close> using iff[of a] aD ms lv by blast
    obtain a' q' where sp: \<open>spick ?f ?S = Some (a', q')\<close>
      using spick_None_iff[of ?f ?S] aS fq by (cases \<open>spick ?f ?S\<close>) auto
    from spick_SomeD[OF sp] have a'S: \<open>a' \<in> set ?S\<close> and fq': \<open>?f a' = Some q'\<close> by auto
    from iff[of a'] a'S fq' obtain gc'' where \<open>a' \<in> set ?D\<close> \<open>mstep G (Xs, w) a' = Some gc''\<close>
      \<open>dlive gc''\<close> by auto
    from uniq[OF aD this(1) ms this(2) lv this(3)] have aa: \<open>a' = a\<close> by simp
    with fq fq' have qq: \<open>q' = q\<close> by simp
    have sp': \<open>spick ?f ?S = Some (a, q)\<close> using sp aa qq by simp
    show ?thesis
    proof (cases a)
      case DShift
      from fq obtain x v'' where v: \<open>v = x # v''\<close> by (cases v) (auto simp: DShift starget_def)
      have q: \<open>q = dnext pgt psts p (Tm (tok x))\<close> and q_lt: \<open>q < length psts\<close>
        using fq unfolding DShift starget_def v hd by (auto simp: Let_def split: if_splits)
      have gc': \<open>gc' = (lgoto ?CL (Tm (tok x)) (FinRep [s_col (span x)]) # Xs, tcols v'')\<close>
        using ms c_shift(1)[OF sim' hd v] unfolding DShift by simp
      show ?thesis
        unfolding dstep_eq ss sstep_def v' t' prod.case sctl_eq sp' Some r DShift
        using c_shift_post[OF sim' hd v q q_lt, of \<open>Leaf x # tstk\<close>] gc' v
        by (simp add: stree_def)
    next
      case (DReduce pr)
      let ?n = \<open>length (snd pr)\<close>
      have RS: \<open>irep_nonempty (red_set ?CL pr)\<close> using aD unfolding DReduce dcands_mem[OF ne] by simp
      have n: \<open>?n < length Xs\<close> and q: \<open>q = dnext pgt psts (snd (stk ! ?n)) (Nt (fst pr))\<close>
        and q_lt: \<open>q < length psts\<close>
        using fq c_len[OF sim' hd] unfolding DReduce starget_def by (auto simp: Let_def split: if_splits)
      have gc': \<open>gc' = (lgoto (xclosure_auto G (Xs ! ?n)) (Nt (fst pr)) (red_set ?CL pr)
          # drop ?n Xs, w)\<close>
        using ms c_reduce(1)[OF sim' hd n RS] unfolding DReduce by simp
      show ?thesis
        unfolding dstep_eq ss sstep_def v' t' prod.case sctl_eq sp' Some r DReduce
        using c_reduce_post[OF sim' hd n RS q q_lt,
            of \<open>Node (fst pr) (rev (take ?n tstk)) # drop ?n tstk\<close>] gc'
        by (simp add: stree_def)
    qed
  qed
qed

lemma ssim_final':
  assumes \<open>ssim G Shn psts st ss\<close>
  shows \<open>gfinal G Shn (fst st) \<longleftrightarrow> sfinal (pfins Shn psts) (sctrl ss)\<close>
proof -
  obtain Xs w cstk istk v tstk where st: \<open>st = ((Xs, w), cstk, istk, v, tstk)\<close> by (cases st) auto
  obtain stk v' tstk' where ss: \<open>ss = (stk, v', tstk')\<close> by (cases ss) auto
  show ?thesis using ssim_final[OF assms[unfolded st ss]] unfolding st ss sctrl_def by simp
qed

lemma ssim_tstk:
  \<open>ssim G Shn psts ((gc, cstk, istk, v, tstk)) (stk, v', tstk') \<Longrightarrow> tstk' = tstk\<close>
  unfolding ssim_def by (cases gc) auto

lemma ssim_drun:
  \<open>ssim G Shn psts st ss \<Longrightarrow>
     drun G Shn gt sts redtab n st = srun gt sts redtab pgt psts pc (pfins Shn psts) n ss\<close>
proof (induction n arbitrary: st ss)
  case 0
  obtain gc cstk istk v tstk where st: \<open>st = (gc, cstk, istk, v, tstk)\<close> by (cases st) auto
  obtain stk v' tstk' where ss: \<open>ss = (stk, v', tstk')\<close> by (cases ss) auto
  have f: \<open>gfinal G Shn gc \<longleftrightarrow> sfinal (pfins Shn psts) (stk, v')\<close>
    using ssim_final'[OF "0"] unfolding st ss sctrl_def by simp
  have t: \<open>tstk' = tstk\<close> using ssim_tstk "0" unfolding st ss by blast
  show ?case using f t unfolding st ss by (auto simp: sresult_def split: list.splits)
next
  case (Suc n)
  obtain gc cstk istk v tstk where st: \<open>st = (gc, cstk, istk, v, tstk)\<close> by (cases st) auto
  obtain stk v' tstk' where ss: \<open>ss = (stk, v', tstk')\<close> by (cases ss) auto
  have f: \<open>gfinal G Shn gc \<longleftrightarrow> sfinal (pfins Shn psts) (stk, v')\<close>
    using ssim_final'[OF Suc.prems] unfolding st ss sctrl_def by simp
  show ?case
  proof (cases \<open>gfinal G Shn gc\<close>)
    case True
    have t: \<open>tstk' = tstk\<close> using ssim_tstk Suc.prems unfolding st ss by blast
    then show ?thesis using f True unfolding st ss by (auto simp: sresult_def split: list.splits)
  next
    case False
    have r: \<open>rel_option (ssim G Shn psts) (dstep G gt sts redtab st) (sstep gt sts redtab pgt psts pc ss)\<close>
      by (rule ssim_step[OF Suc.prems]) (use False st in simp)
    show ?thesis
    proof (cases \<open>dstep G gt sts redtab st\<close>)
      case None
      with r have \<open>sstep gt sts redtab pgt psts pc ss = None\<close> by (cases \<open>sstep gt sts redtab pgt psts pc ss\<close>) auto
      then show ?thesis using None False f unfolding st ss by simp
    next
      case (Some st')
      with r obtain ss' where ss': \<open>sstep gt sts redtab pgt psts pc ss = Some ss'\<close>
        and sim': \<open>ssim G Shn psts st' ss'\<close> by (cases \<open>sstep gt sts redtab pgt psts pc ss\<close>) auto
      show ?thesis using Some ss' False f Suc.IH[OF sim'] unfolding st ss
        by (simp del: srun.simps) (simp add: ss'[unfolded ss])
    qed
  qed
qed

end

subsection \<open>Runs\<close>

lemma srun_imp_srun\<^sub>w\<^sub>f:
  \<open>srun gt sts redtab pgt psts pc pf n st = Some t \<Longrightarrow> srun\<^sub>w\<^sub>f gt sts redtab pgt psts pc pf st = Some t\<close>
  by (induction n arbitrary: st) (auto simp: srun\<^sub>w\<^sub>f.simps split: prod.splits option.splits if_splits)

lemma srun\<^sub>w\<^sub>f_imp_srun_ex:
  assumes \<open>srun\<^sub>w\<^sub>f gt sts redtab pgt psts pc pf st = Some t\<close>
  shows \<open>\<exists>n. srun gt sts redtab pgt psts pc pf n st = Some t\<close>
proof (rule srun\<^sub>w\<^sub>f.raw_induct[OF _ assms], goal_cases)
  case (1 f gt sts redtab pgt psts pc pf st t)
  obtain stk v tstk where st: \<open>st = (stk, v, tstk)\<close> by (cases st)
  show ?case
  proof (cases \<open>sfinal pf (stk, v)\<close>)
    case True
    with "1"(2)[unfolded st] have \<open>srun gt sts redtab pgt psts pc pf 0 st = Some t\<close>
      unfolding st by simp
    then show ?thesis by blast
  next
    case False
    with "1"(2)[unfolded st] obtain st\<^sub>1 where
        sp: \<open>sstep gt sts redtab pgt psts pc (stk, v, tstk) = Some st\<^sub>1\<close>
      and rec: \<open>f gt sts redtab pgt psts pc pf st\<^sub>1 = Some t\<close>
      by (auto simp: bind_eq_Some_conv)
    from "1"(1)[OF rec] obtain n where \<open>srun gt sts redtab pgt psts pc pf n st\<^sub>1 = Some t\<close> ..
    with False sp have \<open>srun gt sts redtab pgt psts pc pf (Suc n) st = Some t\<close>
      unfolding st by simp
    then show ?thesis by blast
  qed
qed

lemma drun\<^sub>w\<^sub>f_srun\<^sub>w\<^sub>f:
  assumes \<open>\<And>n. drun G Shn gt sts redtab n st = srun gt' sts' redtab' pgt psts pc pf n ss\<close>
  shows \<open>drun\<^sub>w\<^sub>f G Shn gt sts redtab st = srun\<^sub>w\<^sub>f gt' sts' redtab' pgt psts pc pf ss\<close>
proof (cases \<open>drun\<^sub>w\<^sub>f G Shn gt sts redtab st\<close>)
  case None
  show ?thesis
  proof (cases \<open>srun\<^sub>w\<^sub>f gt' sts' redtab' pgt psts pc pf ss\<close>)
    case (Some t)
    from srun\<^sub>w\<^sub>f_imp_srun_ex[OF Some] obtain n where \<open>srun gt' sts' redtab' pgt psts pc pf n ss = Some t\<close> ..
    with assms[of n] have \<open>drun G Shn gt sts redtab n st = Some t\<close> by simp
    from drun_imp_drun\<^sub>w\<^sub>f[OF this] None show ?thesis by (metis option.distinct(1))
  qed (simp only: None)
next
  case (Some t)
  from drun\<^sub>w\<^sub>f_imp_drun_ex[OF Some] obtain n where \<open>drun G Shn gt sts redtab n st = Some t\<close> ..
  with assms[of n] have \<open>srun gt' sts' redtab' pgt psts pc pf n ss = Some t\<close> by simp
  from srun_imp_srun\<^sub>w\<^sub>f[OF this] Some show ?thesis by (simp only:)
qed

theorem dparse_eq_sparse:
  assumes \<open>sstatic G Shn\<close>
  shows \<open>dparse G Shn w = sparse G Shn w\<close>
  unfolding dparse_def sparse_def Let_def
  by (rule drun\<^sub>w\<^sub>f_srun\<^sub>w\<^sub>f, rule ssim_drun[OF assms refl refl refl refl refl refl])
     (rule ssim_init[OF refl])

subsection \<open>Repeated stacks: the code equation of \<^const>\<open>srun\<^sub>w\<^sub>f\<close>\<close>

text \<open>As for \<^const>\<open>drun\<^sub>w\<^sub>f\<close>: a run that revisits a control state never
  ends, and \<^const>\<open>srun_hist\<close> stops it. The control state is the stack and
  the input, and reduces keep the input, so the stacks seen since the last
  shift are recorded.\<close>

definition snext :: \<open>(('n, 't) sym \<times> nat) list list \<Rightarrow> ('n, 't) citem list list \<Rightarrow>
    ('n, 't) lacell list list \<Rightarrow> (('n, 't) sym \<times> nat) list list \<Rightarrow> ('n, 't) citem list list \<Rightarrow>
    ('n \<times> ('n, 't) rhs) list list \<Rightarrow> bool list \<Rightarrow> ('m, 'ch, 't) sctl_t \<Rightarrow> ('m, 'ch, 't) sctl_t \<Rightarrow> bool\<close> where
  \<open>snext gt sts redtab pgt psts pc pf c d \<longleftrightarrow>
     \<not> sfinal pf c \<and> (\<exists>a. sctl gt sts redtab pgt psts pc c = Some (a, d))\<close>

lemma sstep_sctl:
  \<open>sstep gt sts redtab pgt psts pc st = Some st' \<longleftrightarrow>
     (\<exists>a. sctl gt sts redtab pgt psts pc (sctrl st) = Some (a, sctrl st') \<and>
        snd (snd st') = stree a (fst (snd st)) (snd (snd st)))\<close>
  unfolding sstep_def sctrl_def by (cases st; cases st') (auto split: prod.splits)

lemma sctl_reduce_v:
  \<open>sctl gt sts redtab pgt psts pc (stk, v) = Some (DReduce pr, stk', v') \<Longrightarrow> v' = v\<close>
  unfolding sctl_def by (auto simp: Let_def split: list.splits option.splits prod.splits)

lemma srun_on_cycle_None:
  assumes \<open>(snext gt sts redtab pgt psts pc pf)\<^sup>+\<^sup>+ c (sctrl st)\<close>
    \<open>(snext gt sts redtab pgt psts pc pf)\<^sup>+\<^sup>+ (sctrl st) c\<close>
  shows \<open>srun gt sts redtab pgt psts pc pf n st = None\<close>
  using assms
proof (induction n arbitrary: st)
  case (0 st)
  from converse_tranclpE[OF "0.prems"(2)] obtain e where \<open>snext gt sts redtab pgt psts pc pf (sctrl st) e\<close>
    by blast
  then show ?case unfolding snext_def sctrl_def by (cases st) auto
next
  case (Suc n st)
  obtain stk v tstk where st: \<open>st = (stk, v, tstk)\<close> by (cases st)
  from converse_tranclpE[OF Suc.prems(2)] obtain e where
    e: \<open>snext gt sts redtab pgt psts pc pf (sctrl st) e\<close> by blast
  then obtain a where nf: \<open>\<not> sfinal pf (stk, v)\<close>
    and sc: \<open>sctl gt sts redtab pgt psts pc (stk, v) = Some (a, e)\<close>
    unfolding snext_def st sctrl_def by auto
  obtain stk' v' where e': \<open>e = (stk', v')\<close> by (cases e)
  let ?st' = \<open>(stk', v', stree a v tstk)\<close>
  have step: \<open>sstep gt sts redtab pgt psts pc st = Some ?st'\<close>
    unfolding sstep_def st using sc e' by simp
  have ce: \<open>(snext gt sts redtab pgt psts pc pf)\<^sup>+\<^sup>+ c (sctrl ?st')\<close>
    using tranclp.trancl_into_trancl[OF Suc.prems(1) e] e' by (simp add: sctrl_def)
  have ec: \<open>(snext gt sts redtab pgt psts pc pf)\<^sup>+\<^sup>+ (sctrl ?st') c\<close>
  proof (rule converse_tranclpE[OF Suc.prems(2)])
    assume \<open>snext gt sts redtab pgt psts pc pf (sctrl st) c\<close>
    with e have \<open>e = c\<close> unfolding snext_def by auto
    then show ?thesis using Suc.prems e' by (auto simp: sctrl_def intro: tranclp_trans)
  next
    fix e'' assume \<open>snext gt sts redtab pgt psts pc pf (sctrl st) e''\<close>
      \<open>(snext gt sts redtab pgt psts pc pf)\<^sup>+\<^sup>+ e'' c\<close>
    with e have \<open>e'' = e\<close> unfolding snext_def by auto
    then show ?thesis using \<open>(snext gt sts redtab pgt psts pc pf)\<^sup>+\<^sup>+ e'' c\<close> e'
      by (simp add: sctrl_def)
  qed
  have \<open>srun gt sts redtab pgt psts pc pf (Suc n) st = srun gt sts redtab pgt psts pc pf n ?st'\<close>
    using nf step unfolding st by simp
  also have \<open>\<dots> = None\<close> by (rule Suc.IH[OF ce ec])
  finally show ?case .
qed

lemma srun\<^sub>w\<^sub>f_on_cycle_None:
  assumes \<open>(snext gt sts redtab pgt psts pc pf)\<^sup>+\<^sup>+ c (sctrl st)\<close>
    \<open>(snext gt sts redtab pgt psts pc pf)\<^sup>+\<^sup>+ (sctrl st) c\<close>
  shows \<open>srun\<^sub>w\<^sub>f gt sts redtab pgt psts pc pf st = None\<close>
  using srun\<^sub>w\<^sub>f_imp_srun_ex[of gt sts redtab pgt psts pc pf st] srun_on_cycle_None[OF assms]
  by (cases \<open>srun\<^sub>w\<^sub>f gt sts redtab pgt psts pc pf st\<close>) auto

definition shist_ok :: \<open>(('n, 't) sym \<times> nat) list list \<Rightarrow> ('n, 't) citem list list \<Rightarrow>
    ('n, 't) lacell list list \<Rightarrow> (('n, 't) sym \<times> nat) list list \<Rightarrow> ('n, 't) citem list list \<Rightarrow>
    ('n \<times> ('n, 't) rhs) list list \<Rightarrow> bool list \<Rightarrow> (nat \<times> nat) list list \<Rightarrow>
    ('m, 'ch, 'n, 't) sst \<Rightarrow> bool\<close> where
  \<open>shist_ok gt sts redtab pgt psts pc pf seen st \<longleftrightarrow>
     (\<forall>k \<in> set seen. (snext gt sts redtab pgt psts pc pf)\<^sup>+\<^sup>+ (k, fst (snd st)) (sctrl st))\<close>

lemma shist_ok_Nil [simp]: \<open>shist_ok gt sts redtab pgt psts pc pf [] st\<close>
  unfolding shist_ok_def by simp

lemma srun_hist_imp_srun\<^sub>w\<^sub>f:
  assumes \<open>srun_hist gt sts redtab pgt psts pc pf seen st = Some t\<close>
  shows \<open>srun\<^sub>w\<^sub>f gt sts redtab pgt psts pc pf st = Some t\<close>
proof (rule srun_hist.raw_induct[OF _ assms], goal_cases)
  case (1 f gt sts redtab pgt psts pc pf seen st t)
  obtain stk v tstk where st: \<open>st = (stk, v, tstk)\<close> by (cases st)
  show ?case
  proof (cases \<open>sfinal pf (stk, v)\<close>)
    case True
    with "1"(2) show ?thesis unfolding st by (simp add: srun\<^sub>w\<^sub>f.simps)
  next
    case False
    from False "1"(2) obtain a stk' v' where
        sc: \<open>sctl gt sts redtab pgt psts pc (stk, v) = Some (a, stk', v')\<close>
      and rec: \<open>f gt sts redtab pgt psts pc pf (if a = DShift then [] else stk # seen)
          (stk', v', stree a v tstk) = Some t\<close>
      unfolding st by (auto simp: bind_eq_Some_conv split: if_splits)
    from "1"(1)[OF rec] have \<open>srun\<^sub>w\<^sub>f gt sts redtab pgt psts pc pf (stk', v', stree a v tstk) = Some t\<close> .
    with False sc show ?thesis unfolding st by (subst srun\<^sub>w\<^sub>f.simps) (simp add: sstep_def)
  qed
qed

lemma srun_imp_srun_hist:
  assumes \<open>srun gt sts redtab pgt psts pc pf n st = Some t\<close>
    and \<open>shist_ok gt sts redtab pgt psts pc pf seen st\<close>
  shows \<open>srun_hist gt sts redtab pgt psts pc pf seen st = Some t\<close>
  using assms
proof (induction n arbitrary: st seen)
  case (0 st seen)
  obtain stk v tstk where st: \<open>st = (stk, v, tstk)\<close> by (cases st)
  show ?case using "0.prems"(1) unfolding st
    by (subst srun_hist.simps) (auto split: if_splits)
next
  case (Suc n st seen)
  obtain stk v tstk where st: \<open>st = (stk, v, tstk)\<close> by (cases st)
  show ?case
  proof (cases \<open>sfinal pf (stk, v)\<close>)
    case True
    with Suc.prems(1) show ?thesis unfolding st by (subst srun_hist.simps) simp
  next
    case False
    with Suc.prems(1) obtain st\<^sub>1 where sp: \<open>sstep gt sts redtab pgt psts pc st = Some st\<^sub>1\<close>
      and rec: \<open>srun gt sts redtab pgt psts pc pf n st\<^sub>1 = Some t\<close>
      unfolding st by (auto split: option.splits)
    from sp obtain a stk' v' where sc: \<open>sctl gt sts redtab pgt psts pc (stk, v) = Some (a, stk', v')\<close>
      and st1: \<open>st\<^sub>1 = (stk', v', stree a v tstk)\<close>
      unfolding st sstep_def by (auto split: prod.splits)
    have r: \<open>snext gt sts redtab pgt psts pc pf (stk, v) (stk', v')\<close>
      unfolding snext_def using False sc by blast
    have nk: \<open>stk \<notin> set seen\<close>
    proof
      assume \<open>stk \<in> set seen\<close>
      with Suc.prems(2) have c: \<open>(snext gt sts redtab pgt psts pc pf)\<^sup>+\<^sup>+ (stk, v) (sctrl st)\<close>
        unfolding shist_ok_def st by simp
      then have \<open>(snext gt sts redtab pgt psts pc pf)\<^sup>+\<^sup>+ (sctrl st) (sctrl st)\<close>
        unfolding st sctrl_def by simp
      from srun\<^sub>w\<^sub>f_on_cycle_None[OF this this] srun_imp_srun\<^sub>w\<^sub>f[OF Suc.prems(1)] show False by simp
    qed
    have ok: \<open>shist_ok gt sts redtab pgt psts pc pf (if a = DShift then [] else stk # seen) st\<^sub>1\<close>
    proof (cases \<open>a = DShift\<close>)
      case True then show ?thesis by simp
    next
      case nsh: False
      then obtain pr where a: \<open>a = DReduce pr\<close> by (cases a) auto
      have vv: \<open>v' = v\<close> using sctl_reduce_v sc[unfolded a] .
      show ?thesis unfolding shist_ok_def st1 sctrl_def
      proof (intro ballI)
        fix k assume \<open>k \<in> set (if a = DShift then [] else stk # seen)\<close>
        with nsh have \<open>k = stk \<or> k \<in> set seen\<close> by simp
        then show \<open>(snext gt sts redtab pgt psts pc pf)\<^sup>+\<^sup>+ (k, fst (snd (stk', v', stree a v tstk)))
            (case (stk', v', stree a v tstk) of (stk, v, tstk) \<Rightarrow> (stk, v))\<close>
        proof
          assume \<open>k = stk\<close>
          then show ?thesis using r vv by simp
        next
          assume \<open>k \<in> set seen\<close>
          with Suc.prems(2) have \<open>(snext gt sts redtab pgt psts pc pf)\<^sup>+\<^sup>+ (k, v) (stk, v)\<close>
            unfolding shist_ok_def st sctrl_def by simp
          then show ?thesis using r vv by (simp add: tranclp.trancl_into_trancl)
        qed
      qed
    qed
    from Suc.IH[OF rec ok] have ih: \<open>srun_hist gt sts redtab pgt psts pc pf
        (if a = DShift then [] else stk # seen) st\<^sub>1 = Some t\<close> .
    show ?thesis using False nk sc ih unfolding st st1 by (subst srun_hist.simps) simp
  qed
qed

theorem srun\<^sub>w\<^sub>f_code [code]:
  \<open>srun\<^sub>w\<^sub>f gt sts redtab pgt psts pc pf st = srun_hist gt sts redtab pgt psts pc pf [] st\<close>
proof (cases \<open>srun_hist gt sts redtab pgt psts pc pf [] st\<close>)
  case None
  show ?thesis
  proof (cases \<open>srun\<^sub>w\<^sub>f gt sts redtab pgt psts pc pf st\<close>)
    case (Some t)
    from srun\<^sub>w\<^sub>f_imp_srun_ex[OF Some] obtain n where \<open>srun gt sts redtab pgt psts pc pf n st = Some t\<close> ..
    from srun_imp_srun_hist[OF this shist_ok_Nil] None show ?thesis by simp
  qed (simp only: None)
next
  case (Some t)
  from srun_hist_imp_srun\<^sub>w\<^sub>f[OF Some] Some show ?thesis by simp
qed

subsection \<open>Table inlining\<close>

text \<open>The counterpart of \<^text>\<open>dparse_via_tables\<close>: under the static
  conditions the parser runs the simple driver on precomputed tables.\<close>

lemma dparse_via_simple_tables:
  assumes static: \<open>sstatic G Shn\<close>
    and st: \<open>lr0_states G Shn = sts\<close> and gt: \<open>la_gtab G sts = gtab\<close>
    and rt: \<open>red_buckets G Shn (length sts) = redtab\<close>
    and ps: \<open>pr0_states G Shn = psts\<close> and pg: \<open>pgtab G psts = pgt\<close>
    and pcs: \<open>pcomps G psts = pc\<close> and pfs: \<open>pfins Shn psts = pf\<close>
    and i0: \<open>st_find sts (lr0_start G Shn) = i\<^sub>0\<close>
    and p0: \<open>st_find psts (lr0_start G Shn) = p\<^sub>0\<close>
  shows \<open>dparse G Shn w = srun\<^sub>w\<^sub>f gtab sts redtab pgt psts pc pf ([(i\<^sub>0, p\<^sub>0)], w, [])\<close>
  unfolding dparse_eq_sparse[OF static] sparse_def sinit_def Let_def
  by (simp add: st gt rt ps pg pcs pfs i0 p0)

end
