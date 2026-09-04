theory LR_Det
  imports LR_Driver
begin

section \<open>The static sufficient condition for \<^const>\<open>mdet\<close>\<close>

text \<open>This theory proves \<open>rlalr_conflicts G Shn = [] \<Longrightarrow> mdet G Shn\<close>
  (\<^text>\<open>rlalr_sufficient\<close>, at the end): an executable check on the
  driver's tables implies the determinism premise of its completeness.
  After Barthwal (2010, Def. 5.3.7 \<open>okSlr\<close> and Thm 5.4.4: conflict
  freedom is demanded on viable-prefix-reachable states only), DeRemer and
  Pennello (1982, Sect. 3: per-item lookahead) and Jourdan, Pottier and
  Leroy (2012, Sect. 3.3 and Thm 4).

  In order: saturation of the anchored reachable closure; the precise
  (viable-prefix) automaton \<^text>\<open>pr0_states\<close> and its worklist; the
  rigid-point conflict analysis \<^text>\<open>rlalr_conflicts\<close>; tracking every
  reachable configuration in the product automaton; the pooled width
  invariant; the canonical tracked stack \<^text>\<open>strack\<close> and its descent;
  the soundness of the rigid-point walk, from which
  \<^text>\<open>rlalr_sufficient\<close> follows.\<close>


section \<open>Saturation of the anchored reachable closure\<close>

text \<open>The report and the check read the fuelled \<^const>\<open>wreach\<close>, which is
  total; this section shows it is saturated.  The general argument:
  \<^const>\<open>wreach_step\<close> only emits dot-0 items, so regardless of the kernel the
  chain grows by at most one item per production per \<^typ>\<open>wrel\<close>, which is
  \<^const>\<open>wreach\<close>'s fuel.  \<^text>\<open>funpow_saturates\<close> bounds the chain by
  \<^term>\<open>card U\<close> for a universe \<^term>\<open>U\<close> containing the start, too coarse
  here; the variant below bounds it by the increment.\<close>

subsection \<open>Saturation bounded by the increment, not the universe\<close>

lemma funpow_saturates_delta:
  fixes f :: \<open>'a list \<Rightarrow> 'a list\<close> and D :: \<open>'a set\<close>
  assumes ext: \<open>\<And>xs ys. set xs = set ys \<Longrightarrow> set (f xs) = set (f ys)\<close>
    and mono: \<open>\<And>xs. set xs \<subseteq> set (f xs)\<close>
    and delta: \<open>\<And>xs. set (f xs) \<subseteq> set xs \<union> D\<close>
    and fin: \<open>finite D\<close>
    and N: \<open>card D \<le> N\<close>
  shows \<open>set (f ((f ^^ N) xs\<^sub>0)) = set ((f ^^ N) xs\<^sub>0)\<close>
proof -
  have chain: \<open>set ((f ^^ k) xs\<^sub>0) \<subseteq> set ((f ^^ Suc k) xs\<^sub>0)\<close> for k
    using mono by simp
  have incr: \<open>set xs\<^sub>0 \<subseteq> set ((f ^^ k) xs\<^sub>0)\<close> for k
    by (induction k) (use chain in auto)
  have inD: \<open>set ((f ^^ k) xs\<^sub>0) \<subseteq> set xs\<^sub>0 \<union> D\<close> for k
    by (induction k) (use delta in auto)
  show ?thesis
  proof (cases \<open>\<exists>k < N. set (f ((f ^^ k) xs\<^sub>0)) = set ((f ^^ k) xs\<^sub>0)\<close>)
    case True
    then obtain k where k: \<open>k < N\<close>
      and st: \<open>set (f ((f ^^ k) xs\<^sub>0)) = set ((f ^^ k) xs\<^sub>0)\<close> by blast
    have stab: \<open>set ((f ^^ (k + d)) xs\<^sub>0) = set ((f ^^ k) xs\<^sub>0)\<close> for d
    proof (induction d)
      case (Suc d)
      have \<open>set ((f ^^ (k + Suc d)) xs\<^sub>0) = set (f ((f ^^ (k + d)) xs\<^sub>0))\<close>
        by (simp add: funpow_swap1)
      also have \<open>\<dots> = set (f ((f ^^ k) xs\<^sub>0))\<close> by (rule ext[OF Suc.IH])
      also have \<open>\<dots> = set ((f ^^ k) xs\<^sub>0)\<close> by (rule st)
      finally show ?case .
    qed simp
    have \<open>set ((f ^^ N) xs\<^sub>0) = set ((f ^^ k) xs\<^sub>0)\<close>
      using stab[of \<open>N - k\<close>] k by simp
    then show ?thesis using st ext by metis
  next
    case False
    \<comment> \<open>no early fixed point: each of the first \<open>N\<close> steps strictly grows,
        so the increment exhausts \<^term>\<open>D\<close>\<close>
    have strict: \<open>k < N \<Longrightarrow> set ((f ^^ k) xs\<^sub>0) \<subset> set ((f ^^ Suc k) xs\<^sub>0)\<close> for k
      using False chain by (simp add: psubset_eq) blast
    have card_ge: \<open>k \<le> N \<Longrightarrow> k \<le> card (set ((f ^^ k) xs\<^sub>0) - set xs\<^sub>0)\<close> for k
    proof (induction k)
      case (Suc k)
      have fk: \<open>finite (set ((f ^^ k) xs\<^sub>0) - set xs\<^sub>0)\<close> by simp
      have sub: \<open>set ((f ^^ k) xs\<^sub>0) - set xs\<^sub>0 \<subset> set ((f ^^ Suc k) xs\<^sub>0) - set xs\<^sub>0\<close>
        using strict[of k] Suc.prems incr[of k] by auto
      have \<open>k \<le> card (set ((f ^^ k) xs\<^sub>0) - set xs\<^sub>0)\<close> using Suc by simp
      moreover have \<open>card (set ((f ^^ k) xs\<^sub>0) - set xs\<^sub>0)
            < card (set ((f ^^ Suc k) xs\<^sub>0) - set xs\<^sub>0)\<close>
        by (rule psubset_card_mono) (use sub in auto)
      ultimately show ?case by simp
    qed simp
    have dsub: \<open>set ((f ^^ N) xs\<^sub>0) - set xs\<^sub>0 \<subseteq> D\<close> using inD by auto
    have \<open>N \<le> card (set ((f ^^ N) xs\<^sub>0) - set xs\<^sub>0)\<close> by (rule card_ge) simp
    moreover have \<open>card (set ((f ^^ N) xs\<^sub>0) - set xs\<^sub>0) \<le> card D\<close>
      by (rule card_mono[OF fin dsub])
    ultimately have eqD: \<open>set ((f ^^ N) xs\<^sub>0) - set xs\<^sub>0 = D\<close>
      using N card_subset_eq[OF fin dsub] by simp
    have \<open>set (f ((f ^^ N) xs\<^sub>0)) \<subseteq> set ((f ^^ N) xs\<^sub>0)\<close>
      using delta[of \<open>(f ^^ N) xs\<^sub>0\<close>] eqD by auto
    with mono show ?thesis by blast
  qed
qed

subsection \<open>\<^const>\<open>wreach_step\<close> is extensional, monotone, and dot-0 bounded\<close>

text \<open>\<^const>\<open>wreach_step\<close> inlines its contribution function; name it for the
  set-level reasoning below.\<close>

definition wcontrib :: \<open>('n, 't) is_cfg \<Rightarrow> ('n, 't) witem \<Rightarrow> ('n, 't) witem list\<close> where
  \<open>wcontrib G = (\<lambda>(pr, m, \<rho>).
      if m < length (snd pr)
      then (case fst (snd pr ! m) of
             Nt B \<Rightarrow> map (\<lambda>br. (br, 0, wcomp (winv (w_of (snd (snd pr ! m)))) \<rho>))
                     (filter (\<lambda>br. fst br = B) (iprods G))
           | Tm _ \<Rightarrow> [])
      else [])\<close>

lemma wreach_step_alt:
  \<open>wreach_step G ws = remdups (ws @ concat (map (wcontrib G) ws))\<close>
  unfolding wreach_step_def wcontrib_def by simp

lemma wreach_step_set:
  \<open>set (wreach_step G xs) = set xs \<union> (\<Union>x \<in> set xs. set (wcontrib G x))\<close>
  unfolding wreach_step_alt by auto

lemma wreach_step_ext:
  \<open>set xs = set ys \<Longrightarrow> set (wreach_step G xs) = set (wreach_step G ys)\<close>
  by (simp add: wreach_step_set)

lemma wreach_step_mono: \<open>set xs \<subseteq> set (wreach_step G xs)\<close>
  by (simp add: wreach_step_set)

text \<open>Every item \<^const>\<open>wreach_step\<close> emits sits at dot 0 on a production of
  the grammar; this bounds the growth independently of the kernel.\<close>

definition wdot0 :: \<open>('n, 't) is_cfg \<Rightarrow> ('n, 't) witem list\<close> where
  \<open>wdot0 G = concat (map (\<lambda>pr. map (\<lambda>\<rho>. (pr, 0, \<rho>))
      [WEq, WGe, WGt, WLe, WLt, WAny]) (iprods G))\<close>

lemma wdot0_mem: \<open>pr \<in> set (iprods G) \<Longrightarrow> (pr, 0, \<rho>) \<in> set (wdot0 G)\<close>
  unfolding wdot0_def by (cases \<rho>) force+

lemma length_wdot0: \<open>length (wdot0 G) = length (iprods G) * 6\<close>
proof -
  have \<open>length (concat (map (\<lambda>pr. [(pr, 0, WEq), (pr, 0, WGe), (pr, 0, WGt),
        (pr, 0, WLe), (pr, 0, WLt), (pr, 0, WAny)]) ps)) = length ps * 6\<close>
    for ps :: \<open>('n \<times> ('n, 't) rhs) list\<close>
    by (induction ps) auto
  then show ?thesis unfolding wdot0_def by simp
qed

lemma wcontrib_simp:
  \<open>wcontrib G (pr, m, \<rho>) =
      (if m < length (snd pr)
       then (case fst (snd pr ! m) of
              Nt B \<Rightarrow> map (\<lambda>br. (br, 0, wcomp (winv (w_of (snd (snd pr ! m)))) \<rho>))
                      (filter (\<lambda>br. fst br = B) (iprods G))
            | Tm _ \<Rightarrow> [])
       else [])\<close>
  unfolding wcontrib_def by simp

lemma wcontrib_dot0:
  assumes \<open>y \<in> set (wcontrib G x)\<close>
  shows \<open>y \<in> set (wdot0 G)\<close>
proof -
  obtain pr m \<rho> where x: \<open>x = (pr, m, \<rho>)\<close> by (cases x) auto
  show ?thesis
  proof (cases \<open>m < length (snd pr)\<close>)
    case False
    then show ?thesis using assms unfolding x wcontrib_simp by simp
  next
    case True
    show ?thesis
    proof (cases \<open>fst (snd pr ! m)\<close>)
      case (Tm a)
      then show ?thesis using assms True unfolding x wcontrib_simp by simp
    next
      case (Nt B)
      have \<open>y \<in> set (map (\<lambda>br. (br, 0, wcomp (winv (w_of (snd (snd pr ! m)))) \<rho>))
                     (filter (\<lambda>br. fst br = B) (iprods G)))\<close>
        using assms True Nt unfolding x wcontrib_simp by simp
      then obtain br where br: \<open>br \<in> set (iprods G)\<close>
        and yeq: \<open>y = (br, 0, wcomp (winv (w_of (snd (snd pr ! m)))) \<rho>)\<close> by auto
      show ?thesis unfolding yeq by (rule wdot0_mem[OF br])
    qed
  qed
qed
lemma wreach_step_delta: \<open>set (wreach_step G xs) \<subseteq> set xs \<union> set (wdot0 G)\<close>
  by (auto simp: wreach_step_set dest: wcontrib_dot0)

subsection \<open>Hence the fuelled \<^const>\<open>wreach\<close> is saturated\<close>

theorem wreach_stable: \<open>set (wreach_step G (wreach G s)) = set (wreach G s)\<close>
  unfolding wreach_def
proof (rule funpow_saturates_delta[where D = \<open>set (wdot0 G)\<close>])
  show \<open>\<And>xs ys. set xs = set ys \<Longrightarrow> set (wreach_step G xs) = set (wreach_step G ys)\<close>
    by (rule wreach_step_ext)
  show \<open>\<And>xs. set xs \<subseteq> set (wreach_step G xs)\<close> by (rule wreach_step_mono)
  show \<open>\<And>xs. set (wreach_step G xs) \<subseteq> set xs \<union> set (wdot0 G)\<close>
    by (rule wreach_step_delta)
  show \<open>finite (set (wdot0 G))\<close> by simp
  show \<open>card (set (wdot0 G)) \<le> Suc (length (iprods G) * 6)\<close>
    using card_length[of \<open>wdot0 G\<close>] length_wdot0[of G] by simp
qed

lemma funpow_wreach_mono: \<open>set xs \<subseteq> set ((wreach_step G ^^ k) xs)\<close>
proof (induction k)
  case (Suc k)
  have \<open>set ((wreach_step G ^^ k) xs) \<subseteq> set ((wreach_step G ^^ Suc k) xs)\<close>
    using wreach_step_mono by simp
  with Suc show ?case by simp
qed simp

lemma wreach_kernel: \<open>set (wkernel s) \<subseteq> set (wreach G s)\<close>
  unfolding wreach_def by (rule funpow_wreach_mono)

text \<open>\<^const>\<open>wreach\<close> is saturated, so it contains everything one
  \<^const>\<open>wreach_step\<close> would add.\<close>

lemma wreach_emit:
  assumes mem: \<open>(pr', m', \<rho>') \<in> set (wreach G s)\<close>
    and m_lt: \<open>m' < length (snd pr')\<close>
    and nxt: \<open>fst (snd pr' ! m') = Nt (fst br)\<close>
    and br: \<open>br \<in> set (iprods G)\<close>
  shows \<open>(br, 0, wcomp (winv (w_of (snd (snd pr' ! m')))) \<rho>') \<in> set (wreach G s)\<close>
proof -
  have \<open>(br, 0, wcomp (winv (w_of (snd (snd pr' ! m')))) \<rho>')
        \<in> set (wcontrib G (pr', m', \<rho>'))\<close>
    unfolding wcontrib_simp using m_lt nxt br by simp
  then have \<open>(br, 0, wcomp (winv (w_of (snd (snd pr' ! m')))) \<rho>')
        \<in> set (wreach_step G (wreach G s))\<close>
    using mem by (auto simp: wreach_step_set)
  then show ?thesis unfolding wreach_stable .
qed

section \<open>The precise automaton\<close>

text \<open>\<^const>\<open>pr0_states\<close> is the worklist construction of \<open>LR\<close> with the
  reachable closure \<^const>\<open>creach\<close> in place of \<^const>\<open>cclosure\<close>; the
  generic \<^text>\<open>wl_states_inv\<close> gives goto-closedness, the start state and
  the universe bound once a goto through \<^const>\<open>creach\<close> is known to stay
  in the universe.\<close>

lemma cgoto_creach_univ:
  assumes \<open>set s \<subseteq> cuniv G Shn\<close>
  shows \<open>set (cgoto (creach G s) X) \<subseteq> cuniv G Shn\<close>
  using cgoto_set_mono[OF creach_sound] cgoto_cclosure_univ[OF assms] by blast

lemma pr0_states_inv:
  \<open>wl_inv G Shn (creach G) {set (lr0_start G Shn), {}} (pr0_states G Shn, [])\<close>
  unfolding pr0_states_def by (rule wl_states_inv[OF cgoto_creach_univ])

theorem pr0_states_closed:
  assumes \<open>s \<in> set (pr0_states G Shn)\<close> and \<open>X \<in> set (gram_syms G)\<close>
  shows \<open>\<exists>t \<in> set (pr0_states G Shn). set t = set (cgoto (creach G s) X)\<close>
  using pr0_states_inv assms unfolding wl_inv_def by fastforce

theorem pr0_states_start:
  \<open>\<exists>t \<in> set (pr0_states G Shn). set t = set (ccore (xinit G Shn))\<close>
proof -
  have \<open>set (lr0_start G Shn) \<in> set ` set (pr0_states G Shn)\<close>
    using pr0_states_inv[of G Shn] unfolding wl_inv_def by auto
  moreover have \<open>set (ccore (xinit G Shn)) = set (lr0_start G Shn)\<close>
    unfolding ccore_def xinit_def lr0_start_def start_prod_def by simp
  ultimately show ?thesis by auto
qed

lemma pr0_states_univ:
  \<open>s \<in> set (pr0_states G Shn) \<Longrightarrow> set s \<subseteq> cuniv G Shn\<close>
  using pr0_states_inv[of G Shn] unfolding wl_inv_def by auto


section \<open>The live part of a frame closure lies in the reachable closure\<close>

text \<open>The frame closure \<^const>\<open>xclosure_auto\<close> predicts every production
  (dead slots carry empty \<^typ>\<open>indrep\<close>s), but an item that carries an
  \<open>anchor\<close> was predicted through a chain of anchored items: its core lies in
  \<^const>\<open>creach\<close> of any kernel covering the anchored kernel items.  This
  connects a runtime frame to the \<open>precise\<close> automaton state of its
  context.  First the \<^const>\<open>creach\<close> lemmas: a set-level characterisation
  of the step, saturation of the fuelled closure (via
  \<open>funpow_saturates_delta\<close>), monotonicity, and the emit lemma.\<close>

lemma creach_step_set:
  \<open>set (creach_step G cs) = set cs \<union>
     {(pr, 0) | pr. pr \<in> set (iprods G) \<and>
        (\<exists>pr' m'. (pr', m') \<in> set cs \<and> m' < length (snd pr') \<and>
                  fst (snd pr' ! m') = Nt (fst pr))}\<close>
  unfolding creach_step_def by (fastforce simp: list_ex_iff split: if_splits)

lemma creach_step_ext:
  \<open>set cs = set cs' \<Longrightarrow> set (creach_step G cs) = set (creach_step G cs')\<close>
  by (simp add: creach_step_set)

lemma creach_step_dot0_delta:
  \<open>set (creach_step G cs) \<subseteq> set cs \<union> set (map (\<lambda>pr. (pr, 0)) (iprods G))\<close>
  by (auto simp: creach_step_set)

theorem creach_stable: \<open>set (creach_step G (creach G cs)) = set (creach G cs)\<close>
  unfolding creach_def
proof (rule funpow_saturates_delta[where D = \<open>set (map (\<lambda>pr. (pr, 0)) (iprods G))\<close>])
  show \<open>\<And>xs ys. set xs = set ys \<Longrightarrow> set (creach_step G xs) = set (creach_step G ys)\<close>
    by (rule creach_step_ext)
  show \<open>\<And>xs. set xs \<subseteq> set (creach_step G xs)\<close> by (rule creach_step_mono)
  show \<open>\<And>xs. set (creach_step G xs) \<subseteq> set xs \<union> set (map (\<lambda>pr. (pr, 0)) (iprods G))\<close>
    by (rule creach_step_dot0_delta)
  show \<open>finite (set (map (\<lambda>pr. (pr, 0)) (iprods G)))\<close> by simp
  show \<open>card (set (map (\<lambda>pr. (pr, 0)) (iprods G))) \<le> Suc (length (iprods G))\<close>
    by (metis card_length length_map le_SucI)
qed

lemma creach_emit:
  assumes mem: \<open>(pr', m') \<in> set (creach G cs)\<close>
    and m_lt: \<open>m' < length (snd pr')\<close>
    and nxt: \<open>fst (snd pr' ! m') = Nt (fst br)\<close>
    and br: \<open>br \<in> set (iprods G)\<close>
  shows \<open>(br, 0) \<in> set (creach G cs)\<close>
proof -
  have \<open>(br, 0) \<in> set (creach_step G (creach G cs))\<close>
    unfolding creach_step_set using mem m_lt nxt br by blast
  then show ?thesis unfolding creach_stable .
qed

text \<open>The live-closure lemma, by induction on the round number: a
  slot with a non-empty anchor set was contributed by an anchored item,
  which is a live kernel item or an earlier live slot.\<close>

lemma xiter_live_creach:
  assumes kern: \<open>\<And>pr m R. (pr, m, R) \<in> set xs \<Longrightarrow> irep_nonempty R \<Longrightarrow> (pr, m) \<in> set s\<close>
  shows \<open>p < length (iprods G) \<Longrightarrow> j \<in> irep_set (xiter G xs t ! p) \<Longrightarrow>
     (iprods G ! p, 0) \<in> set (creach G s)\<close>
proof (induction t arbitrary: p j)
  case 0
  then show ?case by simp
next
  case (Suc t)
  have len: \<open>length (xiter G xs t) = length (iprods G)\<close> by simp
  have \<open>xiter G xs (Suc t) ! p =
      fold (xcontrib (iprods G ! p)) (xslots G xs (xiter G xs t)) (xiter G xs t ! p)\<close>
    by (simp add: xround_nth[OF len Suc.prems(1)])
  with Suc.prems(2) have
    \<open>j \<in> irep_set (xiter G xs t ! p) \<or>
     (\<exists>xit \<in> set (xslots G xs (xiter G xs t)). j \<in> ximg (iprods G ! p) xit)\<close>
    by (simp add: fold_xcontrib_set)
  then show ?case
  proof
    assume \<open>j \<in> irep_set (xiter G xs t ! p)\<close>
    from Suc.IH[OF Suc.prems(1) this] show ?thesis .
  next
    assume \<open>\<exists>xit \<in> set (xslots G xs (xiter G xs t)). j \<in> ximg (iprods G ! p) xit\<close>
    then obtain xit where xit: \<open>xit \<in> set (xslots G xs (xiter G xs t))\<close>
      and jimg: \<open>j \<in> ximg (iprods G ! p) xit\<close> by blast
    obtain pr' m' R' where xeq: \<open>xit = (pr', m', R')\<close> by (cases xit) auto
    obtain A rhs where pr': \<open>pr' = (A, rhs)\<close> by (cases pr')
    from jimg have m_lt: \<open>m' < length rhs\<close>
      and nxt: \<open>fst (rhs ! m') = Nt (fst (iprods G ! p))\<close>
      and jsat: \<open>\<exists>i \<in> irep_set R'. irel_sat (snd (rhs ! m')) j i\<close>
      unfolding xeq pr' by (auto split: if_splits)
    from jsat obtain i where iR: \<open>i \<in> irep_set R'\<close> by blast
    have src: \<open>(pr', m') \<in> set (creach G s)\<close>
      using xit
    proof (rule xslots_memE)
      assume \<open>xit \<in> set xs\<close>
      then have memxs: \<open>(pr', m', R') \<in> set xs\<close> using xeq by simp
      have \<open>(pr', m') \<in> set s\<close> using kern[OF memxs] iR by auto
      then show ?thesis using creach_superset by (auto simp: creach_def creach_funpow_mono)
    next
      fix q assume q: \<open>q < length (iprods G)\<close> and \<open>q < length (xiter G xs t)\<close>
        and xq: \<open>xit = (iprods G ! q, 0, xiter G xs t ! q)\<close>
      have pq: \<open>pr' = iprods G ! q\<close> and mq: \<open>m' = 0\<close>
        and Rq: \<open>R' = xiter G xs t ! q\<close> using xq xeq by auto
      have \<open>i \<in> irep_set (xiter G xs t ! q)\<close> using iR Rq by simp
      from Suc.IH[OF q this] show ?thesis unfolding pq mq by simp
    qed
    have m_lt': \<open>m' < length (snd pr')\<close> using m_lt pr' by simp
    have nxt': \<open>fst (snd pr' ! m') = Nt (fst (iprods G ! p))\<close> using nxt pr' by simp
    have prp: \<open>iprods G ! p \<in> set (iprods G)\<close> using Suc.prems(1) by simp
    from creach_emit[OF src m_lt' nxt' prp] show ?thesis .
  qed
qed

theorem xclosure_auto_live_creach:
  assumes kern: \<open>\<And>pr m R. (pr, m, R) \<in> set xs \<Longrightarrow> irep_nonempty R \<Longrightarrow> (pr, m) \<in> set s\<close>
    and mem: \<open>(pr, m, R) \<in> set (xclosure_auto G xs)\<close>
    and jR: \<open>j \<in> irep_set R\<close>
  shows \<open>(pr, m) \<in> set (creach G s)\<close>
proof -
  have mem': \<open>(pr, m, R) \<in> set (xslots G xs (xiter G xs (xfuel G xs)))\<close>
    using mem unfolding xclosure_auto_def xclosure_def .
  show ?thesis
    using mem'
  proof (rule xslots_memE)
    assume mem2: \<open>(pr, m, R) \<in> set xs\<close>
    have \<open>(pr, m) \<in> set s\<close> using kern[OF mem2] jR by auto
    then show ?thesis using creach_superset by auto
  next
    fix q assume q: \<open>q < length (iprods G)\<close>
      and \<open>q < length (xiter G xs (xfuel G xs))\<close>
      and eq: \<open>(pr, m, R) = (iprods G ! q, 0, xiter G xs (xfuel G xs) ! q)\<close>
    have \<open>j \<in> irep_set (xiter G xs (xfuel G xs) ! q)\<close> using jR eq by simp
    from xiter_live_creach[OF kern q this] show ?thesis using eq by simp
  qed
qed

section \<open>The rigid-point conflict analysis\<close>

text \<open>Comparing the two sides of a candidate pair against a single shared
  state anchor is unsound for \<^const>\<open>mdet\<close>: a reduce-built frame pools
  entry anchors, and the two sides can be live via different ones.  The
  comparison is sound only where the entry anchor is \<open>rigid\<close>, a value both
  sides share: the column of a shifted token, or \<open>istart_ind\<close> at the start
  state.  So the analysis walks back from the pair's state through
  nonterminal (reduce-goto) entries of the precise automaton; over such an
  entry each side composes \<open>independently\<close> with a completed-production class
  of the predecessor's \<open>wreach\<close> (the sides need not pick the same instance),
  and \<^const>\<open>wdisjoint\<close> runs at every rigid entry reached.  The walk is a
  worklist over triples (state, class, class) in the finite algebra;
  exhausted fuel reports a conflict.\<close>

text \<open>The analysis runs over the \<^emph>\<open>merged\<close> automaton
  (\<^const>\<open>lr0_states\<close> with the \<^const>\<open>la_gtab\<close> gotos and the
  \<^const>\<open>la_fix\<close> cells): these are the driver's own tables, so a cell
  that licenses a runtime reduce is one of the cells inspected here.  A
  check over the precise automaton would miss the lookaheads that LALR
  merging pools into one state.\<close>

definition rstart :: \<open>('n, 't) is_cfg \<Rightarrow> 'n \<Rightarrow> nat\<close> where
  \<open>rstart G Shn = st_find (lr0_states G Shn) (lr0_start G Shn)\<close>

definition pin_edges :: \<open>(('n, 't) sym \<times> nat) list list \<Rightarrow> nat \<Rightarrow>
    (nat \<times> ('n, 't) sym) list\<close> where
  \<open>pin_edges gt s = concat (map (\<lambda>p.
       map (\<lambda>(X, s'). (p, X)) (filter (\<lambda>(X, s'). s' = s) (gt ! p)))
     [0..<length gt])\<close>

text \<open>The classes relating a predecessor's entry anchor to the anchor of an
  \<open>A\<close>-subtree reduced onto it: the anchor of a subtree is fixed when its
  dot-0 slot is predicted, so these are the \<open>dot-0\<close> classes of the
  \<open>A\<close>-productions in the predecessor's \<open>wreach\<close> (not the completed ones:
  the completion happens in a deeper state).\<close>

text \<open>All static reads below use \<^const>\<open>wreach\<close>, the form the saturation
  lemmas of this theory speak about.\<close>

definition rho_classes :: \<open>('n, 't) is_cfg \<Rightarrow> ('n, 't) citem list list \<Rightarrow> nat \<Rightarrow> 'n \<Rightarrow> wrel list\<close> where
  \<open>rho_classes G sts p A = remdups (List.map_filter
      (\<lambda>(pr, m, \<rho>). if fst pr = A \<and> m = 0 then Some \<rho> else None)
      (wreach G (sts ! p)))\<close>

text \<open>A nonterminal \<open>A\<close> is \<open>anchored\<close> when every \<open>A\<close>-production starts with
  an \<open>Eq\<close>-related element that is a terminal or itself an anchored
  nonterminal: any tree of \<open>A\<close> then admits exactly one anchor, the column of
  its leftmost token (cf. the \<open>anchored\<close>/\<open>lead_refl\<close> analysis of
  \<open>Indentation_Sensitive\<close> section 4).  A reduce-goto over an anchored
  nonterminal therefore carries a \<open>rigid\<close> entry anchor, a token column
  shared by both sides of a pair, and the \<^const>\<open>wdisjoint\<close> comparison
  is sound there, as at a shift entry.  Computed as a decreasing fixpoint
  from the full nonterminal list.\<close>

definition anchored_nts :: \<open>('n, 't) is_cfg \<Rightarrow> 'n list\<close> where
  \<open>anchored_nts G = (let nts = remdups (map fst (iprods G));
       ok = (\<lambda>S (B, rhs). rhs \<noteq> [] \<and> snd (hd rhs) = Eq \<and>
               (case fst (hd rhs) of Tm _ \<Rightarrow> True | Nt B' \<Rightarrow> B' \<in> set S));
       step = (\<lambda>S. filter (\<lambda>A. list_all (\<lambda>p. fst p \<noteq> A \<or> ok S p) (iprods G)) S)
   in (step ^^ length nts) nts)\<close>

fun rfire :: \<open>('n, 't) is_cfg \<Rightarrow> nat \<Rightarrow> ('n, 't) citem list list \<Rightarrow>
    (('n, 't) sym \<times> nat) list list \<Rightarrow> 'n list \<Rightarrow> nat \<Rightarrow>
    (nat \<times> wrel \<times> wrel) list \<Rightarrow> (nat \<times> wrel \<times> wrel) list \<Rightarrow> bool\<close> where
  \<open>rfire G i\<^sub>0 sts gt anc 0 seen work = True\<close>
| \<open>rfire G i\<^sub>0 sts gt anc (Suc n) seen [] = False\<close>
| \<open>rfire G i\<^sub>0 sts gt anc (Suc n) seen ((i, \<sigma>\<^sub>1, \<sigma>\<^sub>2) # wk) =
     (let ins = pin_edges gt i;
          rigid_in = (\<lambda>(p, X). case X of Tm _ \<Rightarrow> True | Nt A \<Rightarrow> A \<in> set anc);
          rigid = (i = i\<^sub>0 \<or> list_ex rigid_in ins)
      in if rigid \<and> \<not> wdisjoint \<sigma>\<^sub>1 \<sigma>\<^sub>2 then True
         else
           (let succs = concat (map (\<lambda>(p, X). case X of
                  Tm _ \<Rightarrow> []
                | Nt A \<Rightarrow> (if A \<in> set anc then [] else
                    concat (map (\<lambda>\<rho>\<^sub>1. List.map_filter (\<lambda>\<rho>\<^sub>2.
                     let t = (p, wcomp (winv \<rho>\<^sub>1) \<sigma>\<^sub>1, wcomp (winv \<rho>\<^sub>2) \<sigma>\<^sub>2)
                     in if t \<in> set seen \<or> t \<in> set wk then None else Some t)
                     (rho_classes G sts p A)) (rho_classes G sts p A)))) ins)
            in rfire G i\<^sub>0 sts gt anc n ((i, \<sigma>\<^sub>1, \<sigma>\<^sub>2) # seen) (remdups succs @ wk)))\<close>

text \<open>The check pairs the two automata: the \<^emph>\<open>precise\<close> one
  (\<^const>\<open>pr0_states\<close>/\<^const>\<open>pgtab\<close>) separates contexts (which
  completed items can co-occur in a reachable frame), while the
  \<^emph>\<open>merged\<close> cells (\<^const>\<open>la_fix\<close> at the \<^const>\<open>lr0_states\<close>
  index) are what licenses the driver's reduces.  Product states are the
  reachable (precise, merged) index pairs along shared symbol paths.\<close>

definition p0start :: \<open>('n, 't) is_cfg \<Rightarrow> 'n \<Rightarrow> nat\<close> where
  \<open>p0start G Shn = st_find (pr0_states G Shn) (lr0_start G Shn)\<close>

definition xprod_succs :: \<open>(('n, 't) sym \<times> nat) list list \<Rightarrow> (('n, 't) sym \<times> nat) list list \<Rightarrow>
    nat \<times> nat \<Rightarrow> (('n, 't) sym \<times> nat \<times> nat) list\<close> where
  \<open>xprod_succs gp gm = (\<lambda>(p, m).
     if p < length gp \<and> m < length gm
     then List.map_filter (\<lambda>(X, p'). case map_of (gm ! m) X of
            Some m' \<Rightarrow> Some (X, (p', m')) | None \<Rightarrow> None) (gp ! p)
     else [])\<close>

definition prod_succs :: \<open>(('n, 't) sym \<times> nat) list list \<Rightarrow> (('n, 't) sym \<times> nat) list list \<Rightarrow>
    nat \<times> nat \<Rightarrow> (nat \<times> nat) list\<close> where
  \<open>prod_succs gp gm x = map snd (xprod_succs gp gm x)\<close>

fun prod_bfs :: \<open>(('n, 't) sym \<times> nat) list list \<Rightarrow> (('n, 't) sym \<times> nat) list list \<Rightarrow>
    nat \<Rightarrow> (nat \<times> nat) list \<Rightarrow> (nat \<times> nat) list \<Rightarrow> (nat \<times> nat) list\<close> where
  \<open>prod_bfs gp gm 0 seen wk = seen @ wk\<close>
| \<open>prod_bfs gp gm (Suc n) seen [] = seen\<close>
| \<open>prod_bfs gp gm (Suc n) seen (x # wk) =
     (let succs = filter (\<lambda>t. t \<notin> set seen \<and> t \<notin> set (x # wk)) (prod_succs gp gm x)
      in prod_bfs gp gm n (x # seen) (remdups succs @ wk))\<close>

definition mprod_states :: \<open>('n, 't) is_cfg \<Rightarrow> 'n \<Rightarrow> (nat \<times> nat) list\<close> where
  \<open>mprod_states G Shn = (let sp = pr0_states G Shn; sm = lr0_states G Shn;
       gp = pgtab G sp; gm = la_gtab G sm
     in prod_bfs gp gm (Suc ((length sp + 1) * (length sm + 1))) []
          [(p0start G Shn, rstart G Shn)])\<close>

text \<open>Correctness of the bounded product search: everything enqueued ends up
  in the result, and with fuel exceeding the pair universe the result is
  closed under \<^const>\<open>prod_succs\<close>.\<close>

lemma prod_bfs_superset:
  \<open>set seen \<union> set wk \<subseteq> set (prod_bfs gp gm n seen wk)\<close>
  by (induction gp gm n seen wk rule: prod_bfs.induct)
     (auto simp: Let_def)

lemma prod_succs_bound:
  assumes \<open>\<And>p X p'. p < length gp \<Longrightarrow> (X, p') \<in> set (gp ! p) \<Longrightarrow> p' \<le> P\<close>
    and \<open>\<And>m X m'. m < length gm \<Longrightarrow> (X, m') \<in> set (gm ! m) \<Longrightarrow> m' \<le> M\<close>
  shows \<open>set (prod_succs gp gm x) \<subseteq> {..P} \<times> {..M}\<close>
proof
  fix y assume y: \<open>y \<in> set (prod_succs gp gm x)\<close>
  obtain p m where x: \<open>x = (p, m)\<close> by (cases x)
  have lt: \<open>p < length gp\<close> \<open>m < length gm\<close>
    using y unfolding x prod_succs_def xprod_succs_def by (auto split: if_splits)
  obtain X p' m' where y': \<open>y = (p', m')\<close>
    and gp: \<open>(X, p') \<in> set (gp ! p)\<close> and gm: \<open>map_of (gm ! m) X = Some m'\<close>
    using y lt unfolding x prod_succs_def xprod_succs_def
    by (fastforce simp: List.map_filter_def split: option.splits)
  from map_of_SomeD[OF gm] have \<open>(X, m') \<in> set (gm ! m)\<close> .
  with assms gp lt show \<open>y \<in> {..P} \<times> {..M}\<close> unfolding y' by auto
qed

lemma prod_bfs_closed:
  assumes \<open>\<forall>x \<in> set seen. set (prod_succs gp gm x) \<subseteq> set seen \<union> set wk\<close>
    and \<open>distinct (seen @ wk)\<close>
    and \<open>set seen \<union> set wk \<subseteq> U\<close>
    and \<open>\<And>x. set (prod_succs gp gm x) \<subseteq> U\<close>
    and \<open>finite U\<close>
    and \<open>card U < n + card (set seen)\<close>
  shows \<open>\<forall>x \<in> set (prod_bfs gp gm n seen wk).
           set (prod_succs gp gm x) \<subseteq> set (prod_bfs gp gm n seen wk)\<close>
  using assms
proof (induction gp gm n seen wk rule: prod_bfs.induct)
  case (1 gp gm seen wk)
  have \<open>card (set seen) \<le> card U\<close> using 1 by (intro card_mono) auto
  with 1 show ?case by simp
next
  case (2 gp gm n seen)
  then show ?case by simp
next
  case (3 gp gm n seen x wk)
  define succs where
    \<open>succs = filter (\<lambda>t. t \<notin> set seen \<and> t \<notin> set (x # wk)) (prod_succs gp gm x)\<close>
  have res: \<open>prod_bfs gp gm (Suc n) seen (x # wk) =
             prod_bfs gp gm n (x # seen) (remdups succs @ wk)\<close>
    by (simp add: Let_def succs_def)
  have x_new: \<open>x \<notin> set seen\<close> \<open>x \<notin> set wk\<close> \<open>distinct seen\<close> \<open>distinct wk\<close>
    using "3.prems"(2) by auto
  have cov': \<open>\<forall>y \<in> set (x # seen).
      set (prod_succs gp gm y) \<subseteq> set (x # seen) \<union> set (remdups succs @ wk)\<close>
  proof
    fix y assume \<open>y \<in> set (x # seen)\<close>
    then consider \<open>y = x\<close> | \<open>y \<in> set seen\<close> by auto
    then show \<open>set (prod_succs gp gm y) \<subseteq> set (x # seen) \<union> set (remdups succs @ wk)\<close>
    proof cases
      case 1
      show ?thesis
      proof
        fix t assume t: \<open>t \<in> set (prod_succs gp gm y)\<close>
        show \<open>t \<in> set (x # seen) \<union> set (remdups succs @ wk)\<close>
        proof (cases \<open>t \<in> set seen \<or> t \<in> set (x # wk)\<close>)
          case True then show ?thesis by auto
        next
          case False
          then have \<open>t \<in> set succs\<close> using t 1 unfolding succs_def by auto
          then show ?thesis by auto
        qed
      qed
    next
      case 2
      then have \<open>set (prod_succs gp gm y) \<subseteq> set seen \<union> set (x # wk)\<close>
        using "3.prems"(1) by auto
      then show ?thesis by auto
    qed
  qed
  have dist': \<open>distinct ((x # seen) @ (remdups succs @ wk))\<close>
    using "3.prems"(2) unfolding succs_def by auto
  have inU': \<open>set (x # seen) \<union> set (remdups succs @ wk) \<subseteq> U\<close>
    using "3.prems"(3) "3.prems"(4)[of x] unfolding succs_def by auto
  have card': \<open>card U < n + card (set (x # seen))\<close>
    using "3.prems"(6) x_new(1) by (simp add: card_insert_if)
  from "3.IH"[OF succs_def cov' dist' inU' "3.prems"(4) "3.prems"(5) card'] res
  show ?case by simp
qed

lemma pgtab_target_le:
  assumes \<open>p < length (pgtab G sp)\<close> and \<open>(X, p') \<in> set (pgtab G sp ! p)\<close>
  shows \<open>p' \<le> length sp\<close>
proof -
  have \<open>length (pgtab G sp) = length sp\<close> unfolding pgtab_def by simp
  with assms have \<open>(X, p') \<in> set (map (\<lambda>X. (X, st_find sp (cgoto (creach G (sp ! p)) X)))
      (remdups (concat (map (\<lambda>(pr, m).
         if m < length (snd pr) then [fst (snd pr ! m)] else [])
        (creach G (sp ! p))))))\<close>
    unfolding pgtab_def by (simp add: Let_def)
  then obtain Y where \<open>p' = st_find sp (cgoto (creach G (sp ! p)) Y)\<close> by auto
  then show ?thesis using st_find_le by simp
qed

lemma la_gtab_target_le:
  assumes \<open>m < length (la_gtab G sm)\<close> and \<open>(X, m') \<in> set (la_gtab G sm ! m)\<close>
  shows \<open>m' \<le> length sm\<close>
proof -
  have \<open>length (la_gtab G sm) = length sm\<close> unfolding la_gtab_def by simp
  with assms have \<open>(X, m') \<in> set (map (\<lambda>X. (X, st_find sm (cgoto (cclosure G (sm ! m)) X)))
      (remdups (concat (map (\<lambda>(pr, m).
         if m < length (snd pr) then [fst (snd pr ! m)] else [])
        (cclosure G (sm ! m))))))\<close>
    unfolding la_gtab_def by (simp add: Let_def)
  then obtain Y where \<open>m' = st_find sm (cgoto (cclosure G (sm ! m)) Y)\<close> by auto
  then show ?thesis using st_find_le by simp
qed

theorem mprod_states_start:
  \<open>(p0start G Shn, rstart G Shn) \<in> set (mprod_states G Shn)\<close>
  unfolding mprod_states_def Let_def
  using prod_bfs_superset by fastforce

theorem mprod_states_closed:
  assumes mem: \<open>x \<in> set (mprod_states G Shn)\<close>
    and succ: \<open>y \<in> set (prod_succs (pgtab G (pr0_states G Shn))
                 (la_gtab G (lr0_states G Shn)) x)\<close>
  shows \<open>y \<in> set (mprod_states G Shn)\<close>
proof -
  let ?gp = \<open>pgtab G (pr0_states G Shn)\<close> and ?gm = \<open>la_gtab G (lr0_states G Shn)\<close>
  let ?U = \<open>{..length (pr0_states G Shn)} \<times> {..length (lr0_states G Shn)}\<close>
  have succsU: \<open>set (prod_succs ?gp ?gm x) \<subseteq> ?U\<close> for x
    by (rule prod_succs_bound) (auto elim: pgtab_target_le la_gtab_target_le)
  have startU: \<open>(p0start G Shn, rstart G Shn) \<in> ?U\<close>
    unfolding p0start_def rstart_def using st_find_le by auto
  have cardU: \<open>card ?U = (length (pr0_states G Shn) + 1) * (length (lr0_states G Shn) + 1)\<close>
    by (simp add: card_cartesian_product)
  have \<open>\<forall>x \<in> set (mprod_states G Shn). set (prod_succs ?gp ?gm x) \<subseteq> set (mprod_states G Shn)\<close>
    unfolding mprod_states_def Let_def
    by (rule prod_bfs_closed[where U = \<open>?U\<close>])
       (use succsU startU cardU in \<open>auto simp: card_cartesian_product\<close>)
  with mem succ show ?thesis by blast
qed

text \<open>Reduce seeds at a product state: one entry per merged cell of a
  production that is completed \<^emph>\<open>in the precise closure\<close> (its
  \<^const>\<open>wreach\<close> instances supply the classes to the precise state's
  entry anchor).  A completed production the precise context excludes seeds
  nothing; the runtime's anchor filtering excludes it dynamically.\<close>

definition rreds_at :: \<open>('n, 't) is_cfg \<Rightarrow> 'n \<Rightarrow> ('n, 't) citem list list \<Rightarrow>
    ('n, 't) lacell list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> (('n \<times> ('n, 't) rhs) \<times> 't option \<times> wrel) list\<close> where
  \<open>rreds_at G Shn sp L i\<^sub>p i\<^sub>m =
     (let ws = wreach G (sp ! i\<^sub>p)
      in concat (map (\<lambda>(i', (pr, m), t, \<tau>).
           if i' = i\<^sub>m \<and> m = length (snd pr) \<and> fst pr \<noteq> Shn
           then map (\<lambda>(pr', m', \<rho>). (pr, t, wcomp (winv \<rho>) \<tau>))
                  (filter (\<lambda>(pr', m', \<rho>). pr' = pr \<and> m' = m) ws)
           else []) L))\<close>

definition rr_none_at :: \<open>('n, 't) is_cfg \<Rightarrow> 'n \<Rightarrow> ('n, 't) citem list list \<Rightarrow>
    ('n, 't) lacell list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool\<close> where
  \<open>rr_none_at G Shn sp L i\<^sub>p i\<^sub>m =
     (let reds = rreds_at G Shn sp L i\<^sub>p i\<^sub>m
      in list_ex (\<lambda>(pr, t, \<tau>). t = None \<and>
           list_ex (\<lambda>(pr', t', \<tau>'). pr' \<noteq> pr \<and> t' = None) reds) reds)\<close>

definition rpairs_at :: \<open>('n, 't) is_cfg \<Rightarrow> 'n \<Rightarrow> ('n, 't) citem list list \<Rightarrow>
    ('n, 't) lacell list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> (wrel \<times> wrel) list\<close> where
  \<open>rpairs_at G Shn sp L i\<^sub>p i\<^sub>m =
     (let reds = rreds_at G Shn sp L i\<^sub>p i\<^sub>m;
          shifts = shift_cells (wreach G (sp ! i\<^sub>p));
          srs = concat (map (\<lambda>(pr, t, \<tau>). case t of
              Some a \<Rightarrow> map (\<lambda>(a', \<tau>'). (\<tau>, \<tau>')) (filter (\<lambda>(a', \<tau>'). a' = a) shifts)
            | None \<Rightarrow> []) reds);
          rrs = concat (map (\<lambda>(pr, t, \<tau>). List.map_filter (\<lambda>(pr', t', \<tau>').
                 if pr' \<noteq> pr \<and> t' = t \<and> t \<noteq> None then Some (\<tau>, \<tau>') else None) reds) reds)
      in remdups (srs @ rrs))\<close>

definition rlalr_conflict_at :: \<open>('n, 't) is_cfg \<Rightarrow> 'n \<Rightarrow> ('n, 't) citem list list \<Rightarrow>
    ('n, 't) lacell list \<Rightarrow> nat \<times> nat \<Rightarrow> bool\<close> where
  \<open>rlalr_conflict_at G Shn sp L pm \<longleftrightarrow> (case pm of (i\<^sub>p, i\<^sub>m) \<Rightarrow>
     rr_none_at G Shn sp L i\<^sub>p i\<^sub>m \<or>
     list_ex (\<lambda>(\<sigma>\<^sub>1, \<sigma>\<^sub>2). rfire G (p0start G Shn) sp (pgtab G sp) (anchored_nts G)
         (Suc (length sp * 36 + length sp)) [] [(i\<^sub>p, \<sigma>\<^sub>1, \<sigma>\<^sub>2)])
       (rpairs_at G Shn sp L i\<^sub>p i\<^sub>m))\<close>

definition rlalr_conflicts :: \<open>('n, 't) is_cfg \<Rightarrow> 'n \<Rightarrow> (nat \<times> nat) list\<close> where
  \<open>rlalr_conflicts G Shn = (let sp = pr0_states G Shn; L = la_fix G Shn in
     filter (rlalr_conflict_at G Shn sp L) (mprod_states G Shn))\<close>

section \<open>From a determinism violation to concrete witnesses\<close>

text \<open>Eliminations for the sufficiency proof: the negation of
  \<^const>\<open>mdet\<close> yields concrete witnesses, the cell that licensed each
  reduce candidate and the closure item and anchor that keep each successor
  alive.\<close>

lemma liveE:
  assumes \<open>live xs\<close>
  obtains pr m R j where \<open>(pr, m, R) \<in> set xs\<close> and \<open>j \<in> irep_set R\<close>
  using assms that unfolding live_def
  by (fastforce simp: list_ex_iff)

lemma dliveE:
  assumes \<open>dlive (Xs, w)\<close>
  obtains pr m R j where \<open>Xs \<noteq> []\<close> and \<open>(pr, m, R) \<in> set (hd Xs)\<close>
    and \<open>j \<in> irep_set R\<close>
  using assms that unfolding dlive_def by (auto elim: liveE)

lemma dlicE:
  assumes \<open>dlic i cells ((a, c) # w') pr RS\<close>
  obtains \<tau> where \<open>(i, (pr, length (snd pr)), Some a, \<tau>) \<in> set cells\<close>
    and \<open>irep_ex_wsat \<tau> c RS\<close>
  using assms that unfolding dlic_def by (fastforce simp: list_ex_iff)

lemma dlic_NilE:
  assumes \<open>dlic i cells [] pr RS\<close>
  obtains \<tau> where \<open>(i, (pr, length (snd pr)), None, \<tau>) \<in> set cells\<close>
  using assms that unfolding dlic_def by (fastforce simp: list_ex_iff)

text \<open>A live shift successor yields a closure item with the shifted terminal
  at its dot and an anchor compatible with the token's column.\<close>

lemma shift_live_srcE:
  assumes step: \<open>mstep_cached G cstk (Xs, w) DShift = Some gc'\<close>
    and live: \<open>dlive gc'\<close>
  obtains a c w' pr m R j where
    \<open>w = (a, c) # w'\<close>
    and \<open>(pr, m, R) \<in> set (hd cstk)\<close>
    and \<open>m < length (snd pr)\<close>
    and \<open>fst (snd pr ! m) = Tm a\<close>
    and \<open>j \<in> irep_set R\<close>
    and \<open>irel_sat (snd (snd pr ! m)) c j\<close>
proof -
  from step obtain a c w' where
    w: \<open>w = (a, c) # w'\<close> and Xs_ne: \<open>Xs \<noteq> []\<close>
    and gc': \<open>gc' = (lgoto (hd cstk) (Tm a) (FinRep [c]) # Xs, w')\<close>
    by (rule mstep_shift_shape)
  from live obtain pr m' R' j where
    itm: \<open>(pr, m', R') \<in> set (lgoto (hd cstk) (Tm a) (FinRep [c]))\<close>
    and jR': \<open>j \<in> irep_set R'\<close>
    unfolding gc' by (auto elim: dliveE)
  obtain m where m': \<open>m' = Suc m\<close> using lgoto_dot_pos[OF itm] by (cases m') auto
  from lgoto_kernel_step[OF itm[unfolded m']] obtain R where
    src: \<open>(pr, m, R) \<in> set (hd cstk)\<close> and m_lt: \<open>m < length (snd pr)\<close>
    and sym: \<open>fst (snd pr ! m) = Tm a\<close>
    and R': \<open>R' = irep_inter R (irep_pre (snd (snd pr ! m)) (FinRep [c]))\<close> .
  have jR: \<open>j \<in> irep_set R\<close> and jrel: \<open>irel_sat (snd (snd pr ! m)) c j\<close>
    using jR' unfolding R' by auto
  from that[OF w src m_lt sym jR jrel] show thesis .
qed

section \<open>Tracking a reachable configuration in the product automaton\<close>

text \<open>The dynamic half of the sufficiency argument: every reachable stack is
  tracked, frame by frame, by a stack of precise indices, each paired with
  the frame's merged index in \<^const>\<open>mprod_states\<close>.  A frame owes its
  obligations only where it has a \<open>live\<close> (anchored) item: a dead frame never
  contributes a candidate, and by \<open>xclosure_auto_live_creach\<close> over
  the empty kernel a dead kernel has a dead closure.\<close>

definition lcore :: \<open>('n, 't) xitem list \<Rightarrow> ('n, 't) citem set\<close> where
  \<open>lcore xs = {(pr, m) | pr m R. (pr, m, R) \<in> set xs \<and> irep_nonempty R}\<close>

lemma lcoreI: \<open>(pr, m, R) \<in> set xs \<Longrightarrow> j \<in> irep_set R \<Longrightarrow> (pr, m) \<in> lcore xs\<close>
  unfolding lcore_def by (cases pr) auto

lemma lcore_sub_ccore: \<open>lcore xs \<subseteq> set (ccore xs)\<close>
  unfolding lcore_def ccore_def by force

lemma lcore_subD:
  \<open>lcore xs \<subseteq> S \<Longrightarrow> (pr, m, R) \<in> set xs \<Longrightarrow> j \<in> irep_set R \<Longrightarrow> (pr, m) \<in> S\<close>
  using lcoreI by blast

lemma lcore_subD_ne:
  \<open>lcore xs \<subseteq> S \<Longrightarrow> (pr, m, R) \<in> set xs \<Longrightarrow> irep_nonempty R \<Longrightarrow> (pr, m) \<in> S\<close>
  unfolding irep_nonempty_correct using lcore_subD by blast

lemma creach_Nil [simp]: \<open>set (creach G []) = {}\<close>
proof -
  have \<open>set ((creach_step G ^^ k) []) = {}\<close> for k
    by (induction k) (auto simp: creach_step_set)
  then show ?thesis unfolding creach_def by blast
qed

text \<open>A closure with an anchored item sits on a live kernel: by
  \<^text>\<open>xclosure_auto_live_creach\<close> the item's core would otherwise lie in
  the reachable closure of the empty kernel.\<close>

lemma closure_live_kernel:
  assumes mem: \<open>(pr, m, R) \<in> set (xclosure_auto G xs)\<close> and jR: \<open>j \<in> irep_set R\<close>
  shows \<open>lcore xs \<noteq> {}\<close>
proof
  assume dead: \<open>lcore xs = {}\<close>
  have kern: \<open>\<And>pr' m' R'. (pr', m', R') \<in> set xs \<Longrightarrow> irep_nonempty R' \<Longrightarrow>
      (pr', m') \<in> set []\<close>
    using dead by (auto simp: lcore_def)
  from xclosure_auto_live_creach[OF kern mem jR]
  have \<open>(pr, m) \<in> set (creach G [])\<close> .
  then show False by simp
qed

definition mtrack :: \<open>('n, 't) is_cfg \<Rightarrow> 'n \<Rightarrow> ('n, 't) xitem list list \<Rightarrow> nat list \<Rightarrow> bool\<close> where
  \<open>mtrack G Shn Xs pstk \<longleftrightarrow> length pstk = length Xs \<and>
     (\<forall>k < length Xs. lcore (Xs ! k) \<noteq> {} \<longrightarrow>
        pstk ! k < length (pr0_states G Shn) \<and>
        lcore (Xs ! k) \<subseteq> set (pr0_states G Shn ! (pstk ! k)) \<and>
        (pstk ! k, st_find (lr0_states G Shn) (ccore (Xs ! k)))
          \<in> set (mprod_states G Shn))\<close>

lemma mtrack_len [simp]: \<open>mtrack G Shn Xs pstk \<Longrightarrow> length pstk = length Xs\<close>
  unfolding mtrack_def by blast

lemma mtrackD:
  \<open>mtrack G Shn Xs pstk \<Longrightarrow> k < length Xs \<Longrightarrow> lcore (Xs ! k) \<noteq> {} \<Longrightarrow>
     pstk ! k < length (pr0_states G Shn) \<and>
     lcore (Xs ! k) \<subseteq> set (pr0_states G Shn ! (pstk ! k)) \<and>
     (pstk ! k, st_find (lr0_states G Shn) (ccore (Xs ! k))) \<in> set (mprod_states G Shn)\<close>
  unfolding mtrack_def by blast

lemma dot_sym_gram:
  assumes univ: \<open>set cs \<subseteq> cuniv G Shn\<close>
    and mem: \<open>(pr, m) \<in> set cs\<close> and m: \<open>m < length (snd pr)\<close>
  shows \<open>fst (snd pr ! m) \<in> set (gram_syms G)\<close>
proof (cases \<open>pr = start_prod G Shn\<close>)
  case True
  then show ?thesis using m by (simp add: start_prod_def gram_syms_def)
next
  case False
  then have \<open>pr \<in> set (iprods G)\<close> using univ mem unfolding cuniv_def by auto
  then obtain A rhs where preq: \<open>pr = (A, rhs)\<close> and Ar: \<open>(A, rhs) \<in> set (iprods G)\<close>
    by (metis prod.collapse)
  moreover have \<open>rhs ! m \<in> set rhs\<close> using m preq by simp
  ultimately show ?thesis unfolding gram_syms_def by force
qed

lemma pgtab_len [simp]: \<open>length (pgtab G sp) = length sp\<close>
  unfolding pgtab_def by simp

lemma pgtab_mem:
  assumes p: \<open>p < length sp\<close>
    and mem: \<open>(pr, m) \<in> set (creach G (sp ! p))\<close> and m: \<open>m < length (snd pr)\<close>
  shows \<open>(fst (snd pr ! m),
          st_find sp (cgoto (creach G (sp ! p)) (fst (snd pr ! m))))
         \<in> set (pgtab G sp ! p)\<close>
proof -
  let ?f = \<open>\<lambda>(pr, m). if m < length (snd pr) then [fst (snd pr ! m)] else []\<close>
  have h1: \<open>fst (snd pr ! m) \<in> set (?f (pr, m))\<close> using m by simp
  have \<open>fst (snd pr ! m) \<in> \<Union> (set ` ?f ` set (creach G (sp ! p)))\<close>
    using h1 mem by blast
  then have \<open>fst (snd pr ! m) \<in> set (concat (map ?f (creach G (sp ! p))))\<close>
    by simp
  then show ?thesis unfolding pgtab_def using p by (simp add: Let_def)
qed

lemma prod_succsI:
  \<open>p < length gp \<Longrightarrow> m < length gm \<Longrightarrow> (X, p') \<in> set (gp ! p) \<Longrightarrow>
   map_of (gm ! m) X = Some m' \<Longrightarrow> (p', m') \<in> set (prod_succs gp gm (p, m))\<close>
  unfolding prod_succs_def xprod_succs_def
  by (force simp: List.map_filter_def)

text \<open>One goto step from a tracked frame: if the goto frame has a live item,
  the source frame does too, the goto lands in the precise successor state,
  and the product pair advances by \<^const>\<open>prod_succs\<close>.\<close>

lemma mtrack_goto:
  fixes f :: \<open>('n, 't) xitem list\<close> and G :: \<open>('n, 't) is_cfg\<close> and Shn :: 'n
    and p :: nat and X :: \<open>('n, 't) sym\<close> and RA :: indrep
  defines CL_def: \<open>CL \<equiv> xclosure_auto G f\<close>
  defines sp_def: \<open>sp \<equiv> pr0_states G Shn\<close> and sm_def: \<open>sm \<equiv> lr0_states G Shn\<close>
  defines p'_def: \<open>p' \<equiv> st_find sp (cgoto (creach G (sp ! p)) X)\<close>
  assumes cores: \<open>\<exists>s \<in> set sm. set (ccore f) = set s\<close>
    and trk: \<open>lcore f \<noteq> {} \<Longrightarrow>
        p < length sp \<and> lcore f \<subseteq> set (sp ! p) \<and>
        (p, st_find sm (ccore f)) \<in> set (mprod_states G Shn)\<close>
    and live': \<open>lcore (lgoto CL X RA) \<noteq> {}\<close>
  shows \<open>p' < length sp \<and>
         lcore (lgoto CL X RA) \<subseteq> set (sp ! p') \<and>
         (p', st_find sm (ccore (lgoto CL X RA))) \<in> set (mprod_states G Shn)\<close>
proof -
  from live' obtain pr\<^sub>0 n\<^sub>0 R\<^sub>0' j\<^sub>0 where
    g0: \<open>(pr\<^sub>0, n\<^sub>0, R\<^sub>0') \<in> set (lgoto CL X RA)\<close> and j0: \<open>j\<^sub>0 \<in> irep_set R\<^sub>0'\<close>
    unfolding lcore_def by auto
  obtain m\<^sub>0 where n0: \<open>n\<^sub>0 = Suc m\<^sub>0\<close> using lgoto_dot_pos[OF g0] by (cases n\<^sub>0) auto
  from lgoto_kernel_step[OF g0[unfolded n0]] obtain R\<^sub>0 where
    src0: \<open>(pr\<^sub>0, m\<^sub>0, R\<^sub>0) \<in> set CL\<close> and m0_lt: \<open>m\<^sub>0 < length (snd pr\<^sub>0)\<close>
    and X0: \<open>fst (snd pr\<^sub>0 ! m\<^sub>0) = X\<close>
    and R0': \<open>R\<^sub>0' = irep_inter R\<^sub>0 (irep_pre (snd (snd pr\<^sub>0 ! m\<^sub>0)) RA)\<close> .
  have j0R0: \<open>j\<^sub>0 \<in> irep_set R\<^sub>0\<close> using j0 unfolding R0' by auto
  text \<open>The source frame is live: its closure has an anchored item.\<close>
  have f_live: \<open>lcore f \<noteq> {}\<close>
    by (rule closure_live_kernel[OF src0[unfolded CL_def] j0R0])
  from trk[OF f_live] have p_lt: \<open>p < length sp\<close>
    and cover: \<open>lcore f \<subseteq> set (sp ! p)\<close>
    and pair: \<open>(p, st_find sm (ccore f)) \<in> set (mprod_states G Shn)\<close> by auto
  have kern: \<open>\<And>pr m R. (pr, m, R) \<in> set f \<Longrightarrow> irep_nonempty R \<Longrightarrow> (pr, m) \<in> set (sp ! p)\<close>
    using cover by (fastforce simp: lcore_def)
  have src0_cr: \<open>(pr\<^sub>0, m\<^sub>0) \<in> set (creach G (sp ! p))\<close>
    by (rule xclosure_auto_live_creach[OF kern src0[unfolded CL_def] j0R0])
  have univ: \<open>set (creach G (sp ! p)) \<subseteq> cuniv G Shn\<close>
    by (rule creach_univ[OF pr0_states_univ[OF nth_mem[OF p_lt[unfolded sp_def]],
          folded sp_def]])
  have X_gram: \<open>X \<in> set (gram_syms G)\<close>
    using dot_sym_gram[OF univ src0_cr m0_lt] X0 by simp
  from pr0_states_closed[OF nth_mem[OF p_lt[unfolded sp_def]] X_gram]
  obtain t where t: \<open>t \<in> set (pr0_states G Shn)\<close>
    and teq: \<open>set t = set (cgoto (creach G (pr0_states G Shn ! p)) X)\<close> by blast
  from st_find_found[OF t teq]
  have p'_lt: \<open>p' < length sp\<close> and p'_set: \<open>set (sp ! p') = set (cgoto (creach G (sp ! p)) X)\<close>
    unfolding p'_def sp_def by auto
  text \<open>Every live item of the goto frame lands in the precise goto state.\<close>
  have cov': \<open>lcore (lgoto CL X RA) \<subseteq> set (sp ! p')\<close>
  proof
    fix c assume \<open>c \<in> lcore (lgoto CL X RA)\<close>
    then obtain pr\<^sub>2 n\<^sub>2 R\<^sub>2' where ceq: \<open>c = (pr\<^sub>2, n\<^sub>2)\<close>
      and g2: \<open>(pr\<^sub>2, n\<^sub>2, R\<^sub>2') \<in> set (lgoto CL X RA)\<close>
      and ne2: \<open>irep_nonempty R\<^sub>2'\<close>
      unfolding lcore_def by blast
    obtain j\<^sub>2 where j2: \<open>j\<^sub>2 \<in> irep_set R\<^sub>2'\<close> using ne2 by auto
    obtain m\<^sub>2 where n2: \<open>n\<^sub>2 = Suc m\<^sub>2\<close> using lgoto_dot_pos[OF g2] by (cases n\<^sub>2) auto
    from lgoto_kernel_step[OF g2[unfolded n2]] obtain R\<^sub>2 where
      src2: \<open>(pr\<^sub>2, m\<^sub>2, R\<^sub>2) \<in> set CL\<close> and m2_lt: \<open>m\<^sub>2 < length (snd pr\<^sub>2)\<close>
      and X2: \<open>fst (snd pr\<^sub>2 ! m\<^sub>2) = X\<close>
      and R2': \<open>R\<^sub>2' = irep_inter R\<^sub>2 (irep_pre (snd (snd pr\<^sub>2 ! m\<^sub>2)) RA)\<close> .
    have j2R2: \<open>j\<^sub>2 \<in> irep_set R\<^sub>2\<close> using j2 unfolding R2' by auto
    have \<open>(pr\<^sub>2, m\<^sub>2) \<in> set (creach G (sp ! p))\<close>
      by (rule xclosure_auto_live_creach[OF kern src2[unfolded CL_def] j2R2])
    from cgoto_memI[OF this m2_lt X2] show \<open>c \<in> set (sp ! p')\<close>
      unfolding ceq n2 p'_set by simp
  qed
  text \<open>The product pair advances.\<close>
  define m where \<open>m \<equiv> st_find sm (ccore f)\<close>
  from cores obtain s where s: \<open>s \<in> set sm\<close> and seq: \<open>set (ccore f) = set s\<close> by blast
  from st_find_found[OF s[unfolded sm_def] seq[symmetric]]
  have m_lt: \<open>m < length sm\<close> and m_set: \<open>set (sm ! m) = set (ccore f)\<close>
    unfolding m_def sm_def by auto
  have core_cl: \<open>(pr\<^sub>0, m\<^sub>0) \<in> set (cclosure G (sm ! m))\<close>
  proof -
    have \<open>(pr\<^sub>0, m\<^sub>0) \<in> set (ccore CL)\<close> using src0 unfolding ccore_def by force
    also have \<open>set (ccore CL) = set (cclosure G (ccore f))\<close>
      unfolding CL_def by (rule set_ccore_xclosure_auto)
    also have \<open>\<dots> = set (cclosure G (sm ! m))\<close>
      by (rule set_cclosure_cong[OF m_set[symmetric]])
    finally show ?thesis .
  qed
  have gm_lookup: \<open>map_of (la_gtab G sm ! m) X =
      Some (st_find sm (cgoto (cclosure G (sm ! m)) X))\<close>
    using la_gtab_lookup[OF m_lt[unfolded sm_def] core_cl[unfolded sm_def]
        m0_lt] X0 unfolding sm_def by simp
  define m' where \<open>m' \<equiv> st_find sm (cgoto (cclosure G (sm ! m)) X)\<close>
  have edge_p: \<open>(X, p') \<in> set (pgtab G sp ! p)\<close>
    using pgtab_mem[OF p_lt[unfolded sp_def] src0_cr[unfolded sp_def] m0_lt] X0
    unfolding p'_def sp_def by simp
  have succ: \<open>(p', m') \<in> set (prod_succs (pgtab G (pr0_states G Shn))
                (la_gtab G (lr0_states G Shn)) (p, m))\<close>
    by (rule prod_succsI)
       (use p_lt edge_p gm_lookup m_lt m'_def sp_def sm_def in \<open>auto simp: la_gtab_def\<close>)
  have pairm: \<open>(p, m) \<in> set (mprod_states G Shn)\<close>
    using pair unfolding m_def .
  have pair': \<open>(p', m') \<in> set (mprod_states G Shn)\<close>
    by (rule mprod_states_closed[OF pairm succ])
  have new_idx: \<open>st_find sm (ccore (lgoto CL X RA)) = m'\<close>
  proof -
    have \<open>set (ccore (lgoto CL X RA)) = set (cgoto (ccore CL) X)\<close>
      by (rule set_ccore_lgoto)
    also have \<open>\<dots> = set (cgoto (cclosure G (sm ! m)) X)\<close>
      by (rule set_cgoto_cong[OF trans[OF set_ccore_xclosure_auto[of G f, folded CL_def]
            set_cclosure_cong[OF m_set[symmetric]]]])
    finally show ?thesis
      unfolding m'_def by (rule st_find_cong)
  qed
  show ?thesis using p'_lt cov' pair' new_idx by simp
qed

section \<open>License transport: from the runtime tables to the static seeds\<close>

text \<open>The merged index the driver tracks is exactly the canonical
  \<^const>\<open>st_find\<close> index of the frame's core.\<close>

lemma didx_hd_st_find:
  assumes ok: \<open>didx_ok G (lr0_states G Shn) Xs istk\<close> and ne: \<open>Xs \<noteq> []\<close>
  shows \<open>hd istk = st_find (lr0_states G Shn) (ccore (hd Xs))\<close>
proof -
  have istk_ne: \<open>istk \<noteq> []\<close> using didx_ok_len[OF ok] ne by auto
  from didx_okD[OF ok, of 0] ne have
    lt: \<open>istk ! 0 < length (lr0_states G Shn)\<close>
    and eq: \<open>set (lr0_states G Shn ! (istk ! 0)) = set (ccore (Xs ! 0))\<close> by auto
  show ?thesis
    using st_find_unique[OF lr0_states_distinct lt eq] istk_ne ne
    by (simp add: hd_conv_nth)
qed

lemma red_buckets_memD:
  assumes \<open>i < n\<close> and \<open>c \<in> set (red_buckets G Shn n ! i)\<close>
  shows \<open>c \<in> set (la_fix G Shn) \<and> fst c = i \<and>
         (case c of (i', itm, t, \<tau>) \<Rightarrow> snd itm = length (snd (fst itm)))\<close>
  using assms unfolding red_buckets_def cell_buckets_def by (auto simp: Let_def)

section \<open>Accept/reduce conflicts\<close>

text \<open>The case \<^const>\<open>rlalr_conflicts\<close> ignores: the start production
  completed next to an end-of-input reduce cell of another production, the
  driver accepting where the relation of the grammar has a second value.\<close>

definition acc_conflicts :: \<open>('n, 't) is_cfg \<Rightarrow> 'n \<Rightarrow> nat list\<close> where
  \<open>acc_conflicts G Shn = (let sts = lr0_states G Shn in
     filter (\<lambda>i. (start_prod G Shn, Suc 0) \<in> set (sts ! i) \<and>
        list_ex (\<lambda>(i', (pr, m), t, \<tau>). i' = i \<and> m = length (snd pr) \<and>
                  t = None \<and> pr \<noteq> start_prod G Shn) (la_fix G Shn))
       [0..<length sts])\<close>

text \<open>Reducing by the start production is dead: nothing in the initial
  closure expects \<^term>\<open>Nt Shn\<close>.\<close>

lemma lgoto_xinit_Shn:
  assumes fn: \<open>fresh_name G Shn\<close>
  shows \<open>lgoto (xclosure_auto G (xinit G Shn)) (Nt Shn) RA = []\<close>
proof -
  have \<open>\<not> (m < length (snd pr) \<and> fst (snd pr ! m) = Nt Shn)\<close>
    if item: \<open>(pr, m, R) \<in> set (xclosure_auto G (xinit G Shn))\<close> for pr m R
  proof
    assume \<open>m < length (snd pr) \<and> fst (snd pr ! m) = Nt Shn\<close>
    then have m: \<open>m < length (snd pr)\<close> and X: \<open>fst (snd pr ! m) = Nt Shn\<close> by auto
    from dshape_prods[OF dshape_init, of 0 pr m R] item
    have \<open>pr \<in> set (iprods G) \<or> pr = start_prod G Shn\<close> by simp
    then show False
    proof
      assume prG: \<open>pr \<in> set (iprods G)\<close>
      have \<open>snd pr ! m \<in> set (snd pr)\<close> using m by simp
      with fn prG X show False
        unfolding fresh_name_def by (cases pr; cases \<open>snd pr ! m\<close>) fastforce
    next
      assume \<open>pr = start_prod G Shn\<close>
      with m X fn show False unfolding start_prod_def fresh_name_def by simp
    qed
  qed
  then show ?thesis unfolding lgoto_def by (auto simp: filter_empty_conv)
qed

lemma final_shape:
  assumes fn: \<open>fresh_name G Shn\<close>
    and inv: \<open>dinv G Shn w ((Xs, u), cstk, istk, v, tstk)\<close>
    and fin: \<open>gfinal G Shn (Xs, u)\<close>
  shows \<open>\<exists>X. Xs = [X, xinit G Shn]\<close>
proof -
  have fin': \<open>gfinal G Shn (fst ((Xs, u), cstk, istk, v, tstk))\<close> using fin by simp
  from dinv_final[OF fn inv fin'] obtain t where tstk: \<open>tstk = [t]\<close> by auto
  from inv obtain RAs where lenR: \<open>length RAs = length tstk\<close>
    and sh: \<open>dshape G Shn Xs (zip (map asym tstk) RAs)\<close>
    unfolding dinv_def by auto
  have \<open>length Xs = 2\<close> \<open>Xs ! 1 = xinit G Shn\<close>
    using sh lenR tstk unfolding dshape_def by auto
  then show ?thesis
    by (cases Xs) (auto simp: length_Suc_conv)
qed

text \<open>With an empty accept/reduce report, no live reduce is offered at an
  accepting configuration.\<close>

lemma no_reduce_at_final:
  assumes fn: \<open>fresh_name G Shn\<close> and chk: \<open>acc_conflicts G Shn = []\<close>
    and inv: \<open>dinv G Shn w ((Xs, u), cstk, istk, v, tstk)\<close>
    and ok: \<open>didx_ok G (lr0_states G Shn) Xs istk\<close>
    and fin: \<open>gfinal G Shn (Xs, u)\<close>
    and cand: \<open>DReduce pr \<in> set (dcands G (hd istk)
                 (red_buckets G Shn (length (lr0_states G Shn)) ! hd istk)
                 (xclosure_auto G (hd Xs)) (Xs, u))\<close>
    and step: \<open>mstep G (Xs, u) (DReduce pr) = Some gc'\<close> and live: \<open>dlive gc'\<close>
  shows False
proof -
  let ?sts = \<open>lr0_states G Shn\<close> and ?i = \<open>hd istk\<close>
  from final_shape[OF fn inv fin] obtain X where Xs: \<open>Xs = [X, xinit G Shn]\<close> by blast
  have u: \<open>u = []\<close> using fin unfolding gfinal_def by simp
  have istk_ne: \<open>istk \<noteq> []\<close> using didx_ok_len[OF ok] Xs by auto
  have i_lt: \<open>?i < length ?sts\<close> and cores: \<open>set (?sts ! ?i) = set (ccore X)\<close>
    using didx_okD[OF ok, of 0] Xs istk_ne by (auto simp: hd_conv_nth)
  from fin obtain pr\<^sub>0 R where item: \<open>(pr\<^sub>0, Suc 0, R) \<in> set X\<close> and Shn: \<open>fst pr\<^sub>0 = Shn\<close>
    unfolding gfinal_def Xs by (auto simp: list_ex_iff)
  from inv obtain RAs where sh: \<open>dshape G Shn Xs (zip (map asym tstk) RAs)\<close>
    unfolding dinv_def by auto
  have item': \<open>(pr\<^sub>0, Suc 0, R) \<in> set (xclosure_auto G (Xs ! 0))\<close>
    using item xclosure_auto_kernel_sub Xs by fastforce
  have pr0: \<open>pr\<^sub>0 = start_prod G Shn\<close>
    using dshape_prods[OF sh _ item'] Shn fn unfolding fresh_name_def by force
  have acc: \<open>(start_prod G Shn, Suc 0) \<in> set (?sts ! ?i)\<close>
    using item pr0 cores unfolding ccore_def by force
  from dcands_reduceD[OF cand]
  have \<open>dlic ?i (red_buckets G Shn (length ?sts) ! ?i) u pr (red_set (xclosure_auto G (hd Xs)) pr)\<close>
    by simp
  then obtain \<tau> where
      cell: \<open>(?i, (pr, length (snd pr)), None, \<tau>) \<in> set (red_buckets G Shn (length ?sts) ! ?i)\<close>
    unfolding dlic_def u by (auto simp: list_ex_iff)
  then have cellL: \<open>(?i, (pr, length (snd pr)), None, \<tau>) \<in> set (la_fix G Shn)\<close>
    by (rule red_buckets_memD[OF i_lt, THEN conjunct1])
  have ne: \<open>pr \<noteq> start_prod G Shn\<close>
  proof
    assume pr: \<open>pr = start_prod G Shn\<close>
    have \<open>gc' = (lgoto (xclosure_auto G (xinit G Shn)) (Nt Shn)
                   (red_set (xclosure_auto G X) pr) # [xinit G Shn], u)\<close>
      using step unfolding mstep_def mstep_cached_def Xs pr start_prod_def
      by (auto simp: Let_def split: if_splits)
    then have \<open>gc' = ([] # [xinit G Shn], u)\<close> by (simp add: lgoto_xinit_Shn[OF fn])
    with live show False unfolding dlive_def live_def by simp
  qed
  have \<open>?i \<in> set (acc_conflicts G Shn)\<close>
    unfolding acc_conflicts_def Let_def using i_lt acc cellL ne
    by (auto simp: list_ex_iff intro!: bexI[where x = \<open>(?i, (pr, length (snd pr)), None, \<tau>)\<close>])
  with chk show False by simp
qed

section \<open>Soundness of the rigid-point walk\<close>

text \<open>The walk's descendant relation: one backward composition through a
  non-anchored nonterminal entry, each side choosing its own class.  A
  \<open>False\<close> result of \<^const>\<open>rfire\<close> can only arise from an exhausted
  worklist (fuel exhaustion returns \<open>True\<close>), so it certifies that every
  reachable descendant at a rigid state is \<^const>\<open>wdisjoint\<close>.\<close>

inductive rdesc :: \<open>('n, 't) is_cfg \<Rightarrow> ('n, 't) citem list list \<Rightarrow>
    (('n, 't) sym \<times> nat) list list \<Rightarrow> 'n list \<Rightarrow>
    nat \<times> wrel \<times> wrel \<Rightarrow> nat \<times> wrel \<times> wrel \<Rightarrow> bool\<close>
  for G sts gt anc where
  rdesc_step: \<open>(p, Nt A) \<in> set (pin_edges gt i) \<Longrightarrow> A \<notin> set anc \<Longrightarrow>
     \<rho>\<^sub>1 \<in> set (rho_classes G sts p A) \<Longrightarrow> \<rho>\<^sub>2 \<in> set (rho_classes G sts p A) \<Longrightarrow>
     rdesc G sts gt anc (i, \<sigma>\<^sub>1, \<sigma>\<^sub>2)
       (p, wcomp (winv \<rho>\<^sub>1) \<sigma>\<^sub>1, wcomp (winv \<rho>\<^sub>2) \<sigma>\<^sub>2)\<close>

definition rigid_at :: \<open>nat \<Rightarrow> (('n, 't) sym \<times> nat) list list \<Rightarrow> 'n list \<Rightarrow> nat \<Rightarrow> bool\<close> where
  \<open>rigid_at i\<^sub>0 gt anc i \<longleftrightarrow> i = i\<^sub>0 \<or>
     list_ex (\<lambda>(p, X). case X of Tm _ \<Rightarrow> True | Nt A \<Rightarrow> A \<in> set anc) (pin_edges gt i)\<close>

lemma map_filterI:
  \<open>x \<in> set xs \<Longrightarrow> f x = Some y \<Longrightarrow> y \<in> set (List.map_filter f xs)\<close>
  unfolding List.map_filter_def by force

lemma concat_map_memI:
  \<open>x \<in> set xs \<Longrightarrow> y \<in> set (g x) \<Longrightarrow> y \<in> set (concat (map g xs))\<close>
  by auto

lemma rfire_False_sound:
  assumes res: \<open>rfire G i\<^sub>0 sts gt anc n seen work = False\<close>
    and inv: \<open>\<forall>t \<in> set seen.
        (case t of (i, \<sigma>\<^sub>1, \<sigma>\<^sub>2) \<Rightarrow> rigid_at i\<^sub>0 gt anc i \<longrightarrow> wdisjoint \<sigma>\<^sub>1 \<sigma>\<^sub>2) \<and>
        (\<forall>t'. rdesc G sts gt anc t t' \<longrightarrow> t' \<in> set seen \<union> set work)\<close>
    and t0: \<open>t\<^sub>0 \<in> set seen \<union> set work\<close>
    and desc: \<open>(rdesc G sts gt anc)\<^sup>*\<^sup>* t\<^sub>0 t'\<close>
  shows \<open>case t' of (i, \<sigma>\<^sub>1, \<sigma>\<^sub>2) \<Rightarrow> rigid_at i\<^sub>0 gt anc i \<longrightarrow> wdisjoint \<sigma>\<^sub>1 \<sigma>\<^sub>2\<close>
  using res inv t0 desc
proof (induction n arbitrary: seen work t\<^sub>0 t')
  case 0
  then show ?case by simp
next
  case (Suc n)
  show ?case
  proof (cases work)
    case Nil
    have cl: \<open>\<forall>t \<in> set seen. \<forall>t'. rdesc G sts gt anc t t' \<longrightarrow> t' \<in> set seen\<close>
      using Suc.prems(2) Nil by auto
    have dj: \<open>\<forall>t \<in> set seen.
        (case t of (i, \<sigma>\<^sub>1, \<sigma>\<^sub>2) \<Rightarrow> rigid_at i\<^sub>0 gt anc i \<longrightarrow> wdisjoint \<sigma>\<^sub>1 \<sigma>\<^sub>2)\<close>
      using Suc.prems(2) by auto
    have t0: \<open>t\<^sub>0 \<in> set seen\<close> using Suc.prems(3) Nil by simp
    from Suc.prems(4) t0 have \<open>t' \<in> set seen\<close>
      by (induction rule: rtranclp_induct) (use cl in auto)
    then show ?thesis using dj by auto
  next
    case (Cons x wk)
    obtain i \<sigma>\<^sub>1 \<sigma>\<^sub>2 where x: \<open>x = (i, \<sigma>\<^sub>1, \<sigma>\<^sub>2)\<close> by (cases x) auto
    define succs where \<open>succs = concat (map (\<lambda>(p, X). case X of
          Tm _ \<Rightarrow> []
        | Nt A \<Rightarrow> (if A \<in> set anc then [] else
            concat (map (\<lambda>\<rho>\<^sub>1. List.map_filter (\<lambda>\<rho>\<^sub>2.
             let t = (p, wcomp (winv \<rho>\<^sub>1) \<sigma>\<^sub>1, wcomp (winv \<rho>\<^sub>2) \<sigma>\<^sub>2)
             in if t \<in> set seen \<or> t \<in> set wk then None else Some t)
             (rho_classes G sts p A)) (rho_classes G sts p A)))) (pin_edges gt i))\<close>
    have res3: \<open>rfire G i\<^sub>0 sts gt anc n ((i, \<sigma>\<^sub>1, \<sigma>\<^sub>2) # seen) (remdups succs @ wk) = False\<close>
      and ndj: \<open>\<not> ((i = i\<^sub>0 \<or>
        list_ex (\<lambda>(p, X). case X of Tm _ \<Rightarrow> True | Nt A \<Rightarrow> A \<in> set anc)
          (pin_edges gt i)) \<and> \<not> wdisjoint \<sigma>\<^sub>1 \<sigma>\<^sub>2)\<close>
      using Suc.prems(1) unfolding Cons x
      by (auto simp: Let_def succs_def split: if_splits)
    have x_rd: \<open>rigid_at i\<^sub>0 gt anc i \<longrightarrow> wdisjoint \<sigma>\<^sub>1 \<sigma>\<^sub>2\<close>
      using ndj unfolding rigid_at_def by auto
    have x_succ: \<open>\<forall>t'. rdesc G sts gt anc (i, \<sigma>\<^sub>1, \<sigma>\<^sub>2) t' \<longrightarrow>
        t' \<in> set ((i, \<sigma>\<^sub>1, \<sigma>\<^sub>2) # seen) \<union> set (remdups succs @ wk)\<close>
    proof (intro allI impI)
      fix t' assume \<open>rdesc G sts gt anc (i, \<sigma>\<^sub>1, \<sigma>\<^sub>2) t'\<close>
      then obtain p A \<rho>\<^sub>1 \<rho>\<^sub>2 where e: \<open>(p, Nt A) \<in> set (pin_edges gt i)\<close>
        and na: \<open>A \<notin> set anc\<close>
        and r1: \<open>\<rho>\<^sub>1 \<in> set (rho_classes G sts p A)\<close>
        and r2: \<open>\<rho>\<^sub>2 \<in> set (rho_classes G sts p A)\<close>
        and t': \<open>t' = (p, wcomp (winv \<rho>\<^sub>1) \<sigma>\<^sub>1, wcomp (winv \<rho>\<^sub>2) \<sigma>\<^sub>2)\<close>
        by (cases rule: rdesc.cases) auto
      show \<open>t' \<in> set ((i, \<sigma>\<^sub>1, \<sigma>\<^sub>2) # seen) \<union> set (remdups succs @ wk)\<close>
      proof (cases \<open>t' \<in> set seen \<or> t' \<in> set wk\<close>)
        case True
        then show ?thesis by auto
      next
        case False
        define body where \<open>body = (\<lambda>\<rho>\<^sub>1. List.map_filter (\<lambda>\<rho>\<^sub>2.
             let t = (p, wcomp (winv \<rho>\<^sub>1) \<sigma>\<^sub>1, wcomp (winv \<rho>\<^sub>2) \<sigma>\<^sub>2)
             in if t \<in> set seen \<or> t \<in> set wk then None else Some t)
             (rho_classes G sts p A))\<close>
        have inner: \<open>t' \<in> set (body \<rho>\<^sub>1)\<close>
          unfolding body_def
          by (rule map_filterI[OF r2]) (use False t' in \<open>simp add: Let_def\<close>)
        have mid: \<open>t' \<in> set (concat (map body (rho_classes G sts p A)))\<close>
          using r1 inner by auto
        have \<open>t' \<in> set succs\<close>
          unfolding succs_def
        proof (rule concat_map_memI[OF e])
          show \<open>t' \<in> set ((\<lambda>(q, X). case X of
              Tm _ \<Rightarrow> []
            | Nt B \<Rightarrow> (if B \<in> set anc then [] else
                concat (map (\<lambda>\<rho>\<^sub>1. List.map_filter (\<lambda>\<rho>\<^sub>2.
                 let t = (q, wcomp (winv \<rho>\<^sub>1) \<sigma>\<^sub>1, wcomp (winv \<rho>\<^sub>2) \<sigma>\<^sub>2)
                 in if t \<in> set seen \<or> t \<in> set wk then None else Some t)
                 (rho_classes G sts q B)) (rho_classes G sts q B)))) (p, Nt A))\<close>
            using na mid unfolding body_def by simp
        qed
        then show ?thesis by auto
      qed
    qed
    have inv': \<open>\<forall>t \<in> set ((i, \<sigma>\<^sub>1, \<sigma>\<^sub>2) # seen).
        (case t of (i', \<sigma>\<^sub>1', \<sigma>\<^sub>2') \<Rightarrow> rigid_at i\<^sub>0 gt anc i' \<longrightarrow> wdisjoint \<sigma>\<^sub>1' \<sigma>\<^sub>2') \<and>
        (\<forall>t'. rdesc G sts gt anc t t' \<longrightarrow>
           t' \<in> set ((i, \<sigma>\<^sub>1, \<sigma>\<^sub>2) # seen) \<union> set (remdups succs @ wk))\<close>
    proof
      fix t assume \<open>t \<in> set ((i, \<sigma>\<^sub>1, \<sigma>\<^sub>2) # seen)\<close>
      then consider \<open>t = (i, \<sigma>\<^sub>1, \<sigma>\<^sub>2)\<close> | \<open>t \<in> set seen\<close> by auto
      then show \<open>(case t of (i', \<sigma>\<^sub>1', \<sigma>\<^sub>2') \<Rightarrow> rigid_at i\<^sub>0 gt anc i' \<longrightarrow> wdisjoint \<sigma>\<^sub>1' \<sigma>\<^sub>2') \<and>
          (\<forall>t'. rdesc G sts gt anc t t' \<longrightarrow>
             t' \<in> set ((i, \<sigma>\<^sub>1, \<sigma>\<^sub>2) # seen) \<union> set (remdups succs @ wk))\<close>
      proof cases
        case 1
        then show ?thesis using x_rd x_succ by auto
      next
        case 2
        then show ?thesis using Suc.prems(2) unfolding Cons x by auto
      qed
    qed
    have t0': \<open>t\<^sub>0 \<in> set ((i, \<sigma>\<^sub>1, \<sigma>\<^sub>2) # seen) \<union> set (remdups succs @ wk)\<close>
      using Suc.prems(3) unfolding Cons x by auto
    show ?thesis
      by (rule Suc.IH[OF res3 inv' t0' Suc.prems(4)])
  qed
qed

theorem rfire_sound:
  assumes res: \<open>rfire G i\<^sub>0 sts gt anc n [] [t\<^sub>0] = False\<close>
    and desc: \<open>(rdesc G sts gt anc)\<^sup>*\<^sup>* t\<^sub>0 (i, \<sigma>\<^sub>1, \<sigma>\<^sub>2)\<close>
    and rigid: \<open>rigid_at i\<^sub>0 gt anc i\<close>
  shows \<open>wdisjoint \<sigma>\<^sub>1 \<sigma>\<^sub>2\<close>
  using rfire_False_sound[OF res _ _ desc] rigid by auto

section \<open>Stack shape along reachability, and anchor persistence\<close>

lemma dshapeD:
  assumes \<open>dshape G Shn Xs \<alpha>\<close>
  shows \<open>length Xs = length \<alpha> + 1\<close> and \<open>Xs ! length \<alpha> = xinit G Shn\<close>
    and \<open>\<And>k. k < length \<alpha> \<Longrightarrow>
      Xs ! k = lgoto (xclosure_auto G (Xs ! Suc k)) (fst (\<alpha> ! k)) (snd (\<alpha> ! k))\<close>
  using assms unfolding dshape_def by auto

text \<open>Every reachable stack is \<^const>\<open>dshape\<close>-shaped (part of the
  tracking invariant of \<^text>\<open>mreach_strack\<close> below): each frame is the
  \<^const>\<open>lgoto\<close> of the closure of the frame below, along a recorded goto
  history.  Anchors of a kernel item persist from its prediction: descending
  the dots, the item's anchor set only shrinks from the dot-0 slot in the
  closure of the frame where it was predicted.\<close>

lemma wkernel_memI:
  \<open>(pr, m) \<in> set s \<Longrightarrow>
   (pr, m, if m = 0 then WAny else w_of (snd (snd pr ! (m - 1)))) \<in> set (wkernel s)\<close>
  unfolding wkernel_def by force

lemma xclosure_auto_kernelD:
  assumes \<open>(pr, m, R) \<in> set (xclosure_auto G s)\<close> and \<open>1 \<le> m\<close>
  shows \<open>(pr, m, R) \<in> set s\<close>
proof -
  have \<open>(pr, m, R) \<in> set (xslots G s (xiter G s (xfuel G s)))\<close>
    using assms(1) unfolding xclosure_auto_def xclosure_def .
  then show ?thesis
  proof (rule xslots_memE)
    assume \<open>(pr, m, R) \<in> set s\<close> then show ?thesis .
  next
    fix q assume \<open>q < length (iprods G)\<close>
      and \<open>q < length (xiter G s (xfuel G s))\<close>
      and \<open>(pr, m, R) = (iprods G ! q, 0, xiter G s (xfuel G s) ! q)\<close>
    then show ?thesis using assms(2) by auto
  qed
qed

text \<open>A kernel item at dot \<open>m \<ge> 1\<close> in frame \<open>k\<close> descends to the dot-0 slot of
  the closure of frame \<open>k + m\<close>, its anchor set only shrinking.\<close>

lemma dshape_persist:
  assumes sh: \<open>dshape G Shn Xs \<alpha>\<close>
  shows \<open>(pr, m, R) \<in> set (Xs ! k) \<Longrightarrow> k < length Xs \<Longrightarrow> 1 \<le> m \<Longrightarrow>
     \<exists>R\<^sub>0. k + m < length Xs \<and> (pr, 0, R\<^sub>0) \<in> set (xclosure_auto G (Xs ! (k + m))) \<and>
           irep_set R \<subseteq> irep_set R\<^sub>0\<close>
proof (induction m arbitrary: k R)
  case 0
  then show ?case by simp
next
  case (Suc m)
  note lenX = dshapeD(1)[OF sh] and bot = dshapeD(2)[OF sh] and shp = dshapeD(3)[OF sh]
  have k_lt_a: \<open>k < length \<alpha>\<close>
  proof (rule ccontr)
    assume \<open>\<not> k < length \<alpha>\<close>
    then have \<open>k = length \<alpha>\<close> using Suc.prems(2) lenX by simp
    then have \<open>(pr, Suc m, R) \<in> set (xinit G Shn)\<close> using Suc.prems(1) bot by simp
    then show False unfolding xinit_def by auto
  qed
  have frame: \<open>Xs ! k = lgoto (xclosure_auto G (Xs ! Suc k)) (fst (\<alpha> ! k)) (snd (\<alpha> ! k))\<close>
    by (rule shp[OF k_lt_a])
  from lgoto_kernel_step[OF Suc.prems(1)[unfolded frame]] obtain R' where
    src: \<open>(pr, m, R') \<in> set (xclosure_auto G (Xs ! Suc k))\<close>
    and Req: \<open>R = irep_inter R' (irep_pre (snd (snd pr ! m)) (snd (\<alpha> ! k)))\<close> .
  have sub: \<open>irep_set R \<subseteq> irep_set R'\<close> unfolding Req by auto
  show ?case
  proof (cases m)
    case 0
    have \<open>Suc k < length Xs\<close> using k_lt_a lenX by simp
    then show ?thesis using src sub 0 by auto
  next
    case (Suc m')
    have m_pos: \<open>1 \<le> m\<close> using Suc by simp
    have src': \<open>(pr, m, R') \<in> set (xslots G (Xs ! Suc k)
        (xiter G (Xs ! Suc k) (xfuel G (Xs ! Suc k))))\<close>
      using src unfolding xclosure_auto_def xclosure_def .
    have kern: \<open>(pr, m, R') \<in> set (Xs ! Suc k)\<close>
      using src'
    proof (rule xslots_memE)
      assume \<open>(pr, m, R') \<in> set (Xs ! Suc k)\<close>
      then show ?thesis .
    next
      fix q assume \<open>q < length (iprods G)\<close>
        and \<open>q < length (xiter G (Xs ! Suc k) (xfuel G (Xs ! Suc k)))\<close>
        and \<open>(pr, m, R') = (iprods G ! q, 0, xiter G (Xs ! Suc k) (xfuel G (Xs ! Suc k)) ! q)\<close>
      then show ?thesis using Suc by auto
    qed
    have Sk_lt: \<open>Suc k < length Xs\<close> using k_lt_a lenX by simp
    from Suc.IH[OF kern Sk_lt m_pos] obtain R\<^sub>0 where
      \<open>Suc k + m < length Xs\<close>
      and s0: \<open>(pr, 0, R\<^sub>0) \<in> set (xclosure_auto G (Xs ! (Suc k + m)))\<close>
      and sub2: \<open>irep_set R' \<subseteq> irep_set R\<^sub>0\<close> by blast
    then show ?thesis using sub by fastforce
  qed
qed

section \<open>The pooled width invariant\<close>

text \<open>The per-item form of the width invariant: each anchored closure item
  relates to \<open>some\<close> element of the frame's entry pool \<open>P\<close> by a \<open>wreach\<close>
  class; different items may pick different pool elements, as the pooled
  machine's frames demand.  First the closure preservation, by
  induction on the round number of \<open>xiter\<close>: every step reuses its source's
  pool element.\<close>

lemma xiter_pool:
  assumes kern: \<open>\<And>pr m R j. (pr, m, R) \<in> set xs \<Longrightarrow> j \<in> irep_set R \<Longrightarrow>
      \<exists>\<rho> l. (pr, m, \<rho>) \<in> set (wreach G s) \<and> l \<in> P \<and> wsat \<rho> l j\<close>
  shows \<open>p < length (iprods G) \<Longrightarrow> j \<in> irep_set (xiter G xs t ! p) \<Longrightarrow>
     \<exists>\<rho> l. (iprods G ! p, 0, \<rho>) \<in> set (wreach G s) \<and> l \<in> P \<and> wsat \<rho> l j\<close>
proof (induction t arbitrary: p j)
  case 0
  then show ?case by simp
next
  case (Suc t)
  have len: \<open>length (xiter G xs t) = length (iprods G)\<close> by simp
  have \<open>xiter G xs (Suc t) ! p =
      fold (xcontrib (iprods G ! p)) (xslots G xs (xiter G xs t)) (xiter G xs t ! p)\<close>
    by (simp add: xround_nth[OF len Suc.prems(1)])
  with Suc.prems(2) have
    \<open>j \<in> irep_set (xiter G xs t ! p) \<or>
     (\<exists>xit \<in> set (xslots G xs (xiter G xs t)). j \<in> ximg (iprods G ! p) xit)\<close>
    by (simp add: fold_xcontrib_set)
  then show ?case
  proof
    assume \<open>j \<in> irep_set (xiter G xs t ! p)\<close>
    from Suc.IH[OF Suc.prems(1) this] show ?thesis .
  next
    assume \<open>\<exists>xit \<in> set (xslots G xs (xiter G xs t)). j \<in> ximg (iprods G ! p) xit\<close>
    then obtain xit where xit: \<open>xit \<in> set (xslots G xs (xiter G xs t))\<close>
      and jimg: \<open>j \<in> ximg (iprods G ! p) xit\<close> by blast
    obtain pr' m' R' where xeq: \<open>xit = (pr', m', R')\<close> by (cases xit) auto
    obtain A rhs where pr': \<open>pr' = (A, rhs)\<close> by (cases pr')
    from jimg have m_lt: \<open>m' < length rhs\<close>
      and nxt: \<open>fst (rhs ! m') = Nt (fst (iprods G ! p))\<close>
      and jsat: \<open>\<exists>i \<in> irep_set R'. irel_sat (snd (rhs ! m')) j i\<close>
      unfolding xeq pr' by (auto split: if_splits)
    from jsat obtain i where iR: \<open>i \<in> irep_set R'\<close>
      and rel: \<open>irel_sat (snd (rhs ! m')) j i\<close> by blast
    have src: \<open>\<exists>\<rho>' l. (pr', m', \<rho>') \<in> set (wreach G s) \<and> l \<in> P \<and> wsat \<rho>' l i\<close>
      using xit
    proof (rule xslots_memE)
      assume \<open>xit \<in> set xs\<close>
      then have memxs: \<open>(pr', m', R') \<in> set xs\<close> using xeq by simp
      from kern[OF memxs iR] show ?thesis .
    next
      fix q assume q: \<open>q < length (iprods G)\<close> and \<open>q < length (xiter G xs t)\<close>
        and xq: \<open>xit = (iprods G ! q, 0, xiter G xs t ! q)\<close>
      have pq: \<open>pr' = iprods G ! q\<close> and mq: \<open>m' = 0\<close>
        and Rq: \<open>R' = xiter G xs t ! q\<close> using xq xeq by auto
      have \<open>i \<in> irep_set (xiter G xs t ! q)\<close> using iR Rq by simp
      from Suc.IH[OF q this] show ?thesis unfolding pq mq by simp
    qed
    from src obtain \<rho>' l where mem: \<open>(pr', m', \<rho>') \<in> set (wreach G s)\<close>
      and lP: \<open>l \<in> P\<close> and wl: \<open>wsat \<rho>' l i\<close> by blast
    have m_lt': \<open>m' < length (snd pr')\<close> using m_lt pr' by simp
    have nxt': \<open>fst (snd pr' ! m') = Nt (fst (iprods G ! p))\<close> using nxt pr' by simp
    have prp: \<open>iprods G ! p \<in> set (iprods G)\<close> using Suc.prems(1) by simp
    from wreach_emit[OF mem m_lt' nxt' prp]
    have \<open>(iprods G ! p, 0, wcomp (winv (w_of (snd (snd pr' ! m')))) \<rho>')
          \<in> set (wreach G s)\<close> .
    moreover have \<open>wsat (wcomp (winv (w_of (snd (snd pr' ! m')))) \<rho>') l j\<close>
      by (rule wsat_reanchor[OF _ wl]) (use rel pr' in simp)
    ultimately show ?thesis using lP by blast
  qed
qed

theorem xclosure_auto_pool:
  assumes kern: \<open>\<And>pr m R j. (pr, m, R) \<in> set xs \<Longrightarrow> j \<in> irep_set R \<Longrightarrow>
      \<exists>\<rho> l. (pr, m, \<rho>) \<in> set (wreach G s) \<and> l \<in> P \<and> wsat \<rho> l j\<close>
    and mem: \<open>(pr, m, R) \<in> set (xclosure_auto G xs)\<close>
    and jR: \<open>j \<in> irep_set R\<close>
  shows \<open>\<exists>\<rho> l. (pr, m, \<rho>) \<in> set (wreach G s) \<and> l \<in> P \<and> wsat \<rho> l j\<close>
proof -
  have mem': \<open>(pr, m, R) \<in> set (xslots G xs (xiter G xs (xfuel G xs)))\<close>
    using mem unfolding xclosure_auto_def xclosure_def .
  show ?thesis
    using mem'
  proof (rule xslots_memE)
    assume mem2: \<open>(pr, m, R) \<in> set xs\<close>
    from kern[OF mem2 jR] show ?thesis .
  next
    fix q assume q: \<open>q < length (iprods G)\<close>
      and \<open>q < length (xiter G xs (xfuel G xs))\<close>
      and eq: \<open>(pr, m, R) = (iprods G ! q, 0, xiter G xs (xfuel G xs) ! q)\<close>
    have \<open>j \<in> irep_set (xiter G xs (xfuel G xs) ! q)\<close> using jR eq by simp
    from xiter_pool[OF kern q this] show ?thesis using eq by simp
  qed
qed

text \<open>The kernel hypothesis, per frame kind: an \<open>lgoto\<close>-built frame pools the
  goto label's anchors, the bottom frame is pinned at \<open>istart_ind\<close>.\<close>

lemma wanch_pool_lgoto:
  assumes cover: \<open>\<And>pr m R j. (pr, m, R) \<in> set (lgoto CL X RA) \<Longrightarrow> j \<in> irep_set R \<Longrightarrow>
      (pr, m) \<in> set s\<close>
    and mem: \<open>(pr, m, R) \<in> set (lgoto CL X RA)\<close> and jR: \<open>j \<in> irep_set R\<close>
  shows \<open>\<exists>\<rho> l. (pr, m, \<rho>) \<in> set (wreach G s) \<and> l \<in> irep_set RA \<and> wsat \<rho> l j\<close>
proof -
  obtain m\<^sub>0 where m: \<open>m = Suc m\<^sub>0\<close> using lgoto_dot_pos[OF mem] by (cases m) auto
  from lgoto_kernel_step[OF mem[unfolded m]] obtain R\<^sub>s where
    m0_lt: \<open>m\<^sub>0 < length (snd pr)\<close>
    and Req: \<open>R = irep_inter R\<^sub>s (irep_pre (snd (snd pr ! m\<^sub>0)) RA)\<close> .
  from jR obtain l where lRA: \<open>l \<in> irep_set RA\<close>
    and rel: \<open>irel_sat (snd (snd pr ! m\<^sub>0)) l j\<close>
    unfolding Req by auto
  have kmem: \<open>(pr, m) \<in> set s\<close> by (rule cover[OF mem jR])
  have \<open>(pr, m, w_of (snd (snd pr ! (m - 1)))) \<in> set (wkernel s)\<close>
    using wkernel_memI[OF kmem] unfolding m by simp
  then have wmem: \<open>(pr, m, w_of (snd (snd pr ! m\<^sub>0))) \<in> set (wreach G s)\<close>
    using wreach_kernel unfolding m by auto
  have \<open>wsat (w_of (snd (snd pr ! m\<^sub>0))) l j\<close> by (rule w_of_sound[OF rel])
  then show ?thesis using wmem lRA by blast
qed

lemma wanch_pool_xinit:
  assumes mem: \<open>(pr, m, R) \<in> set (xinit G Shn)\<close> and jR: \<open>j \<in> irep_set R\<close>
    and cover: \<open>(pr, m) \<in> set s\<close>
  shows \<open>\<exists>\<rho>. (pr, m, \<rho>) \<in> set (wreach G s) \<and> wsat \<rho> (istart_ind G) j\<close>
proof -
  have m0: \<open>m = 0\<close> using mem unfolding xinit_def by auto
  have \<open>(pr, m, WAny) \<in> set (wkernel s)\<close>
    using wkernel_memI[OF cover] unfolding m0 by simp
  then have \<open>(pr, m, WAny) \<in> set (wreach G s)\<close> using wreach_kernel by auto
  then show ?thesis by auto
qed

section \<open>The anchored-nonterminal fixpoint\<close>

text \<open>\<^const>\<open>anchored_nts\<close> iterates a filter; each round either fixes the
  list or strictly shortens it, so \<open>length nts\<close> rounds reach the greatest
  fixpoint.  The destructor: an anchored nonterminal's productions all start
  with an \<open>Eq\<close>-related terminal or anchored nonterminal.\<close>

lemma funpow_filter_fix:
  fixes stp :: \<open>'a list \<Rightarrow> 'a list\<close>
  assumes step: \<open>\<And>S. stp S = S \<or> length (stp S) < length S\<close>
  shows \<open>stp ((stp ^^ n) S\<^sub>0) = (stp ^^ n) S\<^sub>0 \<or> length ((stp ^^ n) S\<^sub>0) \<le> length S\<^sub>0 - n\<close>
proof (induction n)
  case 0
  then show ?case using step by auto
next
  case (Suc n)
  show ?case
  proof (cases \<open>stp ((stp ^^ n) S\<^sub>0) = (stp ^^ n) S\<^sub>0\<close>)
    case True
    then have \<open>(stp ^^ Suc n) S\<^sub>0 = (stp ^^ n) S\<^sub>0\<close> by simp
    then show ?thesis using True by simp
  next
    case False
    with Suc.IH have len_n: \<open>length ((stp ^^ n) S\<^sub>0) \<le> length S\<^sub>0 - n\<close> by blast
    from step[of \<open>(stp ^^ n) S\<^sub>0\<close>] False
    have \<open>length (stp ((stp ^^ n) S\<^sub>0)) < length ((stp ^^ n) S\<^sub>0)\<close> by blast
    then have \<open>length ((stp ^^ Suc n) S\<^sub>0) \<le> length S\<^sub>0 - Suc n\<close>
      using len_n by simp
    then show ?thesis by blast
  qed
qed

lemma funpow_filter_stable:
  fixes stp :: \<open>'a list \<Rightarrow> 'a list\<close>
  assumes step: \<open>\<And>S. stp S = S \<or> length (stp S) < length S\<close>
    and nil: \<open>stp [] = []\<close>
  shows \<open>stp ((stp ^^ length S\<^sub>0) S\<^sub>0) = (stp ^^ length S\<^sub>0) S\<^sub>0\<close>
proof -
  from funpow_filter_fix[OF step, of \<open>length S\<^sub>0\<close> S\<^sub>0]
  consider \<open>stp ((stp ^^ length S\<^sub>0) S\<^sub>0) = (stp ^^ length S\<^sub>0) S\<^sub>0\<close>
    | \<open>length ((stp ^^ length S\<^sub>0) S\<^sub>0) = 0\<close> by fastforce
  then show ?thesis
  proof cases
    case 1
    then show ?thesis .
  next
    case 2
    then have \<open>(stp ^^ length S\<^sub>0) S\<^sub>0 = []\<close> by simp
    then show ?thesis using nil by simp
  qed
qed

lemma anchored_ntsD:
  fixes G :: \<open>('n, 't) is_cfg\<close>
  assumes A: \<open>A \<in> set (anchored_nts G)\<close> and pr: \<open>(A, rhs) \<in> set (iprods G)\<close>
  shows \<open>rhs \<noteq> [] \<and> snd (hd rhs) = Eq \<and>
         (case fst (hd rhs) of Tm _ \<Rightarrow> True | Nt B \<Rightarrow> B \<in> set (anchored_nts G))\<close>
proof -
  define ok where \<open>ok = (\<lambda>S (B :: 'n, rhs :: ('n, 't) rhs). rhs \<noteq> [] \<and> snd (hd rhs) = Eq \<and>
      (case fst (hd rhs) of Tm _ \<Rightarrow> True | Nt B' \<Rightarrow> B' \<in> set S))\<close>
  define stp where \<open>stp = (\<lambda>S. filter (\<lambda>A. list_all (\<lambda>p. fst p \<noteq> A \<or> ok S p) (iprods G)) S)\<close>
  have step: \<open>stp S = S \<or> length (stp S) < length S\<close> for S
  proof (cases \<open>\<forall>A \<in> set S. list_all (\<lambda>p. fst p \<noteq> A \<or> ok S p) (iprods G)\<close>)
    case True
    then have \<open>stp S = S\<close> unfolding stp_def by (simp add: filter_id_conv)
    then show ?thesis ..
  next
    case False
    then obtain A' where \<open>A' \<in> set S\<close>
      and \<open>\<not> list_all (\<lambda>p. fst p \<noteq> A' \<or> ok S p) (iprods G)\<close> by blast
    then have \<open>length (stp S) < length S\<close>
      unfolding stp_def by (intro length_filter_less) auto
    then show ?thesis ..
  qed
  have nil: \<open>stp [] = []\<close> unfolding stp_def by simp
  have unf: \<open>anchored_nts G = (stp ^^ length (remdups (map fst (iprods G))))
      (remdups (map fst (iprods G)))\<close>
    unfolding anchored_nts_def stp_def ok_def Let_def by simp
  have stable: \<open>stp (anchored_nts G) = anchored_nts G\<close>
    unfolding unf by (rule funpow_filter_stable[OF step nil])
  have \<open>A \<in> set (stp (anchored_nts G))\<close> using A stable by simp
  then have \<open>list_all (\<lambda>p. fst p \<noteq> A \<or> ok (anchored_nts G) p) (iprods G)\<close>
    unfolding stp_def by simp
  then have \<open>ok (anchored_nts G) (A, rhs)\<close>
    using pr by (fastforce simp: list_all_iff)
  then show ?thesis unfolding ok_def by simp
qed

section \<open>Anchored pools are singletons\<close>

lemma anchored_nts_sub: \<open>set (anchored_nts G) \<subseteq> fst ` set (iprods G)\<close>
proof -
  have gen: \<open>set ((stp ^^ k) S\<^sub>0) \<subseteq> set S\<^sub>0\<close>
    if sub: \<open>\<And>S. set (stp S) \<subseteq> set S\<close> for stp :: \<open>'x list \<Rightarrow> 'x list\<close> and k S\<^sub>0
  proof (induction k)
    case 0 then show ?case by simp
  next
    case (Suc k)
    have \<open>set ((stp ^^ Suc k) S\<^sub>0) \<subseteq> set ((stp ^^ k) S\<^sub>0)\<close> using sub by simp
    then show ?case using Suc.IH by blast
  qed
  show ?thesis
    unfolding anchored_nts_def Let_def
    by (rule subset_trans[OF gen]) auto
qed

lemma dshape_persist1:
  assumes sh: \<open>dshape G Shn Xs \<alpha>\<close>
  shows \<open>(pr, m, R) \<in> set (Xs ! k) \<Longrightarrow> k < length Xs \<Longrightarrow> 1 \<le> m \<Longrightarrow>
     \<exists>R\<^sub>1. k + m - 1 < length \<alpha> \<and> (pr, 1, R\<^sub>1) \<in> set (Xs ! (k + m - 1)) \<and>
           irep_set R \<subseteq> irep_set R\<^sub>1\<close>
proof (induction m arbitrary: k R)
  case 0
  then show ?case by simp
next
  case (Suc m)
  note lenX = dshapeD(1)[OF sh] and bot = dshapeD(2)[OF sh] and shp = dshapeD(3)[OF sh]
  have k_lt_a: \<open>k < length \<alpha>\<close>
  proof (rule ccontr)
    assume \<open>\<not> k < length \<alpha>\<close>
    then have \<open>k = length \<alpha>\<close> using Suc.prems(2) lenX by simp
    then have \<open>(pr, Suc m, R) \<in> set (xinit G Shn)\<close> using Suc.prems(1) bot by simp
    then show False unfolding xinit_def by auto
  qed
  show ?case
  proof (cases m)
    case 0
    then show ?thesis using Suc.prems(1) k_lt_a by auto
  next
    case (Suc m')
    have frame: \<open>Xs ! k = lgoto (xclosure_auto G (Xs ! Suc k)) (fst (\<alpha> ! k)) (snd (\<alpha> ! k))\<close>
      by (rule shp[OF k_lt_a])
    from lgoto_kernel_step[OF Suc.prems(1)[unfolded frame]] obtain R' where
      src: \<open>(pr, m, R') \<in> set (xclosure_auto G (Xs ! Suc k))\<close>
      and Req: \<open>R = irep_inter R' (irep_pre (snd (snd pr ! m)) (snd (\<alpha> ! k)))\<close> .
    have sub: \<open>irep_set R \<subseteq> irep_set R'\<close> unfolding Req by auto
    have src'': \<open>(pr, m, R') \<in> set (xslots G (Xs ! Suc k)
        (xiter G (Xs ! Suc k) (xfuel G (Xs ! Suc k))))\<close>
      using src unfolding xclosure_auto_def xclosure_def .
    have kern: \<open>(pr, m, R') \<in> set (Xs ! Suc k)\<close>
      using src''
    proof (rule xslots_memE)
      assume \<open>(pr, m, R') \<in> set (Xs ! Suc k)\<close>
      then show ?thesis .
    next
      fix q assume \<open>q < length (iprods G)\<close>
        and \<open>q < length (xiter G (Xs ! Suc k) (xfuel G (Xs ! Suc k)))\<close>
        and \<open>(pr, m, R') = (iprods G ! q, 0, xiter G (Xs ! Suc k) (xfuel G (Xs ! Suc k)) ! q)\<close>
      then show ?thesis using Suc by auto
    qed
    have Sk_lt: \<open>Suc k < length Xs\<close> using k_lt_a lenX by simp
    have m_pos: \<open>1 \<le> m\<close> using Suc by simp
    from Suc.IH[OF kern Sk_lt m_pos] obtain R\<^sub>1 where
      lt1: \<open>Suc k + m - 1 < length \<alpha>\<close>
      and s1: \<open>(pr, 1, R\<^sub>1) \<in> set (Xs ! (Suc k + m - 1))\<close>
      and sub1: \<open>irep_set R' \<subseteq> irep_set R\<^sub>1\<close> by blast
    have idx: \<open>Suc k + m - 1 = k + Suc m - 1\<close> using m_pos by simp
    show ?thesis using lt1 s1 sub sub1 unfolding idx by blast
  qed
qed

lemma irep_pre_Eq: \<open>irep_set (irep_pre Eq L) = irep_set L\<close>
  by auto

text \<open>The label of a reduce over an anchored nonterminal is bounded by a
  single column: every completed instance descends to its dot-1 form, whose
  \<open>Eq\<close> first-symbol filter bounds it by the pool of the frame where the
  first symbol was crossed: a shift column, or an anchored pool one level
  down.\<close>

lemma red_set_anchored_singleton:
  assumes sh: \<open>dshape G Shn Xs \<alpha>\<close> and ne: \<open>Xs \<noteq> []\<close>
    and tmS: \<open>\<forall>k < length \<alpha>. \<forall>a. fst (\<alpha> ! k) = Tm a \<longrightarrow> (\<exists>c. snd (\<alpha> ! k) = FinRep [c])\<close>
    and sng: \<open>\<forall>k < length \<alpha>. \<forall>B. fst (\<alpha> ! k) = Nt B \<longrightarrow> B \<in> set (anchored_nts G) \<longrightarrow>
                (\<exists>c. irep_set (snd (\<alpha> ! k)) \<subseteq> {c})\<close>
    and fresh: \<open>fresh_name G Shn\<close>
    and anch: \<open>fst pr \<in> set (anchored_nts G)\<close>
  shows \<open>\<exists>c. irep_set (red_set (xclosure_auto G (hd Xs)) pr) \<subseteq> {c}\<close>
proof (cases \<open>\<exists>R. (pr, length (snd pr), R) \<in> set (xclosure_auto G (hd Xs)) \<and>
    irep_set R \<noteq> {}\<close>)
  case False
  have \<open>irep_set (red_set (xclosure_auto G (hd Xs)) pr) \<subseteq> {0}\<close>
    using False by (fastforce simp: red_set_correct)
  then show ?thesis by blast
next
  case True
  then obtain R\<^sub>w where inst_w: \<open>(pr, length (snd pr), R\<^sub>w) \<in> set (xclosure_auto G (hd Xs))\<close>
    by blast
  note lenX = dshapeD(1)[OF sh]
  have hd0: \<open>hd Xs = Xs ! 0\<close> using ne by (simp add: hd_conv_nth)
  have prG: \<open>pr \<in> set (iprods G)\<close>
  proof -
    have \<open>pr \<in> set (iprods G) \<or> pr = start_prod G Shn\<close>
      using dshape_prods[OF sh _ inst_w[unfolded hd0]] by simp
    moreover have \<open>pr \<noteq> start_prod G Shn\<close>
    proof
      assume \<open>pr = start_prod G Shn\<close>
      then have \<open>fst pr = Shn\<close> unfolding start_prod_def by simp
      then have \<open>Shn \<in> set (anchored_nts G)\<close> using anch by simp
      then have \<open>Shn \<in> fst ` set (iprods G)\<close>
        by (rule subsetD[OF anchored_nts_sub])
      then show False using fresh unfolding fresh_name_def by auto
    qed
    ultimately show ?thesis by blast
  qed
  obtain A rhs where preq: \<open>pr = (A, rhs)\<close> by (cases pr)
  from anchored_ntsD[OF anch[unfolded preq fst_conv] prG[unfolded preq]]
  have rhs_ne: \<open>rhs \<noteq> []\<close> and hdEq: \<open>snd (hd rhs) = Eq\<close>
    and hdok: \<open>case fst (hd rhs) of Tm _ \<Rightarrow> True | Nt B \<Rightarrow> B \<in> set (anchored_nts G)\<close>
    by auto
  define d where \<open>d = length (snd pr)\<close>
  have d_pos: \<open>1 \<le> d\<close> unfolding d_def preq using rhs_ne by (cases rhs) auto
  have one: \<open>d - 1 < length \<alpha> \<and> fst (\<alpha> ! (d - 1)) = fst (snd pr ! 0) \<and>
      irep_set R \<subseteq> irep_set (irep_pre (snd (snd pr ! 0)) (snd (\<alpha> ! (d - 1))))\<close>
    if inst: \<open>(pr, length (snd pr), R) \<in> set (xclosure_auto G (hd Xs))\<close> for R
  proof -
    have inst': \<open>(pr, length (snd pr), R) \<in> set (xslots G (hd Xs)
        (xiter G (hd Xs) (xfuel G (hd Xs))))\<close>
      using inst unfolding xclosure_auto_def xclosure_def .
    have kern: \<open>(pr, length (snd pr), R) \<in> set (hd Xs)\<close>
      using inst'
    proof (rule xslots_memE)
      assume \<open>(pr, length (snd pr), R) \<in> set (hd Xs)\<close>
      then show ?thesis .
    next
      fix q assume \<open>q < length (iprods G)\<close>
        and \<open>q < length (xiter G (hd Xs) (xfuel G (hd Xs)))\<close>
        and eq: \<open>(pr, length (snd pr), R) =
           (iprods G ! q, 0, xiter G (hd Xs) (xfuel G (hd Xs)) ! q)\<close>
      have \<open>length (snd pr) = 0\<close> using eq by auto
      then show ?thesis using d_pos unfolding d_def by simp
    qed
    have k0_lt: \<open>(0 :: nat) < length Xs\<close> using ne by (cases Xs) auto
    have dm: \<open>1 \<le> length (snd pr)\<close> using d_pos unfolding d_def by simp
    from dshape_persist1[OF sh kern[unfolded hd0] k0_lt dm]
    obtain R\<^sub>1 where lt1: \<open>0 + length (snd pr) - 1 < length \<alpha>\<close>
      and s1: \<open>(pr, 1, R\<^sub>1) \<in> set (Xs ! (0 + length (snd pr) - 1))\<close>
      and sub1: \<open>irep_set R \<subseteq> irep_set R\<^sub>1\<close> by blast
    have idx: \<open>0 + length (snd pr) - 1 = d - 1\<close> unfolding d_def by simp
    have lt': \<open>d - 1 < length \<alpha>\<close> using lt1 unfolding idx .
    have frame: \<open>Xs ! (d - 1) =
        lgoto (xclosure_auto G (Xs ! Suc (d - 1))) (fst (\<alpha> ! (d - 1))) (snd (\<alpha> ! (d - 1)))\<close>
      using sh lt' unfolding dshape_def by auto
    have s1': \<open>(pr, Suc 0, R\<^sub>1) \<in> set (lgoto (xclosure_auto G (Xs ! Suc (d - 1)))
        (fst (\<alpha> ! (d - 1))) (snd (\<alpha> ! (d - 1))))\<close>
      using s1 unfolding idx frame by simp
    from lgoto_kernel_step[OF s1'] obtain R\<^sub>0 where
      src0: \<open>(pr, 0, R\<^sub>0) \<in> set (xclosure_auto G (Xs ! Suc (d - 1)))\<close>
      and m0: \<open>0 < length (snd pr)\<close>
      and X0: \<open>fst (snd pr ! 0) = fst (\<alpha> ! (d - 1))\<close>
      and R1eq: \<open>R\<^sub>1 = irep_inter R\<^sub>0 (irep_pre (snd (snd pr ! 0)) (snd (\<alpha> ! (d - 1))))\<close> .
    have sub2: \<open>irep_set R\<^sub>1 \<subseteq> irep_set (irep_pre (snd (snd pr ! 0)) (snd (\<alpha> ! (d - 1))))\<close>
      unfolding R1eq by auto
    have \<open>irep_set R \<subseteq> irep_set (irep_pre (snd (snd pr ! 0)) (snd (\<alpha> ! (d - 1))))\<close>
      using sub1 sub2 by (rule subset_trans)
    then show ?thesis using lt' X0 by simp
  qed
  from one[OF inst_w] have k1: \<open>d - 1 < length \<alpha>\<close>
    and Xa: \<open>fst (\<alpha> ! (d - 1)) = fst (snd pr ! 0)\<close> by auto
  have first_rel: \<open>snd (snd pr ! 0) = Eq\<close>
    using hdEq rhs_ne unfolding preq by (simp add: hd_conv_nth)
  have bound: \<open>\<exists>c. irep_set (irep_pre (snd (snd pr ! 0)) (snd (\<alpha> ! (d - 1)))) \<subseteq> {c}\<close>
  proof (cases \<open>fst (snd pr ! 0)\<close>)
    case (Tm b)
    from tmS k1 Xa Tm obtain c where \<open>snd (\<alpha> ! (d - 1)) = FinRep [c]\<close> by auto
    then show ?thesis unfolding first_rel irep_pre_Eq by auto
  next
    case (Nt B)
    have hd0': \<open>fst (hd rhs) = fst (snd pr ! 0)\<close>
      using rhs_ne unfolding preq by (simp add: hd_conv_nth)
    have Banch: \<open>B \<in> set (anchored_nts G)\<close>
      using hdok unfolding hd0' Nt by simp
    have \<open>\<exists>c. irep_set (snd (\<alpha> ! (d - 1))) \<subseteq> {c}\<close>
      using sng[rule_format, of \<open>d - 1\<close> B] k1 Xa Nt Banch by simp
    then obtain c where \<open>irep_set (snd (\<alpha> ! (d - 1))) \<subseteq> {c}\<close> by blast
    then show ?thesis unfolding first_rel irep_pre_Eq by auto
  qed
  have bound': \<open>\<exists>c. \<forall>R. (pr, length (snd pr), R) \<in> set (xclosure_auto G (hd Xs)) \<longrightarrow>
      irep_set R \<subseteq> {c}\<close>
    using bound one by blast
  then obtain c where c: \<open>\<And>R. (pr, length (snd pr), R) \<in> set (xclosure_auto G (hd Xs)) \<Longrightarrow>
      irep_set R \<subseteq> {c}\<close> by blast
  have \<open>irep_set (red_set (xclosure_auto G (hd Xs)) pr) \<subseteq> {c}\<close>
    using c by (fastforce simp: red_set_correct)
  then show ?thesis by blast
qed

section \<open>The canonical tracked stack\<close>

text \<open>The descent needs more than \<^const>\<open>mtrack\<close>: the goto history
  (\<^const>\<open>dshape\<close>), singleton pools on shift entries, the canonical bottom
  index, and the \<open>adjacency\<close> tying each tracked index to the canonical goto
  target of the index below along the recorded symbol.  The reachability
  induction constructs exactly these witnesses.\<close>

definition strack :: \<open>('n, 't) is_cfg \<Rightarrow> 'n \<Rightarrow> ('n, 't) xitem list list \<Rightarrow>
    (('n, 't) sym \<times> indrep) list \<Rightarrow> nat list \<Rightarrow> bool\<close> where
  \<open>strack G Shn Xs \<alpha> pstk \<longleftrightarrow>
     dshape G Shn Xs \<alpha> \<and>
     mtrack G Shn Xs pstk \<and>
     last pstk = p0start G Shn \<and>
     (\<forall>k < length \<alpha>. \<forall>a. fst (\<alpha> ! k) = Tm a \<longrightarrow> (\<exists>c. snd (\<alpha> ! k) = FinRep [c])) \<and>
     (\<forall>k < length \<alpha>. \<forall>B. fst (\<alpha> ! k) = Nt B \<longrightarrow> B \<in> set (anchored_nts G) \<longrightarrow>
        (\<exists>c. irep_set (snd (\<alpha> ! k)) \<subseteq> {c})) \<and>
     (\<forall>k < length \<alpha>. \<forall>B. fst (\<alpha> ! k) = Nt B \<longrightarrow>
        (\<forall>l \<in> irep_set (snd (\<alpha> ! k)). \<exists>pr R\<^sub>0. fst pr = B \<and>
           (pr, 0, R\<^sub>0) \<in> set (xclosure_auto G (Xs ! Suc k)) \<and> l \<in> irep_set R\<^sub>0)) \<and>
     (\<forall>k < length \<alpha>. pstk ! k =
        st_find (pr0_states G Shn)
          (cgoto (creach G (pr0_states G Shn ! (pstk ! Suc k))) (fst (\<alpha> ! k))))\<close>

lemma strackD:
  assumes \<open>strack G Shn Xs \<alpha> pstk\<close>
  shows \<open>dshape G Shn Xs \<alpha>\<close> and \<open>mtrack G Shn Xs pstk\<close> and \<open>last pstk = p0start G Shn\<close>
    and \<open>\<forall>k < length \<alpha>. \<forall>a. fst (\<alpha> ! k) = Tm a \<longrightarrow> (\<exists>c. snd (\<alpha> ! k) = FinRep [c])\<close>
    and \<open>\<forall>k < length \<alpha>. \<forall>B. fst (\<alpha> ! k) = Nt B \<longrightarrow> B \<in> set (anchored_nts G) \<longrightarrow>
        (\<exists>c. irep_set (snd (\<alpha> ! k)) \<subseteq> {c})\<close>
    and \<open>\<forall>k < length \<alpha>. \<forall>B. fst (\<alpha> ! k) = Nt B \<longrightarrow>
        (\<forall>l \<in> irep_set (snd (\<alpha> ! k)). \<exists>pr R\<^sub>0. fst pr = B \<and>
           (pr, 0, R\<^sub>0) \<in> set (xclosure_auto G (Xs ! Suc k)) \<and> l \<in> irep_set R\<^sub>0)\<close>
    and \<open>\<forall>k < length \<alpha>. pstk ! k =
        st_find (pr0_states G Shn)
          (cgoto (creach G (pr0_states G Shn ! (pstk ! Suc k))) (fst (\<alpha> ! k)))\<close>
  using assms unfolding strack_def by blast+

lemma strackI:
  assumes \<open>dshape G Shn Xs \<alpha>\<close> and \<open>mtrack G Shn Xs pstk\<close> and \<open>last pstk = p0start G Shn\<close>
    and \<open>\<forall>k < length \<alpha>. \<forall>a. fst (\<alpha> ! k) = Tm a \<longrightarrow> (\<exists>c. snd (\<alpha> ! k) = FinRep [c])\<close>
    and \<open>\<forall>k < length \<alpha>. \<forall>B. fst (\<alpha> ! k) = Nt B \<longrightarrow> B \<in> set (anchored_nts G) \<longrightarrow>
        (\<exists>c. irep_set (snd (\<alpha> ! k)) \<subseteq> {c})\<close>
    and \<open>\<forall>k < length \<alpha>. \<forall>B. fst (\<alpha> ! k) = Nt B \<longrightarrow>
        (\<forall>l \<in> irep_set (snd (\<alpha> ! k)). \<exists>pr R\<^sub>0. fst pr = B \<and>
           (pr, 0, R\<^sub>0) \<in> set (xclosure_auto G (Xs ! Suc k)) \<and> l \<in> irep_set R\<^sub>0)\<close>
    and \<open>\<forall>k < length \<alpha>. pstk ! k =
        st_find (pr0_states G Shn)
          (cgoto (creach G (pr0_states G Shn ! (pstk ! Suc k))) (fst (\<alpha> ! k)))\<close>
  shows \<open>strack G Shn Xs \<alpha> pstk\<close>
  using assms unfolding strack_def by blast

lemma strack_tl:
  assumes tr: \<open>strack G Shn Xs ((X\<^sub>0, RA) # \<alpha>') pstk\<close>
  shows \<open>strack G Shn (tl Xs) \<alpha>' (tl pstk)\<close>
proof -
  note sh = strackD(1)[OF tr] and mt = strackD(2)[OF tr] and lastp = strackD(3)[OF tr]
    and tmS = strackD(4)[OF tr] and sng = strackD(5)[OF tr] and slot = strackD(6)[OF tr]
    and adj = strackD(7)[OF tr]
  note lenX = dshapeD(1)[OF sh] and bot = dshapeD(2)[OF sh] and shp = dshapeD(3)[OF sh]
  have Xs_ne: \<open>Xs \<noteq> []\<close> using lenX by auto
  obtain x\<^sub>0 Xr where Xs_eq: \<open>Xs = x\<^sub>0 # Xr\<close> using Xs_ne by (cases Xs) auto
  have nthX: \<open>\<And>k. tl Xs ! k = Xs ! Suc k\<close> unfolding Xs_eq by simp
  have len_tl: \<open>length (tl Xs) = length \<alpha>' + 1\<close> using lenX by simp
  have lenp: \<open>length pstk = length Xs\<close> by (rule mtrack_len[OF mt])
  obtain p\<^sub>0 Pr where pstk_eq: \<open>pstk = p\<^sub>0 # Pr\<close>
    using lenp Xs_ne by (cases pstk) auto
  have nthP: \<open>\<And>k. tl pstk ! k = pstk ! Suc k\<close> unfolding pstk_eq by simp
  have Pr_ne: \<open>Pr \<noteq> []\<close> using lenp lenX pstk_eq by auto
  have sh': \<open>dshape G Shn (tl Xs) \<alpha>'\<close>
    unfolding dshape_def
  proof (intro conjI)
    show \<open>length (tl Xs) = length \<alpha>' + 1\<close> by (rule len_tl)
    show \<open>tl Xs ! length \<alpha>' = xinit G Shn\<close> using bot by (simp add: nthX)
    show \<open>\<forall>k < length \<alpha>'. tl Xs ! k =
        lgoto (xclosure_auto G (tl Xs ! Suc k)) (fst (\<alpha>' ! k)) (snd (\<alpha>' ! k))\<close>
    proof (intro allI impI)
      fix k assume k: \<open>k < length \<alpha>'\<close>
      have \<open>Suc k < length ((X\<^sub>0, RA) # \<alpha>')\<close> using k by simp
      from shp[OF this] show \<open>tl Xs ! k =
          lgoto (xclosure_auto G (tl Xs ! Suc k)) (fst (\<alpha>' ! k)) (snd (\<alpha>' ! k))\<close>
        by (simp add: nthX)
    qed
  qed
  have mt': \<open>mtrack G Shn (tl Xs) (tl pstk)\<close>
    unfolding mtrack_def
  proof (intro conjI)
    show \<open>length (tl pstk) = length (tl Xs)\<close> using lenp by (simp add: Xs_eq pstk_eq)
    show \<open>\<forall>k < length (tl Xs). lcore (tl Xs ! k) \<noteq> {} \<longrightarrow>
        tl pstk ! k < length (pr0_states G Shn) \<and>
        lcore (tl Xs ! k) \<subseteq> set (pr0_states G Shn ! (tl pstk ! k)) \<and>
        (tl pstk ! k, st_find (lr0_states G Shn) (ccore (tl Xs ! k)))
          \<in> set (mprod_states G Shn)\<close>
    proof (intro allI impI)
      fix k assume k: \<open>k < length (tl Xs)\<close> and lv: \<open>lcore (tl Xs ! k) \<noteq> {}\<close>
      have sk: \<open>Suc k < length Xs\<close> using k unfolding Xs_eq by simp
      show \<open>tl pstk ! k < length (pr0_states G Shn) \<and>
          lcore (tl Xs ! k) \<subseteq> set (pr0_states G Shn ! (tl pstk ! k)) \<and>
          (tl pstk ! k, st_find (lr0_states G Shn) (ccore (tl Xs ! k)))
            \<in> set (mprod_states G Shn)\<close>
        using mtrackD[OF mt sk] lv by (simp add: nthX nthP)
    qed
  qed
  have last': \<open>last (tl pstk) = p0start G Shn\<close>
    using lastp Pr_ne unfolding pstk_eq by simp
  have tmS': \<open>\<forall>k < length \<alpha>'. \<forall>a. fst (\<alpha>' ! k) = Tm a \<longrightarrow>
      (\<exists>c. snd (\<alpha>' ! k) = FinRep [c])\<close>
  proof (intro allI impI)
    fix k a assume k: \<open>k < length \<alpha>'\<close> and t: \<open>fst (\<alpha>' ! k) = Tm a\<close>
    show \<open>\<exists>c. snd (\<alpha>' ! k) = FinRep [c]\<close>
      using tmS[rule_format, of \<open>Suc k\<close> a] k t by simp
  qed
  have sng': \<open>\<forall>k < length \<alpha>'. \<forall>B. fst (\<alpha>' ! k) = Nt B \<longrightarrow>
      B \<in> set (anchored_nts G) \<longrightarrow> (\<exists>c. irep_set (snd (\<alpha>' ! k)) \<subseteq> {c})\<close>
  proof (intro allI impI)
    fix k B assume k: \<open>k < length \<alpha>'\<close> and t: \<open>fst (\<alpha>' ! k) = Nt B\<close>
      and an: \<open>B \<in> set (anchored_nts G)\<close>
    show \<open>\<exists>c. irep_set (snd (\<alpha>' ! k)) \<subseteq> {c}\<close>
      using sng[rule_format, of \<open>Suc k\<close> B] k t an by simp
  qed
  have slot': \<open>\<forall>k < length \<alpha>'. \<forall>B. fst (\<alpha>' ! k) = Nt B \<longrightarrow>
      (\<forall>l \<in> irep_set (snd (\<alpha>' ! k)). \<exists>pr R\<^sub>0. fst pr = B \<and>
         (pr, 0, R\<^sub>0) \<in> set (xclosure_auto G (tl Xs ! Suc k)) \<and> l \<in> irep_set R\<^sub>0)\<close>
  proof (intro allI impI)
    fix k B assume k: \<open>k < length \<alpha>'\<close> and t: \<open>fst (\<alpha>' ! k) = Nt B\<close>
    have \<open>\<forall>l \<in> irep_set (snd (\<alpha>' ! k)). \<exists>pr R\<^sub>0. fst pr = B \<and>
        (pr, 0, R\<^sub>0) \<in> set (xclosure_auto G (Xs ! Suc (Suc k))) \<and> l \<in> irep_set R\<^sub>0\<close>
      using slot[rule_format, of \<open>Suc k\<close> B] k t by simp
    then show \<open>\<forall>l \<in> irep_set (snd (\<alpha>' ! k)). \<exists>pr R\<^sub>0. fst pr = B \<and>
        (pr, 0, R\<^sub>0) \<in> set (xclosure_auto G (tl Xs ! Suc k)) \<and> l \<in> irep_set R\<^sub>0\<close>
      by (simp add: nthX)
  qed
  have adj': \<open>\<forall>k < length \<alpha>'. tl pstk ! k =
      st_find (pr0_states G Shn)
        (cgoto (creach G (pr0_states G Shn ! (tl pstk ! Suc k))) (fst (\<alpha>' ! k)))\<close>
  proof (intro allI impI)
    fix k assume k: \<open>k < length \<alpha>'\<close>
    have \<open>Suc k < length ((X\<^sub>0, RA) # \<alpha>')\<close> using k by simp
    from adj[rule_format, OF this]
    show \<open>tl pstk ! k = st_find (pr0_states G Shn)
        (cgoto (creach G (pr0_states G Shn ! (tl pstk ! Suc k))) (fst (\<alpha>' ! k)))\<close>
      by (simp add: nthP)
  qed
  show ?thesis
    by (rule strackI[OF sh' mt' last' tmS' sng' slot' adj'])
qed

lemma strack_drop:
  \<open>strack G Shn Xs \<alpha> pstk \<Longrightarrow> d \<le> length \<alpha> \<Longrightarrow>
   strack G Shn (drop d Xs) (drop d \<alpha>) (drop d pstk)\<close>
proof (induction d arbitrary: Xs \<alpha> pstk)
  case 0
  then show ?case by simp
next
  case (Suc d)
  obtain X RA \<alpha>' where \<alpha>: \<open>\<alpha> = (X, RA) # \<alpha>'\<close>
    using Suc.prems(2) by (cases \<alpha>) auto
  have tl: \<open>strack G Shn (tl Xs) \<alpha>' (tl pstk)\<close>
    by (rule strack_tl[OF Suc.prems(1)[unfolded \<alpha>]])
  have d_le: \<open>d \<le> length \<alpha>'\<close> using Suc.prems(2) unfolding \<alpha> by simp
  from Suc.IH[OF tl d_le] show ?case unfolding \<alpha> by (simp add: drop_Suc)
qed

text \<open>Pushing a frame on a tracked stack: the new frame's precise index is
  the goto of the index below along the pushed symbol, and the three
  per-label conditions are checked for the pushed label only.\<close>

lemma mtrack_push:
  assumes mt: \<open>mtrack G Shn Xs pstk\<close>
    and goto: \<open>lcore NF \<noteq> {} \<Longrightarrow>
        p' < length (pr0_states G Shn) \<and>
        lcore NF \<subseteq> set (pr0_states G Shn ! p') \<and>
        (p', st_find (lr0_states G Shn) (ccore NF)) \<in> set (mprod_states G Shn)\<close>
  shows \<open>mtrack G Shn (NF # Xs) (p' # pstk)\<close>
  unfolding mtrack_def
proof (rule conjI)
  show \<open>length (p' # pstk) = length (NF # Xs)\<close> using mtrack_len[OF mt] by simp
next
  show \<open>\<forall>k < length (NF # Xs). lcore ((NF # Xs) ! k) \<noteq> {} \<longrightarrow>
          (p' # pstk) ! k < length (pr0_states G Shn) \<and>
          lcore ((NF # Xs) ! k) \<subseteq> set (pr0_states G Shn ! ((p' # pstk) ! k)) \<and>
          ((p' # pstk) ! k, st_find (lr0_states G Shn) (ccore ((NF # Xs) ! k)))
            \<in> set (mprod_states G Shn)\<close>
  proof (intro allI impI)
    fix k assume k: \<open>k < length (NF # Xs)\<close> and lv: \<open>lcore ((NF # Xs) ! k) \<noteq> {}\<close>
    show \<open>(p' # pstk) ! k < length (pr0_states G Shn) \<and>
          lcore ((NF # Xs) ! k) \<subseteq> set (pr0_states G Shn ! ((p' # pstk) ! k)) \<and>
          ((p' # pstk) ! k, st_find (lr0_states G Shn) (ccore ((NF # Xs) ! k)))
            \<in> set (mprod_states G Shn)\<close>
    proof (cases k)
      case 0
      then show ?thesis using goto lv by simp
    next
      case (Suc j)
      have j_lt: \<open>j < length Xs\<close> using k Suc by simp
      show ?thesis using mtrackD[OF mt j_lt] lv unfolding Suc by simp
    qed
  qed
qed

lemma strack_push:
  assumes tr: \<open>strack G Shn Xs \<alpha> pstk\<close>
    and NF: \<open>NF = lgoto (xclosure_auto G (hd Xs)) X RA\<close>
    and p': \<open>p' = st_find (pr0_states G Shn)
        (cgoto (creach G (pr0_states G Shn ! (pstk ! 0))) X)\<close>
    and goto: \<open>lcore NF \<noteq> {} \<Longrightarrow>
        p' < length (pr0_states G Shn) \<and>
        lcore NF \<subseteq> set (pr0_states G Shn ! p') \<and>
        (p', st_find (lr0_states G Shn) (ccore NF)) \<in> set (mprod_states G Shn)\<close>
    and tm: \<open>\<And>a. X = Tm a \<Longrightarrow> \<exists>c. RA = FinRep [c]\<close>
    and sng: \<open>\<And>B. X = Nt B \<Longrightarrow> B \<in> set (anchored_nts G) \<Longrightarrow> \<exists>c. irep_set RA \<subseteq> {c}\<close>
    and slot: \<open>\<And>B l. X = Nt B \<Longrightarrow> l \<in> irep_set RA \<Longrightarrow> \<exists>pr R\<^sub>0. fst pr = B \<and>
        (pr, 0, R\<^sub>0) \<in> set (xclosure_auto G (hd Xs)) \<and> l \<in> irep_set R\<^sub>0\<close>
  shows \<open>strack G Shn (NF # Xs) ((X, RA) # \<alpha>) (p' # pstk)\<close>
proof -
  note sh = strackD(1)[OF tr] and mt = strackD(2)[OF tr] and lastp = strackD(3)[OF tr]
    and tmS = strackD(4)[OF tr] and sngI = strackD(5)[OF tr] and slotI = strackD(6)[OF tr]
    and adj = strackD(7)[OF tr]
  have ne: \<open>Xs \<noteq> []\<close> using dshapeD(1)[OF sh] by auto
  have pstk_ne: \<open>pstk \<noteq> []\<close> using mtrack_len[OF mt] ne by auto
  have hd0: \<open>hd Xs = Xs ! 0\<close> using ne by (simp add: hd_conv_nth)
  have sh': \<open>dshape G Shn (NF # Xs) ((X, RA) # \<alpha>)\<close>
    unfolding NF by (rule dshape_push[OF sh ne])
  have mt': \<open>mtrack G Shn (NF # Xs) (p' # pstk)\<close> by (rule mtrack_push[OF mt goto])
  have last': \<open>last (p' # pstk) = p0start G Shn\<close> using lastp pstk_ne by simp
  have tmS': \<open>\<forall>k < length ((X, RA) # \<alpha>). \<forall>b. fst (((X, RA) # \<alpha>) ! k) = Tm b \<longrightarrow>
      (\<exists>c'. snd (((X, RA) # \<alpha>) ! k) = FinRep [c'])\<close>
    using tmS tm by (auto simp: less_Suc_eq_0_disj nth_Cons')
  have sng': \<open>\<forall>k < length ((X, RA) # \<alpha>). \<forall>B. fst (((X, RA) # \<alpha>) ! k) = Nt B \<longrightarrow>
      B \<in> set (anchored_nts G) \<longrightarrow> (\<exists>c'. irep_set (snd (((X, RA) # \<alpha>) ! k)) \<subseteq> {c'})\<close>
    using sngI sng by (auto simp: less_Suc_eq_0_disj nth_Cons')
  have slot': \<open>\<forall>k < length ((X, RA) # \<alpha>). \<forall>B. fst (((X, RA) # \<alpha>) ! k) = Nt B \<longrightarrow>
      (\<forall>l \<in> irep_set (snd (((X, RA) # \<alpha>) ! k)). \<exists>pr R\<^sub>0. fst pr = B \<and>
         (pr, 0, R\<^sub>0) \<in> set (xclosure_auto G ((NF # Xs) ! Suc k)) \<and> l \<in> irep_set R\<^sub>0)\<close>
    using slotI slot hd0 by (auto simp: less_Suc_eq_0_disj nth_Cons')
  have adj': \<open>\<forall>k < length ((X, RA) # \<alpha>). (p' # pstk) ! k =
      st_find (pr0_states G Shn)
        (cgoto (creach G (pr0_states G Shn ! ((p' # pstk) ! Suc k)))
          (fst (((X, RA) # \<alpha>) ! k)))\<close>
  proof (intro allI impI)
    fix k assume \<open>k < length ((X, RA) # \<alpha>)\<close>
    then show \<open>(p' # pstk) ! k =
        st_find (pr0_states G Shn)
          (cgoto (creach G (pr0_states G Shn ! ((p' # pstk) ! Suc k)))
            (fst (((X, RA) # \<alpha>) ! k)))\<close>
      using adj p' by (cases k) auto
  qed
  show ?thesis by (rule strackI[OF sh' mt' last' tmS' sng' slot' adj'])
qed

text \<open>Every reachable configuration carries a canonical tracked stack: a
  shift pushes the token's singleton label, a reduce drops the handle and
  pushes the nonterminal with its pooled anchors, whose singleton and slot
  conditions come from \<^text>\<open>red_set_anchored_singleton\<close> and
  \<^text>\<open>dshape_persist\<close>.\<close>

theorem mreach_strack:
  assumes \<open>mreach G Shn gc\<close> and fresh: \<open>fresh_name G Shn\<close>
  shows \<open>\<exists>\<alpha> pstk. strack G Shn (fst gc) \<alpha> pstk\<close>
  using assms(1)
proof (induction rule: mreach.induct)
  case (mreach_init w)
  have obl: \<open>lcore (xinit G Shn) \<noteq> {} \<longrightarrow>
      p0start G Shn < length (pr0_states G Shn) \<and>
      lcore (xinit G Shn) \<subseteq> set (pr0_states G Shn ! p0start G Shn) \<and>
      (p0start G Shn, st_find (lr0_states G Shn) (ccore (xinit G Shn)))
        \<in> set (mprod_states G Shn)\<close>
  proof
    assume \<open>lcore (xinit G Shn) \<noteq> {}\<close>
    obtain t where t: \<open>t \<in> set (pr0_states G Shn)\<close>
      and te: \<open>set t = set (ccore (xinit G Shn))\<close>
      using pr0_states_start[of G Shn] by blast
    from st_find_found[OF t te]
    have lt: \<open>st_find (pr0_states G Shn) (ccore (xinit G Shn)) < length (pr0_states G Shn)\<close>
      and eq: \<open>set (pr0_states G Shn ! st_find (pr0_states G Shn) (ccore (xinit G Shn)))
               = set (ccore (xinit G Shn))\<close> by auto
    have idx: \<open>st_find (pr0_states G Shn) (ccore (xinit G Shn)) = p0start G Shn\<close>
      unfolding p0start_def by (rule st_find_cong[OF ccore_xinit])
    have idxm: \<open>st_find (lr0_states G Shn) (ccore (xinit G Shn)) = rstart G Shn\<close>
      unfolding rstart_def by (rule st_find_cong[OF ccore_xinit])
    have cover: \<open>lcore (xinit G Shn) \<subseteq> set (pr0_states G Shn ! p0start G Shn)\<close>
      using lcore_sub_ccore eq unfolding idx by blast
    show \<open>p0start G Shn < length (pr0_states G Shn) \<and>
      lcore (xinit G Shn) \<subseteq> set (pr0_states G Shn ! p0start G Shn) \<and>
      (p0start G Shn, st_find (lr0_states G Shn) (ccore (xinit G Shn)))
        \<in> set (mprod_states G Shn)\<close>
      using lt cover mprod_states_start unfolding idx idxm by simp
  qed
  have mt: \<open>mtrack G Shn [xinit G Shn] [p0start G Shn]\<close>
    unfolding mtrack_def using obl by (auto simp: less_Suc_eq)
  have \<open>strack G Shn [xinit G Shn] [] [p0start G Shn]\<close>
    unfolding strack_def using dshape_init mt by simp
  then show ?case by auto
next
  case (mreach_step gc act gc')
  obtain \<alpha> pstk where tr0: \<open>strack G Shn (fst gc) \<alpha> pstk\<close>
    using mreach_step.IH by blast
  obtain Xs w where gc: \<open>gc = (Xs, w)\<close> by (cases gc)
  have tr: \<open>strack G Shn Xs \<alpha> pstk\<close> using tr0 unfolding gc by simp
  note sh = strackD(1)[OF tr] and trX = strackD(2)[OF tr]
    and tmS = strackD(4)[OF tr] and sngI = strackD(5)[OF tr]
  note lenXa = dshapeD(1)[OF sh]
  have len: \<open>length pstk = length Xs\<close> by (rule mtrack_len[OF trX])
  have cores: \<open>\<And>f. f \<in> set Xs \<Longrightarrow> \<exists>s \<in> set (lr0_states G Shn). set (ccore f) = set s\<close>
    using mreach_cores[OF mreach_step.hyps(1)] unfolding gc cores_ok_def by auto
  show ?case
  proof (cases act)
    case DShift
    have step: \<open>mstep_cached G (map (xclosure_auto G) Xs) (Xs, w) DShift = Some gc'\<close>
      using mreach_step.hyps(2) unfolding gc DShift mstep_def by simp
    from mstep_shift_shape[OF step] obtain a c w' where
      w: \<open>w = (a, c) # w'\<close> and ne: \<open>Xs \<noteq> []\<close>
      and gc': \<open>gc' = (lgoto (hd (map (xclosure_auto G) Xs)) (Tm a) (FinRep [c]) # Xs, w')\<close> .
    define NF where \<open>NF = lgoto (xclosure_auto G (hd Xs)) (Tm a) (FinRep [c])\<close>
    define p' where
      \<open>p' = st_find (pr0_states G Shn) (cgoto (creach G (pr0_states G Shn ! (pstk ! 0))) (Tm a))\<close>
    have gc'2: \<open>fst gc' = NF # Xs\<close>
      unfolding gc' NF_def using ne by (simp add: hd_map)
    have hd0: \<open>hd Xs = Xs ! 0\<close> using ne by (simp add: hd_conv_nth)
    have trk0: \<open>lcore (hd Xs) \<noteq> {} \<Longrightarrow> pstk ! 0 < length (pr0_states G Shn) \<and>
        lcore (hd Xs) \<subseteq> set (pr0_states G Shn ! (pstk ! 0)) \<and>
        (pstk ! 0, st_find (lr0_states G Shn) (ccore (hd Xs))) \<in> set (mprod_states G Shn)\<close>
      using mtrackD[OF trX] ne unfolding hd0 by simp
    have goto: \<open>lcore NF \<noteq> {} \<Longrightarrow>
        p' < length (pr0_states G Shn) \<and>
        lcore NF \<subseteq> set (pr0_states G Shn ! p') \<and>
        (p', st_find (lr0_states G Shn) (ccore NF)) \<in> set (mprod_states G Shn)\<close>
      using mtrack_goto[OF cores[OF hd_in_set[OF ne]] trk0]
      unfolding NF_def p'_def by blast
    have \<open>strack G Shn (NF # Xs) ((Tm a, FinRep [c]) # \<alpha>) (p' # pstk)\<close>
      by (rule strack_push[OF tr NF_def p'_def goto]) simp_all
    then show ?thesis unfolding gc'2[symmetric] by blast
  next
    case (DReduce pr)
    have step: \<open>mstep_cached G (map (xclosure_auto G) Xs) (Xs, w) (DReduce pr) = Some gc'\<close>
      using mreach_step.hyps(2) unfolding gc DReduce mstep_def by simp
    define d where \<open>d = length (snd pr)\<close>
    have d_lt: \<open>d < length Xs\<close>
      unfolding d_def by (rule mstep_reduce_shape[OF step]) blast
    have gc'0: \<open>gc' = (lgoto (map (xclosure_auto G) Xs ! d) (Nt (fst pr))
                  (red_set (hd (map (xclosure_auto G) Xs)) pr) # drop d Xs, w)\<close>
      unfolding d_def by (rule mstep_reduce_shape[OF step]) blast
    have ne: \<open>Xs \<noteq> []\<close> using d_lt by auto
    have hdd: \<open>hd (drop d Xs) = Xs ! d\<close> using d_lt by (simp add: hd_drop_conv_nth)
    define RA where \<open>RA = red_set (xclosure_auto G (hd Xs)) pr\<close>
    define NF where \<open>NF = lgoto (xclosure_auto G (hd (drop d Xs))) (Nt (fst pr)) RA\<close>
    define p' where
      \<open>p' = st_find (pr0_states G Shn)
              (cgoto (creach G (pr0_states G Shn ! (drop d pstk ! 0))) (Nt (fst pr)))\<close>
    have gc'2: \<open>fst gc' = NF # drop d Xs\<close>
      unfolding gc'0 NF_def RA_def hdd using d_lt ne by (simp add: hd_map)
    have d_le_a: \<open>d \<le> length \<alpha>\<close> using d_lt lenXa by simp
    have trd: \<open>strack G Shn (drop d Xs) (drop d \<alpha>) (drop d pstk)\<close>
      by (rule strack_drop[OF tr d_le_a])
    have pd: \<open>drop d pstk ! 0 = pstk ! d\<close> using len d_lt by simp
    have trkd: \<open>lcore (Xs ! d) \<noteq> {} \<Longrightarrow> pstk ! d < length (pr0_states G Shn) \<and>
        lcore (Xs ! d) \<subseteq> set (pr0_states G Shn ! (pstk ! d)) \<and>
        (pstk ! d, st_find (lr0_states G Shn) (ccore (Xs ! d))) \<in> set (mprod_states G Shn)\<close>
      using mtrackD[OF trX d_lt] by simp
    have goto: \<open>lcore NF \<noteq> {} \<Longrightarrow>
        p' < length (pr0_states G Shn) \<and>
        lcore NF \<subseteq> set (pr0_states G Shn ! p') \<and>
        (p', st_find (lr0_states G Shn) (ccore NF)) \<in> set (mprod_states G Shn)\<close>
      using mtrack_goto[OF cores[OF nth_mem[OF d_lt]] trkd]
      unfolding NF_def p'_def hdd pd by blast
    have sng0: \<open>fst pr \<in> set (anchored_nts G) \<Longrightarrow> \<exists>c. irep_set RA \<subseteq> {c}\<close>
      unfolding RA_def
      by (rule red_set_anchored_singleton[OF sh ne tmS sngI fresh])
    have slot0: \<open>\<And>l. l \<in> irep_set RA \<Longrightarrow> \<exists>pra R\<^sub>0. fst pra = fst pr \<and>
        (pra, 0, R\<^sub>0) \<in> set (xclosure_auto G (Xs ! d)) \<and> l \<in> irep_set R\<^sub>0\<close>
    proof -
      fix l assume l: \<open>l \<in> irep_set RA\<close>
      then obtain R where R: \<open>(pr, d, R) \<in> set (xclosure_auto G (hd Xs))\<close>
        and lR: \<open>l \<in> irep_set R\<close>
        unfolding RA_def red_set_correct d_def[symmetric] by blast
      have hd0: \<open>hd Xs = Xs ! 0\<close> using ne by (simp add: hd_conv_nth)
      show \<open>\<exists>pra R\<^sub>0. fst pra = fst pr \<and>
          (pra, 0, R\<^sub>0) \<in> set (xclosure_auto G (Xs ! d)) \<and> l \<in> irep_set R\<^sub>0\<close>
      proof (cases d)
        case 0
        have \<open>(pr, 0, R) \<in> set (xclosure_auto G (Xs ! d))\<close>
          using R hd0 unfolding 0 by simp
        then show ?thesis using lR by blast
      next
        case (Suc d')
        have kern: \<open>(pr, d, R) \<in> set (Xs ! 0)\<close>
          by (rule xclosure_auto_kernelD[OF R[unfolded hd0]]) (simp add: Suc)
        have z_lt: \<open>0 < length Xs\<close> using ne by simp
        have one_le: \<open>1 \<le> d\<close> using Suc by simp
        from dshape_persist[OF sh kern z_lt one_le] obtain R\<^sub>0 where
          m0: \<open>(pr, 0, R\<^sub>0) \<in> set (xclosure_auto G (Xs ! (0 + d)))\<close>
          and sb: \<open>irep_set R \<subseteq> irep_set R\<^sub>0\<close> by blast
        have \<open>(pr, 0, R\<^sub>0) \<in> set (xclosure_auto G (Xs ! d))\<close> using m0 by simp
        then show ?thesis using sb lR by blast
      qed
    qed
    have \<open>strack G Shn (NF # drop d Xs) ((Nt (fst pr), RA) # drop d \<alpha>) (p' # drop d pstk)\<close>
    proof (rule strack_push[OF trd NF_def p'_def goto])
      show \<open>\<And>a. Nt (fst pr) = Tm a \<Longrightarrow> \<exists>c. RA = FinRep [c]\<close> by simp
      show \<open>\<And>B. Nt (fst pr) = Nt B \<Longrightarrow> B \<in> set (anchored_nts G) \<Longrightarrow> \<exists>c. irep_set RA \<subseteq> {c}\<close>
        using sng0 by simp
      show \<open>\<And>B l. Nt (fst pr) = Nt B \<Longrightarrow> l \<in> irep_set RA \<Longrightarrow> \<exists>pra R\<^sub>0. fst pra = B \<and>
          (pra, 0, R\<^sub>0) \<in> set (xclosure_auto G (hd (drop d Xs))) \<and> l \<in> irep_set R\<^sub>0\<close>
        using slot0 unfolding hdd by simp
    qed
    then show ?thesis unfolding gc'2[symmetric] by blast
  qed
qed

section \<open>The descent to a rigid point\<close>

text \<open>The entry pool of the top frame of a tracked stack: the goto label's
  anchors, or \<open>istart_ind\<close> at the bottom frame.\<close>

definition epool :: \<open>('n, 't) is_cfg \<Rightarrow> (('n, 't) sym \<times> indrep) list \<Rightarrow> nat set\<close> where
  \<open>epool G \<alpha> = (case \<alpha> of [] \<Rightarrow> {istart_ind G} | (X, RA) # _ \<Rightarrow> irep_set RA)\<close>

lemma pin_edgesI:
  \<open>p < length gt \<Longrightarrow> (X, s) \<in> set (gt ! p) \<Longrightarrow> (p, X) \<in> set (pin_edges gt s)\<close>
  unfolding pin_edges_def by fastforce

lemma rho_classesI:
  assumes \<open>(pr, 0, \<rho>) \<in> set (wreach G (sts ! p))\<close> and \<open>fst pr = A\<close>
  shows \<open>\<rho> \<in> set (rho_classes G sts p A)\<close>
proof -
  have \<open>\<rho> \<in> set (List.map_filter
      (\<lambda>(pr, m, \<rho>). if fst pr = A \<and> m = 0 then Some \<rho> else None)
      (wreach G (sts ! p)))\<close>
    by (rule map_filterI[OF assms(1)]) (use assms(2) in simp)
  then show ?thesis unfolding rho_classes_def by simp
qed

text \<open>Popping the top frame of a tracked stack leaves a tracked stack.\<close>

text \<open>The descent: from any tracked stack whose top frame is live and whose
  two walk classes are satisfied at elements of the top entry pool, the
  \<^const>\<open>rdesc\<close> walk reaches a rigid point where both classes are
  satisfied at one \<^emph>\<open>shared\<close> anchor.  Rigid cases: the bottom frame
  (pool \<open>{istart_ind}\<close>), a shifted token (\<open>FinRep [c]\<close> pool), an anchored
  nonterminal (singleton-bounded pool).  Descend case: a non-anchored
  nonterminal entry, where each side re-anchors through its own dot-0 class
  of the predecessor's \<open>wreach\<close> (\<open>rho_classes\<close>), exactly one
  \<^const>\<open>rdesc\<close> step.\<close>

theorem strack_descent:
  assumes tr: \<open>strack G Shn Xs \<alpha> pstk\<close>
    and live: \<open>lcore (hd Xs) \<noteq> {}\<close>
    and l1: \<open>l\<^sub>1 \<in> epool G \<alpha>\<close> and s1: \<open>wsat \<sigma>\<^sub>1 c l\<^sub>1\<close>
    and l2: \<open>l\<^sub>2 \<in> epool G \<alpha>\<close> and s2: \<open>wsat \<sigma>\<^sub>2 c l\<^sub>2\<close>
  shows \<open>\<exists>i \<sigma>\<^sub>1' \<sigma>\<^sub>2' l'.
      (rdesc G (pr0_states G Shn) (pgtab G (pr0_states G Shn)) (anchored_nts G))\<^sup>*\<^sup>*
        (pstk ! 0, \<sigma>\<^sub>1, \<sigma>\<^sub>2) (i, \<sigma>\<^sub>1', \<sigma>\<^sub>2') \<and>
      rigid_at (p0start G Shn) (pgtab G (pr0_states G Shn)) (anchored_nts G) i \<and>
      wsat \<sigma>\<^sub>1' c l' \<and> wsat \<sigma>\<^sub>2' c l'\<close>
  using tr live l1 s1 l2 s2
proof (induction \<alpha> arbitrary: Xs pstk \<sigma>\<^sub>1 \<sigma>\<^sub>2 l\<^sub>1 l\<^sub>2)
  case Nil
  note sh = strackD(1)[OF Nil.prems(1)] and mt = strackD(2)[OF Nil.prems(1)]
    and lastp = strackD(3)[OF Nil.prems(1)]
  have lenX: \<open>length Xs = 1\<close> using dshapeD(1)[OF sh] by simp
  have lenp: \<open>length pstk = 1\<close> using mtrack_len[OF mt] lenX by simp
  have pstk_ne: \<open>pstk \<noteq> []\<close> using lenp by auto
  have p0: \<open>pstk ! 0 = p0start G Shn\<close>
    using lastp last_conv_nth[OF pstk_ne] lenp by simp
  have leq1: \<open>l\<^sub>1 = istart_ind G\<close> and leq2: \<open>l\<^sub>2 = istart_ind G\<close>
    using Nil.prems(3,5) unfolding epool_def by auto
  have rig: \<open>rigid_at (p0start G Shn) (pgtab G (pr0_states G Shn))
      (anchored_nts G) (pstk ! 0)\<close>
    unfolding rigid_at_def p0 by simp
  show ?case
    using rig Nil.prems(4,6) leq1 leq2
    by blast
next
  case (Cons e \<alpha>')
  obtain X\<^sub>0 RA where e: \<open>e = (X\<^sub>0, RA)\<close> by (cases e)
  note tr = Cons.prems(1)[unfolded e]
  note sh = strackD(1)[OF tr] and mt = strackD(2)[OF tr] and lastp = strackD(3)[OF tr]
    and tmS = strackD(4)[OF tr] and sng = strackD(5)[OF tr] and slot = strackD(6)[OF tr]
    and adj = strackD(7)[OF tr]
  note lenX = dshapeD(1)[OF sh] and bot = dshapeD(2)[OF sh] and shp = dshapeD(3)[OF sh]
  have Xs_ne: \<open>Xs \<noteq> []\<close> using lenX by auto
  have hd0: \<open>hd Xs = Xs ! 0\<close> using Xs_ne by (simp add: hd_conv_nth)
  have f0: \<open>Xs ! 0 = lgoto (xclosure_auto G (Xs ! Suc 0)) X\<^sub>0 RA\<close>
    using shp[of 0] by simp
  obtain pm where pm: \<open>pm \<in> lcore (Xs ! 0)\<close>
    using Cons.prems(2) hd0 by auto
  obtain pr m where topc: \<open>(pr, m) \<in> lcore (Xs ! 0)\<close>
    using pm by (cases pm) auto
  obtain R where topm: \<open>(pr, m, R) \<in> set (Xs ! 0)\<close> and topne: \<open>irep_nonempty R\<close>
    using topc unfolding lcore_def by auto
  obtain j where jR: \<open>j \<in> irep_set R\<close>
    using topne unfolding irep_nonempty_correct by blast
  obtain m\<^sub>0 where m: \<open>m = Suc m\<^sub>0\<close>
    using lgoto_dot_pos[OF topm[unfolded f0]] by (cases m) auto
  from lgoto_kernel_step[OF topm[unfolded f0 m]] obtain R\<^sub>s where
    src: \<open>(pr, m\<^sub>0, R\<^sub>s) \<in> set (xclosure_auto G (Xs ! Suc 0))\<close>
    and m0lt: \<open>m\<^sub>0 < length (snd pr)\<close>
    and dsym: \<open>fst (snd pr ! m\<^sub>0) = X\<^sub>0\<close>
    and Req: \<open>R = irep_inter R\<^sub>s (irep_pre (snd (snd pr ! m\<^sub>0)) RA)\<close> .
  have jRs: \<open>j \<in> irep_set R\<^sub>s\<close> using jR unfolding Req by simp
  have live1: \<open>lcore (Xs ! Suc 0) \<noteq> {}\<close>
    by (rule closure_live_kernel[OF src jRs])
  have sk_lt: \<open>Suc 0 < length Xs\<close> using lenX by simp
  have p1_lt: \<open>pstk ! Suc 0 < length (pr0_states G Shn)\<close>
    and cover1: \<open>lcore (Xs ! Suc 0) \<subseteq> set (pr0_states G Shn ! (pstk ! Suc 0))\<close>
    using mtrackD[OF mt sk_lt live1] by blast+
  have kernC: \<open>\<And>pr' m' R'. (pr', m', R') \<in> set (Xs ! Suc 0) \<Longrightarrow>
      irep_nonempty R' \<Longrightarrow> (pr', m') \<in> set (pr0_states G Shn ! (pstk ! Suc 0))\<close>
    by (blast intro: lcore_subD_ne[OF cover1])
  have srcC: \<open>(pr, m\<^sub>0) \<in> set (creach G (pr0_states G Shn ! (pstk ! Suc 0)))\<close>
    by (rule xclosure_auto_live_creach[OF kernC src jRs])
  have adj0: \<open>pstk ! 0 = st_find (pr0_states G Shn)
      (cgoto (creach G (pr0_states G Shn ! (pstk ! Suc 0))) X\<^sub>0)\<close>
    using adj[rule_format, of 0] by simp
  have edge_tab: \<open>(X\<^sub>0, pstk ! 0) \<in> set (pgtab G (pr0_states G Shn) ! (pstk ! Suc 0))\<close>
    using pgtab_mem[OF p1_lt srcC m0lt] unfolding dsym adj0 by simp
  have p1_gt_lt: \<open>pstk ! Suc 0 < length (pgtab G (pr0_states G Shn))\<close>
    using p1_lt by simp
  have edge: \<open>(pstk ! Suc 0, X\<^sub>0)
      \<in> set (pin_edges (pgtab G (pr0_states G Shn)) (pstk ! 0))\<close>
    by (rule pin_edgesI[OF p1_gt_lt edge_tab])
  have ep: \<open>epool G ((X\<^sub>0, RA) # \<alpha>') = irep_set RA\<close>
    unfolding epool_def by simp
  show ?case
  proof (cases \<open>case X\<^sub>0 of Tm a \<Rightarrow> True | Nt A \<Rightarrow> A \<in> set (anchored_nts G)\<close>)
    case True
    have rig: \<open>rigid_at (p0start G Shn) (pgtab G (pr0_states G Shn))
        (anchored_nts G) (pstk ! 0)\<close>
      unfolding rigid_at_def
      using edge True by (auto simp: list_ex_iff)
    have pool_sng: \<open>\<exists>c\<^sub>0. irep_set RA \<subseteq> {c\<^sub>0}\<close>
    proof (cases X\<^sub>0)
      case (Tm a)
      then obtain c\<^sub>0 where \<open>RA = FinRep [c\<^sub>0]\<close>
        using tmS[rule_format, of 0 a] by auto
      then show ?thesis by auto
    next
      case (Nt A)
      then show ?thesis using sng[rule_format, of 0 A] True by auto
    qed
    obtain c\<^sub>0 where sub: \<open>irep_set RA \<subseteq> {c\<^sub>0}\<close> using pool_sng by blast
    have leq1: \<open>l\<^sub>1 = c\<^sub>0\<close> and leq2: \<open>l\<^sub>2 = c\<^sub>0\<close>
      using Cons.prems(3,5)[unfolded e ep] sub by auto
    show ?thesis
      using rig Cons.prems(4,6) leq1 leq2
      by blast
  next
    case False
    then obtain A where XNt: \<open>X\<^sub>0 = Nt A\<close> and Ana: \<open>A \<notin> set (anchored_nts G)\<close>
      by (cases X\<^sub>0) auto
    have kernP: \<open>\<And>pr' m' R' j'. (pr', m', R') \<in> set (Xs ! Suc 0) \<Longrightarrow>
        j' \<in> irep_set R' \<Longrightarrow>
        \<exists>\<rho> l. (pr', m', \<rho>) \<in> set (wreach G (pr0_states G Shn ! (pstk ! Suc 0))) \<and>
              l \<in> epool G \<alpha>' \<and> wsat \<rho> l j'\<close>
    proof -
      fix pr' m' R' j' assume a: \<open>(pr', m', R') \<in> set (Xs ! Suc 0)\<close>
        and b: \<open>j' \<in> irep_set R'\<close>
      have bne: \<open>irep_nonempty R'\<close> using b unfolding irep_nonempty_correct by auto
      have cov: \<open>(pr', m') \<in> set (pr0_states G Shn ! (pstk ! Suc 0))\<close>
        by (rule kernC[OF a bne])
      show \<open>\<exists>\<rho> l. (pr', m', \<rho>) \<in> set (wreach G (pr0_states G Shn ! (pstk ! Suc 0))) \<and>
          l \<in> epool G \<alpha>' \<and> wsat \<rho> l j'\<close>
      proof (cases \<alpha>')
        case Nil
        have x1: \<open>Xs ! Suc 0 = xinit G Shn\<close> using bot unfolding Nil by simp
        from wanch_pool_xinit[OF a[unfolded x1] b cov] obtain \<rho> where
          \<open>(pr', m', \<rho>) \<in> set (wreach G (pr0_states G Shn ! (pstk ! Suc 0)))\<close>
          and \<open>wsat \<rho> (istart_ind G) j'\<close> by blast
        then show ?thesis unfolding epool_def Nil by auto
      next
        case (Cons e' \<alpha>'')
        obtain X\<^sub>1 RA\<^sub>1 where e': \<open>e' = (X\<^sub>1, RA\<^sub>1)\<close> by (cases e')
        have sk1: \<open>Suc 0 < length ((X\<^sub>0, RA) # \<alpha>')\<close> unfolding Cons by simp
        have f1: \<open>Xs ! Suc 0 =
            lgoto (xclosure_auto G (Xs ! Suc (Suc 0))) X\<^sub>1 RA\<^sub>1\<close>
          using shp[OF sk1] unfolding Cons e' by simp
        have covL: \<open>\<And>pra ma Ra ja. (pra, ma, Ra)
            \<in> set (lgoto (xclosure_auto G (Xs ! Suc (Suc 0))) X\<^sub>1 RA\<^sub>1) \<Longrightarrow>
            ja \<in> irep_set Ra \<Longrightarrow>
            (pra, ma) \<in> set (pr0_states G Shn ! (pstk ! Suc 0))\<close>
        proof -
          fix pra ma Ra ja
          assume aa: \<open>(pra, ma, Ra)
              \<in> set (lgoto (xclosure_auto G (Xs ! Suc (Suc 0))) X\<^sub>1 RA\<^sub>1)\<close>
            and bb: \<open>ja \<in> irep_set Ra\<close>
          have mm: \<open>(pra, ma, Ra) \<in> set (Xs ! Suc 0)\<close> using aa f1 by simp
          have nn: \<open>irep_nonempty Ra\<close>
            using bb unfolding irep_nonempty_correct by auto
          show \<open>(pra, ma) \<in> set (pr0_states G Shn ! (pstk ! Suc 0))\<close>
            by (rule kernC[OF mm nn])
        qed
        have ex: \<open>\<exists>\<rho> l. (pr', m', \<rho>)
              \<in> set (wreach G (pr0_states G Shn ! (pstk ! Suc 0))) \<and>
            l \<in> irep_set RA\<^sub>1 \<and> wsat \<rho> l j'\<close>
          by (rule wanch_pool_lgoto[OF _ a[unfolded f1] b]) (rule covL)
        from ex obtain \<rho> l where
          \<open>(pr', m', \<rho>) \<in> set (wreach G (pr0_states G Shn ! (pstk ! Suc 0)))\<close>
          and \<open>l \<in> irep_set RA\<^sub>1\<close> and \<open>wsat \<rho> l j'\<close> by blast
        then show ?thesis unfolding epool_def Cons e' by auto
      qed
    qed
    have side: \<open>\<And>l\<^sub>a \<sigma>\<^sub>a. l\<^sub>a \<in> irep_set RA \<Longrightarrow> wsat \<sigma>\<^sub>a c l\<^sub>a \<Longrightarrow>
        \<exists>\<rho> l'. \<rho> \<in> set (rho_classes G (pr0_states G Shn) (pstk ! Suc 0) A) \<and>
               l' \<in> epool G \<alpha>' \<and> wsat (wcomp (winv \<rho>) \<sigma>\<^sub>a) c l'\<close>
    proof -
      fix l\<^sub>a \<sigma>\<^sub>a assume la: \<open>l\<^sub>a \<in> irep_set RA\<close> and sa: \<open>wsat \<sigma>\<^sub>a c l\<^sub>a\<close>
      have bl: \<open>\<forall>l \<in> irep_set RA. \<exists>pra R\<^sub>0. fst pra = A \<and>
          (pra, 0, R\<^sub>0) \<in> set (xclosure_auto G (Xs ! Suc 0)) \<and> l \<in> irep_set R\<^sub>0\<close>
        using slot[rule_format, of 0 A] XNt by simp
      from bspec[OF bl la] obtain pra R\<^sub>0 where
        fA: \<open>fst pra = A\<close>
        and mem0: \<open>(pra, 0, R\<^sub>0) \<in> set (xclosure_auto G (Xs ! Suc 0))\<close>
        and laR0: \<open>l\<^sub>a \<in> irep_set R\<^sub>0\<close> by blast
      have ex: \<open>\<exists>\<rho> l'. (pra, 0, \<rho>)
            \<in> set (wreach G (pr0_states G Shn ! (pstk ! Suc 0))) \<and>
          l' \<in> epool G \<alpha>' \<and> wsat \<rho> l' l\<^sub>a\<close>
        by (rule xclosure_auto_pool[OF _ mem0 laR0]) (rule kernP)
      from ex obtain \<rho> l' where
        wr: \<open>(pra, 0, \<rho>) \<in> set (wreach G (pr0_states G Shn ! (pstk ! Suc 0)))\<close>
        and l'P: \<open>l' \<in> epool G \<alpha>'\<close> and wl: \<open>wsat \<rho> l' l\<^sub>a\<close> by blast
      have rc: \<open>\<rho> \<in> set (rho_classes G (pr0_states G Shn) (pstk ! Suc 0) A)\<close>
        by (rule rho_classesI[OF wr fA])
      have ws: \<open>wsat (wcomp (winv \<rho>) \<sigma>\<^sub>a) c l'\<close>
        by (rule wcomp_sound[OF sa winv_sound[OF wl]])
      show \<open>\<exists>\<rho> l'. \<rho> \<in> set (rho_classes G (pr0_states G Shn) (pstk ! Suc 0) A) \<and>
          l' \<in> epool G \<alpha>' \<and> wsat (wcomp (winv \<rho>) \<sigma>\<^sub>a) c l'\<close>
        using rc l'P ws by blast
    qed
    have la1: \<open>l\<^sub>1 \<in> irep_set RA\<close> using Cons.prems(3)[unfolded e ep] .
    have la2: \<open>l\<^sub>2 \<in> irep_set RA\<close> using Cons.prems(5)[unfolded e ep] .
    from side[OF la1 Cons.prems(4)] obtain \<rho>\<^sub>1 l\<^sub>1' where
      rc1: \<open>\<rho>\<^sub>1 \<in> set (rho_classes G (pr0_states G Shn) (pstk ! Suc 0) A)\<close>
      and l1': \<open>l\<^sub>1' \<in> epool G \<alpha>'\<close>
      and ws1: \<open>wsat (wcomp (winv \<rho>\<^sub>1) \<sigma>\<^sub>1) c l\<^sub>1'\<close> by blast
    from side[OF la2 Cons.prems(6)] obtain \<rho>\<^sub>2 l\<^sub>2' where
      rc2: \<open>\<rho>\<^sub>2 \<in> set (rho_classes G (pr0_states G Shn) (pstk ! Suc 0) A)\<close>
      and l2': \<open>l\<^sub>2' \<in> epool G \<alpha>'\<close>
      and ws2: \<open>wsat (wcomp (winv \<rho>\<^sub>2) \<sigma>\<^sub>2) c l\<^sub>2'\<close> by blast
    have step: \<open>rdesc G (pr0_states G Shn) (pgtab G (pr0_states G Shn))
        (anchored_nts G) (pstk ! 0, \<sigma>\<^sub>1, \<sigma>\<^sub>2)
        (pstk ! Suc 0, wcomp (winv \<rho>\<^sub>1) \<sigma>\<^sub>1, wcomp (winv \<rho>\<^sub>2) \<sigma>\<^sub>2)\<close>
      by (rule rdesc_step[OF edge[unfolded XNt] Ana rc1 rc2])
    have tr': \<open>strack G Shn (tl Xs) \<alpha>' (tl pstk)\<close> by (rule strack_tl[OF tr])
    obtain x\<^sub>0 Xr where Xs_eq: \<open>Xs = x\<^sub>0 # Xr\<close> using Xs_ne by (cases Xs) auto
    have Xr_ne: \<open>Xr \<noteq> []\<close> using lenX Xs_eq by auto
    have live': \<open>lcore (hd (tl Xs)) \<noteq> {}\<close>
      using live1 hd_conv_nth[OF Xr_ne] unfolding Xs_eq by simp
    have lenp: \<open>length pstk = length Xs\<close> by (rule mtrack_len[OF mt])
    obtain p\<^sub>0 Pr where pstk_eq: \<open>pstk = p\<^sub>0 # Pr\<close>
      using lenp Xs_ne by (cases pstk) auto
    from Cons.IH[OF tr' live' l1' ws1 l2' ws2] obtain i \<sigma>\<^sub>1' \<sigma>\<^sub>2' l' where
      ch: \<open>(rdesc G (pr0_states G Shn) (pgtab G (pr0_states G Shn))
             (anchored_nts G))\<^sup>*\<^sup>*
           (tl pstk ! 0, wcomp (winv \<rho>\<^sub>1) \<sigma>\<^sub>1, wcomp (winv \<rho>\<^sub>2) \<sigma>\<^sub>2) (i, \<sigma>\<^sub>1', \<sigma>\<^sub>2')\<close>
      and rig: \<open>rigid_at (p0start G Shn) (pgtab G (pr0_states G Shn))
             (anchored_nts G) i\<close>
      and w1: \<open>wsat \<sigma>\<^sub>1' c l'\<close> and w2: \<open>wsat \<sigma>\<^sub>2' c l'\<close> by blast
    have tlp0: \<open>tl pstk ! 0 = pstk ! Suc 0\<close> unfolding pstk_eq by simp
    have chain: \<open>(rdesc G (pr0_states G Shn) (pgtab G (pr0_states G Shn))
          (anchored_nts G))\<^sup>*\<^sup>* (pstk ! 0, \<sigma>\<^sub>1, \<sigma>\<^sub>2) (i, \<sigma>\<^sub>1', \<sigma>\<^sub>2')\<close>
      by (rule converse_rtranclp_into_rtranclp[OF step ch[unfolded tlp0]])
    show ?thesis using chain rig w1 w2 by blast
  qed
qed


section \<open>Sufficiency of the rigid-point check\<close>

text \<open>The final assembly: \<open>rlalr_conflicts G Shn = []\<close> plus
  \<^const>\<open>fresh_name\<close> implies \<^const>\<open>mdet\<close>.  A determinism violation
  yields two live candidates at a tracked, live top frame; each candidate's
  runtime license transports to a static seed at the tracked product state
  (\<open>rreds_at\<close> / \<open>shift_cells\<close>), the pair of walk classes is in
  \<open>rpairs_at\<close>, the empty report makes the walk return \<open>False\<close>, and
  \<open>strack_descent\<close> + \<open>rfire_sound\<close> + \<open>wdisjoint_sound\<close> close the
  contradiction.  \<open>None\<close>/\<open>None\<close> pairs are refuted by \<open>rr_none_at\<close>
  directly; a reduce of the fresh start name cannot have a live successor.\<close>

text \<open>The frame-0 pooled width invariant, packaged: every anchored item of
  the top frame's closure carries a \<open>wreach\<close> class at the tracked precise
  state, anchored at some element of the top entry pool.\<close>

lemma strack_pool:
  assumes tr: \<open>strack G Shn Xs \<alpha> pstk\<close> and live: \<open>lcore (hd Xs) \<noteq> {}\<close>
    and mem: \<open>(pr, m, R) \<in> set (xclosure_auto G (hd Xs))\<close>
    and jR: \<open>j \<in> irep_set R\<close>
  shows \<open>\<exists>\<rho> l. (pr, m, \<rho>) \<in> set (wreach G (pr0_states G Shn ! (pstk ! 0))) \<and>
        l \<in> epool G \<alpha> \<and> wsat \<rho> l j\<close>
proof -
  note sh = strackD(1)[OF tr] and mt = strackD(2)[OF tr]
  note lenX = dshapeD(1)[OF sh] and bot = dshapeD(2)[OF sh] and shp = dshapeD(3)[OF sh]
  have Xs_ne: \<open>Xs \<noteq> []\<close> using lenX by auto
  have hd0: \<open>hd Xs = Xs ! 0\<close> using Xs_ne by (simp add: hd_conv_nth)
  have z_lt: \<open>0 < length Xs\<close> using Xs_ne by auto
  have live0: \<open>lcore (Xs ! 0) \<noteq> {}\<close> using live hd0 by simp
  have cover0: \<open>lcore (Xs ! 0) \<subseteq> set (pr0_states G Shn ! (pstk ! 0))\<close>
    using mtrackD[OF mt z_lt live0] by blast
  have kern0: \<open>\<And>pr' m' R' j'. (pr', m', R') \<in> set (Xs ! 0) \<Longrightarrow>
      j' \<in> irep_set R' \<Longrightarrow>
      \<exists>\<rho> l. (pr', m', \<rho>) \<in> set (wreach G (pr0_states G Shn ! (pstk ! 0))) \<and>
            l \<in> epool G \<alpha> \<and> wsat \<rho> l j'\<close>
  proof -
    fix pr' m' R' j' assume a: \<open>(pr', m', R') \<in> set (Xs ! 0)\<close>
      and b: \<open>j' \<in> irep_set R'\<close>
    have cov: \<open>(pr', m') \<in> set (pr0_states G Shn ! (pstk ! 0))\<close>
      by (rule lcore_subD[OF cover0 a b])
    show \<open>\<exists>\<rho> l. (pr', m', \<rho>) \<in> set (wreach G (pr0_states G Shn ! (pstk ! 0))) \<and>
        l \<in> epool G \<alpha> \<and> wsat \<rho> l j'\<close>
    proof (cases \<alpha>)
      case Nil
      have x0: \<open>Xs ! 0 = xinit G Shn\<close> using bot unfolding Nil by simp
      from wanch_pool_xinit[OF a[unfolded x0] b cov] obtain \<rho> where
        \<open>(pr', m', \<rho>) \<in> set (wreach G (pr0_states G Shn ! (pstk ! 0)))\<close>
        and \<open>wsat \<rho> (istart_ind G) j'\<close> by blast
      then show ?thesis unfolding epool_def Nil by auto
    next
      case (Cons e \<alpha>')
      obtain X\<^sub>0 RA where e: \<open>e = (X\<^sub>0, RA)\<close> by (cases e)
      have z_la: \<open>0 < length \<alpha>\<close> unfolding Cons by simp
      have f0: \<open>Xs ! 0 = lgoto (xclosure_auto G (Xs ! Suc 0)) X\<^sub>0 RA\<close>
        using shp[OF z_la] unfolding Cons e by simp
      have covL: \<open>\<And>pra ma Ra ja. (pra, ma, Ra)
          \<in> set (lgoto (xclosure_auto G (Xs ! Suc 0)) X\<^sub>0 RA) \<Longrightarrow>
          ja \<in> irep_set Ra \<Longrightarrow>
          (pra, ma) \<in> set (pr0_states G Shn ! (pstk ! 0))\<close>
      proof -
        fix pra ma Ra ja
        assume aa: \<open>(pra, ma, Ra)
            \<in> set (lgoto (xclosure_auto G (Xs ! Suc 0)) X\<^sub>0 RA)\<close>
          and bb: \<open>ja \<in> irep_set Ra\<close>
        have \<open>(pra, ma, Ra) \<in> set (Xs ! 0)\<close> using aa f0 by simp
        then show \<open>(pra, ma) \<in> set (pr0_states G Shn ! (pstk ! 0))\<close>
          using bb by (rule lcore_subD[OF cover0])
      qed
      have ex: \<open>\<exists>\<rho> l. (pr', m', \<rho>)
            \<in> set (wreach G (pr0_states G Shn ! (pstk ! 0))) \<and>
          l \<in> irep_set RA \<and> wsat \<rho> l j'\<close>
        by (rule wanch_pool_lgoto[OF _ a[unfolded f0] b]) (rule covL)
      then show ?thesis unfolding epool_def Cons e by auto
    qed
  qed
  show ?thesis
    by (rule xclosure_auto_pool[OF _ mem[unfolded hd0] jR]) (rule kern0)
qed

text \<open>Membership constructors for the static seeds.\<close>

lemma rreds_at_memI:
  assumes cell: \<open>(i\<^sub>m, (pr, length (snd pr)), t, \<tau>) \<in> set L\<close>
    and shn: \<open>fst pr \<noteq> Shn\<close>
    and wmem: \<open>(pr, length (snd pr), \<rho>) \<in> set (wreach G (sp ! i\<^sub>p))\<close>
  shows \<open>(pr, t, wcomp (winv \<rho>) \<tau>) \<in> set (rreds_at G Shn sp L i\<^sub>p i\<^sub>m)\<close>
proof -
  have inner: \<open>(pr, t, wcomp (winv \<rho>) \<tau>)
      \<in> set (map (\<lambda>(pr', m', \<rho>). (pr, t, wcomp (winv \<rho>) \<tau>))
          (filter (\<lambda>(pr', m', \<rho>). pr' = pr \<and> m' = length (snd pr))
            (wreach G (sp ! i\<^sub>p))))\<close>
    using wmem by force
  show ?thesis
    unfolding rreds_at_def Let_def
    by (rule concat_map_memI[OF cell]) (use inner shn in auto)
qed

lemma shift_cells_memI:
  assumes \<open>(pr, m, \<rho>) \<in> set ws\<close> and \<open>m < length (snd pr)\<close>
    and \<open>fst (snd pr ! m) = Tm a\<close>
  shows \<open>(a, wcomp (winv \<rho>) (w_of (snd (snd pr ! m)))) \<in> set (shift_cells ws)\<close>
  unfolding shift_cells_def
  by (rule concat_map_memI[OF assms(1)]) (use assms(2,3) in simp)

lemma rpairs_at_srI:
  assumes red: \<open>(pr, Some a, \<tau>) \<in> set (rreds_at G Shn sp L i\<^sub>p i\<^sub>m)\<close>
    and sh: \<open>(a, \<tau>') \<in> set (shift_cells (wreach G (sp ! i\<^sub>p)))\<close>
  shows \<open>(\<tau>, \<tau>') \<in> set (rpairs_at G Shn sp L i\<^sub>p i\<^sub>m)\<close>
proof -
  have \<open>(\<tau>, \<tau>') \<in> set (concat (map (\<lambda>(pr, t, \<tau>). case t of
        Some a \<Rightarrow> map (\<lambda>(a', \<tau>'). (\<tau>, \<tau>'))
            (filter (\<lambda>(a', \<tau>'). a' = a) (shift_cells (wreach G (sp ! i\<^sub>p))))
      | None \<Rightarrow> []) (rreds_at G Shn sp L i\<^sub>p i\<^sub>m)))\<close>
    by (rule concat_map_memI[OF red]) (use sh in force)
  then show ?thesis unfolding rpairs_at_def Let_def by simp
qed

lemma rpairs_at_rrI:
  assumes r1: \<open>(pr\<^sub>1, Some a, \<tau>\<^sub>1) \<in> set (rreds_at G Shn sp L i\<^sub>p i\<^sub>m)\<close>
    and r2: \<open>(pr\<^sub>2, Some a, \<tau>\<^sub>2) \<in> set (rreds_at G Shn sp L i\<^sub>p i\<^sub>m)\<close>
    and ne: \<open>pr\<^sub>2 \<noteq> pr\<^sub>1\<close>
  shows \<open>(\<tau>\<^sub>1, \<tau>\<^sub>2) \<in> set (rpairs_at G Shn sp L i\<^sub>p i\<^sub>m)\<close>
proof -
  have inner: \<open>(\<tau>\<^sub>1, \<tau>\<^sub>2) \<in> set (List.map_filter (\<lambda>(pr', t', \<tau>').
      if pr' \<noteq> pr\<^sub>1 \<and> t' = Some a \<and> Some a \<noteq> None then Some (\<tau>\<^sub>1, \<tau>') else None)
      (rreds_at G Shn sp L i\<^sub>p i\<^sub>m))\<close>
    by (rule map_filterI[OF r2]) (use ne in simp)
  have \<open>(\<tau>\<^sub>1, \<tau>\<^sub>2) \<in> set (concat (map (\<lambda>(pr, t, \<tau>). List.map_filter (\<lambda>(pr', t', \<tau>').
        if pr' \<noteq> pr \<and> t' = t \<and> t \<noteq> None then Some (\<tau>, \<tau>') else None)
        (rreds_at G Shn sp L i\<^sub>p i\<^sub>m)) (rreds_at G Shn sp L i\<^sub>p i\<^sub>m)))\<close>
    by (rule concat_map_memI[OF r1]) (use inner in simp)
  then show ?thesis unfolding rpairs_at_def Let_def by simp
qed

lemma rr_none_atI:
  assumes r1: \<open>(pr\<^sub>1, None, \<tau>\<^sub>1) \<in> set (rreds_at G Shn sp L i\<^sub>p i\<^sub>m)\<close>
    and r2: \<open>(pr\<^sub>2, None, \<tau>\<^sub>2) \<in> set (rreds_at G Shn sp L i\<^sub>p i\<^sub>m)\<close>
    and ne: \<open>pr\<^sub>2 \<noteq> pr\<^sub>1\<close>
  shows \<open>rr_none_at G Shn sp L i\<^sub>p i\<^sub>m\<close>
proof -
  have inner: \<open>list_ex (\<lambda>(pr', t', \<tau>'). pr' \<noteq> pr\<^sub>1 \<and> t' = None)
      (rreds_at G Shn sp L i\<^sub>p i\<^sub>m)\<close>
    unfolding list_ex_iff by (rule bexI[OF _ r2]) (use ne in simp)
  have outer: \<open>list_ex (\<lambda>(pr, t, \<tau>). t = None \<and>
      list_ex (\<lambda>(pr', t', \<tau>'). pr' \<noteq> pr \<and> t' = None)
        (rreds_at G Shn sp L i\<^sub>p i\<^sub>m)) (rreds_at G Shn sp L i\<^sub>p i\<^sub>m)\<close>
    unfolding list_ex_iff
    by (rule bexI[OF _ r1]) (use inner in \<open>fastforce simp: list_ex_iff\<close>)
  show ?thesis unfolding rr_none_at_def Let_def using outer by simp
qed

text \<open>Candidates are a shift on a nonempty input or a licensed,
  non-vacuous reduce.\<close>

lemma dcands_shift_or_reduce:
  assumes \<open>a \<in> set (dcands G i cells CL (Xs, w))\<close>
  shows \<open>a = DShift \<and> w \<noteq> [] \<or> (\<exists>pr. a = DReduce pr \<and>
      irep_nonempty (red_set CL pr) \<and> dlic i cells w pr (red_set CL pr))\<close>
  using assms unfolding dcands_def
  by (auto simp: Let_def split: if_splits list.splits)

text \<open>A reduce of the fresh start name has no live successor: the goto
  frame's kernel items would need \<open>Nt Shn\<close> at a dot of the exposed frame's
  closure, but \<open>Shn\<close> occurs in no grammar symbol.\<close>

lemma shn_reduce_dead:
  assumes tr: \<open>strack G Shn Xs \<alpha> pstk\<close>
    and fresh: \<open>fresh_name G Shn\<close>
    and step: \<open>mstep G (Xs, w) (DReduce pr) = Some gc'\<close>
    and shn: \<open>fst pr = Shn\<close>
    and lv: \<open>dlive gc'\<close>
  shows False
proof -
  note mt = strackD(2)[OF tr]
  have step': \<open>mstep_cached G (map (xclosure_auto G) Xs) (Xs, w) (DReduce pr) = Some gc'\<close>
    using step unfolding mstep_def by simp
  define d where \<open>d = length (snd pr)\<close>
  have d_lt: \<open>d < length Xs\<close>
    unfolding d_def by (rule mstep_reduce_shape[OF step']) blast
  have gc': \<open>gc' = (lgoto (map (xclosure_auto G) Xs ! d) (Nt (fst pr))
        (red_set (hd (map (xclosure_auto G) Xs)) pr) # drop d Xs, w)\<close>
    unfolding d_def by (rule mstep_reduce_shape[OF step']) blast
  have lvt: \<open>dlive (lgoto (xclosure_auto G (Xs ! d)) (Nt Shn)
      (red_set (hd (map (xclosure_auto G) Xs)) pr) # drop d Xs, w)\<close>
    using lv unfolding gc' shn using d_lt by simp
  from lvt obtain pr\<^sub>1 m\<^sub>1 R\<^sub>1 j\<^sub>1 where
    itm0: \<open>(pr\<^sub>1, m\<^sub>1, R\<^sub>1) \<in> set (hd (lgoto (xclosure_auto G (Xs ! d)) (Nt Shn)
        (red_set (hd (map (xclosure_auto G) Xs)) pr) # drop d Xs))\<close>
    and jR1: \<open>j\<^sub>1 \<in> irep_set R\<^sub>1\<close>
    by (blast elim: dliveE)
  have itm: \<open>(pr\<^sub>1, m\<^sub>1, R\<^sub>1) \<in> set (lgoto (xclosure_auto G (Xs ! d)) (Nt Shn)
      (red_set (hd (map (xclosure_auto G) Xs)) pr))\<close>
    using itm0 by simp
  obtain m\<^sub>0 where m1: \<open>m\<^sub>1 = Suc m\<^sub>0\<close>
    using lgoto_dot_pos[OF itm] by (cases m\<^sub>1) auto
  from lgoto_kernel_step[OF itm[unfolded m1]] obtain R\<^sub>s where
    src: \<open>(pr\<^sub>1, m\<^sub>0, R\<^sub>s) \<in> set (xclosure_auto G (Xs ! d))\<close>
    and m0lt: \<open>m\<^sub>0 < length (snd pr\<^sub>1)\<close>
    and dsym: \<open>fst (snd pr\<^sub>1 ! m\<^sub>0) = Nt Shn\<close>
    and Req: \<open>R\<^sub>1 = irep_inter R\<^sub>s (irep_pre (snd (snd pr\<^sub>1 ! m\<^sub>0))
        (red_set (hd (map (xclosure_auto G) Xs)) pr))\<close> .
  have jRs: \<open>j\<^sub>1 \<in> irep_set R\<^sub>s\<close> using jR1 unfolding Req by simp
  have lived: \<open>lcore (Xs ! d) \<noteq> {}\<close> by (rule closure_live_kernel[OF src jRs])
  have pd_lt: \<open>pstk ! d < length (pr0_states G Shn)\<close>
    and coverd: \<open>lcore (Xs ! d) \<subseteq> set (pr0_states G Shn ! (pstk ! d))\<close>
    using mtrackD[OF mt d_lt lived] by blast+
  have kernD: \<open>\<And>pr' m' R'. (pr', m', R') \<in> set (Xs ! d) \<Longrightarrow>
      irep_nonempty R' \<Longrightarrow> (pr', m') \<in> set (pr0_states G Shn ! (pstk ! d))\<close>
    by (blast intro: lcore_subD_ne[OF coverd])
  have srcC: \<open>(pr\<^sub>1, m\<^sub>0) \<in> set (creach G (pr0_states G Shn ! (pstk ! d)))\<close>
    by (rule xclosure_auto_live_creach[OF kernD src jRs])
  have crU: \<open>set (creach G (pr0_states G Shn ! (pstk ! d))) \<subseteq> cuniv G Shn\<close>
    by (rule creach_univ[OF pr0_states_univ[OF nth_mem[OF pd_lt]]])
  have \<open>fst (snd pr\<^sub>1 ! m\<^sub>0) \<in> set (gram_syms G)\<close>
    by (rule dot_sym_gram[OF crU srcC m0lt])
  then have inG: \<open>Nt Shn \<in> set (gram_syms G)\<close> unfolding dsym .
  have \<open>Nt Shn \<notin> set (gram_syms G)\<close>
  proof
    assume mem: \<open>Nt Shn \<in> set (gram_syms G)\<close>
    show False
    proof (cases \<open>Nt Shn = Nt (istart G)\<close>)
      case True
      then show False using fresh unfolding fresh_name_def by simp
    next
      case False
      have inL: \<open>Nt Shn \<in> set (concat (map (\<lambda>(A, y). map fst y) (iprods G)))\<close>
        using mem False unfolding gram_syms_def by (auto split: if_splits)
      from inL obtain A rhs where pmem: \<open>(A, rhs) \<in> set (iprods G)\<close>
        and inrhs: \<open>Nt Shn \<in> set (map fst rhs)\<close> by fastforce
      from inrhs obtain e where emem: \<open>e \<in> set rhs\<close>
        and efst: \<open>fst e = Nt Shn\<close> by auto
      obtain X r where eeq: \<open>e = (X, r)\<close> by (cases e)
      have ball2: \<open>\<forall>(X', r') \<in> set rhs. X' \<noteq> Nt Shn\<close>
        using fresh pmem unfolding fresh_name_def by fastforce
      have \<open>X \<noteq> Nt Shn\<close> using ball2 emem unfolding eeq by fastforce
      then show False using efst eeq by simp
    qed
  qed
  then show False using inG by simp
qed

text \<open>Each runtime license transports to a static seed at the tracked
  product state.\<close>

lemma reduce_seed_Some:
  assumes tr: \<open>strack G Shn Xs \<alpha> pstk\<close>
    and live: \<open>lcore (hd Xs) \<noteq> {}\<close>
    and ne: \<open>Xs \<noteq> []\<close>
    and ok: \<open>didx_ok G (lr0_states G Shn) Xs istk\<close>
    and lic: \<open>dlic (hd istk) (red_buckets G Shn (length (lr0_states G Shn)) ! hd istk)
        ((a, c) # w') pr (red_set (xclosure_auto G (hd Xs)) pr)\<close>
    and shn: \<open>fst pr \<noteq> Shn\<close>
  shows \<open>\<exists>\<sigma> l. (pr, Some a, \<sigma>) \<in> set (rreds_at G Shn (pr0_states G Shn)
          (la_fix G Shn) (pstk ! 0) (hd istk)) \<and>
        l \<in> epool G \<alpha> \<and> wsat \<sigma> c l\<close>
proof -
  have z_lt: \<open>0 < length Xs\<close> using ne by auto
  have istk_ne: \<open>istk \<noteq> []\<close> using didx_ok_len[OF ok] ne by auto
  have i_lt: \<open>hd istk < length (lr0_states G Shn)\<close>
    using didx_okD[OF ok z_lt] istk_ne by (simp add: hd_conv_nth)
  from dlicE[OF lic] obtain \<tau> where
    cellb: \<open>(hd istk, (pr, length (snd pr)), Some a, \<tau>)
        \<in> set (red_buckets G Shn (length (lr0_states G Shn)) ! hd istk)\<close>
    and sat: \<open>irep_ex_wsat \<tau> c (red_set (xclosure_auto G (hd Xs)) pr)\<close> .
  have cell: \<open>(hd istk, (pr, length (snd pr)), Some a, \<tau>) \<in> set (la_fix G Shn)\<close>
    using red_buckets_memD[OF i_lt cellb] by blast
  from sat obtain j\<^sub>r where
    jr: \<open>j\<^sub>r \<in> irep_set (red_set (xclosure_auto G (hd Xs)) pr)\<close>
    and wt: \<open>wsat \<tau> c j\<^sub>r\<close>
    unfolding irep_ex_wsat_correct by blast
  from jr obtain R\<^sub>r where
    mem: \<open>(pr, length (snd pr), R\<^sub>r) \<in> set (xclosure_auto G (hd Xs))\<close>
    and jrR: \<open>j\<^sub>r \<in> irep_set R\<^sub>r\<close>
    unfolding red_set_correct by blast
  from strack_pool[OF tr live mem jrR] obtain \<rho> l where
    wr: \<open>(pr, length (snd pr), \<rho>) \<in> set (wreach G (pr0_states G Shn ! (pstk ! 0)))\<close>
    and lP: \<open>l \<in> epool G \<alpha>\<close> and wl: \<open>wsat \<rho> l j\<^sub>r\<close> by blast
  have memS: \<open>(pr, Some a, wcomp (winv \<rho>) \<tau>) \<in> set (rreds_at G Shn (pr0_states G Shn)
      (la_fix G Shn) (pstk ! 0) (hd istk))\<close>
    by (rule rreds_at_memI[OF cell shn wr])
  have ws: \<open>wsat (wcomp (winv \<rho>) \<tau>) c l\<close>
    by (rule wcomp_sound[OF wt winv_sound[OF wl]])
  show ?thesis using memS lP ws by blast
qed

lemma reduce_seed_None:
  assumes tr: \<open>strack G Shn Xs \<alpha> pstk\<close>
    and live: \<open>lcore (hd Xs) \<noteq> {}\<close>
    and ne: \<open>Xs \<noteq> []\<close>
    and ok: \<open>didx_ok G (lr0_states G Shn) Xs istk\<close>
    and lic: \<open>dlic (hd istk) (red_buckets G Shn (length (lr0_states G Shn)) ! hd istk)
        [] pr (red_set (xclosure_auto G (hd Xs)) pr)\<close>
    and nonvac: \<open>irep_nonempty (red_set (xclosure_auto G (hd Xs)) pr)\<close>
    and shn: \<open>fst pr \<noteq> Shn\<close>
  shows \<open>\<exists>\<sigma>. (pr, None, \<sigma>) \<in> set (rreds_at G Shn (pr0_states G Shn)
          (la_fix G Shn) (pstk ! 0) (hd istk))\<close>
proof -
  have z_lt: \<open>0 < length Xs\<close> using ne by auto
  have istk_ne: \<open>istk \<noteq> []\<close> using didx_ok_len[OF ok] ne by auto
  have i_lt: \<open>hd istk < length (lr0_states G Shn)\<close>
    using didx_okD[OF ok z_lt] istk_ne by (simp add: hd_conv_nth)
  from dlic_NilE[OF lic] obtain \<tau> where
    cellb: \<open>(hd istk, (pr, length (snd pr)), None, \<tau>)
        \<in> set (red_buckets G Shn (length (lr0_states G Shn)) ! hd istk)\<close> .
  have cell: \<open>(hd istk, (pr, length (snd pr)), None, \<tau>) \<in> set (la_fix G Shn)\<close>
    using red_buckets_memD[OF i_lt cellb] by blast
  obtain j\<^sub>r where jr: \<open>j\<^sub>r \<in> irep_set (red_set (xclosure_auto G (hd Xs)) pr)\<close>
    using nonvac unfolding irep_nonempty_correct by blast
  from jr obtain R\<^sub>r where
    mem: \<open>(pr, length (snd pr), R\<^sub>r) \<in> set (xclosure_auto G (hd Xs))\<close>
    and jrR: \<open>j\<^sub>r \<in> irep_set R\<^sub>r\<close>
    unfolding red_set_correct by blast
  from strack_pool[OF tr live mem jrR] obtain \<rho> where
    wr: \<open>(pr, length (snd pr), \<rho>) \<in> set (wreach G (pr0_states G Shn ! (pstk ! 0)))\<close>
    by blast
  show ?thesis using rreds_at_memI[OF cell shn wr] by blast
qed

lemma shift_seed:
  assumes tr: \<open>strack G Shn Xs \<alpha> pstk\<close>
    and ne: \<open>Xs \<noteq> []\<close>
    and step: \<open>mstep G (Xs, w) DShift = Some gc'\<close>
    and lv: \<open>dlive gc'\<close>
  shows \<open>\<exists>a c w' \<sigma> l. w = (a, c) # w' \<and>
      (a, \<sigma>) \<in> set (shift_cells (wreach G (pr0_states G Shn ! (pstk ! 0)))) \<and>
      l \<in> epool G \<alpha> \<and> wsat \<sigma> c l\<close>
proof -
  have step': \<open>mstep_cached G (map (xclosure_auto G) Xs) (Xs, w) DShift = Some gc'\<close>
    using step unfolding mstep_def by simp
  from shift_live_srcE[OF step' lv] obtain a c w' pr m R j where
    w: \<open>w = (a, c) # w'\<close>
    and src0: \<open>(pr, m, R) \<in> set (hd (map (xclosure_auto G) Xs))\<close>
    and m_lt: \<open>m < length (snd pr)\<close>
    and sym: \<open>fst (snd pr ! m) = Tm a\<close>
    and jR: \<open>j \<in> irep_set R\<close>
    and rel: \<open>irel_sat (snd (snd pr ! m)) c j\<close> .
  have src: \<open>(pr, m, R) \<in> set (xclosure_auto G (hd Xs))\<close>
    using src0 ne by (simp add: hd_map)
  have live0: \<open>lcore (hd Xs) \<noteq> {}\<close> by (rule closure_live_kernel[OF src jR])
  from strack_pool[OF tr live0 src jR] obtain \<rho> l where
    wr: \<open>(pr, m, \<rho>) \<in> set (wreach G (pr0_states G Shn ! (pstk ! 0)))\<close>
    and lP: \<open>l \<in> epool G \<alpha>\<close> and wl: \<open>wsat \<rho> l j\<close> by blast
  have memS: \<open>(a, wcomp (winv \<rho>) (w_of (snd (snd pr ! m)))) \<in>
      set (shift_cells (wreach G (pr0_states G Shn ! (pstk ! 0))))\<close>
    by (rule shift_cells_memI[OF wr m_lt sym])
  have ws: \<open>wsat (wcomp (winv \<rho>) (w_of (snd (snd pr ! m)))) c l\<close>
    by (rule wcomp_sound[OF w_of_sound[OF rel] winv_sound[OF wl]])
  show ?thesis using w memS lP ws by blast
qed

text \<open>The sufficiency theorem: an empty rigid-point report makes the pooled
  machine deterministic.  Cf.\ Barthwal (2010, Thm 5.4.4: conflict freedom
  on reachable states suffices) and Jourdan et al. (2012, Thm 4: validator
  soundness); the rigid-point walk replaces their single-anchor comparison,
  which the test grammar \<open>xag\<close> refutes for the pooled machine.\<close>

theorem rlalr_sufficient:
  assumes chk: \<open>rlalr_conflicts G Shn = []\<close> and fresh: \<open>fresh_name G Shn\<close>
  shows \<open>mdet G Shn\<close>
  unfolding mdet_def
proof (intro allI impI)
  fix gc istk i redtab CL a\<^sub>1 a\<^sub>2 gc\<^sub>1 gc\<^sub>2
  assume reach: \<open>mreach G Shn gc\<close> and gcne: \<open>fst gc \<noteq> []\<close>
    and ok0: \<open>didx_ok G (lr0_states G Shn) (fst gc) istk\<close>
    and idef: \<open>i = hd istk\<close>
    and rdef: \<open>redtab = red_buckets G Shn (length (lr0_states G Shn)) ! i\<close>
    and cldef: \<open>CL = xclosure_auto G (hd (fst gc))\<close>
    and c1: \<open>a\<^sub>1 \<in> set (dcands G i redtab CL gc)\<close>
    and c2: \<open>a\<^sub>2 \<in> set (dcands G i redtab CL gc)\<close>
    and ne12: \<open>a\<^sub>1 \<noteq> a\<^sub>2\<close>
    and s1: \<open>mstep G gc a\<^sub>1 = Some gc\<^sub>1\<close> and s2: \<open>mstep G gc a\<^sub>2 = Some gc\<^sub>2\<close>
    and lv1: \<open>dlive gc\<^sub>1\<close> and lv2: \<open>dlive gc\<^sub>2\<close>
  obtain Xs w where gc: \<open>gc = (Xs, w)\<close> by (cases gc)
  have ne: \<open>Xs \<noteq> []\<close> using gcne gc by simp
  have okX: \<open>didx_ok G (lr0_states G Shn) Xs istk\<close> using ok0 unfolding gc by simp
  have clX: \<open>CL = xclosure_auto G (hd Xs)\<close> using cldef unfolding gc by simp
  from mreach_strack[OF reach fresh] obtain \<alpha> pstk where
    tr0: \<open>strack G Shn (fst gc) \<alpha> pstk\<close> by blast
  have tr: \<open>strack G Shn Xs \<alpha> pstk\<close> using tr0 unfolding gc by simp
  note mt = strackD(2)[OF tr]
  have z_lt: \<open>0 < length Xs\<close> using ne by auto
  have hd0: \<open>hd Xs = Xs ! 0\<close> using ne by (simp add: hd_conv_nth)
  have cs1: \<open>a\<^sub>1 = DShift \<and> w \<noteq> [] \<or> (\<exists>pr. a\<^sub>1 = DReduce pr \<and>
      irep_nonempty (red_set CL pr) \<and> dlic i redtab w pr (red_set CL pr))\<close>
    using dcands_shift_or_reduce c1 unfolding gc by blast
  have cs2: \<open>a\<^sub>2 = DShift \<and> w \<noteq> [] \<or> (\<exists>pr. a\<^sub>2 = DReduce pr \<and>
      irep_nonempty (red_set CL pr) \<and> dlic i redtab w pr (red_set CL pr))\<close>
    using dcands_shift_or_reduce c2 unfolding gc by blast
  have live0: \<open>lcore (hd Xs) \<noteq> {}\<close>
  proof -
    from cs1 show ?thesis
    proof (elim disjE conjE exE)
      assume a1s: \<open>a\<^sub>1 = DShift\<close> and \<open>w \<noteq> []\<close>
      have step': \<open>mstep_cached G (map (xclosure_auto G) Xs) (Xs, w) DShift = Some gc\<^sub>1\<close>
        using s1 unfolding gc a1s mstep_def by simp
      from shift_live_srcE[OF step' lv1] obtain a c w' pr m R j where
        \<open>w = (a, c) # w'\<close>
        and src0: \<open>(pr, m, R) \<in> set (hd (map (xclosure_auto G) Xs))\<close>
        and \<open>m < length (snd pr)\<close> and \<open>fst (snd pr ! m) = Tm a\<close>
        and jR0: \<open>j \<in> irep_set R\<close>
        and \<open>irel_sat (snd (snd pr ! m)) c j\<close> .
      have src: \<open>(pr, m, R) \<in> set (xclosure_auto G (hd Xs))\<close>
        using src0 ne by (simp add: hd_map)
      show ?thesis by (rule closure_live_kernel[OF src jR0])
    next
      fix pr assume \<open>irep_nonempty (red_set CL pr)\<close>
      then have \<open>irep_nonempty (red_set (xclosure_auto G (hd Xs)) pr)\<close>
        unfolding clX by blast
      then obtain j\<^sub>r where
        \<open>j\<^sub>r \<in> irep_set (red_set (xclosure_auto G (hd Xs)) pr)\<close>
        unfolding irep_nonempty_correct by blast
      then obtain R\<^sub>r where \<open>(pr, length (snd pr), R\<^sub>r) \<in> set (xclosure_auto G (hd Xs))\<close>
        and \<open>j\<^sub>r \<in> irep_set R\<^sub>r\<close>
        unfolding red_set_correct by blast
      then show ?thesis by (rule closure_live_kernel)
    qed
  qed
  have pairmem: \<open>(pstk ! 0, hd istk) \<in> set (mprod_states G Shn)\<close>
    using mtrackD[OF mt z_lt live0[unfolded hd0]]
      didx_hd_st_find[OF okX ne] hd0 by auto
  have nc: \<open>\<not> rlalr_conflict_at G Shn (pr0_states G Shn) (la_fix G Shn)
      (pstk ! 0, hd istk)\<close>
  proof
    assume \<open>rlalr_conflict_at G Shn (pr0_states G Shn) (la_fix G Shn)
        (pstk ! 0, hd istk)\<close>
    then have \<open>(pstk ! 0, hd istk) \<in> set (rlalr_conflicts G Shn)\<close>
      unfolding rlalr_conflicts_def Let_def using pairmem by simp
    then show False using chk by simp
  qed
  have no_none: \<open>\<not> rr_none_at G Shn (pr0_states G Shn) (la_fix G Shn)
      (pstk ! 0) (hd istk)\<close>
    using nc unfolding rlalr_conflict_at_def by (auto simp: list_ex_iff)
  have walkF: \<open>\<And>\<sigma>\<^sub>1 \<sigma>\<^sub>2. (\<sigma>\<^sub>1, \<sigma>\<^sub>2) \<in> set (rpairs_at G Shn (pr0_states G Shn)
        (la_fix G Shn) (pstk ! 0) (hd istk)) \<Longrightarrow>
      rfire G (p0start G Shn) (pr0_states G Shn) (pgtab G (pr0_states G Shn))
        (anchored_nts G)
        (Suc (length (pr0_states G Shn) * 36 + length (pr0_states G Shn)))
        [] [(pstk ! 0, \<sigma>\<^sub>1, \<sigma>\<^sub>2)] = False\<close>
    using nc unfolding rlalr_conflict_at_def
    by (auto simp: list_ex_iff simp del: rfire.simps)
  have kill: \<open>\<And>c \<sigma>\<^sub>1 \<sigma>\<^sub>2 l\<^sub>1 l\<^sub>2. (\<sigma>\<^sub>1, \<sigma>\<^sub>2) \<in> set (rpairs_at G Shn (pr0_states G Shn)
        (la_fix G Shn) (pstk ! 0) (hd istk)) \<Longrightarrow>
      l\<^sub>1 \<in> epool G \<alpha> \<Longrightarrow> wsat \<sigma>\<^sub>1 c l\<^sub>1 \<Longrightarrow>
      l\<^sub>2 \<in> epool G \<alpha> \<Longrightarrow> wsat \<sigma>\<^sub>2 c l\<^sub>2 \<Longrightarrow> False\<close>
  proof -
    fix c \<sigma>\<^sub>1 \<sigma>\<^sub>2 l\<^sub>1 l\<^sub>2
    assume pm: \<open>(\<sigma>\<^sub>1, \<sigma>\<^sub>2) \<in> set (rpairs_at G Shn (pr0_states G Shn)
        (la_fix G Shn) (pstk ! 0) (hd istk))\<close>
      and e1: \<open>l\<^sub>1 \<in> epool G \<alpha>\<close> and w1: \<open>wsat \<sigma>\<^sub>1 c l\<^sub>1\<close>
      and e2: \<open>l\<^sub>2 \<in> epool G \<alpha>\<close> and w2: \<open>wsat \<sigma>\<^sub>2 c l\<^sub>2\<close>
    from strack_descent[OF tr live0 e1 w1 e2 w2] obtain i' \<sigma>\<^sub>1' \<sigma>\<^sub>2' l' where
      chain: \<open>(rdesc G (pr0_states G Shn) (pgtab G (pr0_states G Shn))
          (anchored_nts G))\<^sup>*\<^sup>* (pstk ! 0, \<sigma>\<^sub>1, \<sigma>\<^sub>2) (i', \<sigma>\<^sub>1', \<sigma>\<^sub>2')\<close>
      and rig: \<open>rigid_at (p0start G Shn) (pgtab G (pr0_states G Shn))
          (anchored_nts G) i'\<close>
      and ws1: \<open>wsat \<sigma>\<^sub>1' c l'\<close> and ws2: \<open>wsat \<sigma>\<^sub>2' c l'\<close> by blast
    have wd: \<open>wdisjoint \<sigma>\<^sub>1' \<sigma>\<^sub>2'\<close>
      by (rule rfire_sound[OF walkF[OF pm] chain rig])
    show False using wdisjoint_sound[OF ws1 ws2] wd by simp
  qed
  have sr_case: \<open>mstep G gc DShift = Some gc\<^sub>s \<Longrightarrow> dlive gc\<^sub>s \<Longrightarrow>
      mstep G gc (DReduce pr) = Some gc\<^sub>r \<Longrightarrow> dlive gc\<^sub>r \<Longrightarrow>
      dlic i redtab w pr (red_set CL pr) \<Longrightarrow> False\<close> for gc\<^sub>s gc\<^sub>r pr
  proof -
    fix gc\<^sub>s gc\<^sub>r pr
    assume ss: \<open>mstep G gc DShift = Some gc\<^sub>s\<close> and lvs: \<open>dlive gc\<^sub>s\<close>
      and sr: \<open>mstep G gc (DReduce pr) = Some gc\<^sub>r\<close> and lvr: \<open>dlive gc\<^sub>r\<close>
      and lic: \<open>dlic i redtab w pr (red_set CL pr)\<close>
    from shift_seed[OF tr ne ss[unfolded gc] lvs] obtain a c w' \<sigma>\<^sub>s l\<^sub>s where
      w: \<open>w = (a, c) # w'\<close>
      and shm: \<open>(a, \<sigma>\<^sub>s) \<in> set (shift_cells (wreach G (pr0_states G Shn ! (pstk ! 0))))\<close>
      and ls: \<open>l\<^sub>s \<in> epool G \<alpha>\<close> and wss: \<open>wsat \<sigma>\<^sub>s c l\<^sub>s\<close> by blast
    show False
    proof (cases \<open>fst pr = Shn\<close>)
      case True
      show False by (rule shn_reduce_dead[OF tr fresh sr[unfolded gc] True lvr])
    next
      case False
      have lic': \<open>dlic (hd istk) (red_buckets G Shn (length (lr0_states G Shn)) ! hd istk)
          ((a, c) # w') pr (red_set (xclosure_auto G (hd Xs)) pr)\<close>
        using lic unfolding idef rdef clX w by simp
      from reduce_seed_Some[OF tr live0 ne okX lic' False] obtain \<sigma>\<^sub>r l\<^sub>r where
        rdm: \<open>(pr, Some a, \<sigma>\<^sub>r) \<in> set (rreds_at G Shn (pr0_states G Shn)
            (la_fix G Shn) (pstk ! 0) (hd istk))\<close>
        and lr: \<open>l\<^sub>r \<in> epool G \<alpha>\<close> and wsr: \<open>wsat \<sigma>\<^sub>r c l\<^sub>r\<close> by blast
      have pm: \<open>(\<sigma>\<^sub>r, \<sigma>\<^sub>s) \<in> set (rpairs_at G Shn (pr0_states G Shn)
          (la_fix G Shn) (pstk ! 0) (hd istk))\<close>
        by (rule rpairs_at_srI[OF rdm shm])
      show False by (rule kill[OF pm lr wsr ls wss])
    qed
  qed
  consider
      (SS) \<open>a\<^sub>1 = DShift\<close> and \<open>a\<^sub>2 = DShift\<close>
    | (SR) pr\<^sub>2 where \<open>a\<^sub>1 = DShift\<close> \<open>a\<^sub>2 = DReduce pr\<^sub>2\<close>
        \<open>irep_nonempty (red_set CL pr\<^sub>2)\<close> \<open>dlic i redtab w pr\<^sub>2 (red_set CL pr\<^sub>2)\<close>
    | (RS) pr\<^sub>1 where \<open>a\<^sub>2 = DShift\<close> \<open>a\<^sub>1 = DReduce pr\<^sub>1\<close>
        \<open>irep_nonempty (red_set CL pr\<^sub>1)\<close> \<open>dlic i redtab w pr\<^sub>1 (red_set CL pr\<^sub>1)\<close>
    | (RR) pr\<^sub>1 pr\<^sub>2 where \<open>a\<^sub>1 = DReduce pr\<^sub>1\<close> \<open>a\<^sub>2 = DReduce pr\<^sub>2\<close>
        \<open>irep_nonempty (red_set CL pr\<^sub>1)\<close> \<open>dlic i redtab w pr\<^sub>1 (red_set CL pr\<^sub>1)\<close>
        \<open>irep_nonempty (red_set CL pr\<^sub>2)\<close> \<open>dlic i redtab w pr\<^sub>2 (red_set CL pr\<^sub>2)\<close>
    using cs1 cs2 by blast
  then show False
  proof cases
    case SS
    then show False using ne12 by simp
  next
    case (SR pr\<^sub>2)
    show False by (rule sr_case[OF s1[unfolded SR(1)] lv1 s2[unfolded SR(2)] lv2 SR(4)])
  next
    case (RS pr\<^sub>1)
    show False by (rule sr_case[OF s2[unfolded RS(1)] lv2 s1[unfolded RS(2)] lv1 RS(4)])
  next
    case (RR pr\<^sub>1 pr\<^sub>2)
    have prne: \<open>pr\<^sub>2 \<noteq> pr\<^sub>1\<close> using ne12 unfolding RR(1) RR(2) by auto
    show False
    proof (cases \<open>fst pr\<^sub>1 = Shn\<close>)
      case True
      show False
        by (rule shn_reduce_dead[OF tr fresh s1[unfolded gc RR(1)] True lv1])
    next
      case False
      note shn1 = False
      show False
      proof (cases \<open>fst pr\<^sub>2 = Shn\<close>)
        case True
        show False
          by (rule shn_reduce_dead[OF tr fresh s2[unfolded gc RR(2)] True lv2])
      next
        case False
        note shn2 = False
        show False
        proof (cases w)
          case Nil
          have lic1: \<open>dlic (hd istk) (red_buckets G Shn
              (length (lr0_states G Shn)) ! hd istk)
              [] pr\<^sub>1 (red_set (xclosure_auto G (hd Xs)) pr\<^sub>1)\<close>
            using RR(4) unfolding idef rdef clX Nil by simp
          have lic2: \<open>dlic (hd istk) (red_buckets G Shn
              (length (lr0_states G Shn)) ! hd istk)
              [] pr\<^sub>2 (red_set (xclosure_auto G (hd Xs)) pr\<^sub>2)\<close>
            using RR(6) unfolding idef rdef clX Nil by simp
          have nv1: \<open>irep_nonempty (red_set (xclosure_auto G (hd Xs)) pr\<^sub>1)\<close>
            using RR(3) unfolding clX .
          have nv2: \<open>irep_nonempty (red_set (xclosure_auto G (hd Xs)) pr\<^sub>2)\<close>
            using RR(5) unfolding clX .
          from reduce_seed_None[OF tr live0 ne okX lic1 nv1 shn1] obtain \<sigma>\<^sub>1 where
            m1: \<open>(pr\<^sub>1, None, \<sigma>\<^sub>1) \<in> set (rreds_at G Shn (pr0_states G Shn)
                (la_fix G Shn) (pstk ! 0) (hd istk))\<close> by blast
          from reduce_seed_None[OF tr live0 ne okX lic2 nv2 shn2] obtain \<sigma>\<^sub>2 where
            m2: \<open>(pr\<^sub>2, None, \<sigma>\<^sub>2) \<in> set (rreds_at G Shn (pr0_states G Shn)
                (la_fix G Shn) (pstk ! 0) (hd istk))\<close> by blast
          have \<open>rr_none_at G Shn (pr0_states G Shn) (la_fix G Shn)
              (pstk ! 0) (hd istk)\<close>
            by (rule rr_none_atI[OF m1 m2 prne])
          then show False using no_none by simp
        next
          case (Cons ac w')
          obtain a c where ac: \<open>ac = (a, c)\<close> by (cases ac)
          have weq: \<open>w = (a, c) # w'\<close> unfolding Cons ac by simp
          have lic1: \<open>dlic (hd istk) (red_buckets G Shn
              (length (lr0_states G Shn)) ! hd istk)
              ((a, c) # w') pr\<^sub>1 (red_set (xclosure_auto G (hd Xs)) pr\<^sub>1)\<close>
            using RR(4) unfolding idef rdef clX weq by simp
          have lic2: \<open>dlic (hd istk) (red_buckets G Shn
              (length (lr0_states G Shn)) ! hd istk)
              ((a, c) # w') pr\<^sub>2 (red_set (xclosure_auto G (hd Xs)) pr\<^sub>2)\<close>
            using RR(6) unfolding idef rdef clX weq by simp
          from reduce_seed_Some[OF tr live0 ne okX lic1 shn1] obtain \<sigma>\<^sub>1 l\<^sub>1 where
            m1: \<open>(pr\<^sub>1, Some a, \<sigma>\<^sub>1) \<in> set (rreds_at G Shn (pr0_states G Shn)
                (la_fix G Shn) (pstk ! 0) (hd istk))\<close>
            and e1: \<open>l\<^sub>1 \<in> epool G \<alpha>\<close> and ws1: \<open>wsat \<sigma>\<^sub>1 c l\<^sub>1\<close> by blast
          from reduce_seed_Some[OF tr live0 ne okX lic2 shn2] obtain \<sigma>\<^sub>2 l\<^sub>2 where
            m2: \<open>(pr\<^sub>2, Some a, \<sigma>\<^sub>2) \<in> set (rreds_at G Shn (pr0_states G Shn)
                (la_fix G Shn) (pstk ! 0) (hd istk))\<close>
            and e2: \<open>l\<^sub>2 \<in> epool G \<alpha>\<close> and ws2: \<open>wsat \<sigma>\<^sub>2 c l\<^sub>2\<close> by blast
          have pm: \<open>(\<sigma>\<^sub>1, \<sigma>\<^sub>2) \<in> set (rpairs_at G Shn (pr0_states G Shn)
              (la_fix G Shn) (pstk ! 0) (hd istk))\<close>
            by (rule rpairs_at_rrI[OF m1 m2 prne])
          show False by (rule kill[OF pm e1 ws1 e2 ws2])
        qed
      qed
    qed
  qed
qed

section \<open>The cells cover the LR(1) lookahead\<close>

text \<open>Algorithm 8 at \<open>k = 1\<close> keeps, per item, the set of one-token lookaheads
  (with their columns); the cells keep, per LR(0) item and state, a token
  with a width relation to the item's anchor.  Along any viable prefix
  \<open>\<gamma>\<close> the cells cover the lookaheads: the LR(0) index is reached by following
  the goto table from the start state along the erased \<open>\<gamma>\<close> (the cells are
  LALR: the index forgets everything about \<open>\<gamma>\<close> but the merged state), and
  every item of the closure of the LR(1) state carrying the lookahead
  \<open>(a, c)\<close> has a cell for \<open>a\<close> whose relation admits the column \<open>c\<close> against
  the item's anchor.  The padded end marker of the abstract machine is the
  \<open>None\<close> cell.  The proof mirrors the cell propagation: \<^const>\<open>la_next\<close>
  for \<^const>\<open>igoto\<close>, and \<^text>\<open>first1_complete\<close> for the lookahead of a
  predicted item, where \<^const>\<open>fscan\<close> stands in for \<^const>\<open>Hk\<close> of the
  remainder.\<close>

definition la_index :: \<open>('n, 't) is_cfg \<Rightarrow> 'n \<Rightarrow> ('n \<times> nat, 't \<times> nat) syms \<Rightarrow> nat\<close> where
  \<open>la_index G Shn \<gamma> =
     fold (\<lambda>Z p. la_next (la_gtab G (lr0_states G Shn)) (lr0_states G Shn) p (unann Z)) \<gamma>
       (st_find (lr0_states G Shn) (lr0_start G Shn))\<close>

lemma la_index_Nil [simp]:
  \<open>la_index G Shn [] = st_find (lr0_states G Shn) (lr0_start G Shn)\<close>
  unfolding la_index_def by simp

lemma la_index_snoc [simp]:
  \<open>la_index G Shn (\<gamma> @ [Z]) =
     la_next (la_gtab G (lr0_states G Shn)) (lr0_states G Shn) (la_index G Shn \<gamma>) (unann Z)\<close>
  unfolding la_index_def by simp

definition lk :: \<open>'t \<times> nat \<Rightarrow> ('t \<times> nat) list \<Rightarrow> ('t \<times> nat) list\<close> where
  \<open>lk dm u = (if u = [dm] then [] else u)\<close>

abbreviation lr1_start :: \<open>('n, 't) is_cfg \<Rightarrow> 'n \<Rightarrow> ('n \<times> nat) \<times> ('n \<times> nat, 't \<times> nat) syms\<close> where
  \<open>lr1_start G Shn \<equiv> ((Shn, istart_ind G), [Nt (istart G, istart_ind G)])\<close>

abbreviation lr1_init :: \<open>('n, 't) is_cfg \<Rightarrow> 'n \<Rightarrow> 't \<times> nat \<Rightarrow> ('n \<times> nat, 't \<times> nat) item set\<close> where
  \<open>lr1_init G Shn dm \<equiv> {init_item (Shn, istart_ind G) (istart G, istart_ind G) dm (Suc 0)}\<close>

text \<open>A production of the augmented infinite grammar is a production of \<open>G\<close>
  (or the augmenting one) under an annotation.\<close>

lemma lr1_prod_cases:
  assumes fn: \<open>fresh_name G Shn\<close> and pr: \<open>((A, i), arhs) \<in> insert (lr1_start G Shn) (infG G)\<close>
  obtains rhs where \<open>(A, rhs) \<in> insert (start_prod G Shn) (set (iprods G))\<close>
    and \<open>annotates i rhs arhs\<close>
proof -
  from pr consider \<open>((A, i), arhs) = lr1_start G Shn\<close> | \<open>((A, i), arhs) \<in> infG G\<close> by blast
  then show thesis
  proof cases
    case 1
    then have \<open>A = Shn\<close> \<open>i = istart_ind G\<close> \<open>arhs = [Nt (istart G, istart_ind G)]\<close> by simp_all
    then show thesis by (intro that[of \<open>snd (start_prod G Shn)\<close>]) (simp_all add: start_prod_def)
  next
    case 2
    then show thesis using that unfolding infG_alt by blast
  qed
qed

lemma gram_terms_of_prod:
  assumes \<open>(A, rhs) \<in> insert (start_prod G Shn) (set (iprods G))\<close> and \<open>(Tm a, r) \<in> set rhs\<close>
  shows \<open>a \<in> set (gram_terms G)\<close>
  using assms gram_termsI unfolding start_prod_def by fastforce

text \<open>The closure step: a kernel whose items are covered at index \<open>p\<close> has
  its closure covered at \<open>p\<close>.\<close>

lemma la_fix_closure_cells:
  assumes fn: \<open>fresh_name G Shn\<close> and dm: \<open>fst dm \<notin> set (gram_terms G)\<close>
    and ok: \<open>items_ok (insert (lr1_start G Shn) (infG G)) \<gamma> S\<close>
    and kernel: \<open>\<And>A i arhs m u rhs. (((A, i), arhs), m, u) \<in> S \<Longrightarrow>
        (A, rhs) \<in> insert (start_prod G Shn) (set (iprods G)) \<Longrightarrow> annotates i rhs arhs \<Longrightarrow>
        length u = Suc 0 \<and> cell_ok (la_fix G Shn) p (A, rhs) m (lk dm u) i\<close>
    and item: \<open>(((A, i), arhs), m, u) \<in> iclosure (infG G) (Suc 0) S\<close>
    and pr: \<open>(A, rhs) \<in> insert (start_prod G Shn) (set (iprods G))\<close>
    and ann: \<open>annotates i rhs arhs\<close>
  shows \<open>length u = Suc 0 \<and> cell_ok (la_fix G Shn) p (A, rhs) m (lk dm u) i\<close>
proof -
  let ?sts = \<open>lr0_states G Shn\<close> and ?gt = \<open>la_gtab G (lr0_states G Shn)\<close> and ?L = \<open>la_fix G Shn\<close>
  have tab: \<open>tables_ok G Shn ?sts ?gt ?L\<close> by (rule tables_ok_concrete)
  have okc: \<open>items_ok (insert (lr1_start G Shn) (infG G)) \<gamma> (iclosure (infG G) (Suc 0) S)\<close>
    by (rule items_ok_iclosure[OF ok subset_insertI])
  have \<open>\<forall>A i arhs m u rhs. it = (((A, i), arhs), m, u) \<longrightarrow>
      (A, rhs) \<in> insert (start_prod G Shn) (set (iprods G)) \<longrightarrow> annotates i rhs arhs \<longrightarrow>
      length u = Suc 0 \<and> cell_ok ?L p (A, rhs) m (lk dm u) i\<close>
    if \<open>it \<in> iclosure (infG G) (Suc 0) S\<close> for it
    using that
  proof (induction rule: iclosure.induct)
    case (iclosure_base it)
    then show ?case using kernel by blast
  next
    case (iclosure_step Ai arhs m u Bj brhs v)
    show ?case
    proof (intro allI impI)
      fix B' j brhs' m' v' rhsB
      assume eq: \<open>((Bj, brhs), 0::nat, v) = (((B', j), brhs'), m', v')\<close>
        and prB: \<open>(B', rhsB) \<in> insert (start_prod G Shn) (set (iprods G))\<close>
        and annB: \<open>annotates j rhsB brhs'\<close>
      have Bj: \<open>Bj = (B', j)\<close> and m': \<open>m' = 0\<close> and v': \<open>v' = v\<close> using eq by simp_all
      obtain A i where Ai: \<open>Ai = (A, i)\<close> by (cases Ai)
      have prod: \<open>((A, i), arhs) \<in> insert (lr1_start G Shn) (infG G)\<close>
        using items_okD[OF okc iclosure_step.hyps(1)[unfolded Ai]] by blast
      from lr1_prod_cases[OF fn prod] obtain rhs where
        prG: \<open>(A, rhs) \<in> insert (start_prod G Shn) (set (iprods G))\<close>
        and ann: \<open>annotates i rhs arhs\<close> .
      from iclosure_step.IH[rule_format, OF _ prG ann] have
        lenu: \<open>length u = Suc 0\<close> and cell: \<open>cell_ok ?L p (A, rhs) m (lk dm u) i\<close>
        unfolding Ai by auto
      have m_lt: \<open>m < length rhs\<close> using iclosure_step.hyps(2) annotates_length[OF ann] by simp
      from annotates_nthD[OF ann m_lt] obtain jj where
        nth: \<open>arhs ! m = annsym (fst (rhs ! m), jj)\<close> and sat: \<open>irel_sat (snd (rhs ! m)) jj i\<close>
        by blast
      have nxtjj: \<open>fst (rhs ! m) = Nt B' \<and> jj = j\<close>
        using iclosure_step.hyps(3) nth unfolding Bj by (cases \<open>fst (rhs ! m)\<close>) auto
      note nxt = conjunct1[OF nxtjj] and jj = conjunct2[OF nxtjj]
      have m_lt': \<open>m < length (snd (A, rhs))\<close> and nxt': \<open>fst (snd (A, rhs) ! m) = Nt B'\<close>
        using m_lt nxt by simp_all
      \<comment> \<open>the predicted nonterminal is one of \<open>G\<close>: its production is in \<open>iprods\<close>\<close>
      have \<open>B' \<in> fst ` set (iprods G)\<close>
        using iclosure_step.hyps(4) unfolding Bj infG_alt by force
      then have brG: \<open>(B', rhsB) \<in> set (iprods G)\<close>
        using prB fn unfolding fresh_name_def start_prod_def by auto
      have vH: \<open>v \<in> fHk G (Suc 0) (drop (Suc m) rhs) i u\<close>
        by (rule fHkI[OF annotates_drop[OF ann] iclosure_step.hyps(5)])
      from cell obtain \<tau> where mem: \<open>(p, ((A, rhs), m), tok_of (lk dm u), \<tau>) \<in> set ?L\<close>
        and rel: \<open>case lk dm u of [] \<Rightarrow> True | (a, c) # _ \<Rightarrow> wsat \<tau> c i\<close>
        unfolding cell_ok_def by blast
      from first1_complete[OF vH] show \<open>length v' = Suc 0 \<and> cell_ok ?L p (B', rhsB) m' (lk dm v') j\<close>
      proof (elim disjE exE conjE)
        fix b c \<sigma>
        assume veq: \<open>v = [(b, c)]\<close>
          and fs: \<open>(b, \<sigma>) \<in> set (fscan (ffix G) (nullables G) (drop (Suc m) rhs))\<close>
          and cs: \<open>csat \<sigma> c i\<close>
        have terms: \<open>(Tm a, r) \<in> set (drop (Suc m) rhs) \<Longrightarrow> a \<in> set (gram_terms G)\<close> for a r
          using gram_terms_of_prod[OF prG, OF in_set_dropD] by blast
        have bT: \<open>b \<in> set (gram_terms G)\<close>
        proof (rule fscan_inU[OF ffix_inU _ fs, THEN conjunct1], goal_cases)
          case 1 then show ?case by (rule terms)
        qed
        have vdm: \<open>v \<noteq> [dm]\<close> using bT dm veq by auto
        have inL: \<open>(p, ((B', rhsB), 0), Some b, wcomp (winv (w_of (snd (rhs ! m)))) (wemb \<sigma>)) \<in> set ?L\<close>
          using cell_child_first[OF tab mem m_lt' nxt' brG fst_conv] fs by simp
        have ws: \<open>wsat (wcomp (winv (w_of (snd (rhs ! m)))) (wemb \<sigma>)) c j\<close>
          by (rule wsat_reanchor[OF sat[unfolded jj] wemb_sound[OF cs]])
        show ?thesis
          unfolding v' m' lk_def using vdm veq inL ws unfolding cell_ok_def by auto
      next
        assume nul: \<open>list_all (\<lambda>(X, r). nsym (nullables G) X) (drop (Suc m) rhs)\<close>
          and veq: \<open>v = take (Suc 0) u\<close>
        have vu: \<open>v = u\<close> using veq lenu by simp
        have inL: \<open>(p, ((B', rhsB), 0), tok_of (lk dm u), wcomp (winv (w_of (snd (rhs ! m)))) \<tau>) \<in> set ?L\<close>
          using cell_child_inherit[OF tab mem m_lt' nxt' brG fst_conv] nul by simp
        have ws: \<open>case lk dm u of [] \<Rightarrow> True
            | (a, c) # _ \<Rightarrow> wsat (wcomp (winv (w_of (snd (rhs ! m)))) \<tau>) c j\<close>
          using rel by (auto split: list.splits intro: wsat_reanchor[OF sat[unfolded jj]])
        show ?thesis
          unfolding v' m' vu using lenu inL ws unfolding cell_ok_def by auto
      qed
    qed
  qed
  then show ?thesis using item pr ann by blast
qed

theorem la_fix_covers_lr1:
  assumes fn: \<open>fresh_name G Shn\<close> and dm: \<open>fst dm \<notin> set (gram_terms G)\<close>
    and item: \<open>(((A, i), arhs), m, u) \<in>
      iclosure (infG G) (Suc 0) (lrstate (infG G) (Suc 0) (lr1_init G Shn dm) \<gamma>)\<close>
    and pr: \<open>(A, rhs) \<in> insert (start_prod G Shn) (set (iprods G))\<close>
    and ann: \<open>annotates i rhs arhs\<close>
  shows \<open>cell_ok (la_fix G Shn) (la_index G Shn \<gamma>) (A, rhs) m (lk dm u) i\<close>
proof -
  let ?sts = \<open>lr0_states G Shn\<close> and ?gt = \<open>la_gtab G (lr0_states G Shn)\<close> and ?L = \<open>la_fix G Shn\<close>
  let ?P = \<open>infG G\<close> and ?Q = \<open>insert (lr1_start G Shn) (infG G)\<close>
  have tab: \<open>tables_ok G Shn ?sts ?gt ?L\<close> by (rule tables_ok_concrete)
  have ok: \<open>items_ok ?Q \<gamma> (lrstate ?P (Suc 0) (lr1_init G Shn dm) \<gamma>)\<close> for \<gamma>
    by (rule items_ok_lrstate[OF items_ok_init subset_insertI])
  have K: \<open>(((A, i), arhs), m, u) \<in> lrstate ?P (Suc 0) (lr1_init G Shn dm) \<gamma> \<Longrightarrow>
      (A, rhs) \<in> insert (start_prod G Shn) (set (iprods G)) \<Longrightarrow> annotates i rhs arhs \<Longrightarrow>
      length u = Suc 0 \<and> cell_ok ?L (la_index G Shn \<gamma>) (A, rhs) m (lk dm u) i\<close>
    for \<gamma> A i arhs m u rhs
  proof (induction \<gamma> arbitrary: A i arhs m u rhs rule: rev_induct)
    case Nil
    then have A: \<open>A = Shn\<close> and i: \<open>i = istart_ind G\<close> and arhs: \<open>arhs = [Nt (istart G, istart_ind G)]\<close>
      and m: \<open>m = 0\<close> and u: \<open>u = [dm]\<close>
      unfolding init_item_def by simp_all
    have rhs: \<open>rhs = [(Nt (istart G), Eq)]\<close>
    proof -
      have \<open>(Shn, rhs) \<notin> set (iprods G)\<close> using fn unfolding fresh_name_def by force
      then show ?thesis using Nil.prems(2) unfolding A start_prod_def by simp
    qed
    have \<open>(st_find ?sts (lr0_start G Shn), (start_prod G Shn, 0), None, WAny) \<in> set ?L\<close>
      using tab unfolding tables_ok_def la_start_def by auto
    then show ?case
      unfolding A i m u rhs lk_def cell_ok_def start_prod_def by auto
  next
    case (snoc Z \<gamma>)
    from snoc.prems(1) obtain m\<^sub>0 where m: \<open>m = Suc m\<^sub>0\<close>
      and parent: \<open>(((A, i), arhs), m\<^sub>0, u) \<in> iclosure ?P (Suc 0) (lrstate ?P (Suc 0) (lr1_init G Shn dm) \<gamma>)\<close>
      and m0_lt: \<open>m\<^sub>0 < length arhs\<close> and Z: \<open>arhs ! m\<^sub>0 = Z\<close>
      unfolding lrstate_snoc igoto_def by blast
    have \<open>length u = Suc 0 \<and> cell_ok ?L (la_index G Shn \<gamma>) (A, rhs) m\<^sub>0 (lk dm u) i\<close>
    proof (rule la_fix_closure_cells[OF fn dm ok _ parent snoc.prems(2,3)], goal_cases)
      case 1 then show ?case by (rule snoc.IH)
    qed
    then have lenu: \<open>length u = Suc 0\<close>
      and cell: \<open>cell_ok ?L (la_index G Shn \<gamma>) (A, rhs) m\<^sub>0 (lk dm u) i\<close> by blast+
    have m0_lt': \<open>m\<^sub>0 < length (snd (A, rhs))\<close>
      using m0_lt annotates_length[OF snoc.prems(3)] by simp
    from annotates_nthD[OF snoc.prems(3) m0_lt'[simplified]] obtain jj where
      nth: \<open>arhs ! m\<^sub>0 = annsym (fst (rhs ! m\<^sub>0), jj)\<close> by blast
    have Zeq: \<open>unann Z = fst (snd (A, rhs) ! m\<^sub>0)\<close> using nth Z by simp
    show ?case
      using cell_ok_step[OF tab cell m0_lt'] lenu unfolding m la_index_snoc Zeq by simp
  qed
  show ?thesis
  proof (rule la_fix_closure_cells[OF fn dm ok _ item pr ann, THEN conjunct2], goal_cases)
    case 1 then show ?case by (rule K)
  qed
qed

end
