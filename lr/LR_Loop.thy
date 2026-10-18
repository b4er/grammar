theory LR_Loop
  imports LR_Prod
begin

section \<open>A cheaper loop check\<close>

text \<open>\<^const>\<open>xrun_hist\<close> stops a run that revisits a stack between two shifts,
  by comparing the stack with all stacks since the last shift. The check only
  matters for the termination of the code: between shifts the input does not
  change, so a revisit means that the run loops, and its result is \<open>None\<close> as
  the run without a check (\<open>nrun\<close>). Any check that fires only on a
  revisit gives the same result. \<open>brun\<close> keeps one stack of the
  current segment and compares only with it, saving the current stack after 1,
  2, 4, \<open>\<dots>\<close> steps (Brent's cycle detection), which finds every cycle.\<close>

partial_function (option) nrun ::
  \<open>('k list \<times> 'w list \<Rightarrow> (('n, 't) dact \<times> 'k list \<times> 'w list) option) \<Rightarrow>
    ('k list \<times> 'w list \<Rightarrow> bool) \<Rightarrow> ('w \<Rightarrow> ('t, 'ch, 'm) token_scheme) \<Rightarrow>
    'k list \<times> 'w list \<times> ('m, 'ch, 'n, 't) ast list \<Rightarrow> ('m, 'ch, 'n, 't) ast option\<close>
  where
  \<open>nrun ctl fin dec st = (case st of (stk, v, tstk) \<Rightarrow>
     if fin (stk, v) then sresult tstk
     else Option.bind (ctl (stk, v)) (\<lambda>(act, stk', v').
       nrun ctl fin dec (stk', v', xtree dec act v tstk)))\<close>

definition bupd :: \<open>'k list option \<times> nat \<times> nat \<Rightarrow> 'k list \<Rightarrow> 'k list option \<times> nat \<times> nat\<close> where
  \<open>bupd d stk = (case d of (sv, c, p) \<Rightarrow> if c = p then (Some stk, 1, 2 * p) else (sv, c + 1, p))\<close>

partial_function (option) brun ::
  \<open>('k list \<times> 'w list \<Rightarrow> (('n, 't) dact \<times> 'k list \<times> 'w list) option) \<Rightarrow>
    ('k list \<times> 'w list \<Rightarrow> bool) \<Rightarrow> ('w \<Rightarrow> ('t, 'ch, 'm) token_scheme) \<Rightarrow>
    'k list option \<times> nat \<times> nat \<Rightarrow>
    'k list \<times> 'w list \<times> ('m, 'ch, 'n, 't) ast list \<Rightarrow> ('m, 'ch, 'n, 't) ast option\<close>
  where
  \<open>brun ctl fin dec d st = (case st of (stk, v, tstk) \<Rightarrow>
     if fin (stk, v) then sresult tstk
     else if fst d = Some stk then None
     else Option.bind (ctl (stk, v)) (\<lambda>(act, stk', v').
       brun ctl fin dec (if act = DShift then (None, 1, 1) else bupd d stk)
         (stk', v', xtree dec act v tstk)))\<close>

lemmas brun_simps [code] = brun.simps

definition cstep :: \<open>('k list \<times> 'w list \<Rightarrow> (('n, 't) dact \<times> 'k list \<times> 'w list) option) \<Rightarrow>
    ('k list \<times> 'w list \<Rightarrow> bool) \<Rightarrow> 'k list \<times> 'w list \<Rightarrow> 'k list \<times> 'w list \<Rightarrow> bool\<close> where
  \<open>cstep ctl fin c c' \<longleftrightarrow> \<not> fin c \<and> (\<exists>a. ctl c = Some (a, c'))\<close>

context
  fixes ctl :: \<open>'k list \<times> 'w list \<Rightarrow> (('n, 't) dact \<times> 'k list \<times> 'w list) option\<close>
    and fin :: \<open>'k list \<times> 'w list \<Rightarrow> bool\<close>
    and dec :: \<open>'w \<Rightarrow> ('t, 'ch, 'm) token_scheme\<close>
  assumes keep: \<open>\<And>stk v a stk' v'. ctl (stk, v) = Some (a, stk', v') \<Longrightarrow> a \<noteq> DShift \<Longrightarrow> v' = v\<close>
begin

abbreviation R where \<open>R \<equiv> cstep ctl fin\<close>

lemma nocycle:
  assumes h: \<open>nrun ctl fin dec st = Some t\<close>
  shows \<open>R\<^sup>*\<^sup>* (fst st, fst (snd st)) c' \<Longrightarrow> \<not> R\<^sup>+\<^sup>+ c' c'\<close>
proof -
  have \<open>ctl = ctl \<longrightarrow> fin = fin \<longrightarrow> (\<forall>c'. R\<^sup>*\<^sup>* (fst st, fst (snd st)) c' \<longrightarrow> \<not> R\<^sup>+\<^sup>+ c' c')\<close>
  proof (rule nrun.raw_induct[OF _ h, where P = \<open>\<lambda>ctl' fin' dec' st t. ctl' = ctl \<longrightarrow> fin' = fin \<longrightarrow>
      (\<forall>c'. R\<^sup>*\<^sup>* (fst st, fst (snd st)) c' \<longrightarrow> \<not> R\<^sup>+\<^sup>+ c' c')\<close>], goal_cases)
    case (1 f ctl' fin' dec' st t)
    obtain stk v ts where st: \<open>st = (stk, v, ts)\<close> by (cases st)
    show ?case
    proof (intro impI allI notI)
      fix c'
      assume c: \<open>ctl' = ctl\<close> and fi: \<open>fin' = fin\<close> and r: \<open>R\<^sup>*\<^sup>* (fst st, fst (snd st)) c'\<close>
        and cyc: \<open>R\<^sup>+\<^sup>+ c' c'\<close>
      have \<open>R\<^sup>+\<^sup>+ (stk, v) c'\<close> using rtranclp_tranclp_tranclp[OF r cyc] unfolding st by simp
      then obtain c1 where s1: \<open>R (stk, v) c1\<close> and r1: \<open>R\<^sup>*\<^sup>* c1 c'\<close>
        by (auto dest: tranclpD)
      from s1 obtain a where nf: \<open>\<not> fin (stk, v)\<close> and sc: \<open>ctl (stk, v) = Some (a, c1)\<close>
        unfolding cstep_def by blast
      obtain stk1 v1 where c1: \<open>c1 = (stk1, v1)\<close> by (cases c1)
      from "1"(2) nf sc obtain t' where
          rec: \<open>f ctl' fin' dec' (stk1, v1, xtree dec' a v ts) = Some t\<close>
        unfolding st c fi c1 by (auto simp: bind_eq_Some_conv)
      have \<open>\<forall>c'. R\<^sup>*\<^sup>* (stk1, v1) c' \<longrightarrow> \<not> R\<^sup>+\<^sup>+ c' c'\<close> using "1"(1)[OF rec] c fi by simp
      then show False using r1 cyc unfolding c1 by blast
    qed
  qed
  then show \<open>R\<^sup>*\<^sup>* (fst st, fst (snd st)) c' \<Longrightarrow> \<not> R\<^sup>+\<^sup>+ c' c'\<close> by blast
qed

lemma x_imp_n:
  assumes h: \<open>xrun_hist ctl fin dec seen st = Some t\<close>
  shows \<open>nrun ctl fin dec st = Some t\<close>
proof -
  have \<open>ctl = ctl \<longrightarrow> fin = fin \<longrightarrow> dec = dec \<longrightarrow> nrun ctl fin dec st = Some t\<close>
  proof (rule xrun_hist.raw_induct[OF _ h, where P = \<open>\<lambda>ctl' fin' dec' seen st t. ctl' = ctl \<longrightarrow>
      fin' = fin \<longrightarrow> dec' = dec \<longrightarrow> nrun ctl fin dec st = Some t\<close>], goal_cases)
    case (1 f ctl' fin' dec' seen st t)
    obtain stk v ts where st: \<open>st = (stk, v, ts)\<close> by (cases st)
    show ?case
    proof (intro impI)
      assume c: \<open>ctl' = ctl\<close> and fi: \<open>fin' = fin\<close> and d: \<open>dec' = dec\<close>
      show \<open>nrun ctl fin dec st = Some t\<close>
      proof (cases \<open>fin (stk, v)\<close>)
        case True
        with "1"(2) show ?thesis unfolding st c fi by (subst nrun.simps) simp
      next
        case False
        from False "1"(2) obtain a stk' v' where
            sc: \<open>ctl (stk, v) = Some (a, stk', v')\<close>
          and rec: \<open>f ctl' fin' dec' (if a = DShift then [] else stk # seen) (stk', v', xtree dec' a v ts) = Some t\<close>
          unfolding st c fi by (auto simp: bind_eq_Some_conv split: if_splits)
        from "1"(1)[OF rec] c fi d have \<open>nrun ctl fin dec (stk', v', xtree dec a v ts) = Some t\<close> by simp
        then show ?thesis unfolding st using False sc by (subst nrun.simps) simp
      qed
    qed
  qed
  then show ?thesis by blast
qed

lemma n_imp_x:
  assumes h: \<open>nrun ctl fin dec st = Some t\<close>
  shows \<open>(\<forall>c'. R\<^sup>*\<^sup>* (fst st, fst (snd st)) c' \<longrightarrow> \<not> R\<^sup>+\<^sup>+ c' c') \<Longrightarrow>
    \<forall>s \<in> set seen. R\<^sup>+\<^sup>+ (s, fst (snd st)) (fst st, fst (snd st)) \<Longrightarrow>
    xrun_hist ctl fin dec seen st = Some t\<close>
proof -
  have \<open>ctl = ctl \<longrightarrow> fin = fin \<longrightarrow> dec = dec \<longrightarrow> (\<forall>c'. R\<^sup>*\<^sup>* (fst st, fst (snd st)) c' \<longrightarrow> \<not> R\<^sup>+\<^sup>+ c' c') \<longrightarrow>
      (\<forall>seen. (\<forall>s \<in> set seen. R\<^sup>+\<^sup>+ (s, fst (snd st)) (fst st, fst (snd st))) \<longrightarrow>
        xrun_hist ctl fin dec seen st = Some t)\<close>
  proof (rule nrun.raw_induct[OF _ h, where P = \<open>\<lambda>ctl' fin' dec' st t. ctl' = ctl \<longrightarrow> fin' = fin \<longrightarrow>
      dec' = dec \<longrightarrow> (\<forall>c'. R\<^sup>*\<^sup>* (fst st, fst (snd st)) c' \<longrightarrow> \<not> R\<^sup>+\<^sup>+ c' c') \<longrightarrow>
      (\<forall>seen. (\<forall>s \<in> set seen. R\<^sup>+\<^sup>+ (s, fst (snd st)) (fst st, fst (snd st))) \<longrightarrow>
        xrun_hist ctl fin dec seen st = Some t)\<close>], goal_cases)
    case (1 f ctl' fin' dec' st t)
    obtain stk v ts where st: \<open>st = (stk, v, ts)\<close> by (cases st)
    show ?case
    proof (intro impI allI)
      fix seen
      assume c: \<open>ctl' = ctl\<close> and fi: \<open>fin' = fin\<close> and d: \<open>dec' = dec\<close>
        and nc: \<open>\<forall>c'. R\<^sup>*\<^sup>* (fst st, fst (snd st)) c' \<longrightarrow> \<not> R\<^sup>+\<^sup>+ c' c'\<close>
        and inv: \<open>\<forall>s \<in> set seen. R\<^sup>+\<^sup>+ (s, fst (snd st)) (fst st, fst (snd st))\<close>
      show \<open>xrun_hist ctl fin dec seen st = Some t\<close>
      proof (cases \<open>fin (stk, v)\<close>)
        case True
        with "1"(2) show ?thesis unfolding st c fi by (subst xrun_hist.simps) simp
      next
        case False
        have ns: \<open>stk \<notin> set seen\<close>
        proof
          assume \<open>stk \<in> set seen\<close>
          with inv have \<open>R\<^sup>+\<^sup>+ (stk, v) (stk, v)\<close> unfolding st by auto
          with nc show False unfolding st by auto
        qed
        from False "1"(2) obtain a stk' v' where
            sc: \<open>ctl (stk, v) = Some (a, stk', v')\<close>
          and rec: \<open>f ctl' fin' dec' (stk', v', xtree dec' a v ts) = Some t\<close>
          unfolding st c fi by (auto simp: bind_eq_Some_conv)
        have s1: \<open>R (stk, v) (stk', v')\<close> using False sc unfolding cstep_def by blast
        have nc': \<open>\<forall>c'. R\<^sup>*\<^sup>* (stk', v') c' \<longrightarrow> \<not> R\<^sup>+\<^sup>+ c' c'\<close>
          using nc s1 unfolding st by (auto intro: converse_rtranclp_into_rtranclp)
        have inv': \<open>\<forall>s \<in> set (if a = DShift then [] else stk # seen). R\<^sup>+\<^sup>+ (s, v') (stk', v')\<close>
        proof (cases \<open>a = DShift\<close>)
          case False
          then have v': \<open>v' = v\<close> using keep[OF sc] by blast
          show ?thesis using False inv s1 unfolding st v' by (auto intro: tranclp.trancl_into_trancl)
        qed simp
        from "1"(1)[OF rec] c fi d nc' inv'
        have \<open>xrun_hist ctl fin dec (if a = DShift then [] else stk # seen) (stk', v', xtree dec a v ts) = Some t\<close>
          by simp
        then show ?thesis unfolding st using False ns sc by (subst xrun_hist.simps) simp
      qed
    qed
  qed
  then show \<open>(\<forall>c'. R\<^sup>*\<^sup>* (fst st, fst (snd st)) c' \<longrightarrow> \<not> R\<^sup>+\<^sup>+ c' c') \<Longrightarrow>
    \<forall>s \<in> set seen. R\<^sup>+\<^sup>+ (s, fst (snd st)) (fst st, fst (snd st)) \<Longrightarrow>
    xrun_hist ctl fin dec seen st = Some t\<close> by blast
qed

lemma b_imp_n:
  assumes h: \<open>brun ctl fin dec d st = Some t\<close>
  shows \<open>nrun ctl fin dec st = Some t\<close>
proof -
  have \<open>ctl = ctl \<longrightarrow> fin = fin \<longrightarrow> dec = dec \<longrightarrow> nrun ctl fin dec st = Some t\<close>
  proof (rule brun.raw_induct[OF _ h, where P = \<open>\<lambda>ctl' fin' dec' d st t. ctl' = ctl \<longrightarrow>
      fin' = fin \<longrightarrow> dec' = dec \<longrightarrow> nrun ctl fin dec st = Some t\<close>], goal_cases)
    case (1 f ctl' fin' dec' d st t)
    obtain stk v ts where st: \<open>st = (stk, v, ts)\<close> by (cases st)
    show ?case
    proof (intro impI)
      assume c: \<open>ctl' = ctl\<close> and fi: \<open>fin' = fin\<close> and dd: \<open>dec' = dec\<close>
      show \<open>nrun ctl fin dec st = Some t\<close>
      proof (cases \<open>fin (stk, v)\<close>)
        case True
        with "1"(2) show ?thesis unfolding st c fi by (subst nrun.simps) simp
      next
        case False
        from False "1"(2) obtain a stk' v' where
            sc: \<open>ctl (stk, v) = Some (a, stk', v')\<close>
          and rec: \<open>f ctl' fin' dec' (if a = DShift then (None, 1, 1) else bupd d stk)
              (stk', v', xtree dec' a v ts) = Some t\<close>
          unfolding st c fi by (auto simp: bind_eq_Some_conv split: if_splits)
        from "1"(1)[OF rec] c fi dd have \<open>nrun ctl fin dec (stk', v', xtree dec a v ts) = Some t\<close> by simp
        then show ?thesis unfolding st using False sc by (subst nrun.simps) simp
      qed
    qed
  qed
  then show ?thesis by blast
qed

lemma fst_bupd: \<open>fst (bupd d stk) = Some stk \<or> fst (bupd d stk) = fst d\<close>
  by (cases d) (auto simp: bupd_def)

lemma n_imp_b:
  assumes h: \<open>nrun ctl fin dec st = Some t\<close>
  shows \<open>(\<forall>c'. R\<^sup>*\<^sup>* (fst st, fst (snd st)) c' \<longrightarrow> \<not> R\<^sup>+\<^sup>+ c' c') \<Longrightarrow>
    (\<forall>s. fst d = Some s \<longrightarrow> R\<^sup>+\<^sup>+ (s, fst (snd st)) (fst st, fst (snd st))) \<Longrightarrow>
    brun ctl fin dec d st = Some t\<close>
proof -
  have \<open>ctl = ctl \<longrightarrow> fin = fin \<longrightarrow> dec = dec \<longrightarrow> (\<forall>c'. R\<^sup>*\<^sup>* (fst st, fst (snd st)) c' \<longrightarrow> \<not> R\<^sup>+\<^sup>+ c' c') \<longrightarrow>
      (\<forall>d. (\<forall>s. fst d = Some s \<longrightarrow> R\<^sup>+\<^sup>+ (s, fst (snd st)) (fst st, fst (snd st))) \<longrightarrow>
        brun ctl fin dec d st = Some t)\<close>
  proof (rule nrun.raw_induct[OF _ h, where P = \<open>\<lambda>ctl' fin' dec' st t. ctl' = ctl \<longrightarrow> fin' = fin \<longrightarrow>
      dec' = dec \<longrightarrow> (\<forall>c'. R\<^sup>*\<^sup>* (fst st, fst (snd st)) c' \<longrightarrow> \<not> R\<^sup>+\<^sup>+ c' c') \<longrightarrow>
      (\<forall>d. (\<forall>s. fst d = Some s \<longrightarrow> R\<^sup>+\<^sup>+ (s, fst (snd st)) (fst st, fst (snd st))) \<longrightarrow>
        brun ctl fin dec d st = Some t)\<close>], goal_cases)
    case (1 f ctl' fin' dec' st t)
    obtain stk v ts where st: \<open>st = (stk, v, ts)\<close> by (cases st)
    show ?case
    proof (intro impI allI)
      fix d :: \<open>'k list option \<times> nat \<times> nat\<close>
      assume c: \<open>ctl' = ctl\<close> and fi: \<open>fin' = fin\<close> and dd: \<open>dec' = dec\<close>
        and nc: \<open>\<forall>c'. R\<^sup>*\<^sup>* (fst st, fst (snd st)) c' \<longrightarrow> \<not> R\<^sup>+\<^sup>+ c' c'\<close>
        and inv: \<open>\<forall>s. fst d = Some s \<longrightarrow> R\<^sup>+\<^sup>+ (s, fst (snd st)) (fst st, fst (snd st))\<close>
      show \<open>brun ctl fin dec d st = Some t\<close>
      proof (cases \<open>fin (stk, v)\<close>)
        case True
        with "1"(2) show ?thesis unfolding st c fi by (subst brun.simps) simp
      next
        case False
        have ns: \<open>fst d \<noteq> Some stk\<close>
        proof
          assume \<open>fst d = Some stk\<close>
          with inv have \<open>R\<^sup>+\<^sup>+ (stk, v) (stk, v)\<close> unfolding st by auto
          with nc show False unfolding st by auto
        qed
        from False "1"(2) obtain a stk' v' where
            sc: \<open>ctl (stk, v) = Some (a, stk', v')\<close>
          and rec: \<open>f ctl' fin' dec' (stk', v', xtree dec' a v ts) = Some t\<close>
          unfolding st c fi by (auto simp: bind_eq_Some_conv)
        have s1: \<open>R (stk, v) (stk', v')\<close> using False sc unfolding cstep_def by blast
        have nc': \<open>\<forall>c'. R\<^sup>*\<^sup>* (stk', v') c' \<longrightarrow> \<not> R\<^sup>+\<^sup>+ c' c'\<close>
          using nc s1 unfolding st by (auto intro: converse_rtranclp_into_rtranclp)
        have inv': \<open>\<forall>s. fst (if a = DShift then (None, 1, 1) else bupd d stk) = Some s \<longrightarrow>
            R\<^sup>+\<^sup>+ (s, v') (stk', v')\<close>
        proof (cases \<open>a = DShift\<close>)
          case False
          then have v': \<open>v' = v\<close> using keep[OF sc] by blast
          show ?thesis using False inv s1 fst_bupd[of d stk] unfolding st v'
            by (auto intro: tranclp.trancl_into_trancl)
        qed simp
        have ih: \<open>\<forall>d. (\<forall>s. fst d = Some s \<longrightarrow> R\<^sup>+\<^sup>+ (s, v') (stk', v')) \<longrightarrow>
            brun ctl fin dec d (stk', v', xtree dec a v ts) = Some t\<close>
          using "1"(1)[OF rec] c fi dd nc' unfolding fst_conv snd_conv by blast
        have \<open>brun ctl fin dec (if a = DShift then (None, 1, 1) else bupd d stk) (stk', v', xtree dec a v ts) = Some t\<close>
          using spec[OF ih, of \<open>if a = DShift then (None, 1, 1) else bupd d stk\<close>] inv' by blast
        then show ?thesis unfolding st using False ns sc by (subst brun.simps) simp
      qed
    qed
  qed
  then show \<open>(\<forall>c'. R\<^sup>*\<^sup>* (fst st, fst (snd st)) c' \<longrightarrow> \<not> R\<^sup>+\<^sup>+ c' c') \<Longrightarrow>
    (\<forall>s. fst d = Some s \<longrightarrow> R\<^sup>+\<^sup>+ (s, fst (snd st)) (fst st, fst (snd st))) \<Longrightarrow>
    brun ctl fin dec d st = Some t\<close> by blast
qed

theorem xrun_hist_brun:
  \<open>xrun_hist ctl fin dec [] st = brun ctl fin dec (None, 1, 1) st\<close>
proof (cases \<open>nrun ctl fin dec st\<close>)
  case None
  have x: \<open>xrun_hist ctl fin dec [] st = None\<close>
    using x_imp_n None by (cases \<open>xrun_hist ctl fin dec [] st\<close>) auto
  have b: \<open>brun ctl fin dec (None, 1, 1) st = None\<close>
    using b_imp_n None by (cases \<open>brun ctl fin dec (None, 1, 1) st\<close>) auto
  show ?thesis using x b by simp
next
  case (Some t)
  have nc: \<open>\<forall>c'. R\<^sup>*\<^sup>* (fst st, fst (snd st)) c' \<longrightarrow> \<not> R\<^sup>+\<^sup>+ c' c'\<close> using nocycle[OF Some] by blast
  show ?thesis using n_imp_x[OF Some nc] n_imp_b[OF Some nc] by simp
qed

end

lemma kctl_keep:
  \<open>kctl K (stk, v) = Some (a, stk', v') \<Longrightarrow> a \<noteq> DShift \<Longrightarrow> v' = v\<close>
  by (auto simp: kctl_def Let_def split: list.splits option.splits prod.splits dact.splits)

lemma dparse_via_prod_loop:
  assumes static: \<open>sstatic G Shn\<close>
    and st: \<open>lr0_states G Shn = sts\<close> and gt: \<open>la_gtab G sts = gtab\<close>
    and rt: \<open>red_buckets G Shn (length sts) = redtab\<close>
    and ps: \<open>pr0_states G Shn = psts\<close> and pg: \<open>pgtab G psts = pgt\<close>
    and pcs: \<open>pcomps G psts = pc\<close> and pfs: \<open>pfins Shn psts = pf\<close>
    and i0: \<open>st_find sts (lr0_start G Shn) = i\<^sub>0\<close>
    and p0: \<open>st_find psts (lr0_start G Shn) = p\<^sub>0\<close>
    and lt: \<open>mk_ltabs gtab sts redtab pgt psts pc pf = L\<close>
    and jt: \<open>jtabs_of L = J\<close>
    and ok: \<open>kok J kps (i\<^sub>0, p\<^sub>0)\<close>
    and kt: \<open>ktabs_of J kps = K\<close> and k0: \<open>kidx kps (i\<^sub>0, p\<^sub>0) = k\<^sub>0\<close>
  shows \<open>dparse G Shn w = brun (kctl K) (kfinal K) fst (None, 1, 1) ([k\<^sub>0], map (kenc K) w, [])\<close>
  unfolding dparse_via_prod_tables[OF static st gt rt ps pg pcs pfs i0 p0 lt jt ok kt k0]
  by (rule xrun_hist_brun) (rule kctl_keep)

end
