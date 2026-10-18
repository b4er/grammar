theory LR_Prod
  imports LR_Tok
begin

section \<open>The product automaton\<close>

text \<open>The simple driver keeps a pair of states per stack entry, one of the
  coarse and one of the precise automaton, and looks up both at every step.
  Here the reachable pairs are numbered, and the driver runs on a stack of
  pair numbers, with tables indexed by pair number: the shift and goto targets
  and, per lookahead, the reduce candidates.\<close>

subsection \<open>Maps and entries of tries\<close>

fun mapk_num :: \<open>(num \<Rightarrow> 'a \<Rightarrow> 'b option) \<Rightarrow> 'a ntrie \<Rightarrow> 'b ntrie\<close> where
  \<open>mapk_num g NTip = NTip\<close>
| \<open>mapk_num g (NNode x l r) = NNode (Option.bind x (g num.One))
     (mapk_num (\<lambda>k. g (num.Bit0 k)) l) (mapk_num (\<lambda>k. g (num.Bit1 k)) r)\<close>

lemma lookup_mapk_num: \<open>lookup_num (mapk_num g t) k = Option.bind (lookup_num t k) (g k)\<close>
proof (induction t arbitrary: g k)
  case (NNode x l r)
  then show ?case by (cases k) auto
qed simp

definition tab_mapk :: \<open>(nat \<Rightarrow> 'a \<Rightarrow> 'b option) \<Rightarrow> 'a ntab \<Rightarrow> 'b ntab\<close> where
  \<open>tab_mapk f t = (case t of NTab z tr \<Rightarrow>
     NTab (Option.bind z (f 0)) (mapk_num (\<lambda>k. f (nat_of_num k)) tr))\<close>

lemma tlookup_tab_mapk: \<open>tlookup (tab_mapk f t) n = Option.bind (tlookup t n) (f n)\<close>
proof (cases t)
  case (NTab z tr)
  show ?thesis
  proof (cases \<open>n = 0\<close>)
    case False
    then have n: \<open>nat_of_num (num_of_nat n) = n\<close> using num_of_nat_inverse by simp
    show ?thesis using False unfolding NTab tab_mapk_def tlookup_def
      by (simp add: lookup_mapk_num n)
  qed (simp add: NTab tab_mapk_def tlookup_def)
qed

fun entries_num :: \<open>(num \<Rightarrow> nat) \<Rightarrow> 'a ntrie \<Rightarrow> (nat \<times> 'a) list\<close> where
  \<open>entries_num f NTip = []\<close>
| \<open>entries_num f (NNode x l r) = (case x of None \<Rightarrow> [] | Some a \<Rightarrow> [(f num.One, a)]) @
     entries_num (\<lambda>k. f (num.Bit0 k)) l @ entries_num (\<lambda>k. f (num.Bit1 k)) r\<close>

lemma entries_num_complete:
  \<open>lookup_num t k = Some a \<Longrightarrow> (f k, a) \<in> set (entries_num f t)\<close>
proof (induction t arbitrary: f k)
  case (NNode x l r)
  show ?case
  proof (cases k)
    case (Bit0 k')
    then show ?thesis using NNode.prems NNode.IH(1)[of k' \<open>\<lambda>k. f (num.Bit0 k)\<close>] by simp
  next
    case (Bit1 k')
    then show ?thesis using NNode.prems NNode.IH(2)[of k' \<open>\<lambda>k. f (num.Bit1 k)\<close>] by simp
  qed (use NNode.prems in simp)
qed simp

definition tentries :: \<open>'a ntab \<Rightarrow> (nat \<times> 'a) list\<close> where
  \<open>tentries t = (case t of NTab z tr \<Rightarrow>
     (case z of None \<Rightarrow> [] | Some a \<Rightarrow> [(0, a)]) @ entries_num nat_of_num tr)\<close>

lemma tentries_complete: \<open>tlookup t n = Some a \<Longrightarrow> (n, a) \<in> set (tentries t)\<close>
proof (cases t)
  case (NTab z tr)
  assume h: \<open>tlookup t n = Some a\<close>
  show ?thesis
  proof (cases \<open>n = 0\<close>)
    case False
    then have n: \<open>nat_of_num (num_of_nat n) = n\<close> using num_of_nat_inverse by simp
    from h False have \<open>lookup_num tr (num_of_nat n) = Some a\<close> unfolding NTab tlookup_def by simp
    from entries_num_complete[OF this, of nat_of_num] show ?thesis
      unfolding NTab tentries_def n by simp
  qed (use h in \<open>simp add: NTab tentries_def tlookup_def\<close>)
qed

definition trow :: \<open>'a ntab ntab \<Rightarrow> nat \<Rightarrow> 'a ntab\<close> where
  \<open>trow t i = (case tlookup t i of None \<Rightarrow> NTab None NTip | Some r \<Rightarrow> r)\<close>

lemma jget_trow: \<open>jget t i k = tlookup (trow t i) k\<close>
  unfolding jget_def trow_def tlookup_def by (simp split: option.splits)

subsection \<open>Runs on re-encoded stacks, under an invariant\<close>

text \<open>\<^const>\<open>xrun_hist\<close> is generic in the stack entries. A run on pairs of state
  numbers equals the run on their numbers in a list of pairs, provided the
  pairs on the stack stay in the list.\<close>

text \<open>The steps agree on stacks whose entries satisfy an invariant that the
  first step preserves, and the encoding is injective on those entries.\<close>

locale stack_transfer =
  fixes enc :: \<open>'a \<Rightarrow> 'b\<close> and P :: \<open>'a \<Rightarrow> bool\<close>
    and ctl1 :: \<open>'a list \<times> 'w list \<Rightarrow> (('n, 't) dact \<times> 'a list \<times> 'w list) option\<close>
    and fin1 :: \<open>'a list \<times> 'w list \<Rightarrow> bool\<close>
    and ctl2 :: \<open>'b list \<times> 'w list \<Rightarrow> (('n, 't) dact \<times> 'b list \<times> 'w list) option\<close>
    and fin2 :: \<open>'b list \<times> 'w list \<Rightarrow> bool\<close>
  assumes inj: \<open>inj_on enc {x. P x}\<close>
    and ctl: \<open>\<And>stk v. \<forall>x \<in> set stk. P x \<Longrightarrow> ctl2 (map enc stk, v) =
      map_option (\<lambda>(a, stk', v'). (a, map enc stk', v')) (ctl1 (stk, v))\<close>
    and fin: \<open>\<And>stk v. \<forall>x \<in> set stk. P x \<Longrightarrow> fin2 (map enc stk, v) = fin1 (stk, v)\<close>
    and pres: \<open>\<And>stk v a stk' v'. \<forall>x \<in> set stk. P x \<Longrightarrow> ctl1 (stk, v) = Some (a, stk', v') \<Longrightarrow>
      \<forall>x \<in> set stk'. P x\<close>
begin

definition allP :: \<open>'a list \<Rightarrow> bool\<close> where
  \<open>allP stk \<longleftrightarrow> (\<forall>x \<in> set stk. P x)\<close>

lemma mem_map_enc:
  assumes \<open>allP stk\<close> \<open>\<forall>s \<in> set seen. allP s\<close>
  shows \<open>map enc stk \<in> set (map (map enc) seen) \<longleftrightarrow> stk \<in> set seen\<close>
proof
  assume \<open>map enc stk \<in> set (map (map enc) seen)\<close>
  then obtain s where s: \<open>s \<in> set seen\<close> \<open>map enc stk = map enc s\<close> by auto
  have \<open>inj_on enc (set stk \<union> set s)\<close>
    by (rule inj_on_subset[OF inj]) (use assms s(1) in \<open>auto simp: allP_def\<close>)
  with s(2) have \<open>stk = s\<close> by (simp add: inj_on_map_eq_map)
  with s(1) show \<open>stk \<in> set seen\<close> by simp
qed auto

lemma t1_imp_t2:
  assumes h: \<open>xrun_hist ctl1 fin1 dec seen st = Some t\<close>
  shows \<open>allP (fst st) \<Longrightarrow> \<forall>s \<in> set seen. allP s \<Longrightarrow>
    xrun_hist ctl2 fin2 dec (map (map enc) seen) (map enc (fst st), snd st) = Some t\<close>
proof -
  have \<open>ctl1 = ctl1 \<longrightarrow> fin1 = fin1 \<longrightarrow> allP (fst st) \<longrightarrow> (\<forall>s \<in> set seen. allP s) \<longrightarrow>
      xrun_hist ctl2 fin2 dec (map (map enc) seen) (map enc (fst st), snd st) = Some t\<close>
  proof (rule xrun_hist.raw_induct[OF _ h, where P = \<open>\<lambda>ctl fin dec seen st t. ctl = ctl1 \<longrightarrow> fin = fin1 \<longrightarrow>
      allP (fst st) \<longrightarrow> (\<forall>s \<in> set seen. allP s) \<longrightarrow>
      xrun_hist ctl2 fin2 dec (map (map enc) seen) (map enc (fst st), snd st) = Some t\<close>], goal_cases)
    case (1 f ctl fin dec seen st t)
    obtain stk v tstk where st: \<open>st = (stk, v, tstk)\<close> by (cases st)
    show ?case
    proof (intro impI)
      assume c: \<open>ctl = ctl1\<close> and fi: \<open>fin = fin1\<close> and ps: \<open>allP (fst st)\<close>
        and pseen: \<open>\<forall>s \<in> set seen. allP s\<close>
      have P: \<open>\<forall>x \<in> set stk. P x\<close> using ps unfolding st allP_def by simp
      show \<open>xrun_hist ctl2 fin2 dec (map (map enc) seen) (map enc (fst st), snd st) = Some t\<close>
      proof (cases \<open>fin1 (stk, v)\<close>)
        case True
        with "1"(2) show ?thesis unfolding st c fi by (subst xrun_hist.simps) (simp add: fin[OF P])
      next
        case False
        from False "1"(2) have nk: \<open>stk \<notin> set seen\<close> unfolding st c fi by (auto split: if_splits)
        from False "1"(2) obtain a stk' v' where
            sc: \<open>ctl1 (stk, v) = Some (a, stk', v')\<close>
          and rec: \<open>f ctl fin dec (if a = DShift then [] else stk # seen) (stk', v', xtree dec a v tstk) = Some t\<close>
          unfolding st c fi by (auto simp: bind_eq_Some_conv split: if_splits)
        have P': \<open>allP stk'\<close> using pres[OF P sc] unfolding allP_def .
        have pseen': \<open>\<forall>s \<in> set (if a = DShift then [] else stk # seen). allP s\<close>
          using pseen ps unfolding st by auto
        from "1"(1)[OF rec] c fi P' pseen'
        have \<open>xrun_hist ctl2 fin2 dec (map (map enc) (if a = DShift then [] else stk # seen))
            (map enc stk', v', xtree dec a v tstk) = Some t\<close> by simp
        then show ?thesis unfolding st using False nk sc mem_map_enc[of stk seen] P pseen unfolding allP_def
          by (subst xrun_hist.simps) (cases \<open>a = DShift\<close>; simp add: fin[OF P] ctl[OF P])
      qed
    qed
  qed
  then show \<open>allP (fst st) \<Longrightarrow> \<forall>s \<in> set seen. allP s \<Longrightarrow>
    xrun_hist ctl2 fin2 dec (map (map enc) seen) (map enc (fst st), snd st) = Some t\<close> by blast
qed

lemma t2_imp_t1:
  assumes h: \<open>xrun_hist ctl2 fin2 dec seen2 st2 = Some t\<close>
  shows \<open>seen2 = map (map enc) seen \<Longrightarrow> st2 = (map enc stk, v, tstk) \<Longrightarrow>
    allP stk \<Longrightarrow> \<forall>s \<in> set seen. allP s \<Longrightarrow> xrun_hist ctl1 fin1 dec seen (stk, v, tstk) = Some t\<close>
proof -
  have \<open>ctl2 = ctl2 \<longrightarrow> fin2 = fin2 \<longrightarrow> (\<forall>seen stk v tstk. seen2 = map (map enc) seen \<longrightarrow>
      st2 = (map enc stk, v, tstk) \<longrightarrow> allP stk \<longrightarrow> (\<forall>s \<in> set seen. allP s) \<longrightarrow>
      xrun_hist ctl1 fin1 dec seen (stk, v, tstk) = Some t)\<close>
  proof (rule xrun_hist.raw_induct[OF _ h, where P = \<open>\<lambda>ctl fin dec seen2 st2 t. ctl = ctl2 \<longrightarrow> fin = fin2 \<longrightarrow>
      (\<forall>seen stk v tstk. seen2 = map (map enc) seen \<longrightarrow> st2 = (map enc stk, v, tstk) \<longrightarrow>
        allP stk \<longrightarrow> (\<forall>s \<in> set seen. allP s) \<longrightarrow> xrun_hist ctl1 fin1 dec seen (stk, v, tstk) = Some t)\<close>],
      goal_cases)
    case (1 f ctl fin dec seen2 st2 t)
    show ?case
    proof (intro impI allI)
      fix seen stk v tstk
      assume c: \<open>ctl = ctl2\<close> and fi: \<open>fin = fin2\<close> and se: \<open>seen2 = map (map enc) seen\<close>
        and st: \<open>st2 = (map enc stk, v, tstk)\<close> and ps: \<open>allP stk\<close> and pseen: \<open>\<forall>s \<in> set seen. allP s\<close>
      have P: \<open>\<forall>x \<in> set stk. P x\<close> using ps unfolding allP_def .
      show \<open>xrun_hist ctl1 fin1 dec seen (stk, v, tstk) = Some t\<close>
      proof (cases \<open>fin1 (stk, v)\<close>)
        case True
        with "1"(2) show ?thesis unfolding st c fi by (subst xrun_hist.simps) (simp add: fin[OF P])
      next
        case False
        from False "1"(2) have nk: \<open>stk \<notin> set seen\<close>
          unfolding st c fi se using mem_map_enc[OF ps pseen] by (auto simp: fin[OF P] split: if_splits)
        from False "1"(2) obtain a stk2 v' where
            sc: \<open>ctl2 (map enc stk, v) = Some (a, stk2, v')\<close>
          and rec: \<open>f ctl fin dec (if a = DShift then [] else map enc stk # seen2)
              (stk2, v', xtree dec a v tstk) = Some t\<close>
          unfolding st c fi by (auto simp: bind_eq_Some_conv fin[OF P] split: if_splits)
        from sc obtain stk' where sc1: \<open>ctl1 (stk, v) = Some (a, stk', v')\<close> and stk2: \<open>stk2 = map enc stk'\<close>
          unfolding ctl[OF P] by (auto split: prod.splits)
        have P': \<open>allP stk'\<close> using pres[OF P sc1] unfolding allP_def .
        have \<open>xrun_hist ctl1 fin1 dec (if a = DShift then [] else stk # seen) (stk', v', xtree dec a v tstk) = Some t\<close>
          using "1"(1)[OF rec] c fi se stk2 P' pseen ps by auto
        then show ?thesis using False nk sc1 by (subst xrun_hist.simps) simp
      qed
    qed
  qed
  then show \<open>seen2 = map (map enc) seen \<Longrightarrow> st2 = (map enc stk, v, tstk) \<Longrightarrow>
    allP stk \<Longrightarrow> \<forall>s \<in> set seen. allP s \<Longrightarrow> xrun_hist ctl1 fin1 dec seen (stk, v, tstk) = Some t\<close> by blast
qed

theorem stack_xrun_hist_eq:
  assumes \<open>\<forall>x \<in> set stk. P x\<close>
  shows \<open>xrun_hist ctl2 fin2 dec [] (map enc stk, v, tstk) = xrun_hist ctl1 fin1 dec [] (stk, v, tstk)\<close>
proof -
  have ps: \<open>allP stk\<close> using assms unfolding allP_def .
  show ?thesis
  proof (cases \<open>xrun_hist ctl1 fin1 dec [] (stk, v, tstk)\<close>)
    case None
    show ?thesis
    proof (cases \<open>xrun_hist ctl2 fin2 dec [] (map enc stk, v, tstk)\<close>)
      case (Some t)
      from t2_imp_t1[OF Some, of \<open>[]\<close> stk v tstk] ps None show ?thesis by simp
    qed (simp add: None)
  next
    case (Some t)
    from t1_imp_t2[OF Some] ps Some show ?thesis by simp
  qed
qed

end

subsection \<open>Numbering the pairs of states\<close>

definition kidx :: \<open>'a list \<Rightarrow> 'a \<Rightarrow> nat\<close> where
  \<open>kidx ps x = (case map_of (zip ps [0..<length ps]) x of Some k \<Rightarrow> k | None \<Rightarrow> length ps)\<close>

lemma map_of_zip_upt_Some:
  \<open>map_of (zip xs [m..<m + length xs]) x = Some k \<Longrightarrow> m \<le> k \<and> k < m + length xs \<and> xs ! (k - m) = x\<close>
proof (induction xs arbitrary: m)
  case (Cons y xs)
  have u: \<open>[m..<m + length (y # xs)] = m # [Suc m..<Suc m + length xs]\<close>
    by (simp add: upt_rec)
  show ?case
  proof (cases \<open>x = y\<close>)
    case False
    with Cons.prems have \<open>map_of (zip xs [Suc m..<Suc m + length xs]) x = Some k\<close>
      unfolding u by simp
    from Cons.IH[OF this] have ih: \<open>Suc m \<le> k\<close> \<open>k < Suc m + length xs\<close> \<open>xs ! (k - Suc m) = x\<close>
      by auto
    have \<open>k - m = Suc (k - Suc m)\<close> using ih(1) by arith
    then show ?thesis using ih by simp
  qed (use Cons.prems u in simp)
qed simp

lemma kidx:
  assumes \<open>x \<in> set ps\<close>
  shows \<open>kidx ps x < length ps\<close> \<open>ps ! kidx ps x = x\<close>
proof -
  have \<open>map_of (zip ps [0..<length ps]) x \<noteq> None\<close>
    using assms by simp
  then obtain k where k: \<open>map_of (zip ps [0..<length ps]) x = Some k\<close> by blast
  from map_of_zip_upt_Some[of ps 0 x k] k show \<open>kidx ps x < length ps\<close> \<open>ps ! kidx ps x = x\<close>
    unfolding kidx_def by simp_all
qed

lemma kidx_inj: \<open>inj_on (kidx ps) (set ps)\<close>
  by (rule inj_on_inverseI[where g = \<open>(!) ps\<close>]) (rule kidx(2))

subsection \<open>The product tables and the product step\<close>

datatype ('n, 't) ktabs = KTabs
  (kt_lal: \<open>('t \<times> nat) list\<close>) (kt_miss: nat)
  (kt_T: \<open>nat ntab ntab\<close>) (kt_N: \<open>nat ntab ntab\<close>) (kt_C: \<open>nat list ntab ntab\<close>)
  (kt_prs: \<open>(('n \<times> ('n, 't) rhs) \<times> nat) ntab\<close>) (kt_pf: \<open>bool ntab\<close>)

definition jcomps :: \<open>('n, 't) jtabs \<Rightarrow> nat \<Rightarrow> nat list\<close> where
  \<open>jcomps J p = (case tlookup (jt_pc J) p of None \<Rightarrow> [] | Some cs \<Rightarrow> cs)\<close>

definition ktabs_of :: \<open>('n, 't) jtabs \<Rightarrow> (nat \<times> nat) list \<Rightarrow> ('n, 't) ktabs\<close> where
  \<open>ktabs_of J ps = KTabs (jt_lal J) (jt_miss J)
     (tab_of_list (map (\<lambda>(i, p). tab_mapk (\<lambda>l q. Some (kidx ps (jgo (jt_cgT J) (jt_ns J) i l, q)))
        (trow (jt_pgT J) p)) ps))
     (tab_of_list (map (\<lambda>(i, p). tab_mapk (\<lambda>A q. Some (kidx ps (jgo (jt_cgN J) (jt_ns J) i A, q)))
        (trow (jt_pgN J) p)) ps))
     (tab_of_list (map (\<lambda>(i, p). tab_mapk (\<lambda>l lics. Some (filter (\<lambda>j. tlookup lics j \<noteq> None) (jcomps J p)))
        (trow (jt_lic J) i)) ps))
     (jt_prs J)
     (tab_of_list (map (\<lambda>(i, p). tlookup (jt_pf J) p = Some True) ps))\<close>

text \<open>The input token with its number, as \<^const>\<open>jenc\<close>.\<close>

definition kenc :: \<open>('n, 't) ktabs \<Rightarrow> ('t, 'ch, 'm) token_scheme \<Rightarrow> ('t, 'ch, 'm) token_scheme \<times> nat\<close> where
  \<open>kenc K x = (x, case map_of (kt_lal K) (tok x) of Some l \<Rightarrow> l | None \<Rightarrow> kt_miss K)\<close>

lemma kenc_ktabs_of: \<open>kenc (ktabs_of J ps) = jenc J\<close>
  by (simp add: fun_eq_iff kenc_def jenc_def jla_def ktabs_of_def split: option.split)

definition kcands :: \<open>('n, 't) ktabs \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat list\<close> where
  \<open>kcands K k l = (case jget (kt_C K) k l of None \<Rightarrow> [] | Some cs \<Rightarrow> cs)\<close>

definition ktarget :: \<open>('n, 't) ktabs \<Rightarrow> nat list \<Rightarrow> nat \<Rightarrow> iact \<Rightarrow> (('n, 't) dact \<times> nat list) option\<close> where
  \<open>ktarget K kstk l act = (case act of
      IShift \<Rightarrow> (case kstk of [] \<Rightarrow> None | k # _ \<Rightarrow> map_option (\<lambda>k'. (DShift, k' # kstk)) (jget (kt_T K) k l))
    | IReduce j \<Rightarrow> (case tlookup (kt_prs K) j of None \<Rightarrow> None | Some (pr, A) \<Rightarrow>
        (case drop_as (snd pr) kstk of [] \<Rightarrow> None | k'' # rest \<Rightarrow>
           map_option (\<lambda>k'. (DReduce pr, k' # k'' # rest)) (jget (kt_N K) k'' A))))\<close>

definition kctl :: \<open>('n, 't) ktabs \<Rightarrow> nat list \<times> (('t, 'ch, 'm) token_scheme \<times> nat) list \<Rightarrow>
    (('n, 't) dact \<times> nat list \<times> (('t, 'ch, 'm) token_scheme \<times> nat) list) option\<close> where
  \<open>kctl K c = (case c of (kstk, v) \<Rightarrow>
     (case kstk of [] \<Rightarrow> None | k # _ \<Rightarrow>
       let l = (case v of [] \<Rightarrow> 0 | (_, l) # _ \<Rightarrow> l);
           cands = (case v of [] \<Rightarrow> [] | _ \<Rightarrow> [IShift]) @ map IReduce (kcands K k l)
       in (case spick (ktarget K kstk l) cands of
            None \<Rightarrow> None
          | Some (_, a, stk') \<Rightarrow> Some (a, stk', (case a of DShift \<Rightarrow> tl v | DReduce _ \<Rightarrow> v)))))\<close>

definition kfinal :: \<open>('n, 't) ktabs \<Rightarrow> nat list \<times> (('t, 'ch, 'm) token_scheme \<times> nat) list \<Rightarrow> bool\<close> where
  \<open>kfinal K c \<longleftrightarrow> (case c of (kstk, v) \<Rightarrow> v = [] \<and>
     (case kstk of [] \<Rightarrow> False | k # _ \<Rightarrow> tlookup (kt_pf K) k = Some True))\<close>

subsection \<open>Correctness of the product step\<close>

lemma spick_map:
  assumes \<open>\<And>a. a \<in> set xs \<Longrightarrow> g a = map_option (h a) (f a)\<close>
  shows \<open>spick g xs = map_option (\<lambda>(a, b). (a, h a b)) (spick f xs)\<close>
  using assms by (induction xs) (auto split: option.splits)

lemma drop_as_map: \<open>drop_as xs (map f ys) = map f (drop_as xs ys)\<close>
  by (induction xs ys rule: drop_as.induct) auto

lemma set_drop_as: \<open>set (drop_as xs ys) \<subseteq> set ys\<close>
  by (induction xs ys rule: drop_as.induct) auto

lemma jlicd_simps: \<open>jlicd None = (\<lambda>_. False)\<close> \<open>jlicd (Some t) = (\<lambda>j. tlookup t j \<noteq> None)\<close>
  by (simp_all add: fun_eq_iff jlicd_def)

context
  fixes J :: \<open>('n, 't) jtabs\<close> and ps :: \<open>(nat \<times> nat) list\<close>
begin

lemma kt_T_row:
  \<open>x \<in> set ps \<Longrightarrow> jget (kt_T (ktabs_of J ps)) (kidx ps x) l =
    map_option (\<lambda>q. kidx ps (jgo (jt_cgT J) (jt_ns J) (fst x) l, q)) (jget (jt_pgT J) (snd x) l)\<close>
  using kidx[of x ps]
  by (cases x) (simp add: ktabs_of_def jget_def tlookup_tab_of_list tlookup_tab_mapk
      jget_trow[symmetric] map_option_case split: option.splits)

lemma kt_N_row:
  \<open>x \<in> set ps \<Longrightarrow> jget (kt_N (ktabs_of J ps)) (kidx ps x) A =
    map_option (\<lambda>q. kidx ps (jgo (jt_cgN J) (jt_ns J) (fst x) A, q)) (jget (jt_pgN J) (snd x) A)\<close>
  using kidx[of x ps]
  by (cases x) (simp add: ktabs_of_def jget_def tlookup_tab_of_list tlookup_tab_mapk
      jget_trow[symmetric] map_option_case split: option.splits)

lemma kcands_row:
  \<open>x \<in> set ps \<Longrightarrow> kcands (ktabs_of J ps) (kidx ps x) l =
    filter (jlicd (jget (jt_lic J) (fst x) l)) (jcomps J (snd x))\<close>
proof -
  assume x: \<open>x \<in> set ps\<close>
  obtain i p where ip: \<open>x = (i, p)\<close> by (cases x)
  have row: \<open>jget (kt_C (ktabs_of J ps)) (kidx ps x) l =
      Option.bind (jget (jt_lic J) i l) (\<lambda>lics. Some (filter (\<lambda>j. tlookup lics j \<noteq> None) (jcomps J p)))\<close>
    using kidx[OF x] unfolding ip
    by (simp add: ktabs_of_def jget_def tlookup_tab_of_list tlookup_tab_mapk jget_trow[symmetric])
  show ?thesis unfolding ip
    by (cases \<open>jget (jt_lic J) i l\<close>) (simp_all add: kcands_def row[unfolded ip] jlicd_simps)
qed

lemma kt_pf_row:
  \<open>x \<in> set ps \<Longrightarrow> tlookup (kt_pf (ktabs_of J ps)) (kidx ps x) = Some (tlookup (jt_pf J) (snd x) = Some True)\<close>
  using kidx[of x ps] by (cases x) (simp add: ktabs_of_def tlookup_tab_of_list)

lemma kfinal_eq:
  \<open>set stk \<subseteq> set ps \<Longrightarrow> kfinal (ktabs_of J ps) (map (kidx ps) stk, v) = jfinal2 J (stk, v)\<close>
  by (cases stk) (auto simp: kfinal_def jfinal2_def kt_pf_row)

lemma ktarget_eq:
  assumes stk: \<open>set stk \<subseteq> set ps\<close> and s: \<open>stk = (i, p) # rest\<close>
  shows \<open>ktarget (ktabs_of J ps) (map (kidx ps) stk) l act = map_option (\<lambda>q. case act of
      IShift \<Rightarrow> (DShift, kidx ps (jgo (jt_cgT J) (jt_ns J) i l, q) # map (kidx ps) stk)
    | IReduce j \<Rightarrow> (case tlookup (jt_prs J) j of None \<Rightarrow> (DShift, []) | Some (pr, A) \<Rightarrow>
        (case drop_as (snd pr) stk of [] \<Rightarrow> (DShift, []) | (i', _) # _ \<Rightarrow>
          (DReduce pr, kidx ps (jgo (jt_cgN J) (jt_ns J) i' A, q) # map (kidx ps) (drop_as (snd pr) stk)))))
    (jtarget J stk l act)\<close>
proof (cases act)
  case IShift
  have ip: \<open>(i, p) \<in> set ps\<close> using stk s by simp
  show ?thesis using kt_T_row[OF ip, of l]
    unfolding IShift s by (simp add: ktarget_def jtarget_def option.map_comp o_def)
next
  case (IReduce j)
  show ?thesis
  proof (cases \<open>tlookup (jt_prs J) j\<close>)
    case (Some prA)
    obtain pr A where prA: \<open>prA = (pr, A)\<close> by (cases prA)
    show ?thesis
    proof (cases \<open>drop_as (snd pr) stk\<close>)
      case (Cons x rest')
      obtain i' p' where x: \<open>x = (i', p')\<close> by (cases x)
      have ip': \<open>(i', p') \<in> set ps\<close> using stk set_drop_as[of \<open>snd pr\<close> stk] Cons x by auto
      show ?thesis using kt_N_row[OF ip', of A] Some Cons
        unfolding IReduce prA x
        by (simp add: ktarget_def jtarget_def ktabs_of_def drop_as_map option.map_comp o_def)
    qed (use Some prA IReduce in \<open>simp add: ktarget_def jtarget_def ktabs_of_def drop_as_map\<close>)
  qed (use IReduce in \<open>simp add: ktarget_def jtarget_def ktabs_of_def\<close>)
qed

theorem kctl_eq:
  assumes stk: \<open>set stk \<subseteq> set ps\<close>
  shows \<open>kctl (ktabs_of J ps) (map (kidx ps) stk, v) =
    map_option (\<lambda>(a, stk', v'). (a, map (kidx ps) stk', v')) (jctl2 J (stk, v))\<close>
proof (cases stk)
  case (Cons x rest)
  obtain i p where x: \<open>x = (i, p)\<close> by (cases x)
  have ip: \<open>(i, p) \<in> set ps\<close> using stk Cons x by simp
  define l where \<open>l = (case v of [] \<Rightarrow> 0 | (_, l) # _ \<Rightarrow> l)\<close>
  define cands where \<open>cands = (case v of [] \<Rightarrow> [] | _ \<Rightarrow> [IShift]) @
    map IReduce (filter (jlicd (jget (jt_lic J) i l)) (jcomps J p))\<close>
  define h where \<open>h = (\<lambda>act q. case act of
      IShift \<Rightarrow> (DShift, kidx ps (jgo (jt_cgT J) (jt_ns J) i l, q) # map (kidx ps) stk)
    | IReduce j \<Rightarrow> (case tlookup (jt_prs J) j of None \<Rightarrow> (DShift, []) | Some (pr, A) \<Rightarrow>
        (case drop_as (snd pr) stk of [] \<Rightarrow> (DShift, []) | (i', _) # _ \<Rightarrow>
          (DReduce pr, kidx ps (jgo (jt_cgN J) (jt_ns J) i' A, q) # map (kidx ps) (drop_as (snd pr) stk)))))\<close>
  have sp: \<open>spick (ktarget (ktabs_of J ps) (map (kidx ps) stk) l) cands =
      map_option (\<lambda>(a, b). (a, h a b)) (spick (jtarget J stk l) cands)\<close>
    by (rule spick_map) (use ktarget_eq[OF stk, of i p rest l] Cons x in \<open>simp add: h_def\<close>)
  have k: \<open>kctl (ktabs_of J ps) (map (kidx ps) stk, v) =
      (case spick (ktarget (ktabs_of J ps) (map (kidx ps) stk) l) cands of None \<Rightarrow> None
        | Some (_, a, stk') \<Rightarrow> Some (a, stk', (case a of DShift \<Rightarrow> tl v | DReduce _ \<Rightarrow> v)))\<close>
    unfolding kctl_def Cons x l_def cands_def using kcands_row[OF ip] Cons x
    by (simp add: Let_def)
  have j: \<open>jctl2 J (stk, v) = (case spick (jtarget J stk l) cands of
            None \<Rightarrow> None
          | Some (IShift, q) \<Rightarrow> Some (DShift, (jgo (jt_cgT J) (jt_ns J) i l, q) # stk, tl v)
          | Some (IReduce j, q) \<Rightarrow> (case tlookup (jt_prs J) j of None \<Rightarrow> None | Some (pr, A) \<Rightarrow>
              (case drop_as (snd pr) stk of [] \<Rightarrow> None | (i', _) # _ \<Rightarrow>
                 Some (DReduce pr, (jgo (jt_cgN J) (jt_ns J) i' A, q) # drop_as (snd pr) stk, v))))\<close>
    unfolding jctl2_def Cons x l_def cands_def jcomps_def by (simp add: Let_def)
  show ?thesis
  proof (cases \<open>spick (jtarget J stk l) cands\<close>)
    case (Some aq)
    obtain act q where aq: \<open>aq = (act, q)\<close> by (cases aq)
    have tq: \<open>jtarget J stk l act = Some q\<close> using spick_SomeD[OF Some[unfolded aq]] by simp
    show ?thesis
    proof (cases act)
      case (IReduce j)
      from tq obtain pr A i' p' rest' where
          prA: \<open>tlookup (jt_prs J) j = Some (pr, A)\<close> and d: \<open>drop_as (snd pr) stk = (i', p') # rest'\<close>
        unfolding IReduce jtarget_def by (auto split: option.splits list.splits)
      show ?thesis unfolding k j sp Some aq IReduce using prA d by (simp add: h_def)
    qed (simp add: k j sp Some aq h_def)
  qed (simp add: k j sp)
qed (simp add: kctl_def jctl2_def)

end

subsection \<open>The reachable pairs\<close>

text \<open>The successors of a pair of states under a shift or a goto. The list of
  pairs is computed by a search from the start pair, and checked to be
  closed under successors.\<close>

definition ksucc :: \<open>('n, 't) jtabs \<Rightarrow> nat \<times> nat \<Rightarrow> (nat \<times> nat) list\<close> where
  \<open>ksucc J x = (case x of (i, p) \<Rightarrow>
     map (\<lambda>(l, q). (jgo (jt_cgT J) (jt_ns J) i l, q)) (tentries (trow (jt_pgT J) p)) @
     map (\<lambda>(A, q). (jgo (jt_cgN J) (jt_ns J) i A, q)) (tentries (trow (jt_pgN J) p)))\<close>

fun kwork :: \<open>('n, 't) jtabs \<Rightarrow> nat \<Rightarrow> (nat \<times> nat) list \<Rightarrow> (nat \<times> nat) list \<Rightarrow> (nat \<times> nat) list\<close> where
  \<open>kwork J 0 todo acc = acc\<close>
| \<open>kwork J (Suc n) [] acc = acc\<close>
| \<open>kwork J (Suc n) (x # todo) acc = (let new = filter (\<lambda>y. y \<notin> set acc) (remdups (ksucc J x)) in
     kwork J n (new @ todo) (acc @ new))\<close>

definition kpairs :: \<open>('n, 't) jtabs \<Rightarrow> nat \<times> nat \<Rightarrow> (nat \<times> nat) list\<close> where
  \<open>kpairs J x0 = kwork J (Suc (jt_ns J) * Suc (jt_ns J) * 64) [x0] [x0]\<close>

definition kok :: \<open>('n, 't) jtabs \<Rightarrow> (nat \<times> nat) list \<Rightarrow> nat \<times> nat \<Rightarrow> bool\<close> where
  \<open>kok J ps x0 \<longleftrightarrow> x0 \<in> set ps \<and> list_all (\<lambda>x. list_all (\<lambda>y. y \<in> set ps) (ksucc J x)) ps\<close>

lemma ksucc_T:
  \<open>jget (jt_pgT J) p l = Some q \<Longrightarrow> (jgo (jt_cgT J) (jt_ns J) i l, q) \<in> set (ksucc J (i, p))\<close>
  using tentries_complete[of \<open>trow (jt_pgT J) p\<close> l q]
  unfolding ksucc_def jget_trow by force

lemma ksucc_N:
  \<open>jget (jt_pgN J) p A = Some q \<Longrightarrow> (jgo (jt_cgN J) (jt_ns J) i A, q) \<in> set (ksucc J (i, p))\<close>
  using tentries_complete[of \<open>trow (jt_pgN J) p\<close> A q]
  unfolding ksucc_def jget_trow by force

lemma drop_as_Cons_sub:
  \<open>drop_as xs ys = y # zs \<Longrightarrow> set ys \<subseteq> A \<Longrightarrow> y \<in> A \<and> set zs \<subseteq> A\<close>
  using set_drop_as[of xs ys] by auto

lemma jctl2_pres:
  assumes ok: \<open>kok J ps x0\<close> and stk: \<open>set stk \<subseteq> set ps\<close>
    and h: \<open>jctl2 J (stk, v) = Some (a, stk', v')\<close>
  shows \<open>set stk' \<subseteq> set ps\<close>
proof -
  have cl: \<open>\<And>x y. x \<in> set ps \<Longrightarrow> y \<in> set (ksucc J x) \<Longrightarrow> y \<in> set ps\<close>
    using ok unfolding kok_def list_all_iff by blast
  from h obtain i p rest where s: \<open>stk = (i, p) # rest\<close>
    by (cases stk) (auto simp: jctl2_def)
  have ip: \<open>(i, p) \<in> set ps\<close> using stk s by simp
  define l where \<open>l = (case v of [] \<Rightarrow> 0 | (_, l) # _ \<Rightarrow> l)\<close>
  define cands where \<open>cands = (case v of [] \<Rightarrow> [] | _ \<Rightarrow> [IShift]) @
    map IReduce (filter (jlicd (jget (jt_lic J) i l)) (jcomps J p))\<close>
  have jeq: \<open>jctl2 J (stk, v) = (case spick (jtarget J stk l) cands of
            None \<Rightarrow> None
          | Some (IShift, q) \<Rightarrow> Some (DShift, (jgo (jt_cgT J) (jt_ns J) i l, q) # stk, tl v)
          | Some (IReduce j, q) \<Rightarrow> (case tlookup (jt_prs J) j of None \<Rightarrow> None | Some (pr, A) \<Rightarrow>
              (case drop_as (snd pr) stk of [] \<Rightarrow> None | (i', _) # _ \<Rightarrow>
                 Some (DReduce pr, (jgo (jt_cgN J) (jt_ns J) i' A, q) # drop_as (snd pr) stk, v))))\<close>
    unfolding jctl2_def s l_def cands_def jcomps_def by (simp add: Let_def)
  from h[unfolded jeq] obtain act q where sp: \<open>spick (jtarget J stk l) cands = Some (act, q)\<close>
    by (auto split: option.splits)
  have tq: \<open>jtarget J stk l act = Some q\<close> using spick_SomeD[OF sp] by simp
  show ?thesis
  proof (cases act)
    case IShift
    then have st: \<open>stk' = (jgo (jt_cgT J) (jt_ns J) i l, q) # stk\<close> using h[unfolded jeq] sp by simp
    have \<open>jget (jt_pgT J) p l = Some q\<close> using tq IShift s by (simp add: jtarget_def)
    then show ?thesis using st stk cl[OF ip ksucc_T] by simp
  next
    case (IReduce j)
    from tq obtain pr A i' p' rest' where prA: \<open>tlookup (jt_prs J) j = Some (pr, A)\<close>
        and d: \<open>drop_as (snd pr) stk = (i', p') # rest'\<close> and g: \<open>jget (jt_pgN J) p' A = Some q\<close>
      unfolding IReduce jtarget_def by (auto split: option.splits list.splits)
    have st: \<open>stk' = (jgo (jt_cgN J) (jt_ns J) i' A, q) # (i', p') # rest'\<close>
      using h[unfolded jeq] sp IReduce prA d by simp
    have sub: \<open>(i', p') \<in> set ps \<and> set rest' \<subseteq> set ps\<close> using drop_as_Cons_sub[OF d stk] .
    show ?thesis using st sub cl[OF _ ksucc_N[OF g]] by auto
  qed
qed
theorem xrun_kctl:
  assumes ok: \<open>kok J ps x0\<close>
  shows \<open>xrun_hist (kctl (ktabs_of J ps)) (kfinal (ktabs_of J ps)) fst [] ([kidx ps x0], v, tstk) =
    xrun_hist (jctl2 J) (jfinal2 J) fst [] ([x0], v, tstk)\<close>
proof -
  interpret stack_transfer \<open>kidx ps\<close> \<open>\<lambda>x. x \<in> set ps\<close> \<open>jctl2 J\<close> \<open>jfinal2 J\<close>
      \<open>kctl (ktabs_of J ps)\<close> \<open>kfinal (ktabs_of J ps)\<close>
    by (rule stack_transfer.intro)
      (use kidx_inj in \<open>simp_all add: kctl_eq[unfolded subset_eq] kfinal_eq[unfolded subset_eq]
        jctl2_pres[OF ok, unfolded subset_eq]\<close>)  have \<open>x0 \<in> set ps\<close> using ok unfolding kok_def by simp
  then show ?thesis using stack_xrun_hist_eq[where stk = \<open>[x0]\<close> and dec = fst and v = v and tstk = tstk] by simp
qed

subsection \<open>The code equation\<close>

lemma dparse_via_prod_tables:
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
  shows \<open>dparse G Shn w = xrun_hist (kctl K) (kfinal K) fst [] ([k\<^sub>0], map (kenc K) w, [])\<close>
  unfolding dparse_via_trie_tok_tables[OF static st gt rt ps pg pcs pfs i0 p0 lt jt]
    xrun_kctl[OF ok, symmetric] kt[symmetric] k0[symmetric] kenc_ktabs_of ..

end
