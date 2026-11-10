theory LR_Int
  imports LR_Simple
begin

section \<open>The simple driver on integer indices\<close>

text \<open>With binary naturals, converting a state index to an integer for every
  array access costs about half of a step. The tables are stored with natural
  numbers, which keeps them static data, and converted once into tables with
  integer indices; the driver then runs on a stack of integer indices.\<close>

partial_function (option) zrun_hist ::
  \<open>('k list \<times> ('m, 'ch, 't) tword \<Rightarrow> (('n, 't) dact \<times> 'k list \<times> ('m, 'ch, 't) tword) option) \<Rightarrow>
    ('k list \<times> ('m, 'ch, 't) tword \<Rightarrow> bool) \<Rightarrow> 'k list list \<Rightarrow>
    'k list \<times> ('m, 'ch, 't) tword \<times> ('m, 'ch, 'n, 't) ast list \<Rightarrow> ('m, 'ch, 'n, 't) ast option\<close>
  where
  \<open>zrun_hist ctl fin seen st = (case st of (stk, v, tstk) \<Rightarrow>
     if fin (stk, v) then sresult tstk
     else if stk \<in> set seen then None
     else Option.bind (ctl (stk, v)) (\<lambda>(act, stk', v').
       zrun_hist ctl fin (if act = DShift then [] else stk # seen)
         (stk', v', stree act v tstk)))\<close>

lemmas zrun_hist_simps [code] = zrun_hist.simps

text \<open>\<^const>\<open>zrun_hist\<close> on encoded stacks computes \<^const>\<open>srun_hist\<close>, if the
  steps and final tests agree under an injective encoding of stack entries.\<close>

locale run_transfer =
  fixes enc :: \<open>nat \<Rightarrow> 'k\<close>
    and ctl1 :: \<open>('m, 'ch, 't) sctl_t \<Rightarrow> (('n, 't) dact \<times> ('m, 'ch, 't) sctl_t) option\<close>
    and fin1 :: \<open>('m, 'ch, 't) sctl_t \<Rightarrow> bool\<close>
    and ctl2 :: \<open>'k list \<times> ('m, 'ch, 't) tword \<Rightarrow> (('n, 't) dact \<times> 'k list \<times> ('m, 'ch, 't) tword) option\<close>
    and fin2 :: \<open>'k list \<times> ('m, 'ch, 't) tword \<Rightarrow> bool\<close>
  assumes inj: \<open>inj enc\<close>
    and ctl: \<open>\<And>stk v. ctl2 (map enc stk, v) =
      map_option (\<lambda>(a, stk', v'). (a, map enc stk', v')) (ctl1 (stk, v))\<close>
    and fin: \<open>\<And>stk v. fin2 (map enc stk, v) = fin1 (stk, v)\<close>
begin

lemma mem_map_enc: \<open>map enc stk \<in> map enc ` set seen \<longleftrightarrow> stk \<in> set seen\<close>
  using inj_mapI[OF inj] by (auto simp: inj_image_mem_iff)

lemma s_imp_z:
  assumes h: \<open>srun_hist ctl1 fin1 seen st = Some t\<close>
  shows \<open>zrun_hist ctl2 fin2 (map (map enc) seen) (map enc (fst st), snd st) = Some t\<close>
proof -
  have \<open>ctl1 = ctl1 \<longrightarrow> fin1 = fin1 \<longrightarrow>
      zrun_hist ctl2 fin2 (map (map enc) seen) (map enc (fst st), snd st) = Some t\<close>
  proof (rule srun_hist.raw_induct[OF _ h, where P = \<open>\<lambda>ctl fin seen st t. ctl = ctl1 \<longrightarrow> fin = fin1 \<longrightarrow>
      zrun_hist ctl2 fin2 (map (map enc) seen) (map enc (fst st), snd st) = Some t\<close>], goal_cases)
    case (1 f ctl fin seen st t)
    obtain stk v tstk where st: \<open>st = (stk, v, tstk)\<close> by (cases st)
    show ?case
    proof (intro impI)
      assume c: \<open>ctl = ctl1\<close> and fi: \<open>fin = fin1\<close>
      show \<open>zrun_hist ctl2 fin2 (map (map enc) seen) (map enc (fst st), snd st) = Some t\<close>
      proof (cases \<open>fin1 (stk, v)\<close>)
        case True
        with "1"(2) show ?thesis unfolding st c fi by (subst zrun_hist.simps) (simp add: fin)
      next
        case False
        from False "1"(2) have nk: \<open>stk \<notin> set seen\<close> unfolding st c fi by (auto split: if_splits)
        from False "1"(2) obtain a stk' v' where
            sc: \<open>ctl1 (stk, v) = Some (a, stk', v')\<close>
          and rec: \<open>f ctl fin (if a = DShift then [] else stk # seen) (stk', v', stree a v tstk) = Some t\<close>
          unfolding st c fi by (auto simp: bind_eq_Some_conv split: if_splits)
        from "1"(1)[OF rec] c fi
        have \<open>zrun_hist ctl2 fin2 (map (map enc) (if a = DShift then [] else stk # seen))
            (map enc stk', v', stree a v tstk) = Some t\<close> by simp
        then show ?thesis unfolding st using False nk sc
          by (subst zrun_hist.simps) (cases \<open>a = DShift\<close>; simp add: fin ctl mem_map_enc)
      qed
    qed
  qed
  then show ?thesis by blast
qed

lemma z_imp_s:
  assumes h: \<open>zrun_hist ctl2 fin2 seen2 st2 = Some t\<close>
  shows \<open>seen2 = map (map enc) seen \<Longrightarrow> st2 = (map enc stk, v, tstk) \<Longrightarrow>
    srun_hist ctl1 fin1 seen (stk, v, tstk) = Some t\<close>
proof -
  have \<open>ctl2 = ctl2 \<longrightarrow> fin2 = fin2 \<longrightarrow> (\<forall>seen stk v tstk. seen2 = map (map enc) seen \<longrightarrow>
      st2 = (map enc stk, v, tstk) \<longrightarrow> srun_hist ctl1 fin1 seen (stk, v, tstk) = Some t)\<close>
  proof (rule zrun_hist.raw_induct[OF _ h, where P = \<open>\<lambda>ctl fin seen2 st2 t. ctl = ctl2 \<longrightarrow> fin = fin2 \<longrightarrow>
      (\<forall>seen stk v tstk. seen2 = map (map enc) seen \<longrightarrow>
        st2 = (map enc stk, v, tstk) \<longrightarrow> srun_hist ctl1 fin1 seen (stk, v, tstk) = Some t)\<close>], goal_cases)
    case (1 f ctl fin seen2 st2 t)
    show ?case
    proof (intro impI allI)
      fix seen stk v tstk
      assume c: \<open>ctl = ctl2\<close> and fi: \<open>fin = fin2\<close> and se: \<open>seen2 = map (map enc) seen\<close>
        and st: \<open>st2 = (map enc stk, v, tstk)\<close>
      show \<open>srun_hist ctl1 fin1 seen (stk, v, tstk) = Some t\<close>
      proof (cases \<open>fin1 (stk, v)\<close>)
        case True
        with "1"(2) show ?thesis unfolding st c fi by (subst srun_hist.simps) (simp add: fin)
      next
        case False
        from False "1"(2) have nk: \<open>stk \<notin> set seen\<close>
          unfolding st c fi se by (auto simp: fin mem_map_enc split: if_splits)
        from False "1"(2) obtain a stk2 v' where
            sc: \<open>ctl2 (map enc stk, v) = Some (a, stk2, v')\<close>
          and rec: \<open>f ctl fin (if a = DShift then [] else map enc stk # seen2) (stk2, v', stree a v tstk) = Some t\<close>
          unfolding st c fi by (auto simp: bind_eq_Some_conv fin split: if_splits)
        from sc obtain stk' where sc1: \<open>ctl1 (stk, v) = Some (a, stk', v')\<close> and stk2: \<open>stk2 = map enc stk'\<close>
          unfolding ctl by (auto split: prod.splits)
        have \<open>srun_hist ctl1 fin1 (if a = DShift then [] else stk # seen) (stk', v', stree a v tstk) = Some t\<close>
          using "1"(1)[OF rec] c fi se stk2 by simp
        then show ?thesis using False nk sc1 by (subst srun_hist.simps) simp
      qed
    qed
  qed
  then show \<open>seen2 = map (map enc) seen \<Longrightarrow> st2 = (map enc stk, v, tstk) \<Longrightarrow>
    srun_hist ctl1 fin1 seen (stk, v, tstk) = Some t\<close> by blast
qed

theorem zrun_hist_eq:
  \<open>zrun_hist ctl2 fin2 (map (map enc) seen) (map enc stk, v, tstk) = srun_hist ctl1 fin1 seen (stk, v, tstk)\<close>
proof (cases \<open>srun_hist ctl1 fin1 seen (stk, v, tstk)\<close>)
  case None
  show ?thesis
  proof (cases \<open>zrun_hist ctl2 fin2 (map (map enc) seen) (map enc stk, v, tstk)\<close>)
    case (Some t)
    from z_imp_s[OF Some refl refl] None show ?thesis by simp
  qed (simp add: None)
next
  case (Some t)
  from s_imp_z[OF Some] Some show ?thesis by simp
qed

end

subsection \<open>Integer tables and the integer step\<close>

datatype ('n, 't) ztabs = ZTabs
  (zt_ns: integer)
  (zt_gtT: \<open>('t \<times> integer) list iarray\<close>) (zt_gtN: \<open>(integer \<times> integer) list iarray\<close>)
  (zt_cells: \<open>(integer \<times> 't option) list iarray\<close>) (zt_pc: \<open>integer list iarray\<close>)
  (zt_prs: \<open>('n \<times> ('n, 't) rhs) iarray\<close>) (zt_plen: \<open>nat iarray\<close>) (zt_plhs: \<open>integer iarray\<close>)
  (zt_pf: \<open>bool iarray\<close>)

abbreviation zi :: \<open>nat \<Rightarrow> integer\<close> where \<open>zi \<equiv> integer_of_nat\<close>

fun ztabs_of :: \<open>('n, 't) ltabs \<Rightarrow> ('n, 't) ztabs\<close> where
  \<open>ztabs_of (LTabs ns gT gN cs pc prs pl ph pf) =
     ZTabs (zi ns)
       (IArray (map (map (\<lambda>(a, j). (a, zi j))) gT)) (IArray (map (map (\<lambda>(k, j). (zi k, zi j))) gN))
       (IArray (map (map (\<lambda>(j, t). (zi j, t))) cs)) (IArray (map (map zi) pc))
       (IArray prs) (IArray pl) (IArray (map zi ph)) (IArray pf)\<close>

definition zinext :: \<open>('k \<times> integer) list iarray \<Rightarrow> integer \<Rightarrow> integer \<Rightarrow> 'k \<Rightarrow> integer\<close> where
  \<open>zinext tab n i k = (if i < IArray.length' tab
     then (case map_of (IArray.sub' (tab, i)) k of Some j \<Rightarrow> min j n | None \<Rightarrow> n) else n)\<close>

datatype zact = ZShift | ZReduce integer

definition zlic :: \<open>(integer \<times> 't option) list \<Rightarrow> ('m, 'ch, 't) tword \<Rightarrow> integer \<Rightarrow> bool\<close> where
  \<open>zlic cells v j \<longleftrightarrow> list_ex (\<lambda>(j', t). j' = j \<and>
     (case v of [] \<Rightarrow> t = None | x # _ \<Rightarrow> t = Some (tok x))) cells\<close>

definition zcands :: \<open>integer list \<Rightarrow> (integer \<times> 't option) list \<Rightarrow> ('m, 'ch, 't) tword \<Rightarrow> zact list\<close> where
  \<open>zcands comps cells v = (let reds = map ZReduce (filter (zlic cells v) comps)
     in (case v of [] \<Rightarrow> reds | _ \<Rightarrow> ZShift # reds))\<close>

definition ztarget :: \<open>('n, 't) ztabs \<Rightarrow> integer list \<Rightarrow> ('m, 'ch, 't) tword \<Rightarrow> zact \<Rightarrow>
    integer option\<close> where
  \<open>ztarget T stk v act = (case act of
      ZShift \<Rightarrow> (case v of [] \<Rightarrow> None | x # _ \<Rightarrow>
        let q = zinext (zt_gtT T) (zt_ns T) (hd stk) (tok x) in
        if q < zt_ns T then Some q else None)
    | ZReduce j \<Rightarrow> (case drop (IArray.sub' (zt_plen T, j)) stk of [] \<Rightarrow> None | i' # _ \<Rightarrow>
        let q = zinext (zt_gtN T) (zt_ns T) i' (IArray.sub' (zt_plhs T, j)) in
        if q < zt_ns T then Some q else None))\<close>

definition zctl :: \<open>('n, 't) ztabs \<Rightarrow> integer list \<times> ('m, 'ch, 't) tword \<Rightarrow>
    (('n, 't) dact \<times> integer list \<times> ('m, 'ch, 't) tword) option\<close> where
  \<open>zctl T c = (case c of (stk, v) \<Rightarrow>
     (case stk of [] \<Rightarrow> None | i # _ \<Rightarrow>
       let cells = (if i < IArray.length' (zt_cells T) then IArray.sub' (zt_cells T, i) else []);
           comps = (if i < IArray.length' (zt_pc T) then IArray.sub' (zt_pc T, i) else [])
       in (case spick (ztarget T stk v) (zcands comps cells v) of
            None \<Rightarrow> None
          | Some (ZShift, q) \<Rightarrow> Some (DShift, q # stk, tl v)
          | Some (ZReduce j, q) \<Rightarrow>
              Some (DReduce (IArray.sub' (zt_prs T, j)),
                q # drop (IArray.sub' (zt_plen T, j)) stk, v))))\<close>

definition zfinal :: \<open>('n, 't) ztabs \<Rightarrow> integer list \<times> ('m, 'ch, 't) tword \<Rightarrow> bool\<close> where
  \<open>zfinal T c \<longleftrightarrow> (case c of (stk, v) \<Rightarrow> v = [] \<and>
     (case stk of [] \<Rightarrow> False | i # _ \<Rightarrow> i < IArray.length' (zt_pf T) \<and> IArray.sub' (zt_pf T, i)))\<close>

subsection \<open>Correctness of the integer step\<close>

lemma zi_inj: \<open>inj zi\<close>
  by (metis injI nat_of_integer_integer_of_nat)

lemma zi_eq [simp]: \<open>zi a = zi b \<longleftrightarrow> a = b\<close>
  using zi_inj by (simp add: inj_eq)

lemma zi_less [simp]: \<open>zi a < zi b \<longleftrightarrow> a < b\<close>
  by (simp add: integer_of_nat_eq_of_nat)

lemma zi_min: \<open>min (zi a) (zi b) = zi (min a b)\<close>
  by (simp add: min_def integer_of_nat_eq_of_nat)

lemma sub'_IArray [simp]: \<open>IArray.sub' (IArray xs, zi i) = xs ! i\<close>
  by simp

lemma length'_IArray [simp]: \<open>IArray.length' (IArray xs) = zi (length xs)\<close>
  by simp

lemma map_of_map_snd: \<open>map_of (map (\<lambda>(a, j). (a, f j)) row) a = map_option f (map_of row a)\<close>
  by (induction row) auto

lemma map_of_map_zi:
  \<open>map_of (map (\<lambda>(k, j). (zi k, zi j)) row) (zi k) = map_option zi (map_of row k)\<close>
  by (induction row) auto

lemma zinext_inext:
  assumes \<open>\<And>row. row \<in> set tab \<Longrightarrow> map_of (f row) k' = map_option zi (map_of row k)\<close>
  shows \<open>zinext (IArray (map f tab)) (zi n) (zi i) k' = zi (inext (IArray tab) n i k)\<close>
  using assms[of \<open>tab ! i\<close>]
  by (auto simp: zinext_def inext_def zi_min split: option.splits)

primrec zact_of :: \<open>iact \<Rightarrow> zact\<close> where
  \<open>zact_of IShift = ZShift\<close>
| \<open>zact_of (IReduce j) = ZReduce (zi j)\<close>

lemma zlic_ilic: \<open>zlic (map (\<lambda>(j, t). (zi j, t)) cells) v (zi j) = ilic cells v j\<close>
  unfolding zlic_def ilic_def by (induction cells) auto

lemma zcands_icands:
  \<open>zcands (map zi comps) (map (\<lambda>(j, t). (zi j, t)) cells) v = map zact_of (icands comps cells v)\<close>
proof -
  have \<open>filter (zlic (map (\<lambda>(j, t). (zi j, t)) cells) v) (map zi comps) =
      map zi (filter (ilic cells v) comps)\<close>
    by (simp add: filter_map comp_def zlic_ilic)
  then show ?thesis unfolding zcands_def icands_def Let_def
    by (cases v) (simp_all add: comp_def)
qed

lemma spick_map_option:
  \<open>spick (\<lambda>x. map_option h (f x)) xs = map_option (\<lambda>(a, b). (a, h b)) (spick f xs)\<close>
  by (induction xs) (auto split: option.splits)

text \<open>Every production number offered as a reduce indexes the table of
  left-hand sides.\<close>

fun lwf :: \<open>('n, 't) ltabs \<Rightarrow> bool\<close> where
  \<open>lwf (LTabs ns gT gN cs pc prs pl ph pf) \<longleftrightarrow> (\<forall>row \<in> set pc. \<forall>j \<in> set row. j < length ph)\<close>

lemma ztarget_itarget:
  assumes L: \<open>L = LTabs ns gT gN cs pc prs pl ph pf\<close>
    and ne: \<open>stk \<noteq> []\<close> and j: \<open>\<And>j. a = IReduce j \<Longrightarrow> j < length ph\<close>
  shows \<open>ztarget (ztabs_of L) (map zi stk) v (zact_of a) =
    map_option zi (itarget (itabs_of L) stk v a)\<close>
proof (cases a)
  case IShift
  have hd: \<open>hd (map zi stk) = zi (hd stk)\<close> using ne by (cases stk) auto
  have n: \<open>zinext (IArray (map (map (\<lambda>(a, j). (a, zi j))) gT)) (zi ns) (zi i) k =
      zi (inext (IArray gT) ns i k)\<close> for i k
    by (rule zinext_inext) (rule map_of_map_snd)
  show ?thesis unfolding IShift L ztarget_def itarget_def
    by (cases v) (simp_all add: hd n Let_def)
next
  case (IReduce j')
  have jl: \<open>j' < length ph\<close> using j IReduce by blast
  have n: \<open>zinext (IArray (map (map (\<lambda>(k, j). (zi k, zi j))) gN)) (zi ns) (zi i) (zi k) =
      zi (inext (IArray gN) ns i k)\<close> for i k
    by (rule zinext_inext) (rule map_of_map_zi)
  show ?thesis
  proof (cases \<open>drop (pl ! j') stk\<close>)
    case Nil
    then show ?thesis unfolding IReduce L ztarget_def itarget_def by (simp add: drop_map)
  next
    case (Cons i' rest)
    show ?thesis unfolding IReduce L ztarget_def itarget_def
      using jl Cons by (simp add: drop_map n Let_def)
  qed
qed

theorem zctl_eq:
  assumes wf: \<open>lwf L\<close>
  shows \<open>zctl (ztabs_of L) (map zi stk, v) =
    map_option (\<lambda>(a, stk', v'). (a, map zi stk', v')) (isctl (itabs_of L) (stk, v))\<close>
proof -
  obtain ns gT gN cs pc prs pl ph pf where L: \<open>L = LTabs ns gT gN cs pc prs pl ph pf\<close>
    by (cases L)
  show ?thesis
  proof (cases stk)
    case Nil
    then show ?thesis unfolding zctl_def isctl_def by simp
  next
    case (Cons i rest)
    define cells where \<open>cells = (if i < length cs then cs ! i else [])\<close>
    define comps where \<open>comps = (if i < length pc then pc ! i else [])\<close>
    define I where \<open>I = icands comps cells v\<close>
    have jc: \<open>j < length ph\<close> if \<open>j \<in> set comps\<close> for j
      using that wf unfolding L comps_def by (auto split: if_splits)
    have jI: \<open>j < length ph\<close> if \<open>IReduce j \<in> set I\<close> for j
      using that jc unfolding I_def icands_def Let_def by (cases v) auto
    have tg: \<open>ztarget (ztabs_of L) (map zi stk) v (zact_of a) =
        map_option zi (itarget (itabs_of L) stk v a)\<close> if \<open>a \<in> set I\<close> for a
      by (rule ztarget_itarget[OF L]) (use Cons jI that in auto)
    have sp: \<open>spick (ztarget (ztabs_of L) (map zi stk) v) (map zact_of I) =
        map_option (\<lambda>(a, b). (zact_of a, zi b)) (spick (itarget (itabs_of L) stk v) I)\<close>
    proof -
      have 1: \<open>spick (ztarget (ztabs_of L) (map zi stk) v) (map zact_of I) =
          map_option (\<lambda>(a, b). (zact_of a, b))
            (spick (\<lambda>x. ztarget (ztabs_of L) (map zi stk) v (zact_of x)) I)\<close>
        by (simp add: spick_map comp_def)
      have 2: \<open>spick (\<lambda>x. ztarget (ztabs_of L) (map zi stk) v (zact_of x)) I =
          spick (\<lambda>x. map_option zi (itarget (itabs_of L) stk v x)) I\<close>
        by (rule spick_cong) (rule tg)
      show ?thesis unfolding 1 2 spick_map_option
        by (cases \<open>spick (itarget (itabs_of L) stk v) I\<close>) auto
    qed
    have cz: \<open>(if zi i < IArray.length' (zt_cells (ztabs_of L))
        then IArray.sub' (zt_cells (ztabs_of L), zi i) else []) = map (\<lambda>(j, t). (zi j, t)) cells\<close>
      by (simp add: L cells_def)
    have pz: \<open>(if zi i < IArray.length' (zt_pc (ztabs_of L))
        then IArray.sub' (zt_pc (ztabs_of L), zi i) else []) = map zi comps\<close>
      by (simp add: L comps_def)
    have ci: \<open>(if i < IArray.length (it_cells (itabs_of L))
        then it_cells (itabs_of L) !! i else []) = cells\<close>
      by (simp add: L cells_def)
    have pi: \<open>(if i < IArray.length (it_pc (itabs_of L))
        then it_pc (itabs_of L) !! i else []) = comps\<close>
      by (simp add: L comps_def)
    have zc: \<open>zcands (map zi comps) (map (\<lambda>(j, t). (zi j, t)) cells) v = map zact_of I\<close>
      unfolding I_def by (rule zcands_icands)
    show ?thesis
    proof (cases \<open>spick (itarget (itabs_of L) stk v) I\<close>)
      case None
      show ?thesis unfolding zctl_def isctl_def Cons
        using None sp cz pz ci pi zc I_def Cons by (simp add: Let_def)
    next
      case (Some r)
      obtain a q where r: \<open>r = (a, q)\<close> by (cases r)
      from spick_SomeD[OF Some[unfolded r]] have aI: \<open>a \<in> set I\<close> by blast
      have sp': \<open>spick (ztarget (ztabs_of L) (zi i # map zi rest) v) (map zact_of I) =
          map_option (\<lambda>(a, b). (zact_of a, zi b)) (spick (itarget (itabs_of L) (i # rest) v) I)\<close>
        using sp unfolding Cons by simp
      have fl: \<open>IArray.sub' (zt_plen (ztabs_of L), zi j) = it_plen (itabs_of L) !! j\<close>
        \<open>IArray.sub' (zt_prs (ztabs_of L), zi j) = it_prs (itabs_of L) !! j\<close> for j
        unfolding L by simp_all
      show ?thesis
      proof (cases a)
        case IShift
        have Some': \<open>spick (itarget (itabs_of L) (i # rest) v) I = Some (IShift, q)\<close>
          using Some r IShift unfolding Cons by simp
        show ?thesis unfolding zctl_def isctl_def Cons
          by (simp only: list.map prod.case list.case Let_def cz pz ci pi zc I_def[symmetric] sp'
              Some' option.map option.case zact_of.simps zact.case iact.case)
      next
        case (IReduce j)
        have Some': \<open>spick (itarget (itabs_of L) (i # rest) v) I = Some (IReduce j, q)\<close>
          using Some r IReduce unfolding Cons by simp
        have dm: \<open>map zi (drop (it_plen (itabs_of L) !! j) (i # rest)) =
            drop (it_plen (itabs_of L) !! j) (zi i # map zi rest)\<close>
          using drop_map[of \<open>it_plen (itabs_of L) !! j\<close> zi \<open>i # rest\<close>] by simp
        show ?thesis unfolding zctl_def isctl_def Cons
          by (simp only: list.map prod.case list.case Let_def cz pz ci pi zc I_def[symmetric] sp'
              Some' option.map option.case zact_of.simps zact.case iact.case fl dm[symmetric])
      qed
    qed
  qed
qed

lemma zfinal_eq: \<open>zfinal (ztabs_of L) (map zi stk, v) = isfinal (itabs_of L) (stk, v)\<close>
  by (cases L; cases stk) (auto simp: zfinal_def isfinal_def)

lemma lwf_mk_ltabs: \<open>lwf (mk_ltabs gt sts redtab pc pf)\<close>
proof -
  have \<open>la_tindex (remdups (concat pc)) pr < length (remdups (concat pc))\<close>
    if \<open>row \<in> set pc\<close> \<open>pr \<in> set row\<close> for row pr
    using la_tindex_nth[of pr \<open>remdups (concat pc)\<close>] that by auto
  then show ?thesis unfolding mk_ltabs_def Let_def by auto
qed

theorem zrun_eq:
  assumes \<open>lwf L\<close>
  shows \<open>zrun_hist (zctl (ztabs_of L)) (zfinal (ztabs_of L)) [] ([zi i\<^sub>0], w, []) =
     srun_hist (isctl (itabs_of L)) (isfinal (itabs_of L)) [] ([i\<^sub>0], w, [])\<close>
proof -
  interpret run_transfer zi \<open>isctl (itabs_of L)\<close> \<open>isfinal (itabs_of L)\<close>
    \<open>zctl (ztabs_of L)\<close> \<open>zfinal (ztabs_of L)\<close>
    by (rule run_transfer.intro) (rule zi_inj, rule zctl_eq[OF assms], rule zfinal_eq)
  show ?thesis using zrun_hist_eq[of \<open>[]\<close> \<open>[i\<^sub>0]\<close>] by simp
qed

subsection \<open>Table inlining\<close>

lemma dparse_via_int_tables:
  assumes static: \<open>sstatic G Shn\<close>
    and st: \<open>pr0_states G Shn = sts\<close> and gt: \<open>pgtab G sts = gtab\<close>
    and rt: \<open>red_buckets G Shn (length sts) = redtab\<close>
    and pcs: \<open>pcomps G sts = pc\<close> and pfs: \<open>pfins Shn sts = pf\<close>
    and i0: \<open>st_find sts (lr0_start G Shn) = i\<^sub>0\<close>
    and lt: \<open>mk_ltabs gtab sts redtab pc pf = L\<close>
    and zt: \<open>ztabs_of L = Z\<close>
  shows \<open>dparse G Shn w = zrun_hist (zctl Z) (zfinal Z) [] ([zi i\<^sub>0], w, [])\<close>
proof -
  have \<open>lwf L\<close> using lwf_mk_ltabs lt by blast
  then show ?thesis
    unfolding dparse_via_index_tables[OF static st gt rt pcs pfs i0 lt refl] zt[symmetric]
    by (rule zrun_eq[symmetric])
qed

end
