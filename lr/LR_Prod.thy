theory LR_Prod
  imports LR_Tok
begin

section \<open>Candidate tables\<close>

text \<open>The trie step filters the completed productions of a state by its
  lookahead cell at every step. Here the filtered lists are computed once, per
  state and lookahead, and the driver reads its reduce candidates off that
  table.\<close>

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

subsection \<open>The candidate tables and their step\<close>

datatype ('n, 't) ktabs = KTabs
  (kt_lal: \<open>('t \<times> nat) list\<close>) (kt_miss: nat)
  (kt_T: \<open>nat ntab ntab\<close>) (kt_N: \<open>nat ntab ntab\<close>) (kt_C: \<open>nat list ntab ntab\<close>)
  (kt_prs: \<open>(('n \<times> ('n, 't) rhs) \<times> nat) ntab\<close>) (kt_pf: \<open>bool ntab\<close>)

definition jcomps :: \<open>('n, 't) jtabs \<Rightarrow> nat \<Rightarrow> nat list\<close> where
  \<open>jcomps J i = (case tlookup (jt_pc J) i of None \<Rightarrow> [] | Some cs \<Rightarrow> cs)\<close>

definition ktabs_of :: \<open>('n, 't) jtabs \<Rightarrow> ('n, 't) ktabs\<close> where
  \<open>ktabs_of J = KTabs (jt_lal J) (jt_miss J) (jt_gT J) (jt_gN J)
     (tab_mapk (\<lambda>i lics. Some (tab_mapk
        (\<lambda>l t. Some (filter (\<lambda>j. tlookup t j \<noteq> None) (jcomps J i))) lics)) (jt_lic J))
     (jt_prs J) (jt_pf J)\<close>

text \<open>The input token with its number, as \<^const>\<open>jenc\<close>.\<close>

definition kenc :: \<open>('n, 't) ktabs \<Rightarrow> ('t, 'ch, 'm) token_scheme \<Rightarrow>
    ('t, 'ch, 'm) token_scheme \<times> nat\<close> where
  \<open>kenc K x = (x, case map_of (kt_lal K) (tok x) of Some l \<Rightarrow> l | None \<Rightarrow> kt_miss K)\<close>

lemma kenc_ktabs_of: \<open>kenc (ktabs_of J) = jenc J\<close>
  by (simp add: fun_eq_iff kenc_def jenc_def jla_def ktabs_of_def split: option.split)

definition kcands :: \<open>('n, 't) ktabs \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat list\<close> where
  \<open>kcands K k l = (case jget (kt_C K) k l of None \<Rightarrow> [] | Some cs \<Rightarrow> cs)\<close>

definition ktarget :: \<open>('n, 't) ktabs \<Rightarrow> nat list \<Rightarrow> nat \<Rightarrow> iact \<Rightarrow>
    (('n, 't) dact \<times> nat list) option\<close> where
  \<open>ktarget K kstk l act = (case act of
      IShift \<Rightarrow> (case kstk of [] \<Rightarrow> None
        | k # _ \<Rightarrow> map_option (\<lambda>k'. (DShift, k' # kstk)) (jget (kt_T K) k l))
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

definition kfinal :: \<open>('n, 't) ktabs \<Rightarrow> nat list \<times> (('t, 'ch, 'm) token_scheme \<times> nat) list \<Rightarrow>
    bool\<close> where
  \<open>kfinal K c \<longleftrightarrow> (case c of (kstk, v) \<Rightarrow> v = [] \<and>
     (case kstk of [] \<Rightarrow> False | k # _ \<Rightarrow> tlookup (kt_pf K) k = Some True))\<close>

subsection \<open>Correctness of the step on candidate tables\<close>

lemma spick_map:
  assumes \<open>\<And>a. a \<in> set xs \<Longrightarrow> g a = map_option (h a) (f a)\<close>
  shows \<open>spick g xs = map_option (\<lambda>(a, b). (a, h a b)) (spick f xs)\<close>
  using assms by (induction xs) (auto split: option.splits)

lemma jlicd_simps: \<open>jlicd None = (\<lambda>_. False)\<close> \<open>jlicd (Some t) = (\<lambda>j. tlookup t j \<noteq> None)\<close>
  by (simp_all add: fun_eq_iff jlicd_def)

lemma kt_rows:
  \<open>kt_T (ktabs_of J) = jt_gT J\<close> \<open>kt_N (ktabs_of J) = jt_gN J\<close>
  \<open>kt_prs (ktabs_of J) = jt_prs J\<close> \<open>kt_pf (ktabs_of J) = jt_pf J\<close>
  by (simp_all add: ktabs_of_def)

lemma kcands_row:
  \<open>kcands (ktabs_of J) i l = filter (jlicd (jget (jt_lic J) i l)) (jcomps J i)\<close>
proof -
  have row: \<open>jget (kt_C (ktabs_of J)) i l =
      Option.bind (jget (jt_lic J) i l) (\<lambda>t. Some (filter (\<lambda>j. tlookup t j \<noteq> None) (jcomps J i)))\<close>
    by (simp add: ktabs_of_def jget_def tlookup_tab_mapk split: option.splits)
  show ?thesis by (cases \<open>jget (jt_lic J) i l\<close>) (simp_all add: kcands_def row jlicd_simps)
qed

lemma kfinal_eq: \<open>kfinal (ktabs_of J) (stk, v) = jfinal2 J (stk, v)\<close>
  by (cases stk) (auto simp: kfinal_def jfinal2_def kt_rows)

lemma ktarget_eq:
  assumes s: \<open>stk = i # rest\<close>
  shows \<open>ktarget (ktabs_of J) stk l act = map_option (\<lambda>q. case act of
      IShift \<Rightarrow> (DShift, q # stk)
    | IReduce j \<Rightarrow> (case tlookup (jt_prs J) j of None \<Rightarrow> (DShift, []) | Some (pr, A) \<Rightarrow>
        (DReduce pr, q # drop_as (snd pr) stk)))
    (jtarget J stk l act)\<close>
proof (cases act)
  case IShift
  show ?thesis unfolding IShift s by (simp add: ktarget_def jtarget_def kt_rows)
next
  case (IReduce j)
  show ?thesis
  proof (cases \<open>tlookup (jt_prs J) j\<close>)
    case (Some prA)
    obtain pr A where prA: \<open>prA = (pr, A)\<close> by (cases prA)
    show ?thesis
    proof (cases \<open>drop_as (snd pr) stk\<close>)
      case (Cons i' rest')
      show ?thesis using Some Cons unfolding IReduce prA
        by (simp add: ktarget_def jtarget_def kt_rows option.map_comp o_def)
    qed (use Some prA IReduce in \<open>simp add: ktarget_def jtarget_def kt_rows\<close>)
  qed (use IReduce in \<open>simp add: ktarget_def jtarget_def kt_rows\<close>)
qed

theorem kctl_eq: \<open>kctl (ktabs_of J) (stk, v) = jctl2 J (stk, v)\<close>
proof (cases stk)
  case (Cons i rest)
  define l where \<open>l = (case v of [] \<Rightarrow> 0 | (_, l) # _ \<Rightarrow> l)\<close>
  define cands where \<open>cands = (case v of [] \<Rightarrow> [] | _ \<Rightarrow> [IShift]) @
    map IReduce (filter (jlicd (jget (jt_lic J) i l)) (jcomps J i))\<close>
  define h where \<open>h = (\<lambda>act q. case act of
      IShift \<Rightarrow> (DShift, q # stk)
    | IReduce j \<Rightarrow> (case tlookup (jt_prs J) j of None \<Rightarrow> (DShift, []) | Some (pr, A) \<Rightarrow>
        (DReduce pr, q # drop_as (snd pr) stk)))\<close>
  have sp: \<open>spick (ktarget (ktabs_of J) stk l) cands =
      map_option (\<lambda>(a, b). (a, h a b)) (spick (jtarget J stk l) cands)\<close>
    by (rule spick_map) (use ktarget_eq[OF Cons] in \<open>simp add: h_def\<close>)
  have k: \<open>kctl (ktabs_of J) (stk, v) =
      (case spick (ktarget (ktabs_of J) stk l) cands of None \<Rightarrow> None
        | Some (_, a, stk') \<Rightarrow> Some (a, stk', (case a of DShift \<Rightarrow> tl v | DReduce _ \<Rightarrow> v)))\<close>
    unfolding kctl_def Cons l_def cands_def by (simp add: Let_def kcands_row)
  have j: \<open>jctl2 J (stk, v) = (case spick (jtarget J stk l) cands of
            None \<Rightarrow> None
          | Some (IShift, q) \<Rightarrow> Some (DShift, q # stk, tl v)
          | Some (IReduce j, q) \<Rightarrow> (case tlookup (jt_prs J) j of None \<Rightarrow> None | Some (pr, A) \<Rightarrow>
              Some (DReduce pr, q # drop_as (snd pr) stk, v)))\<close>
    unfolding jctl2_def Cons l_def cands_def jcomps_def by (simp add: Let_def)
  show ?thesis
  proof (cases \<open>spick (jtarget J stk l) cands\<close>)
    case (Some aq)
    obtain act q where aq: \<open>aq = (act, q)\<close> by (cases aq)
    have tq: \<open>jtarget J stk l act = Some q\<close> using spick_SomeD[OF Some[unfolded aq]] by simp
    show ?thesis
    proof (cases act)
      case (IReduce j)
      from tq obtain pr A where prA: \<open>tlookup (jt_prs J) j = Some (pr, A)\<close>
        unfolding IReduce jtarget_def by (auto split: option.splits list.splits)
      show ?thesis unfolding k j sp Some aq IReduce using prA by (simp add: h_def)
    qed (simp add: k j sp Some aq h_def)
  qed (simp add: k j sp)
qed (simp add: kctl_def jctl2_def)

lemma kctl_eq_fun: \<open>kctl (ktabs_of J) = jctl2 J\<close>
  by (rule ext) (case_tac x, simp only: kctl_eq)

lemma kfinal_eq_fun: \<open>kfinal (ktabs_of J) = jfinal2 J\<close>
  by (rule ext) (case_tac x, simp only: kfinal_eq)

theorem xrun_kctl:
  \<open>xrun_hist (kctl (ktabs_of J)) (kfinal (ktabs_of J)) fst seen (stk, v, tstk) =
    xrun_hist (jctl2 J) (jfinal2 J) fst seen (stk, v, tstk)\<close>
  unfolding kctl_eq_fun kfinal_eq_fun ..

subsection \<open>The code equation\<close>

lemma dparse_via_prod_tables:
  assumes static: \<open>sstatic G Shn\<close>
    and st: \<open>pr0_states G Shn = sts\<close> and gt: \<open>pgtab G sts = gtab\<close>
    and rt: \<open>red_buckets G Shn (length sts) = redtab\<close>
    and pcs: \<open>pcomps G sts = pc\<close> and pfs: \<open>pfins Shn sts = pf\<close>
    and i0: \<open>st_find sts (lr0_start G Shn) = i\<^sub>0\<close>
    and lt: \<open>mk_ltabs gtab sts redtab pc pf = L\<close>
    and jt: \<open>jtabs_of L = J\<close>
    and kt: \<open>ktabs_of J = K\<close>
  shows \<open>dparse G Shn w = xrun_hist (kctl K) (kfinal K) fst [] ([i\<^sub>0], map (kenc K) w, [])\<close>
  unfolding dparse_via_trie_tok_tables[OF static st gt rt pcs pfs i0 lt jt]
    xrun_kctl[symmetric] kt[symmetric] kenc_ktabs_of ..

end
