theory LR_Plain
  imports LR_Loop
begin

section \<open>A plain action table\<close>

text \<open>The step on candidate tables (\<^const>\<open>kctl\<close>) tries the shift and then
  the reduce candidates of the lookahead, which takes a lookup in the shift
  table, one in the table of candidates, and one in the table of productions
  per candidate. Here one table gives per state and lookahead the actions to try: the
  shift with its target if there is one (the step takes it before any
  reduce), otherwise the reduces, each with its production and the number of
  its left-hand side. A second table gives the reduces at the end of the
  input, where there is no shift. The step on these tables equals the step on
  candidate tables on every stack, so the run is the same.\<close>

datatype ('n, 't) pact = PShift nat | PReduce \<open>'n \<times> ('n, 't) rhs\<close> nat

datatype ('n, 't) ptabs = PTabs
  (pt_lal: \<open>('t \<times> nat) list\<close>) (pt_miss: nat)
  (pt_A: \<open>('n, 't) pact list ntab ntab\<close>) (pt_E: \<open>('n, 't) pact list ntab\<close>)
  (pt_N: \<open>nat ntab ntab\<close>) (pt_pf: \<open>bool ntab\<close>)

subsection \<open>The tables\<close>

definition kred :: \<open>('n, 't) ktabs \<Rightarrow> nat \<Rightarrow> ('n, 't) pact list\<close> where
  \<open>kred K j = (case tlookup (kt_prs K) j of None \<Rightarrow> [] | Some (pr, A) \<Rightarrow> [PReduce pr A])\<close>

definition kreds :: \<open>('n, 't) ktabs \<Rightarrow> nat list \<Rightarrow> ('n, 't) pact list\<close> where
  \<open>kreds K js = concat (map (kred K) js)\<close>

definition pent :: \<open>('n, 't) ktabs \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> ('n, 't) pact list\<close> where
  \<open>pent K k l = (case jget (kt_T K) k l of
     Some k' \<Rightarrow> [PShift k'] | None \<Rightarrow> kreds K (kcands K k l))\<close>

definition tkeys :: \<open>'a ntab \<Rightarrow> nat list\<close> where
  \<open>tkeys t = map fst (tentries t)\<close>

definition ptabs_of :: \<open>('n, 't) ktabs \<Rightarrow> ('n, 't) ptabs\<close> where
  \<open>ptabs_of K = PTabs (kt_lal K) (kt_miss K)
     (tab_of_assoc (map (\<lambda>k. (k, tab_of_assoc (map (\<lambda>l. (l, pent K k l))
         (remdups (tkeys (trow (kt_T K) k) @ tkeys (trow (kt_C K) k))))))
       (remdups (tkeys (kt_T K) @ tkeys (kt_C K)))))
     (tab_of_assoc (map (\<lambda>k. (k, kreds K (kcands K k 0))) (tkeys (kt_C K))))
     (kt_N K) (kt_pf K)\<close>

subsection \<open>The step\<close>

fun sfind :: \<open>('a \<Rightarrow> 'b option) \<Rightarrow> 'a list \<Rightarrow> 'b option\<close> where
  \<open>sfind f [] = None\<close>
| \<open>sfind f (a # as) = (case f a of Some b \<Rightarrow> Some b | None \<Rightarrow> sfind f as)\<close>

definition pcands :: \<open>('n, 't) ptabs \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> ('n, 't) pact list\<close> where
  \<open>pcands P k l = (case jget (pt_A P) k l of None \<Rightarrow> [] | Some es \<Rightarrow> es)\<close>

definition pecands :: \<open>('n, 't) ptabs \<Rightarrow> nat \<Rightarrow> ('n, 't) pact list\<close> where
  \<open>pecands P k = (case tlookup (pt_E P) k of None \<Rightarrow> [] | Some es \<Rightarrow> es)\<close>

definition ptarget :: \<open>('n, 't) ptabs \<Rightarrow> nat list \<Rightarrow> ('n, 't) pact \<Rightarrow> (('n, 't) dact \<times> nat list) option\<close> where
  \<open>ptarget P kstk a = (case a of
      PShift k' \<Rightarrow> Some (DShift, k' # kstk)
    | PReduce pr A \<Rightarrow> (case drop_as (snd pr) kstk of [] \<Rightarrow> None | k'' # rest \<Rightarrow>
        map_option (\<lambda>k'. (DReduce pr, k' # k'' # rest)) (jget (pt_N P) k'' A)))\<close>

definition pctl :: \<open>('n, 't) ptabs \<Rightarrow> nat list \<times> (('t, 'ch, 'm) token_scheme \<times> nat) list \<Rightarrow>
    (('n, 't) dact \<times> nat list \<times> (('t, 'ch, 'm) token_scheme \<times> nat) list) option\<close> where
  \<open>pctl P c = (case c of (kstk, v) \<Rightarrow>
     (case kstk of [] \<Rightarrow> None | k # _ \<Rightarrow>
       (case v of
         [] \<Rightarrow> map_option (\<lambda>(a, stk'). (a, stk', v)) (sfind (ptarget P kstk) (pecands P k))
       | (_, l) # v' \<Rightarrow> map_option (\<lambda>(a, stk'). (a, stk', case a of DShift \<Rightarrow> v' | DReduce _ \<Rightarrow> v))
           (sfind (ptarget P kstk) (pcands P k l)))))\<close>

definition pfinal :: \<open>('n, 't) ptabs \<Rightarrow> nat list \<times> (('t, 'ch, 'm) token_scheme \<times> nat) list \<Rightarrow> bool\<close> where
  \<open>pfinal P c \<longleftrightarrow> (case c of (kstk, v) \<Rightarrow> v = [] \<and>
     (case kstk of [] \<Rightarrow> False | k # _ \<Rightarrow> tlookup (pt_pf P) k = Some True))\<close>

text \<open>The number of a token, by a search in the list of terminals. The code
  equation takes any function equal to it: for tokens of a datatype whose
  constructors have no arguments, the \<^theory_text>\<open>parser\<close> command defines one by
  a case distinction, proved equal constructor by constructor.\<close>

definition pnum :: \<open>('n, 't) ptabs \<Rightarrow> 't \<Rightarrow> nat\<close> where
  \<open>pnum P t = (case map_of (pt_lal P) t of Some l \<Rightarrow> l | None \<Rightarrow> pt_miss P)\<close>

definition tenc :: \<open>('t \<Rightarrow> nat) \<Rightarrow> ('t, 'ch, 'm) token_scheme \<Rightarrow> ('t, 'ch, 'm) token_scheme \<times> nat\<close> where
  \<open>tenc f x = (x, f (tok x))\<close>

subsection \<open>Correctness\<close>

lemma sfind_spick: \<open>sfind f xs = map_option snd (spick f xs)\<close>
  by (induction xs) (auto split: option.split)

lemma sfind_map: \<open>sfind f (map g xs) = sfind (f \<circ> g) xs\<close>
  by (induction xs) (auto split: option.split)

lemma sfind_concat: \<open>sfind f (concat (map h xs)) = sfind (\<lambda>x. sfind f (h x)) xs\<close>
proof (induction xs)
  case (Cons x xs)
  have \<open>sfind f (ys @ zs) = (case sfind f ys of Some b \<Rightarrow> Some b | None \<Rightarrow> sfind f zs)\<close> for ys zs
    by (induction ys) (auto split: option.split)
  then show ?case using Cons by (simp split: option.split)
qed simp

lemma sfind_cong: \<open>(\<And>x. x \<in> set xs \<Longrightarrow> f x = g x) \<Longrightarrow> sfind f xs = sfind g xs\<close>
  by (induction xs) (auto split: option.split)

lemma tkeys_complete: \<open>tlookup t n = Some a \<Longrightarrow> n \<in> set (tkeys t)\<close>
  unfolding tkeys_def using tentries_complete by force

lemma map_of_keys: \<open>map_of (map (\<lambda>k. (k, f k)) ks) k = (if k \<in> set ks then Some (f k) else None)\<close>
  by (induction ks) auto

lemma jget_keys:
  assumes \<open>jget t k l = Some a\<close>
  shows \<open>k \<in> set (tkeys t)\<close> \<open>l \<in> set (tkeys (trow t k))\<close>
proof -
  from assms obtain r where \<open>tlookup t k = Some r\<close> unfolding jget_def by (auto split: option.splits)
  then show \<open>k \<in> set (tkeys t)\<close> by (rule tkeys_complete)
  from assms show \<open>l \<in> set (tkeys (trow t k))\<close> unfolding jget_trow by (rule tkeys_complete)
qed

lemma pent_Nil:
  assumes \<open>jget (kt_T K) k l = None\<close> \<open>jget (kt_C K) k l = None\<close>
  shows \<open>pent K k l = []\<close>
  using assms by (simp add: pent_def kcands_def kreds_def)

lemma pcands_ptabs_of: \<open>pcands (ptabs_of K) k l = pent K k l\<close>
proof -
  let ?ks = \<open>remdups (tkeys (kt_T K) @ tkeys (kt_C K))\<close>
  let ?ls = \<open>remdups (tkeys (trow (kt_T K) k) @ tkeys (trow (kt_C K) k))\<close>
  show ?thesis
  proof (cases \<open>k \<in> set ?ks \<and> l \<in> set ?ls\<close>)
    case True
    then show ?thesis
      by (simp add: pcands_def ptabs_of_def jget_def tlookup_tab_of_assoc map_of_keys del: set_remdups)
  next
    case False
    have T: \<open>jget (kt_T K) k l = None\<close> using jget_keys[of \<open>kt_T K\<close> k l] False by fastforce
    have C: \<open>jget (kt_C K) k l = None\<close> using jget_keys[of \<open>kt_C K\<close> k l] False by fastforce
    have \<open>jget (pt_A (ptabs_of K)) k l = None \<or> jget (pt_A (ptabs_of K)) k l = Some []\<close>
      using False pent_Nil[OF T C]
      by (auto simp: ptabs_of_def jget_def tlookup_tab_of_assoc map_of_keys simp del: set_remdups)
    then show ?thesis unfolding pcands_def pent_Nil[OF T C] by auto
  qed
qed

lemma pecands_ptabs_of: \<open>pecands (ptabs_of K) k = kreds K (kcands K k 0)\<close>
proof (cases \<open>k \<in> set (tkeys (kt_C K))\<close>)
  case False
  then have \<open>jget (kt_C K) k 0 = None\<close> using jget_keys[of \<open>kt_C K\<close> k 0] by (cases \<open>jget (kt_C K) k 0\<close>) auto
  then show ?thesis using False
    by (simp add: pecands_def ptabs_of_def tlookup_tab_of_assoc map_of_keys kcands_def kreds_def)
qed (simp add: pecands_def ptabs_of_def tlookup_tab_of_assoc map_of_keys)

lemma ktarget_reduce:
  \<open>ktarget K kstk l (IReduce j) = sfind (ptarget (ptabs_of K) kstk) (kred K j)\<close>
  by (auto simp: ktarget_def ptarget_def kred_def ptabs_of_def split: option.split list.split)

lemma ktarget_reduces:
  \<open>sfind (ktarget K kstk l) (map IReduce js) = sfind (ptarget (ptabs_of K) kstk) (kreds K js)\<close>
  unfolding sfind_map kreds_def sfind_concat by (simp add: o_def ktarget_reduce)

lemma case_dact_same: \<open>(case a of DShift \<Rightarrow> tl [] | DReduce _ \<Rightarrow> []) = []\<close>
  by (cases a) simp_all

theorem pctl_eq: \<open>pctl (ptabs_of K) c = kctl K c\<close>
proof -
  obtain kstk v where c: \<open>c = (kstk, v)\<close> by (cases c)
  show ?thesis
  proof (cases kstk)
    case (Cons k rest)
    have kc: \<open>kctl K (kstk, v) = map_option (\<lambda>(a, stk'). (a, stk', case a of DShift \<Rightarrow> tl v | DReduce _ \<Rightarrow> v))
        (sfind (ktarget K kstk (case v of [] \<Rightarrow> 0 | (_, l) # _ \<Rightarrow> l))
          ((case v of [] \<Rightarrow> [] | _ \<Rightarrow> [IShift]) @ map IReduce (kcands K k (case v of [] \<Rightarrow> 0 | (_, l) # _ \<Rightarrow> l))))\<close>
      unfolding kctl_def Cons sfind_spick by (simp add: Let_def option.map_comp split: option.split prod.split)
    show ?thesis
    proof (cases v)
      case Nil
      show ?thesis unfolding c kc unfolding Cons Nil
        by (simp add: pctl_def pecands_ptabs_of ktarget_reduces case_dact_same)
    next
      case (Cons x v')
      obtain t l where x: \<open>x = (t, l)\<close> by (cases x)
      show ?thesis
      proof (cases \<open>jget (kt_T K) k l\<close>)
        case None
        have \<open>ktarget K kstk l IShift = None\<close> using None \<open>kstk = k # rest\<close> by (simp add: ktarget_def)
        then show ?thesis unfolding c kc unfolding \<open>kstk = k # rest\<close> Cons x
          using None \<open>kstk = k # rest\<close>
          by (simp add: pctl_def pcands_ptabs_of pent_def ktarget_reduces ktarget_def cong: dact.case_cong)
      next
        case (Some k')
        then show ?thesis unfolding c kc unfolding \<open>kstk = k # rest\<close> Cons x
          by (simp add: pctl_def pcands_ptabs_of pent_def ptarget_def ktarget_def)
      qed
    qed
  qed (simp add: c pctl_def kctl_def)
qed

lemma pctl_eq_fun: \<open>pctl (ptabs_of K) = kctl K\<close>
  by (rule ext) (rule pctl_eq)

lemma ptabs_of_sel: \<open>pt_lal (ptabs_of K) = kt_lal K\<close> \<open>pt_miss (ptabs_of K) = kt_miss K\<close>
  \<open>pt_N (ptabs_of K) = kt_N K\<close> \<open>pt_pf (ptabs_of K) = kt_pf K\<close>
  unfolding ptabs_of_def ptabs.sel by (rule refl)+

lemma pfinal_eq: \<open>pfinal (ptabs_of K) = kfinal K\<close>
  by (rule ext) (unfold pfinal_def kfinal_def ptabs_of_sel, rule refl)

lemma tenc_eq: \<open>tenc (pnum (ptabs_of K)) = kenc K\<close>
  by (rule ext) (unfold tenc_def pnum_def kenc_def ptabs_of_sel, rule refl)

subsection \<open>The code equation\<close>

lemma dparse_via_plain:
  assumes static: \<open>sstatic G Shn\<close>
    and st: \<open>pr0_states G Shn = sts\<close> and gt: \<open>pgtab G sts = gtab\<close>
    and rt: \<open>red_buckets G Shn (length sts) = redtab\<close>
    and pcs: \<open>pcomps G sts = pc\<close> and pfs: \<open>pfins Shn sts = pf\<close>
    and i0: \<open>st_find sts (lr0_start G Shn) = i\<^sub>0\<close>
    and lt: \<open>mk_ltabs gtab sts redtab pc pf = L\<close>
    and jt: \<open>jtabs_of L = J\<close>
    and kt: \<open>ktabs_of J = K\<close>
    and pt: \<open>ptabs_of K = P\<close> and tn: \<open>pnum P = f\<close>
  shows \<open>dparse G Shn w = brun (pctl P) (pfinal P) fst (None, 1, 1) ([i\<^sub>0], map (tenc f) w, [])\<close>
  unfolding tn[symmetric] pt[symmetric] pctl_eq_fun pfinal_eq tenc_eq
  by (rule dparse_via_prod_loop[OF static st gt rt pcs pfs i0 lt jt kt])

end
