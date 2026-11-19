(* Author: Basil Fürer *)

theory LR_Arr
  imports LR_Plain
begin

section \<open>The action table as arrays\<close>

text \<open>The binary tries of \<^const>\<open>ptabs_of\<close> need no arithmetic with binary
  naturals, but their keys arrive as natural numbers, and a lookup converts its key
  into a numeral first (\<^const>\<open>tlookup\<close>). Unless the code represents
  \<^typ>\<open>nat\<close> in binary, that conversion costs time linear in the key, and it
  dominates the run. Here the same tables are arrays indexed by \<^typ>\<open>integer\<close>:
  the states, lookaheads and nonterminal numbers of the step are integers, and a
  lookup is an index into an array, under any representation of \<^typ>\<open>nat\<close>.
  The arrays are computed once from the tries. The run on them is the run on the
  tries, so the diagnostics, which read the tries, stay as they are.\<close>

subsection \<open>Tries as arrays\<close>

definition tbound :: \<open>'a ntab \<Rightarrow> nat\<close> where
  \<open>tbound t = Suc (fold max (tkeys t) 0)\<close>

lemma tlookup_tbound: \<open>tbound t \<le> n \<Longrightarrow> tlookup t n = None\<close>
proof (rule ccontr)
  assume b: \<open>tbound t \<le> n\<close> and \<open>tlookup t n \<noteq> None\<close>
  then have \<open>n \<in> set (tkeys t)\<close> using tkeys_complete by (cases \<open>tlookup t n\<close>) auto
  then have \<open>n \<le> fold max (tkeys t) 0\<close> by (rule fold_max_ge)
  with b show False unfolding tbound_def by simp
qed

definition darr :: \<open>('a \<Rightarrow> 'b) \<Rightarrow> 'a ntab \<Rightarrow> 'b option iarray\<close> where
  \<open>darr g t = IArray (map (\<lambda>n. map_option g (tlookup t n)) [0..<tbound t])\<close>

definition aget :: \<open>'b option iarray \<Rightarrow> integer \<Rightarrow> 'b option\<close> where
  \<open>aget a i = (if 0 \<le> i \<and> i < IArray.length' a then IArray.sub' (a, i) else None)\<close>

lemma zi_nonneg [simp]: \<open>0 \<le> zi n\<close>
  by (simp add: integer_of_nat_eq_of_nat)

lemma aget_darr [simp]: \<open>aget (darr g t) (zi n) = map_option g (tlookup t n)\<close>
  by (cases \<open>n < tbound t\<close>) (auto simp: aget_def darr_def tlookup_tbound)

definition darr2 :: \<open>('a \<Rightarrow> 'b) \<Rightarrow> 'a ntab ntab \<Rightarrow> 'b option iarray option iarray\<close> where
  \<open>darr2 g t = darr (darr g) t\<close>

definition aget2 :: \<open>'b option iarray option iarray \<Rightarrow> integer \<Rightarrow> integer \<Rightarrow> 'b option\<close> where
  \<open>aget2 a i j = (case aget a i of None \<Rightarrow> None | Some r \<Rightarrow> aget r j)\<close>

lemma aget2_darr2 [simp]: \<open>aget2 (darr2 g t) (zi i) (zi j) = map_option g (jget t i j)\<close>
  by (simp add: aget2_def darr2_def jget_def split: option.split)

subsection \<open>The tables and the step\<close>

datatype ('n, 't) aact = AShift integer | AReduce \<open>'n \<times> ('n, 't) rhs\<close> integer

primrec aact_of :: \<open>('n, 't) pact \<Rightarrow> ('n, 't) aact\<close> where
  \<open>aact_of (PShift k) = AShift (zi k)\<close>
| \<open>aact_of (PReduce pr A) = AReduce pr (zi A)\<close>

datatype ('n, 't) atabs = ATabs
  (at_lal: \<open>('t \<times> integer) list\<close>) (at_miss: integer)
  (at_A: \<open>('n, 't) aact list option iarray option iarray\<close>)
  (at_E: \<open>('n, 't) aact list option iarray\<close>)
  (at_N: \<open>integer option iarray option iarray\<close>) (at_pf: \<open>bool option iarray\<close>)

definition atabs_of :: \<open>('n, 't) ptabs \<Rightarrow> ('n, 't) atabs\<close> where
  \<open>atabs_of P = ATabs (map (\<lambda>(t, l). (t, zi l)) (pt_lal P)) (zi (pt_miss P))
     (darr2 (map aact_of) (pt_A P)) (darr (map aact_of) (pt_E P))
     (darr2 zi (pt_N P)) (darr id (pt_pf P))\<close>

definition acands :: \<open>('n, 't) atabs \<Rightarrow> integer \<Rightarrow> integer \<Rightarrow> ('n, 't) aact list\<close> where
  \<open>acands A k l = (case aget2 (at_A A) k l of None \<Rightarrow> [] | Some es \<Rightarrow> es)\<close>

definition aecands :: \<open>('n, 't) atabs \<Rightarrow> integer \<Rightarrow> ('n, 't) aact list\<close> where
  \<open>aecands A k = (case aget (at_E A) k of None \<Rightarrow> [] | Some es \<Rightarrow> es)\<close>

definition atarget :: \<open>('n, 't) atabs \<Rightarrow> integer list \<Rightarrow> ('n, 't) aact \<Rightarrow>
    (('n, 't) dact \<times> integer list) option\<close> where
  \<open>atarget A kstk a = (case a of
      AShift k' \<Rightarrow> Some (DShift, k' # kstk)
    | AReduce pr B \<Rightarrow> (case drop_as (snd pr) kstk of [] \<Rightarrow> None | k'' # rest \<Rightarrow>
        map_option (\<lambda>k'. (DReduce pr, k' # k'' # rest)) (aget2 (at_N A) k'' B)))\<close>

definition actl :: \<open>('n, 't) atabs \<Rightarrow> integer list \<times> (('t, 'ch, 'm) token_scheme \<times> integer) list \<Rightarrow>
    (('n, 't) dact \<times> integer list \<times> (('t, 'ch, 'm) token_scheme \<times> integer) list) option\<close> where
  \<open>actl A c = (case c of (kstk, v) \<Rightarrow>
     (case kstk of [] \<Rightarrow> None | k # _ \<Rightarrow>
       (case v of
         [] \<Rightarrow> map_option (\<lambda>(a, stk'). (a, stk', v)) (sfind (atarget A kstk) (aecands A k))
       | (_, l) # v' \<Rightarrow> map_option (\<lambda>(a, stk'). (a, stk', case a of DShift \<Rightarrow> v' | DReduce _ \<Rightarrow> v))
           (sfind (atarget A kstk) (acands A k l)))))\<close>

definition afinal :: \<open>('n, 't) atabs \<Rightarrow> integer list \<times> (('t, 'ch, 'm) token_scheme \<times> integer) list \<Rightarrow>
    bool\<close> where
  \<open>afinal A c \<longleftrightarrow> (case c of (kstk, v) \<Rightarrow> v = [] \<and>
     (case kstk of [] \<Rightarrow> False | k # _ \<Rightarrow> aget (at_pf A) k = Some True))\<close>

text \<open>The number of a token, as \<^const>\<open>pnum\<close>; the code equation takes any
  function equal to it, as there.\<close>

definition anum :: \<open>('n, 't) atabs \<Rightarrow> 't \<Rightarrow> integer\<close> where
  \<open>anum A t = (case map_of (at_lal A) t of Some l \<Rightarrow> l | None \<Rightarrow> at_miss A)\<close>

definition atenc :: \<open>('t \<Rightarrow> integer) \<Rightarrow> ('t, 'ch, 'm) token_scheme \<Rightarrow>
    ('t, 'ch, 'm) token_scheme \<times> integer\<close> where
  \<open>atenc g x = (x, g (tok x))\<close>

subsection \<open>Correctness\<close>

definition zenc :: \<open>'a \<times> nat \<Rightarrow> 'a \<times> integer\<close> where
  \<open>zenc x = (fst x, zi (snd x))\<close>

lemma acands_atabs_of: \<open>acands (atabs_of P) (zi k) (zi l) = map aact_of (pcands P k l)\<close>
  by (simp add: acands_def pcands_def atabs_of_def split: option.split)

lemma aecands_atabs_of: \<open>aecands (atabs_of P) (zi k) = map aact_of (pecands P k)\<close>
  by (simp add: aecands_def pecands_def atabs_of_def split: option.split)

lemma drop_as_map: \<open>drop_as xs (map f ys) = map f (drop_as xs ys)\<close>
  by (simp add: drop_as_eq drop_map)

lemma atarget_atabs_of:
  \<open>atarget (atabs_of P) (map zi kstk) (aact_of a) =
    map_option (\<lambda>(d, s). (d, map zi s)) (ptarget P kstk a)\<close>
proof (cases a)
  case (PReduce pr B)
  show ?thesis
  proof (cases \<open>drop_as (snd pr) kstk\<close>)
    case (Cons k'' rest)
    then show ?thesis unfolding PReduce
      by (simp add: atarget_def ptarget_def drop_as_map atabs_of_def option.map_comp o_def)
  qed (simp add: PReduce atarget_def ptarget_def drop_as_map)
qed (simp add: atarget_def ptarget_def)

lemma sfind_map_option: \<open>sfind (\<lambda>x. map_option h (f x)) xs = map_option h (sfind f xs)\<close>
  by (induction xs) (auto split: option.split)

lemma sfind_atarget:
  \<open>sfind (atarget (atabs_of P) (map zi kstk)) (map aact_of xs) =
    map_option (\<lambda>(d, s). (d, map zi s)) (sfind (ptarget P kstk) xs)\<close>
  unfolding sfind_map o_def atarget_atabs_of sfind_map_option ..

theorem actl_eq:
  \<open>actl (atabs_of P) (map zi kstk, map zenc v) =
    map_option (\<lambda>(a, stk', v'). (a, map zi stk', map zenc v')) (pctl P (kstk, v))\<close>
proof (cases kstk)
  case (Cons k rest)
  have sa: \<open>sfind (atarget (atabs_of P) (zi k # map zi rest)) (map aact_of xs) =
      map_option (\<lambda>(d, s). (d, map zi s)) (sfind (ptarget P (k # rest)) xs)\<close> for xs
    using sfind_atarget[of P \<open>k # rest\<close> xs] by simp
  show ?thesis
  proof (cases v)
    case Nil
    show ?thesis unfolding Cons Nil
      by (simp add: actl_def pctl_def aecands_atabs_of sa option.map_comp o_def split_beta)
  next
    case (Cons x v')
    show ?thesis unfolding \<open>kstk = k # rest\<close> Cons
      by (simp add: actl_def pctl_def zenc_def acands_atabs_of sa option.map_comp o_def split_beta
          dact.case_distrib[where h = \<open>map zenc\<close>] cong: dact.case_cong)
  qed
qed (simp add: actl_def pctl_def)

lemma afinal_eq: \<open>afinal (atabs_of P) (map zi kstk, map zenc v) = pfinal P (kstk, v)\<close>
  by (cases kstk) (auto simp: afinal_def pfinal_def atabs_of_def)

lemma anum_eq: \<open>anum (atabs_of P) t = zi (pnum P t)\<close>
proof -
  have \<open>map_of (map (\<lambda>(t, l). (t, zi l)) xs) t = map_option zi (map_of xs t)\<close> for xs
    by (induction xs) auto
  then show ?thesis by (simp add: anum_def pnum_def atabs_of_def split: option.split)
qed

subsection \<open>The run\<close>

text \<open>A run without a loop check on encoded configurations is the run on the
  original ones, if the steps and the final tests agree under the encoding.\<close>

lemma nrun_transfer:
  fixes E1 :: \<open>'k1 list \<Rightarrow> 'k2 list\<close> and E2 :: \<open>'w1 list \<Rightarrow> 'w2 list\<close>
  assumes ctl: \<open>\<And>stk v. ctl2 (E1 stk, E2 v) =
      map_option (\<lambda>(a, stk', v'). (a, E1 stk', E2 v')) (ctl1 (stk, v))\<close>
    and fin: \<open>\<And>stk v. fin2 (E1 stk, E2 v) = fin1 (stk, v)\<close>
    and xt: \<open>\<And>stk v a r tstk. ctl1 (stk, v) = Some (a, r) \<Longrightarrow>
      xtree dec2 a (E2 v) tstk = xtree dec1 a v tstk\<close>
  shows \<open>nrun ctl2 fin2 dec2 (E1 stk, E2 v, tstk) = nrun ctl1 fin1 dec1 (stk, v, tstk)\<close>
proof -
  have one: \<open>nrun ctl2 fin2 dec2 (E1 (fst st), E2 (fst (snd st)), snd (snd st)) = Some t\<close>
    if h: \<open>nrun ctl1 fin1 dec1 st = Some t\<close> for st t
  proof -
    have \<open>ctl1 = ctl1 \<longrightarrow> fin1 = fin1 \<longrightarrow> dec1 = dec1 \<longrightarrow>
        nrun ctl2 fin2 dec2 (E1 (fst st), E2 (fst (snd st)), snd (snd st)) = Some t\<close>
    proof (rule nrun.raw_induct[OF _ h, where P = \<open>\<lambda>c f d st t. c = ctl1 \<longrightarrow> f = fin1 \<longrightarrow> d = dec1 \<longrightarrow>
        nrun ctl2 fin2 dec2 (E1 (fst st), E2 (fst (snd st)), snd (snd st)) = Some t\<close>], goal_cases)
      case (1 F c f d st t)
      obtain stk v tstk where st: \<open>st = (stk, v, tstk)\<close> by (cases st)
      show ?case
      proof (intro impI)
        assume c: \<open>c = ctl1\<close> and f: \<open>f = fin1\<close> and d: \<open>d = dec1\<close>
        show \<open>nrun ctl2 fin2 dec2 (E1 (fst st), E2 (fst (snd st)), snd (snd st)) = Some t\<close>
        proof (cases \<open>fin1 (stk, v)\<close>)
          case True
          with "1"(2) show ?thesis unfolding st c f by (subst nrun.simps) (simp add: fin)
        next
          case False
          from False "1"(2) obtain a stk' v' where
              sc: \<open>ctl1 (stk, v) = Some (a, stk', v')\<close>
            and rec: \<open>F c f d (stk', v', xtree d a v tstk) = Some t\<close>
            unfolding st c f by (auto simp: bind_eq_Some_conv)
          from "1"(1)[OF rec] c f d
          have \<open>nrun ctl2 fin2 dec2 (E1 stk', E2 v', xtree dec1 a v tstk) = Some t\<close> by simp
          then show ?thesis unfolding st using False sc xt[OF sc]
            by (subst nrun.simps) (simp add: fin ctl)
        qed
      qed
    qed
    then show ?thesis by blast
  qed
  have two: \<open>nrun ctl1 fin1 dec1 (stk, v, tstk) = Some t\<close>
    if h: \<open>nrun ctl2 fin2 dec2 st2 = Some t\<close> and e: \<open>st2 = (E1 stk, E2 v, tstk)\<close> for st2 t stk v tstk
  proof -
    have \<open>ctl2 = ctl2 \<longrightarrow> fin2 = fin2 \<longrightarrow> dec2 = dec2 \<longrightarrow> (\<forall>stk v tstk.
        st2 = (E1 stk, E2 v, tstk) \<longrightarrow> nrun ctl1 fin1 dec1 (stk, v, tstk) = Some t)\<close>
    proof (rule nrun.raw_induct[OF _ h, where P = \<open>\<lambda>c f d st2 t. c = ctl2 \<longrightarrow> f = fin2 \<longrightarrow> d = dec2 \<longrightarrow>
        (\<forall>stk v tstk. st2 = (E1 stk, E2 v, tstk) \<longrightarrow> nrun ctl1 fin1 dec1 (stk, v, tstk) = Some t)\<close>],
        goal_cases)
      case (1 F c f d st2 t)
      show ?case
      proof (intro impI allI)
        fix stk v tstk
        assume c: \<open>c = ctl2\<close> and f: \<open>f = fin2\<close> and d: \<open>d = dec2\<close>
          and st: \<open>st2 = (E1 stk, E2 v, tstk)\<close>
        show \<open>nrun ctl1 fin1 dec1 (stk, v, tstk) = Some t\<close>
        proof (cases \<open>fin1 (stk, v)\<close>)
          case True
          with "1"(2) show ?thesis unfolding st c f by (subst nrun.simps) (simp add: fin)
        next
          case False
          from False "1"(2) obtain a s2 v2 where
              sc: \<open>ctl2 (E1 stk, E2 v) = Some (a, s2, v2)\<close>
            and rec: \<open>F c f d (s2, v2, xtree d a (E2 v) tstk) = Some t\<close>
            unfolding st c f by (auto simp: bind_eq_Some_conv fin)
          from sc obtain stk' v' where sc1: \<open>ctl1 (stk, v) = Some (a, stk', v')\<close>
            and s2: \<open>s2 = E1 stk'\<close> and v2: \<open>v2 = E2 v'\<close>
            unfolding ctl by (auto split: prod.splits)
          have \<open>nrun ctl1 fin1 dec1 (stk', v', xtree dec1 a v tstk) = Some t\<close>
            using "1"(1)[OF rec] c f d s2 v2 xt[OF sc1] by simp
          then show ?thesis using False sc1 by (subst nrun.simps) simp
        qed
      qed
    qed
    then show ?thesis using e by blast
  qed
  show ?thesis
  proof (cases \<open>nrun ctl1 fin1 dec1 (stk, v, tstk)\<close>)
    case None
    then show ?thesis using two[OF _ refl]
      by (cases \<open>nrun ctl2 fin2 dec2 (E1 stk, E2 v, tstk)\<close>) auto
  next
    case (Some t)
    then show ?thesis using one[OF Some] by simp
  qed
qed

lemma actl_keep:
  \<open>actl A (stk, v) = Some (a, stk', v') \<Longrightarrow> a \<noteq> DShift \<Longrightarrow> v' = v\<close>
  by (auto simp: actl_def split: list.splits option.splits prod.splits dact.splits)

lemma pctl_keep:
  \<open>pctl P (stk, v) = Some (a, stk', v') \<Longrightarrow> a \<noteq> DShift \<Longrightarrow> v' = v\<close>
  by (auto simp: pctl_def split: list.splits option.splits prod.splits dact.splits)

text \<open>At the end of the input the tables offer only reduces.\<close>

lemma pctl_shift: \<open>pctl (ptabs_of K) (stk, v) = Some (DShift, r) \<Longrightarrow> v \<noteq> []\<close>
proof
  assume h: \<open>pctl (ptabs_of K) (stk, v) = Some (DShift, r)\<close> and v: \<open>v = []\<close>
  have \<open>ptarget (ptabs_of K) stk a \<noteq> Some (DShift, s)\<close> if \<open>a \<in> set (kred K j)\<close> for a s j
    using that by (auto simp: kred_def ptarget_def split: option.splits list.splits)
  then have \<open>sfind (ptarget (ptabs_of K) stk) (kreds K js) \<noteq> Some (DShift, s)\<close> for js s
    unfolding kreds_def sfind_concat
  proof (induction js)
    case (Cons j js)
    have \<open>sfind (ptarget (ptabs_of K) stk) (kred K j) \<noteq> Some (DShift, s)\<close> for s
      using Cons.prems sfind_spick[of \<open>ptarget (ptabs_of K) stk\<close> \<open>kred K j\<close>]
      by (auto dest!: spick_SomeD)
    then show ?case using Cons by (auto split: option.split)
  qed simp
  with h v show False
    by (auto simp: pctl_def pecands_ptabs_of split: list.splits)
qed

theorem brun_atabs:
  assumes P: \<open>P = ptabs_of K\<close>
  shows \<open>brun (actl (atabs_of P)) (afinal (atabs_of P)) fst (None, 1, 1) (map zi stk, map zenc v, tstk) =
    brun (pctl P) (pfinal P) fst (None, 1, 1) (stk, v, tstk)\<close>
proof -
  have xt: \<open>xtree fst a (map zenc v) tstk = xtree fst a v tstk\<close>
    if \<open>pctl P (stk, v) = Some (a, r)\<close> for stk v a r tstk
    using pctl_shift[of K stk v] that unfolding P
    by (cases a; cases v) (auto simp: xtree_def zenc_def)
  have \<open>brun (actl (atabs_of P)) (afinal (atabs_of P)) fst (None, 1, 1) (map zi stk, map zenc v, tstk) =
      nrun (actl (atabs_of P)) (afinal (atabs_of P)) fst (map zi stk, map zenc v, tstk)\<close>
    by (rule brun_nrun) (rule actl_keep)
  also have \<open>\<dots> = nrun (pctl P) (pfinal P) fst (stk, v, tstk)\<close>
    by (rule nrun_transfer) (simp_all add: actl_eq afinal_eq xt)
  also have \<open>\<dots> = brun (pctl P) (pfinal P) fst (None, 1, 1) (stk, v, tstk)\<close>
    by (rule brun_nrun[symmetric]) (rule pctl_keep)
  finally show ?thesis .
qed

subsection \<open>The code equation\<close>

text \<open>The run of a parser's code equation on the tries, over the run on the
  arrays: the backend rewrites the code equation with it, for the constants
  \<open>A\<close> of the arrays and \<open>g\<close> of the token numbers.\<close>

lemma brun_via_arr:
  assumes pt: \<open>ptabs_of K = P\<close> and at: \<open>atabs_of P = A\<close> and g: \<open>\<And>t. zi (f t) = g t\<close>
  shows \<open>brun (pctl P) (pfinal P) fst (None, 1, 1) ([i\<^sub>0], map (tenc f) w, []) =
    brun (actl A) (afinal A) fst (None, 1, 1) ([zi i\<^sub>0], map (atenc g) w, [])\<close>
proof -
  have e: \<open>map (atenc g) w = map zenc (map (tenc f) w)\<close>
    by (simp add: atenc_def tenc_def zenc_def g[symmetric])
  have b: \<open>brun (actl A) (afinal A) fst (None, 1, 1) ([zi i\<^sub>0], map zenc (map (tenc f) w), []) =
      brun (pctl P) (pfinal P) fst (None, 1, 1) ([i\<^sub>0], map (tenc f) w, [])\<close>
    using brun_atabs[OF pt[symmetric], of \<open>[i\<^sub>0]\<close> \<open>map (tenc f) w\<close> \<open>[]\<close>]
    unfolding at list.map(1,2) .
  show ?thesis unfolding e b ..
qed

text \<open>Without a nullable cycle the code runs with no loop check at all: the two
  runs are equal for every grammar (\<^const>\<open>brun\<close> only stops runs that would
  not terminate), and the backend picks \<^const>\<open>nrun\<close> only when no derivation
  \<open>A \<Rightarrow>\<^sup>+ A\<close> consumes nothing, so no configuration repeats between two shifts.
  The choice decides the termination of the generated code, not its result.\<close>

lemma brun_arr_nrun:
  \<open>brun (actl A) (afinal A) fst (None, 1, 1) st = nrun (actl A) (afinal A) fst st\<close>
  by (rule brun_nrun) (rule actl_keep)

text \<open>For the backend's token numbers by a case distinction with literals.\<close>

lemma zi_lits: \<open>zi 0 = 0\<close> \<open>zi 1 = 1\<close> \<open>zi (Suc 0) = 1\<close> \<open>zi (numeral n) = numeral n\<close>
  by (simp_all add: integer_of_nat_numeral integer_of_nat_eq_of_nat)

lemma anum_via: \<open>atabs_of P = A \<Longrightarrow> zi (pnum P t) = anum A t\<close>
  using anum_eq by metis

end
