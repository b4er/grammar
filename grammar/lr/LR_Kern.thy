(* Author: Basil Fürer *)

theory LR_Kern
  imports LR_Fuse
begin

section \<open>The kernel of the run on values\<close>

text \<open>The code of the run on values (\<^const>\<open>frun\<close> over \<^const>\<open>actl\<close>) without
  bounds checks. Every table is padded to full width, with one more state and one more
  column whose entries are all empty, and every index into it is clamped to that range:
  the targets of the actions when the table is built, the start state once per parse,
  and the number of a token once per token. A lookup at a clamped index is the checked
  lookup at the original index (\<open>uget_clamp\<close>, \<open>uget2_clamp\<close>), for every index, so
  nothing about the tables has to be shown; the run on the padded tables is the run on
  the original ones under the clamping (\<open>frun_upad\<close>).

  The step is unfolded into the run (\<open>ukrun_code\<close>), with the lookups written as
  \<^const>\<open>IArray.sub'\<close>, so that the target code inlines them: a cell with one action shifts or
  reduces on the spot, without \<^const>\<open>sfind\<close> and the options and pairs of the
  control, and the final test is made only at the end of the input. A cell with several
  actions takes the step of \<open>uactl\<close>. The backend rewrites the parser's code
  equation with \<open>frun_ukrun\<close> and the padded tables are a constant.\<close>

subsection \<open>Padded arrays\<close>

definition clamp :: \<open>integer \<Rightarrow> integer \<Rightarrow> integer\<close> where
  \<open>clamp n k = (if 0 \<le> k \<and> k < n then k else n)\<close>

definition uget :: \<open>'b iarray \<Rightarrow> integer \<Rightarrow> 'b\<close> where
  \<open>uget a i = IArray.sub' (a, i)\<close>

definition utab :: \<open>integer \<Rightarrow> (integer \<Rightarrow> 'b) \<Rightarrow> 'b iarray\<close> where
  \<open>utab n f = IArray.tabulate (n + 1, f)\<close>

lemma uget_utab: \<open>0 \<le> i \<Longrightarrow> i \<le> n \<Longrightarrow> uget (utab n f) i = f i\<close>
proof -
  assume i: \<open>0 \<le> i\<close> \<open>i \<le> n\<close>
  then have \<open>nat_of_integer i < nat_of_integer (n + 1)\<close>
    by (simp add: less_integer.rep_eq less_eq_integer.rep_eq nat_of_integer.rep_eq nat_less_iff)
  moreover have \<open>integer_of_nat (nat_of_integer i) = i\<close> using i(1) by (rule zi_nat_of_integer)
  ultimately show ?thesis by (simp add: uget_def utab_def)
qed

lemma clamp_range: \<open>0 \<le> n \<Longrightarrow> 0 \<le> clamp n k \<and> clamp n k \<le> n\<close>
  by (simp add: clamp_def)

lemma aget_clamp: \<open>IArray.length' a \<le> n \<Longrightarrow> aget a (clamp n k) = aget a k\<close>
  by (auto simp: clamp_def aget_def)

lemma length'_nonneg: \<open>0 \<le> IArray.length' a\<close>
  by (simp add: integer_of_nat_eq_of_nat)

lemma uget_clamp:
  assumes \<open>IArray.length' a \<le> n\<close>
  shows \<open>uget (utab n (\<lambda>i. h (aget a i))) (clamp n k) = h (aget a k)\<close>
proof -
  have \<open>0 \<le> n\<close> using assms length'_nonneg[of a] by linarith
  then show ?thesis using clamp_range[of n k] by (simp add: uget_utab aget_clamp[OF assms])
qed

definition rlen :: \<open>'b iarray option \<Rightarrow> integer\<close> where
  \<open>rlen x = (case x of None \<Rightarrow> 0 | Some r \<Rightarrow> IArray.length' r)\<close>

definition rmax :: \<open>'b iarray option iarray \<Rightarrow> integer\<close> where
  \<open>rmax a = fold (\<lambda>x m. max (rlen x) m) (IArray.list_of a) 0\<close>

lemma fold_max_mono: \<open>z \<le> fold (\<lambda>x m. max (f x) m) xs (z :: integer)\<close>
  by (induction xs arbitrary: z) (auto intro: order_trans[OF max.cobounded2])

lemma fold_max_ge: \<open>x \<in> set xs \<Longrightarrow> f x \<le> fold (\<lambda>x m. max (f x) m) xs (z :: integer)\<close>
proof (induction xs arbitrary: z)
  case (Cons y ys)
  then show ?case
    using fold_max_mono[of \<open>max (f y) z\<close> f ys] by (auto intro: order_trans[OF max.cobounded1])
qed simp

lemma rmax_ge: \<open>aget a i = Some r \<Longrightarrow> IArray.length' r \<le> rmax a\<close>
proof -
  assume h: \<open>aget a i = Some r\<close>
  then have \<open>Some r \<in> set (IArray.list_of a)\<close>
    by (cases a) (auto simp: aget_def less_zi split: if_splits; metis nth_mem)
  from fold_max_ge[OF this, of rlen 0] show ?thesis by (simp add: rmax_def rlen_def)
qed

definition utab2 :: \<open>integer \<Rightarrow> integer \<Rightarrow> ('b \<Rightarrow> 'c) \<Rightarrow> 'b option iarray option iarray \<Rightarrow>
    'c option iarray iarray\<close> where
  \<open>utab2 n m g a = utab n (\<lambda>i. utab m (\<lambda>j. map_option g (aget2 a i j)))\<close>

lemma uget2_clamp:
  assumes \<open>IArray.length' a \<le> n\<close> \<open>rmax a \<le> m\<close>
  shows \<open>uget (uget (utab2 n m g a) (clamp n k)) (clamp m l) = map_option g (aget2 a k l)\<close>
proof -
  have n: \<open>0 \<le> n\<close> using assms(1) length'_nonneg[of a] by linarith
  have \<open>0 \<le> rmax a\<close> using fold_max_mono[of 0 rlen] by (simp add: rmax_def)
  then have m: \<open>0 \<le> m\<close> using assms(2) by linarith
  have row: \<open>aget2 a k (clamp m l) = aget2 a k l\<close>
    using rmax_ge[of a k] assms(2) by (auto simp: aget2_def aget_clamp split: option.split)
  show ?thesis using clamp_range[OF n, of k] clamp_range[OF m, of l]
    by (simp add: utab2_def uget_utab aget2_def aget_clamp[OF assms(1)] row[unfolded aget2_def])
qed

subsection \<open>The padded tables\<close>

datatype ('n, 't) utabs = UTabs
  (ut_A: \<open>('n, 't) aact list option iarray iarray\<close>)
  (ut_E: \<open>('n, 't) aact list option iarray\<close>)
  (ut_N: \<open>integer option iarray iarray\<close>) (ut_pf: \<open>bool option iarray\<close>)
  (ut_n: integer) (ut_w: integer)

definition pn :: \<open>('n, 't) atabs \<Rightarrow> integer\<close> where
  \<open>pn A = max (max (IArray.length' (at_A A)) (IArray.length' (at_E A)))
     (max (IArray.length' (at_N A)) (IArray.length' (at_pf A)))\<close>

definition actf :: \<open>integer \<Rightarrow> integer \<Rightarrow> ('n, 't) aact \<Rightarrow> ('n, 't) aact\<close> where
  \<open>actf n m a = (case a of AShift k \<Rightarrow> AShift (clamp n k) | AReduce pr B \<Rightarrow> AReduce pr (clamp m B))\<close>

definition upad :: \<open>('n, 't) atabs \<Rightarrow> ('n, 't) utabs\<close> where
  \<open>upad A = (let n = pn A; w = rmax (at_A A); m = rmax (at_N A) in
     UTabs (utab2 n w (map (actf n m)) (at_A A))
       (utab n (\<lambda>i. map_option (map (actf n m)) (aget (at_E A) i)))
       (utab2 n m (clamp n) (at_N A)) (utab n (\<lambda>i. aget (at_pf A) i)) n w)\<close>

lemma ut_n_upad: \<open>ut_n (upad A) = pn A\<close> and ut_w_upad: \<open>ut_w (upad A) = rmax (at_A A)\<close>
  by (simp_all add: upad_def Let_def)

lemma pn_ge: \<open>IArray.length' (at_A A) \<le> pn A\<close> \<open>IArray.length' (at_E A) \<le> pn A\<close>
    \<open>IArray.length' (at_N A) \<le> pn A\<close> \<open>IArray.length' (at_pf A) \<le> pn A\<close>
  by (simp_all add: pn_def)

subsection \<open>The step on the padded tables\<close>

definition uatarget :: \<open>('n, 't) utabs \<Rightarrow> integer list \<Rightarrow> ('n, 't) aact \<Rightarrow>
    (('n, 't) dact \<times> integer list) option\<close> where
  \<open>uatarget U kstk a = (case a of
      AShift k' \<Rightarrow> Some (DShift, k' # kstk)
    | AReduce pr B \<Rightarrow> (case drop_as (snd pr) kstk of [] \<Rightarrow> None | k'' # rest \<Rightarrow>
        map_option (\<lambda>k'. (DReduce pr, k' # k'' # rest)) (uget (uget (ut_N U) k'') B)))\<close>

definition uacands :: \<open>('n, 't) utabs \<Rightarrow> integer \<Rightarrow> integer \<Rightarrow> ('n, 't) aact list\<close> where
  \<open>uacands U k l = (case uget (uget (ut_A U) k) l of None \<Rightarrow> [] | Some es \<Rightarrow> es)\<close>

definition uaecands :: \<open>('n, 't) utabs \<Rightarrow> integer \<Rightarrow> ('n, 't) aact list\<close> where
  \<open>uaecands U k = (case uget (ut_E U) k of None \<Rightarrow> [] | Some es \<Rightarrow> es)\<close>

definition uactl :: \<open>('n, 't) utabs \<Rightarrow> integer list \<times> (('t, 'ch, 'm) token_scheme \<times> integer) list \<Rightarrow>
    (('n, 't) dact \<times> integer list \<times> (('t, 'ch, 'm) token_scheme \<times> integer) list) option\<close> where
  \<open>uactl U c = (case c of (kstk, v) \<Rightarrow>
     (case kstk of [] \<Rightarrow> None | k # _ \<Rightarrow>
       (case v of
         [] \<Rightarrow> map_option (\<lambda>(a, stk'). (a, stk', v)) (sfind (uatarget U kstk) (uaecands U k))
       | (_, l) # v' \<Rightarrow> map_option (\<lambda>(a, stk'). (a, stk', case a of DShift \<Rightarrow> v' | DReduce _ \<Rightarrow> v))
           (sfind (uatarget U kstk) (uacands U k l)))))\<close>

definition uafinal :: \<open>('n, 't) utabs \<Rightarrow> integer list \<times> (('t, 'ch, 'm) token_scheme \<times> integer) list \<Rightarrow>
    bool\<close> where
  \<open>uafinal U c \<longleftrightarrow> (case c of (kstk, v) \<Rightarrow> v = [] \<and>
     (case kstk of [] \<Rightarrow> False | k # _ \<Rightarrow> uget (ut_pf U) k = Some True))\<close>

subsection \<open>Correctness\<close>

definition lenc :: \<open>integer \<Rightarrow> 'a \<times> integer \<Rightarrow> 'a \<times> integer\<close> where
  \<open>lenc w x = (fst x, clamp w (snd x))\<close>

context
  fixes A :: \<open>(integer, 't) atabs\<close>
begin

lemma uatarget_eq:
  \<open>uatarget (upad A) (map (clamp (pn A)) kstk) (actf (pn A) (rmax (at_N A)) a) =
    map_option (\<lambda>(d, s). (d, map (clamp (pn A)) s)) (atarget A kstk a)\<close>
proof (cases a)
  case (AReduce pr B)
  show ?thesis
  proof (cases \<open>drop_as (snd pr) kstk\<close>)
    case (Cons k'' rest)
    have \<open>uget (uget (ut_N (upad A)) (clamp (pn A) k'')) (clamp (rmax (at_N A)) B) = map_option (clamp (pn A)) (aget2 (at_N A) k'' B)\<close>
      unfolding upad_def Let_def utabs.sel by (rule uget2_clamp[OF pn_ge(3) order.refl])
    then show ?thesis using Cons unfolding AReduce
      by (simp add: uatarget_def atarget_def actf_def drop_as_map option.map_comp o_def)
  qed (simp add: AReduce uatarget_def atarget_def actf_def drop_as_map)
qed (simp add: uatarget_def atarget_def actf_def)

lemma uacands_eq: \<open>uacands (upad A) (clamp (pn A) k) (clamp (rmax (at_A A)) l) = map (actf (pn A) (rmax (at_N A))) (acands A k l)\<close>
proof -
  have \<open>uget (uget (ut_A (upad A)) (clamp (pn A) k)) (clamp (rmax (at_A A)) l) = map_option (map (actf (pn A) (rmax (at_N A)))) (aget2 (at_A A) k l)\<close>
    unfolding upad_def Let_def utabs.sel by (rule uget2_clamp[OF pn_ge(1) order.refl])
  then show ?thesis by (simp add: uacands_def acands_def split: option.split)
qed

lemma uaecands_eq: \<open>uaecands (upad A) (clamp (pn A) k) = map (actf (pn A) (rmax (at_N A))) (aecands A k)\<close>
proof -
  have \<open>uget (ut_E (upad A)) (clamp (pn A) k) = map_option (map (actf (pn A) (rmax (at_N A)))) (aget (at_E A) k)\<close>
    unfolding upad_def Let_def utabs.sel by (rule uget_clamp[OF pn_ge(2)])
  then show ?thesis by (simp add: uaecands_def aecands_def split: option.split)
qed

lemma usfind_eq:
  \<open>sfind (uatarget (upad A) (map (clamp (pn A)) kstk)) (map (actf (pn A) (rmax (at_N A))) xs) =
    map_option (\<lambda>(d, s). (d, map (clamp (pn A)) s)) (sfind (atarget A kstk) xs)\<close>
  unfolding sfind_map o_def uatarget_eq sfind_map_option ..

theorem uactl_eq:
  \<open>uactl (upad A) (map (clamp (pn A)) kstk, map (lenc (rmax (at_A A))) v) =
    map_option (\<lambda>(a, stk', v'). (a, map (clamp (pn A)) stk', map (lenc (rmax (at_A A))) v')) (actl A (kstk, v))\<close>
proof (cases kstk)
  case (Cons k rest)
  have sa: \<open>sfind (uatarget (upad A) (clamp (pn A) k # map (clamp (pn A)) rest)) (map (actf (pn A) (rmax (at_N A))) xs) =
      map_option (\<lambda>(d, s). (d, map (clamp (pn A)) s)) (sfind (atarget A (k # rest)) xs)\<close> for xs
    using usfind_eq[of \<open>k # rest\<close> xs] by simp
  show ?thesis
  proof (cases v)
    case Nil
    show ?thesis unfolding Cons Nil
      by (simp add: uactl_def actl_def uaecands_eq sa option.map_comp o_def split_beta)
  next
    case (Cons x v')
    show ?thesis unfolding \<open>kstk = k # rest\<close> Cons
      by (simp add: uactl_def actl_def lenc_def uacands_eq sa option.map_comp o_def split_beta
          dact.case_distrib[where h = \<open>map (lenc (rmax (at_A A)))\<close>] cong: dact.case_cong)
  qed
qed (simp add: uactl_def actl_def)

lemma uafinal_eq: \<open>uafinal (upad A) (map (clamp (pn A)) kstk, map (lenc (rmax (at_A A))) v) = afinal A (kstk, v)\<close>
proof -
  have \<open>uget (ut_pf (upad A)) (clamp (pn A) k) = aget (at_pf A) k\<close> for k
    unfolding upad_def Let_def utabs.sel using uget_clamp[OF pn_ge(4), where h = id] by simp
  then show ?thesis by (cases kstk) (auto simp: uafinal_def afinal_def)
qed

text \<open>For any value of a tree that the run's node function computes bottom-up
  (\<open>U\<close>, a homomorphism): the fold of the actions, or the fold after the
  translation of a restricted grammar's trees.\<close>

theorem frun_upad_hom:
  assumes ul: \<open>\<And>w. U (Leaf w) = FLeaf w\<close> and un: \<open>\<And>i cs. U (Node i cs) = N i (map U cs)\<close>
  shows \<open>frun (actl A) (afinal A) N fst (stk, v, []) =
    frun (uactl (upad A)) (uafinal (upad A)) N fst (map (clamp (pn A)) stk, map (lenc (rmax (at_A A))) v, [])\<close>
proof -
  have xt: \<open>xtree fst a (map (lenc (rmax (at_A A))) v) tstk = xtree fst a v tstk\<close> for a v tstk
    by (cases a; cases v) (simp_all add: xtree_def lenc_def)
  have \<open>frun (actl A) (afinal A) N fst (stk, v, map U []) =
      map_option U (nrun (actl A) (afinal A) fst (stk, v, []))\<close>
    by (rule frun_map[OF ul un])
  also have \<open>nrun (actl A) (afinal A) fst (stk, v, []) =
      nrun (uactl (upad A)) (uafinal (upad A)) fst (map (clamp (pn A)) stk, map (lenc (rmax (at_A A))) v, [])\<close>
    by (rule nrun_transfer[symmetric]) (simp_all add: uactl_eq uafinal_eq xt)
  also have \<open>map_option U \<dots> =
      frun (uactl (upad A)) (uafinal (upad A)) N fst (map (clamp (pn A)) stk, map (lenc (rmax (at_A A))) v, map U [])\<close>
    by (rule frun_map[OF ul un, symmetric])
  finally show ?thesis by simp
qed

corollary frun_upad:
  assumes N: \<open>\<And>i us. N i us = FNode i (K i us)\<close>
  shows \<open>frun (actl A) (afinal A) N fst (stk, v, []) =
    frun (uactl (upad A)) (uafinal (upad A)) N fst (map (clamp (pn A)) stk, map (lenc (rmax (at_A A))) v, [])\<close>
  by (rule frun_upad_hom[where U = \<open>afold K\<close>]) (simp_all add: N)

end

subsection \<open>The kernel\<close>

definition ukrun :: \<open>(integer, 't) utabs \<Rightarrow>
    (integer \<Rightarrow> ('m, 'ch, 't, 'v) fv list \<Rightarrow> ('m, 'ch, 't, 'v) fv) \<Rightarrow>
    integer list \<Rightarrow> (('t, 'ch, 'm) token_scheme \<times> integer) list \<Rightarrow> ('m, 'ch, 't, 'v) fv list \<Rightarrow>
    ('m, 'ch, 't, 'v) fv option\<close> where
  \<open>ukrun U N stk v us = frun (uactl U) (uafinal U) N fst (stk, v, us)\<close>

lemma ukrun_unfold:
  \<open>ukrun U N stk v us = (case stk of [] \<Rightarrow> None | k # _ \<Rightarrow>
     (case v of
       [] \<Rightarrow> if IArray.sub' (ut_pf U, k) = Some True then fresult us
            else (case sfind (uatarget U stk) (uaecands U k) of None \<Rightarrow> None
              | Some (a, stk') \<Rightarrow> ukrun U N stk' v (ftree fst N a v us))
     | w # v' \<Rightarrow> (case IArray.sub' (IArray.sub' (ut_A U, k), snd w) of
         None \<Rightarrow> None
       | Some cs \<Rightarrow> (case cs of
           [] \<Rightarrow> None
         | c # cs' \<Rightarrow> if List.null cs' then
               (case c of
                 AShift k' \<Rightarrow> ukrun U N (k' # stk) v' (FLeaf (fst w) # us)
               | AReduce pr B \<Rightarrow> (case drop_as (snd pr) stk of [] \<Rightarrow> None
                   | k'' # rest \<Rightarrow> (case IArray.sub' (IArray.sub' (ut_N U, k''), B) of None \<Rightarrow> None
                       | Some k' \<Rightarrow> ukrun U N (k' # k'' # rest) v
                           (N (fst pr) (rev (take_as (snd pr) us)) # drop_as (snd pr) us))))
             else (case sfind (uatarget U stk) cs of None \<Rightarrow> None
               | Some (a, stk') \<Rightarrow> ukrun U N stk' (case a of DShift \<Rightarrow> v' | DReduce _ \<Rightarrow> v)
                   (ftree fst N a v us))))))\<close>
  unfolding ukrun_def
  apply (subst frun.simps)
  apply (auto simp: uactl_def uafinal_def uacands_def uaecands_def uatarget_def ftree_def uget_def
      split: list.split option.split aact.split dact.split prod.split)
  done

text \<open>A reduction without walking the right-hand side: a right-hand side of
  length 0, 1 or 2 pops both stacks by pattern and lists the children in order;
  longer ones take the generic path.\<close>

lemma ukrun_red:
  \<open>(case drop_as xs stk of [] \<Rightarrow> None
     | k'' # rest \<Rightarrow> (case IArray.sub' (IArray.sub' (ut_N U, k''), B) of None \<Rightarrow> None
         | Some k' \<Rightarrow> ukrun U N (k' # k'' # rest) v (N l (rev (take_as xs us)) # drop_as xs us))) =
   (case xs of
      [] \<Rightarrow> (case stk of [] \<Rightarrow> None
        | k'' # rest \<Rightarrow> (case IArray.sub' (IArray.sub' (ut_N U, k''), B) of None \<Rightarrow> None
            | Some k' \<Rightarrow> ukrun U N (k' # k'' # rest) v (N l [] # us)))
    | [_] \<Rightarrow> (case stk of _ # k'' # rest \<Rightarrow>
          (case IArray.sub' (IArray.sub' (ut_N U, k''), B) of None \<Rightarrow> None
           | Some k' \<Rightarrow> (case us of
               u # us' \<Rightarrow> ukrun U N (k' # k'' # rest) v (N l [u] # us')
             | [] \<Rightarrow> ukrun U N (k' # k'' # rest) v [N l []]))
        | _ \<Rightarrow> None)
    | [_, _] \<Rightarrow> (case stk of _ # _ # k'' # rest \<Rightarrow>
          (case IArray.sub' (IArray.sub' (ut_N U, k''), B) of None \<Rightarrow> None
           | Some k' \<Rightarrow> (case us of
               u2 # u1 # us' \<Rightarrow> ukrun U N (k' # k'' # rest) v (N l [u1, u2] # us')
             | _ \<Rightarrow> ukrun U N (k' # k'' # rest) v (N l (rev (take_as xs us)) # drop_as xs us)))
        | _ \<Rightarrow> None)
    | _ \<Rightarrow> (case drop_as xs stk of [] \<Rightarrow> None
        | k'' # rest \<Rightarrow> (case IArray.sub' (IArray.sub' (ut_N U, k''), B) of None \<Rightarrow> None
            | Some k' \<Rightarrow> ukrun U N (k' # k'' # rest) v (N l (rev (take_as xs us)) # drop_as xs us))))\<close>
  by (auto simp: take_as_eq drop_as_eq split: list.split option.split)

lemma ukrun_code [code]:
  \<open>ukrun U N stk v us = (case stk of [] \<Rightarrow> None | k # _ \<Rightarrow>
     (case v of
       [] \<Rightarrow> if IArray.sub' (ut_pf U, k) = Some True then fresult us
            else (case sfind (uatarget U stk) (uaecands U k) of None \<Rightarrow> None
              | Some (a, stk') \<Rightarrow> ukrun U N stk' v (ftree fst N a v us))
     | w # v' \<Rightarrow> (case IArray.sub' (IArray.sub' (ut_A U, k), snd w) of
         None \<Rightarrow> None
       | Some cs \<Rightarrow> (case cs of
           [] \<Rightarrow> None
         | c # cs' \<Rightarrow> if List.null cs' then
               (case c of
                 AShift k' \<Rightarrow> ukrun U N (k' # stk) v' (FLeaf (fst w) # us)
               | AReduce pr B \<Rightarrow> (case snd pr of
                    [] \<Rightarrow> (case stk of [] \<Rightarrow> None
                      | k'' # rest \<Rightarrow> (case IArray.sub' (IArray.sub' (ut_N U, k''), B) of None \<Rightarrow> None
                          | Some k' \<Rightarrow> ukrun U N (k' # k'' # rest) v (N (fst pr) [] # us)))
                  | [_] \<Rightarrow> (case stk of _ # k'' # rest \<Rightarrow>
                        (case IArray.sub' (IArray.sub' (ut_N U, k''), B) of None \<Rightarrow> None
                         | Some k' \<Rightarrow> (case us of
                             u # us' \<Rightarrow> ukrun U N (k' # k'' # rest) v (N (fst pr) [u] # us')
                           | [] \<Rightarrow> ukrun U N (k' # k'' # rest) v [N (fst pr) []]))
                      | _ \<Rightarrow> None)
                  | [_, _] \<Rightarrow> (case stk of _ # _ # k'' # rest \<Rightarrow>
                        (case IArray.sub' (IArray.sub' (ut_N U, k''), B) of None \<Rightarrow> None
                         | Some k' \<Rightarrow> (case us of
                             u2 # u1 # us' \<Rightarrow> ukrun U N (k' # k'' # rest) v (N (fst pr) [u1, u2] # us')
                           | _ \<Rightarrow> ukrun U N (k' # k'' # rest) v
                               (N (fst pr) (rev (take_as (snd pr) us)) # drop_as (snd pr) us)))
                      | _ \<Rightarrow> None)
                  | _ \<Rightarrow> (case drop_as (snd pr) stk of [] \<Rightarrow> None
                      | k'' # rest \<Rightarrow> (case IArray.sub' (IArray.sub' (ut_N U, k''), B) of None \<Rightarrow> None
                          | Some k' \<Rightarrow> ukrun U N (k' # k'' # rest) v
                              (N (fst pr) (rev (take_as (snd pr) us)) # drop_as (snd pr) us)))))
             else (case sfind (uatarget U stk) cs of None \<Rightarrow> None
               | Some (a, stk') \<Rightarrow> ukrun U N stk' (case a of DShift \<Rightarrow> v' | DReduce _ \<Rightarrow> v)
                   (ftree fst N a v us))))))\<close>
  unfolding ukrun_red[symmetric] by (rule ukrun_unfold)

text \<open>The rewrite of the parser's code equation.\<close>

theorem frun_ukrun_hom:
  assumes ul: \<open>\<And>w. U (Leaf w) = FLeaf w\<close> and un: \<open>\<And>i cs. U (Node i cs) = N i (map U cs)\<close>
  shows \<open>frun (actl A) (afinal A) N fst ([k0], map (atenc g) w, []) =
    ukrun (upad A) N [clamp (ut_n (upad A)) k0] (map (atenc (\<lambda>t. clamp (ut_w (upad A)) (g t))) w) []\<close>
proof -
  have e: \<open>map (lenc (rmax (at_A A))) (map (atenc g) w) = map (atenc (\<lambda>t. clamp (rmax (at_A A)) (g t))) w\<close>
    by (induction w) (simp_all add: lenc_def atenc_def)
  show ?thesis
    unfolding frun_upad_hom[OF ul un] ukrun_def ut_n_upad ut_w_upad e list.map(1,2) ..
qed

corollary frun_ukrun:
  assumes N: \<open>\<And>i us. N i us = FNode i (K i us)\<close>
  shows \<open>frun (actl A) (afinal A) N fst ([k0], map (atenc g) w, []) =
    ukrun (upad A) N [clamp (ut_n (upad A)) k0] (map (atenc (\<lambda>t. clamp (ut_w (upad A)) (g t))) w) []\<close>
  by (rule frun_ukrun_hom[where U = \<open>afold K\<close>]) (simp_all add: N)

end
