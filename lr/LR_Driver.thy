theory LR_Driver
  imports LR
begin

section \<open>A complete deterministic LR driver with set-valued anchors\<close>

text \<open>
  A driver that guesses a single anchor column per reduce is incomplete.
  This driver gives the reduce a \<^emph>\<open>set-valued\<close> goto: the reduced
  nonterminal carries the set of all anchors its completed item admits, and
  each parent item keeps the anchors compatible with some of them.  The
  frames are the item-wise union of all single-anchor GLR frames, acceptance
  is exact, and no anchor is guessed.  Reduce licensing tests the LALR cell's
  width relation against that anchor set, so the remaining nondeterminism is
  the layout/LALR nondeterminism of the grammar.
\<close>

subsection \<open>Closure-cached machine steps\<close>

text \<open>Frame closures are computed once, when the frame is pushed, and
  cached in a stack running in lockstep with the frame stack; the cache
  invariant \<open>cstk_ok\<close> says the two agree.\<close>

definition cstk_ok :: \<open>('n, 't) is_cfg \<Rightarrow> ('n, 't) xitem list list \<Rightarrow>
    ('n, 't) xitem list list \<Rightarrow> bool\<close> where
  \<open>cstk_ok G Xs cstk \<longleftrightarrow> list_all2 (\<lambda>f c. c = xclosure_auto G f) Xs cstk\<close>

lemma cstk_ok_len: \<open>cstk_ok G Xs cstk \<Longrightarrow> length cstk = length Xs\<close>
  unfolding cstk_ok_def by (simp add: list_all2_conv_all_nth)

lemma cstk_ok_nth:
  \<open>cstk_ok G Xs cstk \<Longrightarrow> k < length Xs \<Longrightarrow> cstk ! k = xclosure_auto G (Xs ! k)\<close>
  unfolding cstk_ok_def by (auto simp: list_all2_conv_all_nth)

lemma cstk_ok_hd:
  \<open>cstk_ok G Xs cstk \<Longrightarrow> Xs \<noteq> [] \<Longrightarrow> hd cstk = xclosure_auto G (hd Xs)\<close>
  using cstk_ok_len cstk_ok_nth[of G Xs cstk 0]
  by (metis hd_conv_nth length_0_conv length_greater_0_conv)

lemma cstk_ok_drop:
  \<open>cstk_ok G Xs cstk \<Longrightarrow> cstk_ok G (drop k Xs) (drop k cstk)\<close>
  unfolding cstk_ok_def by (rule list_all2_dropI)

lemma cstk_ok_push:
  \<open>cstk_ok G Xs cstk \<Longrightarrow> cstk_ok G (f # Xs) (xclosure_auto G f # cstk)\<close>
  unfolding cstk_ok_def by simp

text \<open>Liveness of a configuration, and the sentinel-safe table plumbing
  the driver consults (\<^const>\<open>la_next\<close> over the goto table; the reduce
  cells of \<^const>\<open>la_fix\<close> bucketed by state).\<close>

fun tok_of :: \<open>('t \<times> nat) list \<Rightarrow> 't option\<close> where
  \<open>tok_of [] = None\<close>
| \<open>tok_of ((a, _) # _) = Some a\<close>

definition dlive :: \<open>('n, 't) gconfig \<Rightarrow> bool\<close> where
  \<open>dlive gc = (case gc of (Xs, w) \<Rightarrow> Xs \<noteq> [] \<and> live (hd Xs))\<close>


text \<open>Sentinel-safe successor lookup.\<close>

definition dnext :: \<open>(('n, 't) sym \<times> nat) list list \<Rightarrow>
    ('n, 't) citem list list \<Rightarrow> nat \<Rightarrow> ('n, 't) sym \<Rightarrow> nat\<close> where
  \<open>dnext gt sts i X = (if i < length gt then la_next gt sts i X else length sts)\<close>


text \<open>Completed cells, bucketed by state index; the reduce cells of the
  driver are those of \<^const>\<open>la_fix\<close>.\<close>

definition cell_buckets :: \<open>('n, 't) lacell list \<Rightarrow> nat \<Rightarrow> ('n, 't) lacell list list\<close> where
  \<open>cell_buckets L n = (let rt = filter (\<lambda>(i, itm, t, \<tau>).
         snd itm = length (snd (fst itm))) L
     in map (\<lambda>i. filter (\<lambda>(i', itm, t, \<tau>). i' = i) rt) [0..<n])\<close>

definition red_buckets :: \<open>('n, 't) is_cfg \<Rightarrow> 'n \<Rightarrow> nat \<Rightarrow> ('n, 't) lacell list list\<close> where
  \<open>red_buckets G Shn n = cell_buckets (la_fix G Shn) n\<close>


text \<open>Auxiliary reasoning about \<^const>\<open>xclosure_auto\<close> and \<^const>\<open>xgoto\<close>.
  The closure only adds slot items (dot at \<open>0\<close>), so a kernel item found
  in a closure was already in the frame.\<close>

lemma xclosure_auto_kernel:
  assumes \<open>m > 0\<close> and \<open>((pr, m, R)) \<in> set (xclosure_auto G xs)\<close>
  shows \<open>((pr, m, R)) \<in> set xs\<close>
proof -
  have \<open>((pr, m, R)) \<in> set (xslots G xs (xiter G xs (xfuel G xs)))\<close>
    using assms(2) by (simp add: xclosure_auto_def xclosure_def)
  then show ?thesis
    by (cases rule: xslots_memE) (use assms(1) in simp_all)
qed

text \<open>The extraction lemma for the option ccpo: on a chain, whenever the
  pointwise least upper bound is \<^const>\<open>Some\<close>, some chain element is.
  Follows from the shape of \<^text>\<open>fun_lub\<close> and \<^text>\<open>flat_lub\<close>.\<close>

subsection \<open>Set-valued indentation operations\<close>

text \<open>Preimage of an indentation set under a relation: the parent anchors
  compatible with some child anchor in \<open>R\<close>,
  \<open>{i. \<exists>j \<in> R. irel_sat r j i}\<close>. For \<^const>\<open>Gt\<close> and \<^const>\<open>Ge\<close> this is
  the downward closure of the maximum, or everything if \<open>R\<close> is unbounded.\<close>
fun irep_pre :: \<open>irel \<Rightarrow> indrep \<Rightarrow> indrep\<close> where
  \<open>irep_pre Eq R = R\<close>
| \<open>irep_pre Gt (FinRep xs) = FinRep (filter (\<lambda>i. list_ex (\<lambda>x. i < x) xs) [0..<fold max xs 0])\<close>
| \<open>irep_pre Gt (UpRep xs n) = UpRep [] 0\<close>
| \<open>irep_pre Ge (FinRep xs) = FinRep (filter (\<lambda>i. list_ex (\<lambda>x. i \<le> x) xs) [0..<Suc (fold max xs 0)])\<close>
| \<open>irep_pre Ge (UpRep xs n) = UpRep [] 0\<close>
| \<open>irep_pre Any R = (if irep_nonempty R then UpRep [] 0 else FinRep [])\<close>

lemma fold_max_acc: \<open>a \<le> fold max xs (a :: nat)\<close>
proof (induction xs arbitrary: a)
  case (Cons y ys)
  have \<open>a \<le> max y a\<close> by simp
  also have \<open>\<dots> \<le> fold max ys (max y a)\<close> by (rule Cons.IH)
  finally show ?case by simp
qed simp

lemma fold_max_ge: \<open>x \<in> set xs \<Longrightarrow> x \<le> fold max xs (a :: nat)\<close>
proof (induction xs arbitrary: a)
  case (Cons y ys)
  show ?case
  proof (cases \<open>x = y\<close>)
    case True
    have \<open>y \<le> max y a\<close> by simp
    also have \<open>\<dots> \<le> fold max ys (max y a)\<close> by (rule fold_max_acc)
    finally show ?thesis using True by simp
  next
    case False
    with Cons show ?thesis by simp
  qed
qed simp

lemma irep_pre_correct [simp]:
  \<open>irep_set (irep_pre r R) = {i. \<exists>j \<in> irep_set R. irel_sat r j i}\<close>
proof (cases r)
  case Eq then show ?thesis by auto
next
  case Gt
  show ?thesis
  proof (cases R)
    case (FinRep xs)
    have bnd: \<open>\<And>i. \<exists>x\<in>set xs. i < x \<Longrightarrow> i < fold max xs 0\<close>
      using fold_max_ge[of _ xs 0] by (auto intro: less_le_trans)
    then show ?thesis using Gt FinRep by (auto simp: list_ex_iff)
  next
    case (UpRep xs n)
    have \<open>\<exists>xa \<in> set xs \<union> {m. n \<le> m}. x < xa\<close> for x
      by (rule bexI[of _ \<open>Suc (max n x)\<close>]) auto
    then show ?thesis using Gt UpRep by auto
  qed
next
  case Ge
  show ?thesis
  proof (cases R)
    case (FinRep xs)
    have bnd: \<open>\<And>i j. j \<in> set xs \<Longrightarrow> i \<le> j \<Longrightarrow> i \<le> fold max xs 0\<close>
      using fold_max_ge[of _ xs 0] by (auto intro: le_trans)
    then show ?thesis using Ge FinRep
      by (auto simp: list_ex_iff intro: bnd le_neq_implies_less)
  next
    case (UpRep xs n)
    have \<open>\<exists>xa \<in> set xs \<union> {m. n \<le> m}. x \<le> xa\<close> for x
      by (rule bexI[of _ \<open>max n x\<close>]) auto
    then show ?thesis using Ge UpRep by auto
  qed
next
  case Any
  then show ?thesis by (cases R) auto
qed

text \<open>Intersection of two indentation sets.\<close>

fun irep_inter :: \<open>indrep \<Rightarrow> indrep \<Rightarrow> indrep\<close> where
  \<open>irep_inter (FinRep xs) R = FinRep (filter (\<lambda>i. irep_mem i R) xs)\<close>
| \<open>irep_inter (UpRep xs n) (FinRep ys) = FinRep (filter (\<lambda>i. irep_mem i (UpRep xs n)) ys)\<close>
| \<open>irep_inter (UpRep xs n) (UpRep ys m) =
     UpRep (filter (\<lambda>i. irep_mem i (UpRep ys m)) xs @ filter (\<lambda>i. irep_mem i (UpRep xs n)) ys)
           (max n m)\<close>

lemma irep_inter_correct [simp]:
  \<open>irep_set (irep_inter R\<^sub>1 R\<^sub>2) = irep_set R\<^sub>1 \<inter> irep_set R\<^sub>2\<close>
  by (cases R\<^sub>1; cases R\<^sub>2) auto

text \<open>Existence of an anchor in \<open>R\<close> related by a \<^typ>\<open>wrel\<close> to a column.\<close>

fun wsat_up :: \<open>wrel \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool\<close> where
  \<open>wsat_up WEq c n \<longleftrightarrow> n \<le> c\<close>
| \<open>wsat_up WGe c n \<longleftrightarrow> n \<le> c\<close>
| \<open>wsat_up WGt c n \<longleftrightarrow> n < c\<close>
| \<open>wsat_up WLe c n \<longleftrightarrow> True\<close>
| \<open>wsat_up WLt c n \<longleftrightarrow> True\<close>
| \<open>wsat_up WAny c n \<longleftrightarrow> True\<close>

lemma wsat_up_correct: \<open>wsat_up \<tau> c n \<longleftrightarrow> (\<exists>j \<ge> n. wsat \<tau> c j)\<close>
  by (cases \<tau>) (auto intro: exI[of _ \<open>Suc (max c n)\<close>] exI[of _ \<open>max c n\<close>])

fun irep_ex_wsat :: \<open>wrel \<Rightarrow> nat \<Rightarrow> indrep \<Rightarrow> bool\<close> where
  \<open>irep_ex_wsat \<tau> c (FinRep xs) = list_ex (wsat \<tau> c) xs\<close>
| \<open>irep_ex_wsat \<tau> c (UpRep xs n) = (list_ex (wsat \<tau> c) xs \<or> wsat_up \<tau> c n)\<close>

lemma irep_ex_wsat_correct [simp]:
  \<open>irep_ex_wsat \<tau> c R \<longleftrightarrow> (\<exists>j \<in> irep_set R. wsat \<tau> c j)\<close>
  by (cases R) (auto simp: list_ex_iff wsat_up_correct)

subsection \<open>Set-valued goto\<close>

text \<open>Advance the dot over \<open>X\<close> whose anchor is known to lie in \<open>RA\<close>; every
  item keeps the anchors compatible with some element of \<open>RA\<close>. For a terminal
  \<open>RA\<close> is the singleton of its column and this is \<^const>\<open>xgoto\<close> up to the
  list representation of the indentation sets.\<close>

definition lgoto :: \<open>('n, 't) xitem list \<Rightarrow> ('n, 't) sym \<Rightarrow> indrep \<Rightarrow> ('n, 't) xitem list\<close> where
  \<open>lgoto xs X RA =
     map (\<lambda>(pr, m, R). (pr, Suc m, irep_inter R (irep_pre (snd (snd pr ! m)) RA)))
       (filter (\<lambda>(pr, m, R). m < length (snd pr) \<and> fst (snd pr ! m) = X) xs)\<close>

lemma lgoto_dot_pos: \<open>((pr, m, R)) \<in> set (lgoto xs X RA) \<Longrightarrow> m > 0\<close>
  unfolding lgoto_def by (auto simp: image_iff)

lemma lgoto_kernel_step:
  assumes \<open>((pr, Suc m, R')) \<in> set (lgoto xs X RA)\<close>
  obtains R where \<open>((pr, m, R)) \<in> set xs\<close>
    and \<open>m < length (snd pr)\<close>
    and \<open>fst (snd pr ! m) = X\<close>
    and \<open>R' = irep_inter R (irep_pre (snd (snd pr ! m)) RA)\<close>
  using assms unfolding lgoto_def by (auto simp: image_iff)

lemma lgoto_memI:
  assumes \<open>((pr, m, R)) \<in> set xs\<close> and \<open>m < length (snd pr)\<close> and \<open>fst (snd pr ! m) = X\<close>
  shows \<open>((pr, Suc m, irep_inter R (irep_pre (snd (snd pr ! m)) RA))) \<in> set (lgoto xs X RA)\<close>
  using assms unfolding lgoto_def by force

lemma set_ccore_lgoto:
  \<open>set (ccore (lgoto xs X RA)) = set (cgoto (ccore xs) X)\<close>
  unfolding ccore_def cgoto_def lgoto_def by force

text \<open>The anchor set of a reduce: the union over the completed items of the
  production in the closure (there is one, but the union needs no
  distinctness argument).\<close>

definition red_set :: \<open>('n, 't) xitem list \<Rightarrow> 'n \<times> ('n, 't) rhs \<Rightarrow> indrep\<close> where
  \<open>red_set CL pr = foldr (\<lambda>(pr', m, R) acc.
      if pr' = pr \<and> m = length (snd pr) then irep_union R acc else acc) CL (FinRep [])\<close>

lemma red_set_correct:
  \<open>irep_set (red_set CL pr) =
     \<Union> {irep_set R | R. ((pr, length (snd pr), R)) \<in> set CL}\<close>
  unfolding red_set_def
  by (induction CL) (auto split: prod.splits if_splits)

lemma red_set_nonempty_iff:
  \<open>irep_nonempty (red_set CL pr) \<longleftrightarrow>
     (\<exists>R. ((pr, length (snd pr), R)) \<in> set CL \<and> irep_nonempty R)\<close>
  by (auto simp: red_set_correct)

subsection \<open>The set-anchored machine\<close>

text \<open>Actions carry no anchor: a reduce is determined by its production. The
  step reads the frame closures off a cache stack running in lockstep with the
  frame stack; \<^text>\<open>mstep\<close> is the cache-free form.\<close>

datatype ('n, 't) dact = DShift | DReduce \<open>'n \<times> ('n, 't) rhs\<close>

definition mstep_cached :: \<open>('n, 't) is_cfg \<Rightarrow> ('n, 't) xitem list list \<Rightarrow>
    ('n, 't) gconfig \<Rightarrow> ('n, 't) dact \<Rightarrow> ('n, 't) gconfig option\<close> where
  \<open>mstep_cached G cstk gc act = (case gc of (Xs, w) \<Rightarrow> (case act of
      DShift \<Rightarrow> (case w of [] \<Rightarrow> None | (a, c) # w' \<Rightarrow>
        (if Xs = [] then None
         else Some (lgoto (hd cstk) (Tm a) (FinRep [c]) # Xs, w')))
    | DReduce pr \<Rightarrow>
        (if Xs = [] \<or> \<not> length (snd pr) < length Xs then None
         else let R = red_set (hd cstk) pr in
           if irep_nonempty R
           then Some (lgoto (cstk ! length (snd pr)) (Nt (fst pr)) R
                      # drop (length (snd pr)) Xs, w)
           else None)))\<close>

definition mstep :: \<open>('n, 't) is_cfg \<Rightarrow> ('n, 't) gconfig \<Rightarrow> ('n, 't) dact \<Rightarrow>
    ('n, 't) gconfig option\<close> where
  \<open>mstep G gc act = mstep_cached G (map (xclosure_auto G) (fst gc)) gc act\<close>

lemma mstep_shift_shape:
  assumes \<open>mstep_cached G cstk (Xs, w) DShift = Some gc'\<close>
  obtains a c w' where \<open>w = (a, c) # w'\<close> and \<open>Xs \<noteq> []\<close>
    and \<open>gc' = (lgoto (hd cstk) (Tm a) (FinRep [c]) # Xs, w')\<close>
  using assms unfolding mstep_cached_def by (auto split: list.splits if_splits)

lemma mstep_reduce_shape:
  assumes \<open>mstep_cached G cstk (Xs, w) (DReduce pr) = Some gc'\<close>
  obtains \<open>length (snd pr) < length Xs\<close> and \<open>irep_nonempty (red_set (hd cstk) pr)\<close>
    and \<open>gc' = (lgoto (cstk ! length (snd pr)) (Nt (fst pr)) (red_set (hd cstk) pr)
                # drop (length (snd pr)) Xs, w)\<close>
  using assms unfolding mstep_cached_def by (auto simp: Let_def split: if_splits)

fun mrun :: \<open>('n, 't) is_cfg \<Rightarrow> ('n, 't) dact list \<Rightarrow> ('n, 't) gconfig \<Rightarrow> ('n, 't) gconfig option\<close> where
  \<open>mrun G [] gc = Some gc\<close>
| \<open>mrun G (act # acts) gc = (case mstep G gc act of None \<Rightarrow> None | Some gc' \<Rightarrow> mrun G acts gc')\<close>

definition mcompletes :: \<open>('n, 't) is_cfg \<Rightarrow> 'n \<Rightarrow> ('n, 't) dact list \<Rightarrow> ('n, 't) gconfig \<Rightarrow> bool\<close> where
  \<open>mcompletes G Shn acts gc \<longleftrightarrow>
     (case mrun G acts gc of None \<Rightarrow> False | Some gc' \<Rightarrow> gfinal G Shn gc')\<close>

text \<open>Configurations reachable from an initial one with any input.\<close>

inductive mreach :: \<open>('n, 't) is_cfg \<Rightarrow> 'n \<Rightarrow> ('n, 't) gconfig \<Rightarrow> bool\<close> for G Shn where
  mreach_init: \<open>mreach G Shn ([xinit G Shn], w)\<close>
| mreach_step: \<open>mreach G Shn gc \<Longrightarrow> mstep G gc act = Some gc' \<Longrightarrow> mreach G Shn gc'\<close>

subsection \<open>The deterministic driver\<close>

text \<open>Driver state: machine configuration, closure cache, state-index stack,
  remaining spanned input, tree stack.\<close>

type_synonym ('m, 'ch, 'n, 't) dst =
  \<open>('n, 't) gconfig \<times> ('n, 't) xitem list list \<times> nat list \<times> ('m, 'ch, 't) tword \<times>
   ('m, 'ch, 'n, 't) ast list\<close>

text \<open>Candidate actions at state index \<open>i\<close> with its reduce cells. A reduce of
  \<open>pr\<close> is offered when the closure completes \<open>pr\<close> with a non-empty anchor set
  \<open>RS\<close> and some cell for \<open>(i, pr)\<close> names the current token (or end of input)
  with a width relation that some anchor in \<open>RS\<close> satisfies against the token's
  column. The shift comes first whenever input remains.\<close>

definition dlic :: \<open>nat \<Rightarrow> ('n, 't) lacell list \<Rightarrow> ('t \<times> nat) list \<Rightarrow>
    'n \<times> ('n, 't) rhs \<Rightarrow> indrep \<Rightarrow> bool\<close> where
  \<open>dlic i cells w pr RS \<longleftrightarrow> list_ex (\<lambda>(i', itm, t, \<tau>).
       i' = i \<and> itm = (pr, length (snd pr)) \<and>
       (case w of [] \<Rightarrow> t = None
                | (a, c) # _ \<Rightarrow> t = Some a \<and> irep_ex_wsat \<tau> c RS)) cells\<close>

definition dcands :: \<open>('n, 't) is_cfg \<Rightarrow> nat \<Rightarrow> ('n, 't) lacell list \<Rightarrow> ('n, 't) xitem list \<Rightarrow>
    ('n, 't) gconfig \<Rightarrow> ('n, 't) dact list\<close> where
  \<open>dcands G i cells CL gc = (case gc of (Xs, w) \<Rightarrow>
     if Xs = [] then [] else
     let comps = remdups (map fst (filter (\<lambda>(pr, m, R). m = length (snd pr)) CL));
         reds = map DReduce (filter (\<lambda>pr. let RS = red_set CL pr in
                    irep_nonempty RS \<and> dlic i cells w pr RS) comps)
     in (case w of [] \<Rightarrow> reds | _ \<Rightarrow> DShift # reds))\<close>

fun dpick :: \<open>('n, 't) is_cfg \<Rightarrow> ('n, 't) xitem list list \<Rightarrow> ('n, 't) gconfig \<Rightarrow>
    ('n, 't) dact list \<Rightarrow> (('n, 't) dact \<times> ('n, 't) gconfig) option\<close> where
  \<open>dpick G cstk gc [] = None\<close>
| \<open>dpick G cstk gc (act # acts) =
     (case mstep_cached G cstk gc act of
        Some gc' \<Rightarrow> (if dlive gc' then Some (act, gc') else dpick G cstk gc acts)
      | None \<Rightarrow> dpick G cstk gc acts)\<close>

definition dstep :: \<open>('n, 't) is_cfg \<Rightarrow> (('n, 't) sym \<times> nat) list list \<Rightarrow>
    ('n, 't) citem list list \<Rightarrow> ('n, 't) lacell list list \<Rightarrow>
    ('m, 'ch, 'n, 't) dst \<Rightarrow> ('m, 'ch, 'n, 't) dst option\<close> where
  \<open>dstep G gt sts redtab st = (case st of (gc, cstk, istk, v, tstk) \<Rightarrow>
     let i = (case istk of [] \<Rightarrow> length sts | j # _ \<Rightarrow> j);
         cells = (if i < length redtab then redtab ! i else []);
         CL = (case cstk of [] \<Rightarrow> [] | c # _ \<Rightarrow> c)
     in (case dpick G cstk gc (dcands G i cells CL gc) of
        None \<Rightarrow> None
      | Some (act, gc') \<Rightarrow> Some (case act of
          DShift \<Rightarrow> (gc',
              xclosure_auto G (hd (fst gc')) # cstk,
              dnext gt sts i (Tm (tok (hd v))) # istk,
              tl v,
              Leaf (hd v) # tstk)
        | DReduce pr \<Rightarrow> (gc',
              xclosure_auto G (hd (fst gc')) # drop (length (snd pr)) cstk,
              dnext gt sts (istk ! length (snd pr)) (Nt (fst pr))
                # drop (length (snd pr)) istk,
              v,
              Node (fst pr) (rev (take (length (snd pr)) tstk))
                # drop (length (snd pr)) tstk))))\<close>

fun drun :: \<open>('n, 't) is_cfg \<Rightarrow> 'n \<Rightarrow> (('n, 't) sym \<times> nat) list list \<Rightarrow>
    ('n, 't) citem list list \<Rightarrow> ('n, 't) lacell list list \<Rightarrow> nat \<Rightarrow>
    ('m, 'ch, 'n, 't) dst \<Rightarrow> ('m, 'ch, 'n, 't) ast option\<close> where
  \<open>drun G Shn gt sts redtab 0 st = (case st of (gc, cstk, istk, v, tstk) \<Rightarrow>
     if gfinal G Shn gc then (case tstk of t # _ \<Rightarrow> Some t | [] \<Rightarrow> None)
     else None)\<close>
| \<open>drun G Shn gt sts redtab (Suc n) st = (case st of (gc, cstk, istk, v, tstk) \<Rightarrow>
     if gfinal G Shn gc then (case tstk of t # _ \<Rightarrow> Some t | [] \<Rightarrow> None)
     else (case dstep G gt sts redtab st of
             None \<Rightarrow> None
           | Some st' \<Rightarrow> drun G Shn gt sts redtab n st'))\<close>

partial_function (option) drun\<^sub>w\<^sub>f ::
  \<open>('n, 't) is_cfg \<Rightarrow> 'n \<Rightarrow> (('n, 't) sym \<times> nat) list list \<Rightarrow>
    ('n, 't) citem list list \<Rightarrow> ('n, 't) lacell list list \<Rightarrow>
    ('m, 'ch, 'n, 't) dst \<Rightarrow> ('m, 'ch, 'n, 't) ast option\<close>
  where
  \<open>drun\<^sub>w\<^sub>f G Shn gt sts redtab st =
     (case st of (gc, cstk, istk, v, tstk) \<Rightarrow>
        if gfinal G Shn gc then (case tstk of t # _ \<Rightarrow> Some t | [] \<Rightarrow> None)
        else Option.bind (dstep G gt sts redtab st) (drun\<^sub>w\<^sub>f G Shn gt sts redtab))\<close>

lemmas drun\<^sub>w\<^sub>f_simps [simp] = drun\<^sub>w\<^sub>f.simps

text \<open>Not a code equation: generated code runs \<^text>\<open>drun_hist\<close>, which ends a
  run that revisits a configuration (\<^text>\<open>drun\<^sub>w\<^sub>f_code\<close> below).\<close>

text \<open>Entry points over the precise automaton: the six tables the
  \<^text>\<open>parser\<close> command defines as constants, so generated code computes
  each once (\<^text>\<open>dparse_via_tables\<close> below).\<close>

definition dinit :: \<open>('n, 't) is_cfg \<Rightarrow> 'n \<Rightarrow> ('n, 't) citem list list \<Rightarrow> ('m, 'ch, 't) tword \<Rightarrow>
    ('m, 'ch, 'n, 't) dst\<close> where
  \<open>dinit G Shn sts w = (([xinit G Shn], tcols w), [xclosure_auto G (xinit G Shn)],
     [st_find sts (lr0_start G Shn)], w, [])\<close>

definition dparse\<^sub>n :: \<open>('n, 't) is_cfg \<Rightarrow> 'n \<Rightarrow> nat \<Rightarrow> ('m, 'ch, 't) tword \<Rightarrow>
    ('m, 'ch, 'n, 't) ast option\<close> where
  \<open>dparse\<^sub>n G Shn fuel w = (let sts = pr0_states G Shn; gt = pgtab G sts;
       redtab = red_buckets G Shn (length sts)
     in drun G Shn gt sts redtab fuel (dinit G Shn sts w))\<close>

definition dparse :: \<open>('n, 't) is_cfg \<Rightarrow> 'n \<Rightarrow> ('m, 'ch, 't) tword \<Rightarrow>
    ('m, 'ch, 'n, 't) ast option\<close> where
  \<open>dparse G Shn w = (let sts = pr0_states G Shn; gt = pgtab G sts;
       redtab = red_buckets G Shn (length sts)
     in drun\<^sub>w\<^sub>f G Shn gt sts redtab (dinit G Shn sts w))\<close>

text \<open>Table inlining for the code generator: the six tables become constants,
  each defined by its term over the ones before it (or by its value under
  \<^text>\<open>parser_literal_tables\<close>), and the driver is applied to those
  constants, so exported code computes each table once when it loads and each
  step is O(frame). The backend's \<^text>\<open>lr_build_parse\<close> consumes this
  equation.\<close>

lemma dparse_via_tables:
  assumes st:  \<open>pr0_states G Shn = sts\<close>
    and   gt:  \<open>pgtab G sts = gtab\<close>
    and   rt:  \<open>red_buckets G Shn (length sts) = redtab\<close>
    and   xi:  \<open>xinit G Shn = xin\<close>
    and   xc:  \<open>xclosure_auto G xin = xclos\<close>
    and   i0:  \<open>st_find sts (lr0_start G Shn) = i\<^sub>0\<close>
  shows \<open>dparse G Shn w =
     drun\<^sub>w\<^sub>f G Shn gtab sts redtab (([xin], tcols w), [xclos], [i\<^sub>0], w, [])\<close>
  unfolding dparse_def dinit_def Let_def
  by (simp add: st gt rt xi xc i0)

lemma drun_imp_drun\<^sub>w\<^sub>f:
  \<open>drun G Shn gt sts redtab n st = Some t \<Longrightarrow> drun\<^sub>w\<^sub>f G Shn gt sts redtab st = Some t\<close>
  by (induction n arbitrary: st)
     (auto split: prod.splits option.splits if_splits list.splits)

subsection \<open>Iterating the driver, and the bridge to \<^const>\<open>drun\<close>\<close>

text \<open>\<^const>\<open>drun\<close> stops at the first \<^const>\<open>gfinal\<close> state, so it does
  not compose across a subtree. \<^text>\<open>dsteps\<close> is the \<open>n\<close>-fold iteration of
  \<^const>\<open>dstep\<close>; it composes, and \<^text>\<open>drun_of_dsteps\<close> converts a
  completed chain back into a \<^const>\<open>drun\<close> result.\<close>

fun dsteps :: \<open>('n, 't) is_cfg \<Rightarrow> (('n, 't) sym \<times> nat) list list \<Rightarrow>
    ('n, 't) citem list list \<Rightarrow> ('n, 't) lacell list list \<Rightarrow> nat \<Rightarrow>
    ('m, 'ch, 'n, 't) dst \<Rightarrow> ('m, 'ch, 'n, 't) dst option\<close> where
  \<open>dsteps G gt sts redtab 0 st = Some st\<close>
| \<open>dsteps G gt sts redtab (Suc n) st =
     (case dstep G gt sts redtab st of
        None \<Rightarrow> None | Some st' \<Rightarrow> dsteps G gt sts redtab n st')\<close>

lemma dsteps_Suc_step:
  \<open>dstep G gt sts redtab st = Some st\<^sub>1 \<Longrightarrow>
     dsteps G gt sts redtab (Suc k) st = dsteps G gt sts redtab k st\<^sub>1\<close>
  by simp

lemma drun_of_dsteps:
  \<open>dsteps G gt sts redtab n st = Some st' \<Longrightarrow>
   (\<forall>k < n. \<exists>st\<^sub>k. dsteps G gt sts redtab k st = Some st\<^sub>k \<and> \<not> gfinal G Shn (fst st\<^sub>k)) \<Longrightarrow>
   gfinal G Shn (fst st') \<Longrightarrow>
   (case st' of (gc, cstk, istk, v, tstk) \<Rightarrow> tstk) = t # rest \<Longrightarrow>
   drun G Shn gt sts redtab n st = Some t\<close>
proof (induction n arbitrary: st)
  case 0
  then have \<open>st' = st\<close> by simp
  then show ?case using 0 by (cases st) (auto split: list.splits)
next
  case (Suc n)
  have nf: \<open>\<not> gfinal G Shn (fst st)\<close>
    using Suc.prems(2)[rule_format, of 0] by simp
  from Suc.prems(1) obtain st\<^sub>1 where
      sp: \<open>dstep G gt sts redtab st = Some st\<^sub>1\<close>
    and rest_run: \<open>dsteps G gt sts redtab n st\<^sub>1 = Some st'\<close>
    by (auto split: option.splits)
  have shift: \<open>\<forall>k < n. \<exists>st\<^sub>k. dsteps G gt sts redtab k st\<^sub>1 = Some st\<^sub>k \<and>
                  \<not> gfinal G Shn (fst st\<^sub>k)\<close>
  proof (intro allI impI)
    fix k assume \<open>k < n\<close>
    then have \<open>Suc k < Suc n\<close> by simp
    from Suc.prems(2)[rule_format, OF this] obtain st\<^sub>k where
        e: \<open>dsteps G gt sts redtab (Suc k) st = Some st\<^sub>k\<close>
      and nfk: \<open>\<not> gfinal G Shn (fst st\<^sub>k)\<close> by blast
    show \<open>\<exists>st\<^sub>k. dsteps G gt sts redtab k st\<^sub>1 = Some st\<^sub>k \<and> \<not> gfinal G Shn (fst st\<^sub>k)\<close>
      using e nfk unfolding dsteps_Suc_step[OF sp] by blast
  qed
  from Suc.IH[OF rest_run shift Suc.prems(3) Suc.prems(4)]
  have \<open>drun G Shn gt sts redtab n st\<^sub>1 = Some t\<close> .
  then show ?case using nf sp by (cases st) simp
qed

subsection \<open>Shape of reachable stacks\<close>

text \<open>Every frame above the bottom is the set-valued goto of the closure of
  the frame below on a labelled symbol; \<open>\<alpha>\<close> lists the labels, top first.\<close>

definition dshape :: \<open>('n, 't) is_cfg \<Rightarrow> 'n \<Rightarrow> ('n, 't) xitem list list \<Rightarrow>
    (('n, 't) sym \<times> indrep) list \<Rightarrow> bool\<close> where
  \<open>dshape G Shn Xs \<alpha> \<longleftrightarrow>
     length Xs = length \<alpha> + 1 \<and> Xs ! length \<alpha> = xinit G Shn \<and>
     (\<forall>k < length \<alpha>. Xs ! k =
        lgoto (xclosure_auto G (Xs ! Suc k)) (fst (\<alpha> ! k)) (snd (\<alpha> ! k)))\<close>

lemma dshape_init: \<open>dshape G Shn [xinit G Shn] []\<close>
  unfolding dshape_def by simp

lemma dshape_push:
  assumes sh: \<open>dshape G Shn Xs \<alpha>\<close> and ne: \<open>Xs \<noteq> []\<close>
  shows \<open>dshape G Shn (lgoto (xclosure_auto G (hd Xs)) X RA # Xs) ((X, RA) # \<alpha>)\<close>
proof -
  have lenX: \<open>length Xs = length \<alpha> + 1\<close> and bot: \<open>Xs ! length \<alpha> = xinit G Shn\<close>
    and shp: \<open>\<forall>k < length \<alpha>. Xs ! k =
        lgoto (xclosure_auto G (Xs ! Suc k)) (fst (\<alpha> ! k)) (snd (\<alpha> ! k))\<close>
    using sh unfolding dshape_def by auto
  have hd_eq: \<open>hd Xs = Xs ! 0\<close> using ne by (simp add: hd_conv_nth)
  show ?thesis unfolding dshape_def
  proof (intro conjI allI impI)
    fix k assume \<open>k < length ((X, RA) # \<alpha>)\<close>
    then show \<open>(lgoto (xclosure_auto G (hd Xs)) X RA # Xs) ! k =
        lgoto (xclosure_auto G ((lgoto (xclosure_auto G (hd Xs)) X RA # Xs) ! Suc k))
          (fst (((X, RA) # \<alpha>) ! k)) (snd (((X, RA) # \<alpha>) ! k))\<close>
      using shp hd_eq by (cases k) auto
  qed (use lenX bot in auto)
qed

lemma dshape_reduce:
  assumes sh: \<open>dshape G Shn Xs \<alpha>\<close> and k_lt: \<open>k < length Xs\<close>
  shows \<open>dshape G Shn (lgoto (xclosure_auto G (Xs ! k)) X RA # drop k Xs) ((X, RA) # drop k \<alpha>)\<close>
proof -
  have lenX: \<open>length Xs = length \<alpha> + 1\<close> and bot: \<open>Xs ! length \<alpha> = xinit G Shn\<close>
    and shp: \<open>\<forall>k < length \<alpha>. Xs ! k =
        lgoto (xclosure_auto G (Xs ! Suc k)) (fst (\<alpha> ! k)) (snd (\<alpha> ! k))\<close>
    using sh unfolding dshape_def by auto
  have k_le: \<open>k \<le> length \<alpha>\<close> using k_lt lenX by simp
  show ?thesis unfolding dshape_def
  proof (intro conjI allI impI)
    show \<open>length (lgoto (xclosure_auto G (Xs ! k)) X RA # drop k Xs) = length ((X, RA) # drop k \<alpha>) + 1\<close>
      using lenX k_le by simp
    show \<open>(lgoto (xclosure_auto G (Xs ! k)) X RA # drop k Xs) ! length ((X, RA) # drop k \<alpha>) = xinit G Shn\<close>
      using lenX k_le bot by simp
    fix k' assume k'_lt: \<open>k' < length ((X, RA) # drop k \<alpha>)\<close>
    show \<open>(lgoto (xclosure_auto G (Xs ! k)) X RA # drop k Xs) ! k' =
        lgoto (xclosure_auto G ((lgoto (xclosure_auto G (Xs ! k)) X RA # drop k Xs) ! Suc k'))
          (fst (((X, RA) # drop k \<alpha>) ! k')) (snd (((X, RA) # drop k \<alpha>) ! k'))\<close>
    proof (cases k')
      case 0
      then show ?thesis using k_lt by simp
    next
      case (Suc j)
      with k'_lt have j_lt: \<open>k + j < length \<alpha>\<close> by simp
      then show ?thesis using shp Suc lenX by (simp add: add.commute)
    qed
  qed
qed

text \<open>Every item of a closure on a shaped stack is a grammar production or
  the fresh start production (the latter only through the bottom frame).\<close>

lemma dshape_prods:
  assumes sh: \<open>dshape G Shn Xs \<alpha>\<close>
  shows \<open>d \<le> length \<alpha> \<Longrightarrow> ((pr, m, R)) \<in> set (xclosure_auto G (Xs ! d)) \<Longrightarrow>
         pr \<in> set (iprods G) \<or> pr = start_prod G Shn\<close>
proof (induct m arbitrary: d R)
  case 0
  have item: \<open>((pr, 0, R)) \<in> set (xclosure_auto G (Xs ! d))\<close> by fact
  have d_le: \<open>d \<le> length \<alpha>\<close> by fact
  have item_slot:
    \<open>((pr, 0, R)) \<in> set (xslots G (Xs ! d) (xiter G (Xs ! d) (xfuel G (Xs ! d))))\<close>
    using item unfolding xclosure_auto_def xclosure_def by simp
  show ?case
  proof (cases rule: xslots_memE[OF item_slot])
    case 1
    show ?thesis
    proof (cases \<open>d = length \<alpha>\<close>)
      case True
      then have \<open>((pr, 0, R)) \<in> set (xinit G Shn)\<close>
        using 1 sh unfolding dshape_def by simp
      then show ?thesis unfolding xinit_def start_prod_def by simp
    next
      case False
      then have d_lt: \<open>d < length \<alpha>\<close> using d_le by simp
      have \<open>Xs ! d = lgoto (xclosure_auto G (Xs ! Suc d)) (fst (\<alpha> ! d)) (snd (\<alpha> ! d))\<close>
        using sh d_lt unfolding dshape_def by blast
      with 1 have \<open>((pr, 0, R)) \<in> set (lgoto (xclosure_auto G (Xs ! Suc d)) (fst (\<alpha> ! d)) (snd (\<alpha> ! d)))\<close>
        by simp
      from lgoto_dot_pos[OF this] show ?thesis by simp
    qed
  next
    case (2 p)
    then show ?thesis using nth_mem by force
  qed
next
  case (Suc n)
  have item: \<open>((pr, Suc n, R)) \<in> set (xclosure_auto G (Xs ! d))\<close> by fact
  have d_le: \<open>d \<le> length \<alpha>\<close> by fact
  from xclosure_auto_kernel[OF _ item] have item_ker: \<open>((pr, Suc n, R)) \<in> set (Xs ! d)\<close> by simp
  show ?case
  proof (cases \<open>d = length \<alpha>\<close>)
    case True
    then have \<open>((pr, Suc n, R)) \<in> set (xinit G Shn)\<close>
      using item_ker sh unfolding dshape_def by simp
    then show ?thesis unfolding xinit_def by simp
  next
    case False
    then have d_lt: \<open>d < length \<alpha>\<close> using d_le by simp
    have Xs_d: \<open>Xs ! d = lgoto (xclosure_auto G (Xs ! Suc d)) (fst (\<alpha> ! d)) (snd (\<alpha> ! d))\<close>
      using sh d_lt unfolding dshape_def by blast
    from lgoto_kernel_step[OF item_ker[unfolded Xs_d]]
    obtain R\<^sub>1 where \<open>((pr, n, R\<^sub>1)) \<in> set (xclosure_auto G (Xs ! Suc d))\<close> by blast
    from Suc.hyps[OF _ this] d_lt show ?thesis by simp
  qed
qed

lemma lgoto_Nt_Shn_empty:
  assumes fn: \<open>fresh_name G Shn\<close> and sh: \<open>dshape G Shn Xs \<alpha>\<close> and d_lt: \<open>d < length Xs\<close>
  shows \<open>lgoto (xclosure_auto G (Xs ! d)) (Nt Shn) RA = []\<close>
proof -
  have d_le: \<open>d \<le> length \<alpha>\<close> using d_lt sh unfolding dshape_def by simp
  have no_match: \<open>\<not> (m < length (snd pr) \<and> fst (snd pr ! m) = Nt Shn)\<close>
    if mem: \<open>((pr, m, R)) \<in> set (xclosure_auto G (Xs ! d))\<close> for pr m R
  proof (rule notI)
    assume A: \<open>m < length (snd pr) \<and> fst (snd pr ! m) = Nt Shn\<close>
    from dshape_prods[OF sh d_le mem]
    show False
    proof
      assume \<open>pr \<in> set (iprods G)\<close>
      then have \<open>(fst pr, snd pr) \<in> set (iprods G)\<close> by simp
      moreover have \<open>snd pr ! m \<in> set (snd pr)\<close> using A by simp
      ultimately show False
        using fn A unfolding fresh_name_def by (cases \<open>snd pr ! m\<close>) fastforce
    next
      assume \<open>pr = start_prod G Shn\<close>
      then show False using A fn unfolding start_prod_def fresh_name_def
        by (cases m) auto
    qed
  qed
  show ?thesis unfolding lgoto_def using no_match
    by (auto simp: filter_empty_conv case_prod_beta)
qed

text \<open>Past-symbols descent on a shaped stack: an item at dot \<open>m\<close> in the
  closure of frame \<open>d\<close> was built over the \<open>m\<close> labels below, each compatible
  with every anchor the item still admits, from a dot-0 item admitting the
  same anchor.\<close>

lemma past_symbols_set:
  assumes sh: \<open>dshape G Shn Xs \<alpha>\<close>
  shows \<open>m + d \<le> length \<alpha> \<Longrightarrow> ((pr, m, R)) \<in> set (xclosure_auto G (Xs ! d)) \<Longrightarrow>
         j \<in> irep_set R \<Longrightarrow>
         list_all2 (\<lambda>Xr (X, RA). X = fst Xr \<and> (\<exists>j' \<in> irep_set RA. irel_sat (snd Xr) j' j))
                   (take m (snd pr)) (rev (map ((!) \<alpha>) [d..<d + m])) \<and>
         (\<exists>R\<^sub>0. ((pr, 0, R\<^sub>0)) \<in> set (xclosure_auto G (Xs ! (d + m))) \<and> j \<in> irep_set R\<^sub>0)\<close>
proof (induct m arbitrary: d R)
  case 0
  then show ?case by auto
next
  case (Suc n)
  have bnd: \<open>Suc n + d \<le> length \<alpha>\<close> and item: \<open>((pr, Suc n, R)) \<in> set (xclosure_auto G (Xs ! d))\<close>
    and jmem: \<open>j \<in> irep_set R\<close> by fact+
  have d_lt: \<open>d < length \<alpha>\<close> using bnd by simp
  from xclosure_auto_kernel[OF _ item] have item_ker: \<open>((pr, Suc n, R)) \<in> set (Xs ! d)\<close> by simp
  have Xs_d: \<open>Xs ! d = lgoto (xclosure_auto G (Xs ! Suc d)) (fst (\<alpha> ! d)) (snd (\<alpha> ! d))\<close>
    using sh d_lt unfolding dshape_def by blast
  from lgoto_kernel_step[OF item_ker[unfolded Xs_d]]
  obtain R\<^sub>1 where item\<^sub>1: \<open>((pr, n, R\<^sub>1)) \<in> set (xclosure_auto G (Xs ! Suc d))\<close>
    and n_lt: \<open>n < length (snd pr)\<close>
    and Xeq: \<open>fst (snd pr ! n) = fst (\<alpha> ! d)\<close>
    and Req: \<open>R = irep_inter R\<^sub>1 (irep_pre (snd (snd pr ! n)) (snd (\<alpha> ! d)))\<close>
    by blast
  from jmem[unfolded Req] have j1: \<open>j \<in> irep_set R\<^sub>1\<close>
    and jsat: \<open>\<exists>j' \<in> irep_set (snd (\<alpha> ! d)). irel_sat (snd (snd pr ! n)) j' j\<close>
    by auto
  have bnd': \<open>n + Suc d \<le> length \<alpha>\<close> using bnd by simp
  from Suc.hyps[OF bnd' item\<^sub>1 j1]
  have IH: \<open>list_all2 (\<lambda>Xr (X, RA). X = fst Xr \<and> (\<exists>j' \<in> irep_set RA. irel_sat (snd Xr) j' j))
              (take n (snd pr)) (rev (map ((!) \<alpha>) [Suc d..<Suc d + n]))\<close>
    and R0: \<open>\<exists>R\<^sub>0. ((pr, 0, R\<^sub>0)) \<in> set (xclosure_auto G (Xs ! (Suc d + n))) \<and> j \<in> irep_set R\<^sub>0\<close>
    by auto
  have take_expand: \<open>take (Suc n) (snd pr) = take n (snd pr) @ [snd pr ! n]\<close>
    using n_lt by (simp add: take_Suc_conv_app_nth)
  have rev_expand:
    \<open>rev (map ((!) \<alpha>) [d..<d + Suc n]) = rev (map ((!) \<alpha>) [Suc d..<Suc d + n]) @ [\<alpha> ! d]\<close>
    by (simp add: Suc_le_eq upt_rec)
  have last_pair: \<open>(\<lambda>Xr (X, RA). X = fst Xr \<and> (\<exists>j' \<in> irep_set RA. irel_sat (snd Xr) j' j))
       (snd pr ! n) (\<alpha> ! d)\<close>
    using Xeq jsat by (cases \<open>\<alpha> ! d\<close>) auto
  show ?case
  proof (intro conjI)
    show \<open>list_all2 (\<lambda>Xr (X, RA). X = fst Xr \<and> (\<exists>j' \<in> irep_set RA. irel_sat (snd Xr) j' j))
            (take (Suc n) (snd pr)) (rev (map ((!) \<alpha>) [d..<d + Suc n]))\<close>
      unfolding take_expand rev_expand
      by (rule list_all2_appendI[OF IH]) (simp add: last_pair)
    show \<open>\<exists>R\<^sub>0. ((pr, 0, R\<^sub>0)) \<in> set (xclosure_auto G (Xs ! (d + Suc n))) \<and> j \<in> irep_set R\<^sub>0\<close>
      using R0 by simp
  qed
qed

subsection \<open>Realizability of the tree stack\<close>

text \<open>An AST realizes a labelled symbol when every anchor of the label is the
  root indentation of some wellformed annotation of the AST.\<close>

definition realizes :: \<open>('n, 't) is_cfg \<Rightarrow> ('m, 'ch, 'n, 't) ast \<Rightarrow> ('n, 't) sym \<times> indrep \<Rightarrow> bool\<close> where
  \<open>realizes G a XR \<longleftrightarrow>
     (\<forall>j \<in> irep_set (snd XR). \<exists>pt. wf_ptree G pt \<and> erase pt = a \<and> proot pt = (fst XR, j))\<close>

fun ayield :: \<open>('m, 'ch, 'n, 't) ast \<Rightarrow> ('m, 'ch, 't) tword\<close> where
  \<open>ayield (Leaf t) = [t]\<close>
| \<open>ayield (Node A ts) = concat (map ayield ts)\<close>

lemma pyield_erase: \<open>pyield pt = ayield (erase pt)\<close>
  by (induction pt) (auto simp: map_concat cong: map_cong)

lemma realizes_leaf: \<open>realizes G (Leaf t) (Tm (tok t), FinRep [s_col (token.span t)])\<close>
  unfolding realizes_def
  by (auto intro!: exI[of _ \<open>PLeaf t\<close>] wf_ptree.wf_leaf)

text \<open>Choosing realizations for the children of a reduce.\<close>

lemma reduce_realizes:
  assumes sh: \<open>dshape G Shn Xs \<alpha>\<close>
    and real: \<open>\<And>k. k < length \<alpha> \<Longrightarrow> realizes G (ts ! k) (\<alpha> ! k)\<close>
    and len_ts: \<open>length ts = length \<alpha>\<close>
    and mem: \<open>((pr, length (snd pr), R)) \<in> set (xclosure_auto G (Xs ! 0))\<close>
    and k_le: \<open>length (snd pr) \<le> length \<alpha>\<close>
    and j: \<open>j \<in> irep_set R\<close>
    and pr_ip: \<open>pr \<in> set (iprods G)\<close>
  shows \<open>\<exists>pt. wf_ptree G pt \<and> erase pt = Node (fst pr) (rev (take (length (snd pr)) ts)) \<and>
              proot pt = (Nt (fst pr), j)\<close>
proof -
  let ?k = \<open>length (snd pr)\<close>
  from past_symbols_set[OF sh, of ?k 0 pr R j] k_le mem j
  have la: \<open>list_all2 (\<lambda>Xr (X, RA). X = fst Xr \<and> (\<exists>j' \<in> irep_set RA. irel_sat (snd Xr) j' j))
              (snd pr) (rev (map ((!) \<alpha>) [0..<?k]))\<close> by simp
  have map_take: \<open>map ((!) \<alpha>) [0..<?k] = take ?k \<alpha>\<close>
    using k_le by (intro nth_equalityI) auto
  have la': \<open>list_all2 (\<lambda>Xr (X, RA). X = fst Xr \<and> (\<exists>j' \<in> irep_set RA. irel_sat (snd Xr) j' j))
              (snd pr) (rev (take ?k \<alpha>))\<close>
    using la map_take by simp
  have ex: \<open>\<forall>p < ?k. \<exists>pt. wf_ptree G pt \<and> erase pt = rev (take ?k ts) ! p \<and>
              fst (proot pt) = fst (snd pr ! p) \<and> irel_sat (snd (snd pr ! p)) (snd (proot pt)) j\<close>
  proof (intro allI impI)
    fix p assume p_lt: \<open>p < ?k\<close>
    have idx: \<open>rev (take ?k \<alpha>) ! p = \<alpha> ! (?k - Suc p)\<close>
      using p_lt k_le by (simp add: rev_nth)
    have idx_ts: \<open>rev (take ?k ts) ! p = ts ! (?k - Suc p)\<close>
      using p_lt k_le len_ts by (simp add: rev_nth)
    obtain X RA where XRA: \<open>\<alpha> ! (?k - Suc p) = (X, RA)\<close> by (cases \<open>\<alpha> ! (?k - Suc p)\<close>)
    from list_all2_nthD[OF la', of p] p_lt
    have \<open>X = fst (snd pr ! p)\<close> and \<open>\<exists>j' \<in> irep_set RA. irel_sat (snd (snd pr ! p)) j' j\<close>
      using idx XRA by auto
    then obtain j' where j'mem: \<open>j' \<in> irep_set RA\<close> and sat: \<open>irel_sat (snd (snd pr ! p)) j' j\<close>
      and Xeq: \<open>X = fst (snd pr ! p)\<close> by blast
    have \<open>realizes G (ts ! (?k - Suc p)) (X, RA)\<close>
      using real[of \<open>?k - Suc p\<close>] p_lt k_le XRA by simp
    then obtain pt where \<open>wf_ptree G pt\<close> \<open>erase pt = ts ! (?k - Suc p)\<close> \<open>proot pt = (X, j')\<close>
      unfolding realizes_def using j'mem by auto
    then show \<open>\<exists>pt. wf_ptree G pt \<and> erase pt = rev (take ?k ts) ! p \<and>
              fst (proot pt) = fst (snd pr ! p) \<and> irel_sat (snd (snd pr ! p)) (snd (proot pt)) j\<close>
      using idx_ts Xeq sat by auto
  qed
  from ex obtain f where f: \<open>\<forall>p < ?k. wf_ptree G (f p) \<and> erase (f p) = rev (take ?k ts) ! p \<and>
              fst (proot (f p)) = fst (snd pr ! p) \<and> irel_sat (snd (snd pr ! p)) (snd (proot (f p))) j\<close>
    by (metis (no_types, lifting))
  let ?pts = \<open>map f [0..<?k]\<close>
  have la2: \<open>list_all2 (\<lambda>Xr pt. fst (proot pt) = fst Xr \<and> irel_sat (snd Xr) (snd (proot pt)) j \<and>
                wf_ptree G pt) (snd pr) ?pts\<close>
    using f by (auto simp: list_all2_conv_all_nth)
  have wf: \<open>wf_ptree G (PNode (fst pr) j ?pts)\<close>
    using wf_ptree.wf_node[OF _ la2] pr_ip by (cases pr) auto
  have er: \<open>map erase ?pts = rev (take ?k ts)\<close>
    using f len_ts k_le by (intro nth_equalityI) auto
  show ?thesis
    by (intro exI[of _ \<open>PNode (fst pr) j ?pts\<close>]) (use wf er in simp)
qed

subsection \<open>The driver invariant and soundness\<close>

definition dinv :: \<open>('n, 't) is_cfg \<Rightarrow> 'n \<Rightarrow> ('m, 'ch, 't) tword \<Rightarrow> ('m, 'ch, 'n, 't) dst \<Rightarrow> bool\<close> where
  \<open>dinv G Shn w st \<longleftrightarrow> (case st of (gc, cstk, istk, v, tstk) \<Rightarrow> (case gc of (Xs, w') \<Rightarrow>
     cstk_ok G Xs cstk \<and> length istk = length Xs \<and> w' = tcols v \<and>
     (\<exists>RAs. length RAs = length tstk \<and>
            dshape G Shn Xs (zip (map asym tstk) RAs) \<and>
            (\<forall>k < length tstk. realizes G (tstk ! k) (asym (tstk ! k), RAs ! k)) \<and>
            w = concat (map ayield (rev tstk)) @ v)))\<close>

lemma dinv_init: \<open>dinv G Shn w (dinit G Shn sts w)\<close>
  unfolding dinv_def dinit_def
  by (auto simp: cstk_ok_def dshape_init intro!: exI[of _ \<open>[]\<close>])

lemma dpick_sound:
  \<open>dpick G cstk gc acts = Some (act, gc') \<Longrightarrow>
     act \<in> set acts \<and> mstep_cached G cstk gc act = Some gc' \<and> dlive gc'\<close>
  by (induction acts) (auto split: option.splits if_splits)

lemma dstep_inv:
  assumes fn: \<open>fresh_name G Shn\<close>
    and inv: \<open>dinv G Shn w st\<close>
    and sp: \<open>dstep G gt sts redtab st = Some st'\<close>
  shows \<open>dinv G Shn w st'\<close>
proof -
  obtain gc cstk istk v tstk where st: \<open>st = (gc, cstk, istk, v, tstk)\<close> by (cases st)
  obtain Xs w' where gc: \<open>gc = (Xs, w')\<close> by (cases gc)
  from inv[unfolded st gc dinv_def] obtain RAs where
      okc: \<open>cstk_ok G Xs cstk\<close> and len_i: \<open>length istk = length Xs\<close> and w': \<open>w' = tcols v\<close>
    and lenR: \<open>length RAs = length tstk\<close>
    and sh: \<open>dshape G Shn Xs (zip (map asym tstk) RAs)\<close>
    and real: \<open>\<forall>k < length tstk. realizes G (tstk ! k) (asym (tstk ! k), RAs ! k)\<close>
    and yld: \<open>w = concat (map ayield (rev tstk)) @ v\<close>
    by auto
  have lenX: \<open>length Xs = length tstk + 1\<close> using sh lenR unfolding dshape_def by simp
  have Xs_ne: \<open>Xs \<noteq> []\<close> using lenX by auto
  define i where \<open>i = (case istk of [] \<Rightarrow> length sts | j # _ \<Rightarrow> j)\<close>
  define cells where \<open>cells = (if i < length redtab then redtab ! i else [])\<close>
  define CL where \<open>CL = (case cstk of [] \<Rightarrow> [] | c # _ \<Rightarrow> c)\<close>
  from sp[unfolded st gc dstep_def Let_def] obtain act gc' where
      pick: \<open>dpick G cstk (Xs, w') (dcands G i cells CL (Xs, w')) = Some (act, gc')\<close>
    and st': \<open>st' = (case act of
          DShift \<Rightarrow> (gc', xclosure_auto G (hd (fst gc')) # cstk,
              dnext gt sts i (Tm (tok (hd v))) # istk, tl v, Leaf (hd v) # tstk)
        | DReduce pr \<Rightarrow> (gc', xclosure_auto G (hd (fst gc')) # drop (length (snd pr)) cstk,
              dnext gt sts (istk ! length (snd pr)) (Nt (fst pr)) # drop (length (snd pr)) istk,
              v, Node (fst pr) (rev (take (length (snd pr)) tstk)) # drop (length (snd pr)) tstk))\<close>
    unfolding i_def cells_def CL_def by (auto split: option.splits)
  from dpick_sound[OF pick] have ms: \<open>mstep_cached G cstk (Xs, w') act = Some gc'\<close> and live: \<open>dlive gc'\<close>
    by auto
  show ?thesis
  proof (cases act)
    case DShift
    from mstep_shift_shape[OF ms[unfolded DShift]] obtain a c w'' where
        w'_eq: \<open>w' = (a, c) # w''\<close>
      and gc': \<open>gc' = (lgoto (hd cstk) (Tm a) (FinRep [c]) # Xs, w'')\<close> by blast
    from w' w'_eq obtain t\<^sub>0 v' where v: \<open>v = t\<^sub>0 # v'\<close> and a: \<open>a = tok t\<^sub>0\<close>
      and c: \<open>c = s_col (token.span t\<^sub>0)\<close> and w'': \<open>w'' = tcols v'\<close>
      by (cases v) auto
    have hdc: \<open>hd cstk = xclosure_auto G (hd Xs)\<close> using cstk_ok_hd[OF okc Xs_ne] .
    let ?F = \<open>lgoto (xclosure_auto G (hd Xs)) (Tm a) (FinRep [c])\<close>
    have st'_eq: \<open>st' = ((?F # Xs, w''), xclosure_auto G ?F # cstk,
        dnext gt sts i (Tm (tok (hd v))) # istk, v', Leaf t\<^sub>0 # tstk)\<close>
      using st' gc' hdc v unfolding DShift by simp
    have sh': \<open>dshape G Shn (?F # Xs) (zip (map asym (Leaf t\<^sub>0 # tstk)) (FinRep [c] # RAs))\<close>
      using dshape_push[OF sh Xs_ne, of \<open>Tm a\<close> \<open>FinRep [c]\<close>] a by simp
    have real': \<open>\<forall>k < length (Leaf t\<^sub>0 # tstk).
        realizes G ((Leaf t\<^sub>0 # tstk) ! k) (asym ((Leaf t\<^sub>0 # tstk) ! k), (FinRep [c] # RAs) ! k)\<close>
    proof (intro allI impI)
      fix k assume \<open>k < length (Leaf t\<^sub>0 # tstk)\<close>
      then show \<open>realizes G ((Leaf t\<^sub>0 # tstk) ! k)
          (asym ((Leaf t\<^sub>0 # tstk) ! k), (FinRep [c] # RAs) ! k)\<close>
        using real realizes_leaf[of G t\<^sub>0] c by (cases k) auto
    qed
    have yld': \<open>w = concat (map ayield (rev (Leaf t\<^sub>0 # tstk))) @ v'\<close>
      using yld v by simp
    show ?thesis unfolding st'_eq dinv_def
      using cstk_ok_push[OF okc] len_i w'' lenR sh' real' yld'
      by (auto intro!: exI[of _ \<open>FinRep [c] # RAs\<close>])
  next
    case (DReduce pr)
    let ?k = \<open>length (snd pr)\<close>
    let ?RS = \<open>red_set (hd cstk) pr\<close>
    from mstep_reduce_shape[OF ms[unfolded DReduce]] have k_lt: \<open>?k < length Xs\<close>
      and RS_ne: \<open>irep_nonempty ?RS\<close>
      and gc': \<open>gc' = (lgoto (cstk ! ?k) (Nt (fst pr)) ?RS # drop ?k Xs, w')\<close> by blast+
    have hdc: \<open>hd cstk = xclosure_auto G (hd Xs)\<close> using cstk_ok_hd[OF okc Xs_ne] .
    have hd0: \<open>hd Xs = Xs ! 0\<close> using Xs_ne by (simp add: hd_conv_nth)
    have ck: \<open>cstk ! ?k = xclosure_auto G (Xs ! ?k)\<close> using cstk_ok_nth[OF okc k_lt] .
    from RS_ne obtain R where memR: \<open>((pr, ?k, R)) \<in> set (xclosure_auto G (Xs ! 0))\<close>
      and R_ne: \<open>irep_nonempty R\<close>
      unfolding red_set_nonempty_iff hdc hd0 by blast
    let ?F = \<open>lgoto (xclosure_auto G (Xs ! ?k)) (Nt (fst pr)) ?RS\<close>
    have gc'_eq: \<open>gc' = (?F # drop ?k Xs, w')\<close> using gc' ck by simp
    have pr_ip: \<open>pr \<in> set (iprods G)\<close>
    proof -
      from dshape_prods[OF sh _ memR] have \<open>pr \<in> set (iprods G) \<or> pr = start_prod G Shn\<close> by simp
      moreover have \<open>pr \<noteq> start_prod G Shn\<close>
      proof
        assume \<open>pr = start_prod G Shn\<close>
        then have \<open>fst pr = Shn\<close> unfolding start_prod_def by simp
        then have \<open>?F = []\<close> using lgoto_Nt_Shn_empty[OF fn sh k_lt] by simp
        then show False using live unfolding gc'_eq dlive_def live_def by simp
      qed
      ultimately show ?thesis by simp
    qed
    let ?node = \<open>Node (fst pr) (rev (take ?k tstk))\<close>
    let ?tstk' = \<open>?node # drop ?k tstk\<close>
    let ?RAs' = \<open>?RS # drop ?k RAs\<close>
    have st'_eq: \<open>st' = ((?F # drop ?k Xs, w'), xclosure_auto G ?F # drop ?k cstk,
        dnext gt sts (istk ! ?k) (Nt (fst pr)) # drop ?k istk, v, ?tstk')\<close>
      using st' gc'_eq unfolding DReduce by simp
    have k_le: \<open>?k \<le> length tstk\<close> using k_lt lenX by simp
    have zip_drop: \<open>zip (map asym ?tstk') ?RAs' =
        (Nt (fst pr), ?RS) # drop ?k (zip (map asym tstk) RAs)\<close>
      by (simp add: drop_map drop_zip)
    have sh': \<open>dshape G Shn (?F # drop ?k Xs) (zip (map asym ?tstk') ?RAs')\<close>
      unfolding zip_drop using dshape_reduce[OF sh k_lt] .
    have real_node: \<open>realizes G ?node (Nt (fst pr), ?RS)\<close>
      unfolding realizes_def
    proof (intro ballI)
      fix j assume \<open>j \<in> irep_set (snd (Nt (fst pr), ?RS))\<close>
      then obtain R' where memR': \<open>((pr, ?k, R')) \<in> set (xclosure_auto G (Xs ! 0))\<close>
        and j: \<open>j \<in> irep_set R'\<close>
        by (auto simp: red_set_correct hdc hd0)
      have real_z: \<open>\<And>k'. k' < length (zip (map asym tstk) RAs) \<Longrightarrow>
          realizes G (tstk ! k') (zip (map asym tstk) RAs ! k')\<close>
        using real lenR by simp
      have len_eq: \<open>length tstk = length (zip (map asym tstk) RAs)\<close> using lenR by simp
      have k_le': \<open>?k \<le> length (zip (map asym tstk) RAs)\<close> using k_le lenR by simp
      from reduce_realizes[OF sh real_z len_eq memR' k_le' j pr_ip]
      show \<open>\<exists>pt. wf_ptree G pt \<and> erase pt = ?node \<and> proot pt = (fst (Nt (fst pr), ?RS), j)\<close>
        by simp
    qed
    have real': \<open>\<forall>k' < length ?tstk'. realizes G (?tstk' ! k') (asym (?tstk' ! k'), ?RAs' ! k')\<close>
    proof (intro allI impI)
      fix k' assume \<open>k' < length ?tstk'\<close>
      then show \<open>realizes G (?tstk' ! k') (asym (?tstk' ! k'), ?RAs' ! k')\<close>
        using real_node real lenR k_le by (cases k') auto
    qed
    have yld': \<open>w = concat (map ayield (rev ?tstk')) @ v\<close>
    proof -
      have rv: \<open>rev (drop ?k tstk) @ rev (take ?k tstk) = rev tstk\<close>
        by (metis append_take_drop_id rev_append)
      have \<open>concat (map ayield (rev ?tstk')) =
            concat (map ayield (rev (drop ?k tstk) @ rev (take ?k tstk)))\<close> by simp
      then show ?thesis using yld rv by simp
    qed
    show ?thesis unfolding st'_eq dinv_def
      using cstk_ok_push[OF cstk_ok_drop[OF okc]] len_i w' lenR k_le sh' real' yld' lenX k_lt
      by (auto intro!: exI[of _ ?RAs'])
  qed
qed

lemma dinv_final:
  assumes fn: \<open>fresh_name G Shn\<close>
    and inv: \<open>dinv G Shn w st\<close>
    and fin: \<open>gfinal G Shn (fst st)\<close>
  shows \<open>\<exists>t. (case st of (_, _, _, _, tstk) \<Rightarrow> tstk) = [t] \<and>
             ast_of G (Nt (istart G)) (istart_ind G) t w\<close>
proof -
  obtain gc cstk istk v tstk where st: \<open>st = (gc, cstk, istk, v, tstk)\<close> by (cases st)
  obtain Xs w' where gc: \<open>gc = (Xs, w')\<close> by (cases gc)
  from inv[unfolded st gc dinv_def] obtain RAs where
      w': \<open>w' = tcols v\<close>
    and lenR: \<open>length RAs = length tstk\<close>
    and sh: \<open>dshape G Shn Xs (zip (map asym tstk) RAs)\<close>
    and real: \<open>\<forall>k < length tstk. realizes G (tstk ! k) (asym (tstk ! k), RAs ! k)\<close>
    and yld: \<open>w = concat (map ayield (rev tstk)) @ v\<close>
    by auto
  have lenX: \<open>length Xs = length tstk + 1\<close> using sh lenR unfolding dshape_def by simp
  from fin[unfolded st gc] obtain pr R where w'_nil: \<open>w' = []\<close> and Xs_ne: \<open>Xs \<noteq> []\<close>
    and item: \<open>((pr, Suc 0, R)) \<in> set (hd Xs)\<close> and prShn: \<open>fst pr = Shn\<close>
    and i0: \<open>irep_mem (istart_ind G) R\<close>
    unfolding gfinal_def by (auto simp: list_ex_iff)
  have v_nil: \<open>v = []\<close> using w' w'_nil by (cases v) auto
  have tstk_ne: \<open>tstk \<noteq> []\<close>
  proof
    assume \<open>tstk = []\<close>
    then have \<open>Xs = [xinit G Shn]\<close> using lenX sh unfolding dshape_def by (cases Xs) auto
    then show False using item unfolding xinit_def by simp
  qed
  then have len_pos: \<open>0 < length tstk\<close> by simp
  have Xs0: \<open>Xs ! 0 = lgoto (xclosure_auto G (Xs ! Suc 0)) (asym (tstk ! 0)) (RAs ! 0)\<close>
    using sh len_pos lenR unfolding dshape_def by simp
  have hd0: \<open>hd Xs = Xs ! 0\<close> using Xs_ne by (simp add: hd_conv_nth)
  from lgoto_kernel_step[OF item[unfolded hd0 Xs0]] obtain R\<^sub>1 where
      item\<^sub>1: \<open>((pr, 0, R\<^sub>1)) \<in> set (xclosure_auto G (Xs ! Suc 0))\<close>
    and lt: \<open>0 < length (snd pr)\<close>
    and X0: \<open>fst (snd pr ! 0) = asym (tstk ! 0)\<close>
    and Req: \<open>R = irep_inter R\<^sub>1 (irep_pre (snd (snd pr ! 0)) (RAs ! 0))\<close> by blast
  have one_le: \<open>Suc 0 \<le> length (zip (map asym tstk) RAs)\<close> using len_pos lenR by (cases tstk) auto
  from dshape_prods[OF sh one_le item\<^sub>1] have pr_start: \<open>pr = start_prod G Shn\<close>
    using prShn fn unfolding fresh_name_def by force
  then have snd_pr: \<open>snd pr = [(Nt (istart G), Eq)]\<close> unfolding start_prod_def by simp
  have sym0: \<open>asym (tstk ! 0) = Nt (istart G)\<close> using X0 snd_pr by simp
  have i0_RA: \<open>istart_ind G \<in> irep_set (RAs ! 0)\<close> using i0 Req snd_pr by auto
  from real[rule_format, OF len_pos] i0_RA sym0 obtain pt where
      wf: \<open>wf_ptree G pt\<close> and er: \<open>erase pt = tstk ! 0\<close>
    and rt: \<open>proot pt = (Nt (istart G), istart_ind G)\<close>
    unfolding realizes_def by auto
  have len1: \<open>length tstk = 1\<close>
  proof -
    have \<open>((pr, 0, R\<^sub>1)) \<in> set (Xs ! Suc 0)\<close>
    proof -
      have \<open>((pr, 0, R\<^sub>1)) \<in> set (xslots G (Xs ! Suc 0) (xiter G (Xs ! Suc 0) (xfuel G (Xs ! Suc 0))))\<close>
        using item\<^sub>1 unfolding xclosure_auto_def xclosure_def by simp
      then show ?thesis
      proof (cases rule: xslots_memE)
        case (2 p)
        then have \<open>pr \<in> set (iprods G)\<close> using nth_mem by force
        then show ?thesis using pr_start fn unfolding start_prod_def fresh_name_def by force
      qed
    qed
    moreover have \<open>\<not> Suc 0 < length tstk\<close>
    proof
      assume \<open>Suc 0 < length tstk\<close>
      then have \<open>Xs ! Suc 0 = lgoto (xclosure_auto G (Xs ! Suc (Suc 0)))
          (asym (tstk ! Suc 0)) (RAs ! Suc 0)\<close>
        using sh lenR unfolding dshape_def by simp
      with \<open>((pr, 0, R\<^sub>1)) \<in> set (Xs ! Suc 0)\<close> show False using lgoto_dot_pos by fastforce
    qed
    ultimately show ?thesis using len_pos by (cases tstk) auto
  qed
  then obtain t where tstk_eq: \<open>tstk = [t]\<close> by (cases tstk) auto
  have \<open>ast_of G (Nt (istart G)) (istart_ind G) t w\<close>
    unfolding ast_of_def using wf er rt yld tstk_eq v_nil
    by (auto simp: pyield_erase intro!: exI[of _ pt])
  then show ?thesis using tstk_eq unfolding st by simp
qed

theorem drun_sound_ast:
  assumes fn: \<open>fresh_name G Shn\<close>
  shows \<open>drun G Shn gt sts redtab n st = Some t \<Longrightarrow> dinv G Shn w st \<Longrightarrow>
         ast_of G (Nt (istart G)) (istart_ind G) t w\<close>
proof (induction n arbitrary: st)
  case 0
  then have fin: \<open>gfinal G Shn (fst st)\<close>
    by (cases st) (auto split: if_splits)
  from dinv_final[OF fn 0(2) fin] 0(1) fin show ?case
    by (cases st) (auto split: if_splits)
next
  case (Suc n)
  show ?case
  proof (cases \<open>gfinal G Shn (fst st)\<close>)
    case True
    from dinv_final[OF fn Suc.prems(2) True] Suc.prems(1) True show ?thesis
      by (cases st) (auto split: if_splits)
  next
    case False
    with Suc.prems(1) obtain st\<^sub>1 where
        sp: \<open>dstep G gt sts redtab st = Some st\<^sub>1\<close>
      and rn: \<open>drun G Shn gt sts redtab n st\<^sub>1 = Some t\<close>
      by (cases st) (auto split: option.splits if_splits)
    from dstep_inv[OF fn Suc.prems(2) sp] have \<open>dinv G Shn w st\<^sub>1\<close> .
    from Suc.IH[OF rn this] show ?thesis .
  qed
qed

theorem dparse\<^sub>n_sound_ast:
  assumes fn: \<open>fresh_name G Shn\<close> and rec: \<open>dparse\<^sub>n G Shn fuel w = Some t\<close>
  shows \<open>ast_of G (Nt (istart G)) (istart_ind G) t w\<close>
  using drun_sound_ast[OF fn rec[unfolded dparse\<^sub>n_def Let_def] dinv_init] .

subsection \<open>The fuel-free driver\<close>

lemma drun\<^sub>w\<^sub>f_imp_drun_ex:
  assumes \<open>drun\<^sub>w\<^sub>f G Shn gt sts redtab st = Some t\<close>
  shows \<open>\<exists>n. drun G Shn gt sts redtab n st = Some t\<close>
proof (rule drun\<^sub>w\<^sub>f.raw_induct[OF _ assms], goal_cases)
  case (1 f G Shn gt sts redtab st t)
  obtain gc cstk istk v tstk where st: \<open>st = (gc, cstk, istk, v, tstk)\<close>
    by (cases st)
  show ?case
  proof (cases \<open>gfinal G Shn gc\<close>)
    case True
    with "1"(2)[unfolded st] obtain rest where \<open>tstk = t # rest\<close>
      by (cases tstk) auto
    with True have \<open>drun G Shn gt sts redtab 0 st = Some t\<close>
      unfolding st by simp
    then show ?thesis by blast
  next
    case False
    with "1"(2)[unfolded st] obtain st\<^sub>1 where
        sp: \<open>dstep G gt sts redtab (gc, cstk, istk, v, tstk) = Some st\<^sub>1\<close>
      and rec: \<open>f G Shn gt sts redtab st\<^sub>1 = Some t\<close>
      by (auto simp: bind_eq_Some_conv)
    from "1"(1)[OF rec] obtain n where
      \<open>drun G Shn gt sts redtab n st\<^sub>1 = Some t\<close> ..
    with False sp have \<open>drun G Shn gt sts redtab (Suc n) st = Some t\<close>
      unfolding st by simp
    then show ?thesis by blast
  qed
qed

subsection \<open>Repeated configurations: the code equation of \<^const>\<open>drun\<^sub>w\<^sub>f\<close>\<close>

text \<open>\<^const>\<open>drun\<^sub>w\<^sub>f\<close> is a least fixed point: a run that revisits a
  configuration denotes \<^const>\<open>None\<close>, but its unfolding equation, run as
  code, never returns.  Such runs exist for grammars the static check rejects
  (the command still emits their parser, with \<^text>\<open>mdet\<close> as a premise):
  a unit self-loop \<open>B = B\<close> whose reduce is licensed at the end of the input
  rebuilds the frame it just popped.  Generated code therefore runs
  \<^text>\<open>drun_hist\<close>, which records the configurations visited since the last
  shift and gives up on a repeat; \<^text>\<open>drun\<^sub>w\<^sub>f_code\<close> proves the two equal.
  The control part of a state is everything but the tree stack, and two
  states between the same shifts share the input, so only the stacks are
  compared.  A chain of reduces that grows the stack without bound is not
  caught.\<close>

type_synonym ('m, 'ch, 'n, 't) dctrl_t =
  \<open>('n, 't) gconfig \<times> ('n, 't) xitem list list \<times> nat list \<times> ('m, 'ch, 't) tword\<close>

type_synonym ('n, 't) dkey = \<open>('n, 't) xitem list list \<times> ('n, 't) xitem list list \<times> nat list\<close>

definition dctrl :: \<open>('m, 'ch, 'n, 't) dst \<Rightarrow> ('m, 'ch, 'n, 't) dctrl_t\<close> where
  \<open>dctrl st = (case st of (gc, cstk, istk, v, tstk) \<Rightarrow> (gc, cstk, istk, v))\<close>

definition ckey :: \<open>('m, 'ch, 'n, 't) dctrl_t \<Rightarrow> ('n, 't) dkey\<close> where
  \<open>ckey c = (case c of ((Xs, w), cstk, istk, v) \<Rightarrow> (Xs, cstk, istk))\<close>

definition cwv :: \<open>('m, 'ch, 'n, 't) dctrl_t \<Rightarrow> ('t \<times> nat) list \<times> ('m, 'ch, 't) tword\<close> where
  \<open>cwv c = (case c of ((Xs, w), cstk, istk, v) \<Rightarrow> (w, v))\<close>

lemma ctrl_eqI: \<open>ckey c = ckey d \<Longrightarrow> cwv c = cwv d \<Longrightarrow> c = d\<close>
  unfolding ckey_def cwv_def by (cases c; cases d) auto

text \<open>\<^const>\<open>dstep\<close>, with the action it took.\<close>

definition dstep_act :: \<open>('n, 't) is_cfg \<Rightarrow> (('n, 't) sym \<times> nat) list list \<Rightarrow>
    ('n, 't) citem list list \<Rightarrow> ('n, 't) lacell list list \<Rightarrow>
    ('m, 'ch, 'n, 't) dst \<Rightarrow> (('n, 't) dact \<times> ('m, 'ch, 'n, 't) dst) option\<close> where
  \<open>dstep_act G gt sts redtab st = (case st of (gc, cstk, istk, v, tstk) \<Rightarrow>
     let i = (case istk of [] \<Rightarrow> length sts | j # _ \<Rightarrow> j);
         cells = (if i < length redtab then redtab ! i else []);
         CL = (case cstk of [] \<Rightarrow> [] | c # _ \<Rightarrow> c)
     in (case dpick G cstk gc (dcands G i cells CL gc) of
        None \<Rightarrow> None
      | Some (act, gc') \<Rightarrow> Some (act, case act of
          DShift \<Rightarrow> (gc',
              xclosure_auto G (hd (fst gc')) # cstk,
              dnext gt sts i (Tm (tok (hd v))) # istk,
              tl v,
              Leaf (hd v) # tstk)
        | DReduce pr \<Rightarrow> (gc',
              xclosure_auto G (hd (fst gc')) # drop (length (snd pr)) cstk,
              dnext gt sts (istk ! length (snd pr)) (Nt (fst pr))
                # drop (length (snd pr)) istk,
              v,
              Node (fst pr) (rev (take (length (snd pr)) tstk))
                # drop (length (snd pr)) tstk))))\<close>

lemma dstep_eq_dstep_act:
  \<open>dstep G gt sts redtab st = map_option snd (dstep_act G gt sts redtab st)\<close>
  unfolding dstep_def dstep_act_def
  by (auto simp: Let_def split: prod.splits option.splits dact.splits)

lemma dstep_act_dctrl:
  assumes \<open>dctrl st\<^sub>1 = dctrl st\<^sub>2\<close>
  shows \<open>rel_option (\<lambda>(a, s) (b, t). a = b \<and> dctrl s = dctrl t)
           (dstep_act G gt sts redtab st\<^sub>1) (dstep_act G gt sts redtab st\<^sub>2)\<close>
proof -
  obtain gc cstk istk v tstk where s1: \<open>st\<^sub>1 = (gc, cstk, istk, v, tstk)\<close> by (cases st\<^sub>1)
  obtain gc' cstk' istk' v' tstk' where s2: \<open>st\<^sub>2 = (gc', cstk', istk', v', tstk')\<close> by (cases st\<^sub>2)
  from assms have eq: \<open>gc' = gc\<close> \<open>cstk' = cstk\<close> \<open>istk' = istk\<close> \<open>v' = v\<close>
    unfolding s1 s2 dctrl_def by auto
  show ?thesis unfolding s1 s2 eq dstep_act_def dctrl_def
    by (auto simp: Let_def split: option.splits dact.splits)
qed

lemma dstep_act_reduce_wv:
  assumes \<open>dstep_act G gt sts redtab st = Some (DReduce pr, st')\<close>
  shows \<open>cwv (dctrl st') = cwv (dctrl st)\<close>
proof -
  obtain gc cstk istk v tstk where st: \<open>st = (gc, cstk, istk, v, tstk)\<close> by (cases st)
  obtain Xs w where gc: \<open>gc = (Xs, w)\<close> by (cases gc)
  from assms obtain gc' where pick: \<open>dpick G cstk gc (dcands G (case istk of [] \<Rightarrow> length sts | j # _ \<Rightarrow> j)
        (if (case istk of [] \<Rightarrow> length sts | j # _ \<Rightarrow> j) < length redtab
         then redtab ! (case istk of [] \<Rightarrow> length sts | j # _ \<Rightarrow> j) else [])
        (case cstk of [] \<Rightarrow> [] | c # _ \<Rightarrow> c) gc) = Some (DReduce pr, gc')\<close>
    and st': \<open>st' = (gc', xclosure_auto G (hd (fst gc')) # drop (length (snd pr)) cstk,
              dnext gt sts (istk ! length (snd pr)) (Nt (fst pr)) # drop (length (snd pr)) istk, v,
              Node (fst pr) (rev (take (length (snd pr)) tstk)) # drop (length (snd pr)) tstk)\<close>
    unfolding st dstep_act_def by (auto simp: Let_def split: option.splits dact.splits)
  from dpick_sound[OF pick] have \<open>mstep_cached G cstk gc (DReduce pr) = Some gc'\<close> by simp
  then have \<open>snd gc' = w\<close>
    unfolding mstep_cached_def gc by (auto simp: Let_def split: if_splits)
  then show ?thesis unfolding st st' gc cwv_def dctrl_def by (cases gc') auto
qed

text \<open>The step on control parts, with \<^const>\<open>gfinal\<close> ending a run as
  \<^const>\<open>drun\<close> does; \<^text>\<open>crel\<close> is its graph, and a cycle in it makes
  every fuelled run fail.\<close>

definition cnext :: \<open>('n, 't) is_cfg \<Rightarrow> 'n \<Rightarrow> (('n, 't) sym \<times> nat) list list \<Rightarrow>
    ('n, 't) citem list list \<Rightarrow> ('n, 't) lacell list list \<Rightarrow>
    ('m, 'ch, 'n, 't) dctrl_t \<Rightarrow> (('n, 't) dact \<times> ('m, 'ch, 'n, 't) dctrl_t) option\<close> where
  \<open>cnext G Shn gt sts redtab c = (case c of (gc, cstk, istk, v) \<Rightarrow>
     if gfinal G Shn gc then None
     else map_option (\<lambda>(a, st'). (a, dctrl st')) (dstep_act G gt sts redtab (gc, cstk, istk, v, [])))\<close>

lemma cnext_dstep_act:
  assumes \<open>\<not> gfinal G Shn (fst (dctrl st))\<close>
  shows \<open>cnext G Shn gt sts redtab (dctrl st) =
         map_option (\<lambda>(a, st'). (a, dctrl st')) (dstep_act G gt sts redtab st)\<close>
proof -
  obtain gc cstk istk v tstk where st: \<open>st = (gc, cstk, istk, v, tstk)\<close> by (cases st)
  have \<open>dctrl (gc, cstk, istk, v, []) = dctrl st\<close> unfolding st dctrl_def by simp
  have rel: \<open>rel_option (\<lambda>(a, s) (b, t). a = b \<and> dctrl s = dctrl t)
      (dstep_act G gt sts redtab (gc, cstk, istk, v, [])) (dstep_act G gt sts redtab st)\<close>
    by (rule dstep_act_dctrl) (simp add: st dctrl_def)
  show ?thesis using assms rel unfolding st cnext_def
    by (cases \<open>dstep_act G gt sts redtab (gc, cstk, istk, v, [])\<close>;
        cases \<open>dstep_act G gt sts redtab (gc, cstk, istk, v, tstk)\<close>)
       (auto simp: dctrl_def)
qed

definition crel :: \<open>('n, 't) is_cfg \<Rightarrow> 'n \<Rightarrow> (('n, 't) sym \<times> nat) list list \<Rightarrow>
    ('n, 't) citem list list \<Rightarrow> ('n, 't) lacell list list \<Rightarrow>
    ('m, 'ch, 'n, 't) dctrl_t \<Rightarrow> ('m, 'ch, 'n, 't) dctrl_t \<Rightarrow> bool\<close> where
  \<open>crel G Shn gt sts redtab c d \<longleftrightarrow> (\<exists>a. cnext G Shn gt sts redtab c = Some (a, d))\<close>

lemma crel_det: \<open>crel G Shn gt sts redtab c d \<Longrightarrow> crel G Shn gt sts redtab c e \<Longrightarrow> d = e\<close>
  unfolding crel_def by auto

lemma crel_not_final:
  \<open>crel G Shn gt sts redtab (dctrl st) e \<Longrightarrow> \<not> gfinal G Shn (fst (dctrl st))\<close>
  unfolding crel_def cnext_def dctrl_def by (cases st) auto

lemma crel_step:
  assumes \<open>crel G Shn gt sts redtab (dctrl st) e\<close>
  obtains a st' where \<open>dstep_act G gt sts redtab st = Some (a, st')\<close> \<open>dctrl st' = e\<close>
proof -
  from assms obtain a where
    \<open>map_option (\<lambda>(a, st'). (a, dctrl st')) (dstep_act G gt sts redtab st) = Some (a, e)\<close>
    unfolding crel_def cnext_dstep_act[OF crel_not_final[OF assms]] by blast
  then show thesis by (cases \<open>dstep_act G gt sts redtab st\<close>) (auto intro: that)
qed

lemma drun_on_cycle_None:
  assumes \<open>(crel G Shn gt sts redtab)\<^sup>+\<^sup>+ c (dctrl st)\<close> \<open>(crel G Shn gt sts redtab)\<^sup>+\<^sup>+ (dctrl st) c\<close>
  shows \<open>drun G Shn gt sts redtab n st = None\<close>
  using assms
proof (induction n arbitrary: st)
  case (0 st)
  from converse_tranclpE[OF "0.prems"(2)] obtain e where \<open>crel G Shn gt sts redtab (dctrl st) e\<close>
    by blast
  from crel_not_final[OF this] show ?case by (cases st) (auto simp: dctrl_def)
next
  case (Suc n st)
  from converse_tranclpE[OF Suc.prems(2)] obtain e where e: \<open>crel G Shn gt sts redtab (dctrl st) e\<close>
    by blast
  note nf = crel_not_final[OF e]
  from crel_step[OF e] obtain a st' where
    step: \<open>dstep_act G gt sts redtab st = Some (a, st')\<close> and st': \<open>dctrl st' = e\<close> by blast
  have ce: \<open>(crel G Shn gt sts redtab)\<^sup>+\<^sup>+ c e\<close>
    using Suc.prems(1) e by (rule tranclp.trancl_into_trancl)
  have ec: \<open>(crel G Shn gt sts redtab)\<^sup>+\<^sup>+ e c\<close>
  proof (rule converse_tranclpE[OF Suc.prems(2)])
    assume \<open>crel G Shn gt sts redtab (dctrl st) c\<close>
    from crel_det[OF e this] have \<open>e = c\<close> .
    then show ?thesis using Suc.prems by (auto intro: tranclp_trans)
  next
    fix e' assume \<open>crel G Shn gt sts redtab (dctrl st) e'\<close> \<open>(crel G Shn gt sts redtab)\<^sup>+\<^sup>+ e' c\<close>
    with crel_det[OF e] show ?thesis by blast
  qed
  have \<open>drun G Shn gt sts redtab (Suc n) st = drun G Shn gt sts redtab n st'\<close>
    using nf step by (cases st) (auto simp: dctrl_def dstep_eq_dstep_act)
  also have \<open>\<dots> = None\<close> using Suc.IH[OF ce[unfolded st'[symmetric]] ec[unfolded st'[symmetric]]] .
  finally show ?case .
qed

lemma drun\<^sub>w\<^sub>f_on_cycle_None:
  assumes \<open>(crel G Shn gt sts redtab)\<^sup>+\<^sup>+ c (dctrl st)\<close> \<open>(crel G Shn gt sts redtab)\<^sup>+\<^sup>+ (dctrl st) c\<close>
  shows \<open>drun\<^sub>w\<^sub>f G Shn gt sts redtab st = None\<close>
  using drun\<^sub>w\<^sub>f_imp_drun_ex[of G Shn gt sts redtab st] drun_on_cycle_None[OF assms]
  by (cases \<open>drun\<^sub>w\<^sub>f G Shn gt sts redtab st\<close>) auto

text \<open>The driver with a history of the configurations since the last shift.\<close>

partial_function (option) drun_hist ::
  \<open>('n, 't) is_cfg \<Rightarrow> 'n \<Rightarrow> (('n, 't) sym \<times> nat) list list \<Rightarrow>
    ('n, 't) citem list list \<Rightarrow> ('n, 't) lacell list list \<Rightarrow> ('n, 't) dkey list \<Rightarrow>
    ('m, 'ch, 'n, 't) dst \<Rightarrow> ('m, 'ch, 'n, 't) ast option\<close>
  where
  \<open>drun_hist G Shn gt sts redtab seen st =
     (case st of (gc, cstk, istk, v, tstk) \<Rightarrow>
        if gfinal G Shn gc then (case tstk of t # _ \<Rightarrow> Some t | [] \<Rightarrow> None)
        else if ckey (dctrl st) \<in> set seen then None
        else Option.bind (dstep_act G gt sts redtab st) (\<lambda>(a, st').
               drun_hist G Shn gt sts redtab
                 (if a = DShift then [] else ckey (dctrl st) # seen) st'))\<close>

lemmas drun_hist_simps [code] = drun_hist.simps

text \<open>Every recorded configuration precedes the current one in \<^text>\<open>crel\<close>
  and shares its input, so a repeat is a cycle.\<close>

definition hist_ok :: \<open>('n, 't) is_cfg \<Rightarrow> 'n \<Rightarrow> (('n, 't) sym \<times> nat) list list \<Rightarrow>
    ('n, 't) citem list list \<Rightarrow> ('n, 't) lacell list list \<Rightarrow> ('n, 't) dkey list \<Rightarrow>
    ('m, 'ch, 'n, 't) dst \<Rightarrow> bool\<close> where
  \<open>hist_ok G Shn gt sts redtab seen st \<longleftrightarrow>
     (\<forall>k \<in> set seen. \<exists>c. ckey c = k \<and> cwv c = cwv (dctrl st) \<and>
        (crel G Shn gt sts redtab)\<^sup>+\<^sup>+ c (dctrl st))\<close>

lemma hist_ok_Nil [simp]: \<open>hist_ok G Shn gt sts redtab [] st\<close>
  unfolding hist_ok_def by simp

lemma hist_ok_seen_cycle:
  assumes \<open>hist_ok G Shn gt sts redtab seen st\<close> \<open>ckey (dctrl st) \<in> set seen\<close>
  shows \<open>drun\<^sub>w\<^sub>f G Shn gt sts redtab st = None\<close>
proof -
  from assms obtain c where \<open>ckey c = ckey (dctrl st)\<close> \<open>cwv c = cwv (dctrl st)\<close>
    and r: \<open>(crel G Shn gt sts redtab)\<^sup>+\<^sup>+ c (dctrl st)\<close> unfolding hist_ok_def by blast
  from ctrl_eqI[OF this(1,2)] r have \<open>(crel G Shn gt sts redtab)\<^sup>+\<^sup>+ (dctrl st) (dctrl st)\<close> by simp
  from drun\<^sub>w\<^sub>f_on_cycle_None[OF this this] show ?thesis .
qed

lemma hist_ok_step:
  assumes ok: \<open>hist_ok G Shn gt sts redtab seen st\<close>
    and nf: \<open>\<not> gfinal G Shn (fst (dctrl st))\<close>
    and step: \<open>dstep_act G gt sts redtab st = Some (a, st')\<close>
  shows \<open>hist_ok G Shn gt sts redtab (if a = DShift then [] else ckey (dctrl st) # seen) st'\<close>
proof (cases \<open>a = DShift\<close>)
  case True
  then show ?thesis by simp
next
  case False
  then obtain pr where a: \<open>a = DReduce pr\<close> by (cases a) auto
  have r: \<open>crel G Shn gt sts redtab (dctrl st) (dctrl st')\<close>
    unfolding crel_def cnext_dstep_act[OF nf] step by simp
  have wv: \<open>cwv (dctrl st') = cwv (dctrl st)\<close> using dstep_act_reduce_wv step[unfolded a] .
  show ?thesis
  proof (unfold hist_ok_def, intro ballI)
    fix k assume \<open>k \<in> set (if a = DShift then [] else ckey (dctrl st) # seen)\<close>
    with False have \<open>k = ckey (dctrl st) \<or> k \<in> set seen\<close> by simp
    then show \<open>\<exists>c. ckey c = k \<and> cwv c = cwv (dctrl st') \<and> (crel G Shn gt sts redtab)\<^sup>+\<^sup>+ c (dctrl st')\<close>
    proof
      assume \<open>k = ckey (dctrl st)\<close>
      then show ?thesis using r wv
        by (intro exI[where x = \<open>dctrl st\<close>] conjI) (simp_all add: tranclp.r_into_trancl)
    next
      assume \<open>k \<in> set seen\<close>
      with ok obtain c where \<open>ckey c = k\<close> \<open>cwv c = cwv (dctrl st)\<close>
        and \<open>(crel G Shn gt sts redtab)\<^sup>+\<^sup>+ c (dctrl st)\<close> unfolding hist_ok_def by blast
      then show ?thesis using r wv
        by (intro exI[where x = c] conjI) (simp_all add: tranclp.trancl_into_trancl)
    qed
  qed
qed

lemma drun_hist_imp_drun\<^sub>w\<^sub>f:
  assumes \<open>drun_hist G Shn gt sts redtab seen st = Some t\<close>
  shows \<open>hist_ok G Shn gt sts redtab seen st \<longrightarrow> drun\<^sub>w\<^sub>f G Shn gt sts redtab st = Some t\<close>
proof (rule drun_hist.raw_induct[OF _ assms], goal_cases)
  case (1 f G Shn gt sts redtab seen st t)
  obtain gc cstk istk v tstk where st: \<open>st = (gc, cstk, istk, v, tstk)\<close> by (cases st)
  show ?case
  proof (cases \<open>gfinal G Shn gc\<close>)
    case True
    with "1"(2)[unfolded st] obtain rest where \<open>tstk = t # rest\<close> by (cases tstk) auto
    with True show ?thesis unfolding st by simp
  next
    case False
    have nf: \<open>\<not> gfinal G Shn (fst (dctrl st))\<close> using False unfolding st dctrl_def by simp
    show ?thesis
    proof
      assume ok: \<open>hist_ok G Shn gt sts redtab seen st\<close>
      from False "1"(2) have nk: \<open>ckey (dctrl st) \<notin> set seen\<close>
        unfolding st by (auto split: if_splits)
      from False nk "1"(2) obtain a st\<^sub>1 where
          step: \<open>dstep_act G gt sts redtab st = Some (a, st\<^sub>1)\<close>
        and rec: \<open>f G Shn gt sts redtab (if a = DShift then [] else ckey (dctrl st) # seen) st\<^sub>1 = Some t\<close>
        unfolding st by (auto simp: bind_eq_Some_conv)
      from "1"(1)[OF rec] hist_ok_step[OF ok nf step]
      have \<open>drun\<^sub>w\<^sub>f G Shn gt sts redtab st\<^sub>1 = Some t\<close> by blast
      with False step show \<open>drun\<^sub>w\<^sub>f G Shn gt sts redtab st = Some t\<close>
        unfolding st by (simp add: dstep_eq_dstep_act)
    qed
  qed
qed

lemma drun_imp_drun_hist:
  assumes \<open>drun G Shn gt sts redtab n st = Some t\<close> \<open>hist_ok G Shn gt sts redtab seen st\<close>
  shows \<open>drun_hist G Shn gt sts redtab seen st = Some t\<close>
  using assms
proof (induction n arbitrary: st seen)
  case (0 st seen)
  obtain gc cstk istk v tstk where st: \<open>st = (gc, cstk, istk, v, tstk)\<close> by (cases st)
  show ?case using "0.prems"(1) unfolding st
    by (subst drun_hist_simps) (auto split: if_splits list.splits)
next
  case (Suc n st seen)
  obtain gc cstk istk v tstk where st: \<open>st = (gc, cstk, istk, v, tstk)\<close> by (cases st)
  show ?case
  proof (cases \<open>gfinal G Shn gc\<close>)
    case True
    with Suc.prems(1) show ?thesis unfolding st
      by (subst drun_hist_simps) (auto split: list.splits)
  next
    case False
    with Suc.prems(1) obtain st\<^sub>1 where sp: \<open>dstep G gt sts redtab st = Some st\<^sub>1\<close>
      and rec: \<open>drun G Shn gt sts redtab n st\<^sub>1 = Some t\<close>
      unfolding st by (auto split: option.splits)
    from sp obtain a where step: \<open>dstep_act G gt sts redtab st = Some (a, st\<^sub>1)\<close>
      unfolding dstep_eq_dstep_act by (cases \<open>dstep_act G gt sts redtab st\<close>) auto
    have nf: \<open>\<not> gfinal G Shn (fst (dctrl st))\<close> using False unfolding st dctrl_def by simp
    have nk: \<open>ckey (dctrl st) \<notin> set seen\<close>
    proof
      assume \<open>ckey (dctrl st) \<in> set seen\<close>
      from hist_ok_seen_cycle[OF Suc.prems(2) this] drun_imp_drun\<^sub>w\<^sub>f[OF Suc.prems(1)]
      show False by simp
    qed
    from Suc.IH[OF rec hist_ok_step[OF Suc.prems(2) nf step]]
    have ih: \<open>drun_hist G Shn gt sts redtab (if a = DShift then [] else ckey (dctrl st) # seen) st\<^sub>1
        = Some t\<close> .
    show ?thesis using False nk step ih unfolding st
      by (subst drun_hist_simps) simp
  qed
qed

theorem drun\<^sub>w\<^sub>f_eq_drun_hist:
  assumes \<open>hist_ok G Shn gt sts redtab seen st\<close>
  shows \<open>drun\<^sub>w\<^sub>f G Shn gt sts redtab st = drun_hist G Shn gt sts redtab seen st\<close>
proof (cases \<open>drun_hist G Shn gt sts redtab seen st\<close>)
  case None
  show ?thesis
  proof (cases \<open>drun\<^sub>w\<^sub>f G Shn gt sts redtab st\<close>)
    case (Some t)
    from drun\<^sub>w\<^sub>f_imp_drun_ex[OF Some] obtain n where \<open>drun G Shn gt sts redtab n st = Some t\<close> ..
    from drun_imp_drun_hist[OF this assms] None show ?thesis by simp
  qed (simp only: None)
next
  case (Some t)
  from drun_hist_imp_drun\<^sub>w\<^sub>f[OF Some] assms show ?thesis using Some by simp
qed

theorem drun\<^sub>w\<^sub>f_code [code]:
  \<open>drun\<^sub>w\<^sub>f G Shn gt sts redtab st = drun_hist G Shn gt sts redtab [] st\<close>
  by (rule drun\<^sub>w\<^sub>f_eq_drun_hist) simp

lemma dparse_imp_dparse\<^sub>n_ex:
  assumes \<open>dparse G Shn w = Some t\<close>
  shows \<open>\<exists>fuel. dparse\<^sub>n G Shn fuel w = Some t\<close>
  using assms drun\<^sub>w\<^sub>f_imp_drun_ex
  by (fastforce simp: dparse_def dparse\<^sub>n_def Let_def)

theorem dparse_sound_ast:
  assumes fn: \<open>fresh_name G Shn\<close> and rec: \<open>dparse G Shn w = Some t\<close>
  shows \<open>ast_of G (Nt (istart G)) (istart_ind G) t w\<close>
  using dparse_imp_dparse\<^sub>n_ex[OF rec] dparse\<^sub>n_sound_ast[OF fn] by blast

theorem dparse_sound:
  assumes \<open>fresh_name G Shn\<close> and \<open>dparse G Shn w = Some t\<close>
  shows \<open>w \<in> ilang G\<close>
  using dparse_sound_ast[OF assms] by (auto simp: ilang_iff_ast)

section \<open>Completeness\<close>

subsection \<open>Traces of parse trees\<close>

text \<open>The action trace of a wellformed parse tree: a leaf shifts, a node runs
  its children and reduces by its production.\<close>

inductive mtrace :: \<open>('n, 't) is_cfg \<Rightarrow> ('m, 'ch, 'n, 't) ptree \<Rightarrow> ('n, 't) dact list \<Rightarrow> bool\<close>
  for G where
  mt_leaf: \<open>mtrace G (PLeaf t) [DShift]\<close>
| mt_node: \<open>(A, rhs) \<in> set (iprods G) \<Longrightarrow>
    list_all2 (\<lambda>Xr pt. fst (proot pt) = fst Xr \<and>
      irel_sat (snd Xr) (snd (proot pt)) i) rhs pts \<Longrightarrow>
    list_all2 (mtrace G) pts trs \<Longrightarrow>
    mtrace G (PNode A i pts) (concat trs @ [DReduce (A, rhs)])\<close>

lemma mtrace_ex_list:
  \<open>\<forall>pt \<in> set pts. \<exists>tr. mtrace G pt tr \<Longrightarrow> \<exists>trs. list_all2 (mtrace G) pts trs\<close>
proof (induction pts)
  case Nil
  show ?case by (auto intro: exI[of _ \<open>[]\<close>])
next
  case (Cons pt pts')
  from Cons.prems obtain tr where tr: \<open>mtrace G pt tr\<close> by auto
  from Cons.prems Cons.IH obtain trs where trs: \<open>list_all2 (mtrace G) pts' trs\<close> by auto
  from tr trs show ?case by (auto intro: exI[of _ \<open>tr # trs\<close>])
qed

lemma mtrace_ex: \<open>wf_ptree G pt \<Longrightarrow> \<exists>acts. mtrace G pt acts\<close>
proof (induction pt)
  case (PLeaf t)
  show ?case by (intro exI[of _ \<open>[DShift]\<close>]) (rule mt_leaf)
next
  case (PNode A i pts)
  from PNode.prems obtain rhs where
    prod: \<open>(A, rhs) \<in> set (iprods G)\<close> and
    all2: \<open>list_all2 (\<lambda>Xr pt. fst (proot pt) = fst Xr \<and>
      irel_sat (snd Xr) (snd (proot pt)) i \<and> wf_ptree G pt) rhs pts\<close>
    by (auto elim: wf_ptree.cases)
  from all2 have \<open>\<forall>pt \<in> set pts. wf_ptree G pt\<close>
    by (auto simp: list_all2_conv_all_nth set_conv_nth)
  with PNode.IH have \<open>\<forall>pt \<in> set pts. \<exists>tr. mtrace G pt tr\<close> by auto
  from mtrace_ex_list[OF this] obtain trs where trs: \<open>list_all2 (mtrace G) pts trs\<close> by blast
  from all2 have all2': \<open>list_all2 (\<lambda>Xr pt. fst (proot pt) = fst Xr \<and>
      irel_sat (snd Xr) (snd (proot pt)) i) rhs pts\<close>
    by (auto elim!: list_all2_mono)
  from mt_node[OF prod all2' trs] show ?case ..
qed

lemma mtrace_node_last:
  assumes \<open>mtrace G (PNode A i pts) acts\<close>
  obtains rhs trs where \<open>acts = concat trs @ [DReduce (A, rhs)]\<close>
    and \<open>(A, rhs) \<in> set (iprods G)\<close>
    and \<open>list_all2 (\<lambda>Xr pt. fst (proot pt) = fst Xr \<and> irel_sat (snd Xr) (snd (proot pt)) i) rhs pts\<close>
    and \<open>list_all2 (mtrace G) pts trs\<close>
  using assms by (cases rule: mtrace.cases) auto

subsection \<open>Closure slots carry the relational images\<close>

lemma xclosure_auto_kernel_sub: \<open>set xs \<subseteq> set (xclosure_auto G xs)\<close>
  unfolding xclosure_auto_def xclosure_def xslots_def by simp

lemma xclosure_auto_slot:
  assumes mem: \<open>((pr, m, R)) \<in> set (xclosure_auto G xs)\<close>
    and m_lt: \<open>m < length (snd pr)\<close>
    and nxt: \<open>fst (snd pr ! m) = Nt B\<close>
    and brhs: \<open>(B, brhs) \<in> set (iprods G)\<close>
    and j: \<open>j \<in> irep_set R\<close>
    and sat: \<open>irel_sat (snd (snd pr ! m)) j' j\<close>
  shows \<open>\<exists>R'. (((B, brhs), 0, R')) \<in> set (xclosure_auto G xs) \<and> j' \<in> irep_set R'\<close>
proof -
  let ?cls = \<open>xiter G xs (xfuel G xs)\<close>
  have stable: \<open>xstable G xs ?cls\<close> by (rule xfuel_stable)
  obtain p where p: \<open>p < length (iprods G)\<close> and ip: \<open>iprods G ! p = (B, brhs)\<close>
    using brhs by (metis in_set_conv_nth)
  have len: \<open>length ?cls = length (iprods G)\<close> by simp
  have mem': \<open>((pr, m, R)) \<in> set (xslots G xs ?cls)\<close>
    using mem unfolding xclosure_auto_def xclosure_def .
  obtain A rhs where pr: \<open>pr = (A, rhs)\<close> by (cases pr)
  have img: \<open>j' \<in> ximg (iprods G ! p) (pr, m, R)\<close>
    unfolding ip pr using m_lt nxt j sat pr by auto
  have \<open>xround G xs ?cls ! p = fold (xcontrib (iprods G ! p)) (xslots G xs ?cls) (?cls ! p)\<close>
    by (rule xround_nth[OF len p])
  then have \<open>j' \<in> irep_set (xround G xs ?cls ! p)\<close>
    using fold_xcontrib_set[of \<open>iprods G ! p\<close> \<open>xslots G xs ?cls\<close> \<open>?cls ! p\<close>] img mem' by auto
  then have j'_slot: \<open>j' \<in> irep_set (?cls ! p)\<close>
    using xstableD[OF stable len p] by blast
  have \<open>(iprods G ! p, 0, ?cls ! p) \<in> set (xslots G xs ?cls)\<close>
    by (rule xslots_slot[OF p]) (simp add: len p)
  then show ?thesis
    using j'_slot ip unfolding xclosure_auto_def xclosure_def by auto
qed

subsection \<open>The runtime tables are the precise ones\<close>

text \<open>The driver indexes its frames by \<^const>\<open>pr0_states\<close>, the automaton of
  the reachable closure \<^const>\<open>creach\<close>.  A frame's closure
  \<^const>\<open>xclosure_auto\<close> has a slot for every production, but only its live
  slots (a non-empty anchor set) matter to the driver, and
  \<open>xclosure_auto_live_creach\<close> places every live slot in \<^const>\<open>creach\<close> of
  any state covering the frame's live kernel items.  So a precise state covers
  each frame's live core, and the goto table resolves every live symbol after a
  dot.\<close>

lemma cell_buckets_red_buckets: \<open>cell_buckets (la_fix G Shn) n = red_buckets G Shn n\<close>
  by (simp add: red_buckets_def)

subsection \<open>The table contract\<close>

text \<open>What the completeness proof needs from the three tables: the start
  state is present, the state list is closed under goto through the reachable
  closure \<^const>\<open>creach\<close>, the goto table resolves every symbol after a dot
  of a reachable item, and the cell table contains the start cell and is
  closed under \<^const>\<open>la_cell\<close>.\<close>

definition tables_ok :: \<open>('n, 't) is_cfg \<Rightarrow> 'n \<Rightarrow> ('n, 't) citem list list \<Rightarrow>
    (('n, 't) sym \<times> nat) list list \<Rightarrow> ('n, 't) lacell list \<Rightarrow> bool\<close> where
  \<open>tables_ok G Shn sts gt L \<longleftrightarrow>
     (\<exists>t \<in> set sts. set t = set (lr0_start G Shn)) \<and>
     (\<forall>s \<in> set sts. \<forall>X \<in> set (gram_syms G). \<exists>t \<in> set sts. set t = set (cgoto (creach G s) X)) \<and>
     (\<forall>s \<in> set sts. set s \<subseteq> cuniv G Shn) \<and>
     length gt = length sts \<and>
     (\<forall>i < length sts. \<forall>pr m. (pr, m) \<in> set (creach G (sts ! i)) \<longrightarrow> m < length (snd pr) \<longrightarrow>
         map_of (gt ! i) (fst (snd pr ! m)) =
           Some (st_find sts (cgoto (creach G (sts ! i)) (fst (snd pr ! m))))) \<and>
     set (la_start G Shn sts) \<subseteq> set L \<and>
     set (la_step G (ffix G) (nullables G) gt sts L) = set L\<close>

theorem tables_ok_concrete:
  \<open>tables_ok G Shn (pr0_states G Shn) (pgtab G (pr0_states G Shn)) (la_fix G Shn)\<close>
  unfolding tables_ok_def
proof (intro conjI)
  show \<open>\<exists>t \<in> set (pr0_states G Shn). set t = set (lr0_start G Shn)\<close>
    using pr0_states_start[of G Shn]
    by (auto simp: ccore_def xinit_def lr0_start_def start_prod_def)
  show \<open>\<forall>s \<in> set (pr0_states G Shn). \<forall>X \<in> set (gram_syms G).
      \<exists>t \<in> set (pr0_states G Shn). set t = set (cgoto (creach G s) X)\<close>
    by (intro ballI pr0_states_closed)
  show \<open>\<forall>s \<in> set (pr0_states G Shn). set s \<subseteq> cuniv G Shn\<close>
    by (intro ballI pr0_states_univ)
  show \<open>length (pgtab G (pr0_states G Shn)) = length (pr0_states G Shn)\<close> by simp
  show \<open>\<forall>i < length (pr0_states G Shn). \<forall>pr m.
      (pr, m) \<in> set (creach G (pr0_states G Shn ! i)) \<longrightarrow> m < length (snd pr) \<longrightarrow>
      map_of (pgtab G (pr0_states G Shn) ! i) (fst (snd pr ! m)) =
        Some (st_find (pr0_states G Shn)
                (cgoto (creach G (pr0_states G Shn ! i)) (fst (snd pr ! m))))\<close>
    by (intro allI impI pgtab_lookup)
  show \<open>set (la_start G Shn (pr0_states G Shn)) \<subseteq> set (la_fix G Shn)\<close>
    by (rule la_fix_start)
  show \<open>set (la_step G (ffix G) (nullables G) (pgtab G (pr0_states G Shn))
        (pr0_states G Shn) (la_fix G Shn)) = set (la_fix G Shn)\<close>
    using la_fix_stable[of G Shn] by simp
qed

text \<open>A symbol after a dot of a frame-closure item of a tabulated state is
  resolved by the goto table to a tabulated state.\<close>

lemma dnext_resolve:
  assumes tab: \<open>tables_ok G Shn sts gt L\<close> and i_lt: \<open>i < length sts\<close>
    and mem: \<open>(pr, m) \<in> set (creach G (sts ! i))\<close> and m_lt: \<open>m < length (snd pr)\<close>
  shows \<open>dnext gt sts i (fst (snd pr ! m)) < length sts\<close>
    and \<open>set (sts ! dnext gt sts i (fst (snd pr ! m))) =
      set (cgoto (creach G (sts ! i)) (fst (snd pr ! m)))\<close>
    and \<open>dnext gt sts i (fst (snd pr ! m)) = la_next gt sts i (fst (snd pr ! m))\<close>
proof -
  let ?X = \<open>fst (snd pr ! m)\<close>
  have s_in: \<open>sts ! i \<in> set sts\<close> using i_lt by simp
  have univ: \<open>set (sts ! i) \<subseteq> cuniv G Shn\<close> using tab s_in unfolding tables_ok_def by blast
  have \<open>(pr, m) \<in> cuniv G Shn\<close> using creach_univ[OF univ] mem by blast
  from cuniv_next_gram_syms[OF this m_lt] have X_sym: \<open>?X \<in> set (gram_syms G)\<close> .
  obtain t where \<open>t \<in> set sts\<close> and \<open>set t = set (cgoto (creach G (sts ! i)) ?X)\<close>
    using tab s_in X_sym unfolding tables_ok_def by blast
  from st_find_found[OF this]
  have sf_lt: \<open>st_find sts (cgoto (creach G (sts ! i)) ?X) < length sts\<close>
    and sf_set: \<open>set (sts ! st_find sts (cgoto (creach G (sts ! i)) ?X)) =
      set (cgoto (creach G (sts ! i)) ?X)\<close>
    by auto
  have lookup: \<open>map_of (gt ! i) ?X = Some (st_find sts (cgoto (creach G (sts ! i)) ?X))\<close>
    using tab i_lt mem m_lt unfolding tables_ok_def by blast
  have len_gt: \<open>length gt = length sts\<close> using tab unfolding tables_ok_def by blast
  have la: \<open>la_next gt sts i ?X = st_find sts (cgoto (creach G (sts ! i)) ?X)\<close>
    unfolding la_next_def lookup using sf_lt by simp
  have dn: \<open>dnext gt sts i ?X = la_next gt sts i ?X\<close>
    unfolding dnext_def using i_lt len_gt by simp
  show \<open>dnext gt sts i ?X < length sts\<close> using dn la sf_lt by simp
  show \<open>set (sts ! dnext gt sts i ?X) = set (cgoto (creach G (sts ! i)) ?X)\<close>
    using dn la sf_set by simp
  show \<open>dnext gt sts i ?X = la_next gt sts i ?X\<close> by (rule dn)
qed

subsection \<open>Cell-table closure, by rule\<close>

lemma la_cell_goto_mem:
  \<open>m < length (snd pr) \<Longrightarrow>
   (la_next gt sts i (fst (snd pr ! m)), (pr, Suc m), t, \<tau>) \<in> set (la_cell G ft ns gt sts (i, (pr, m), t, \<tau>))\<close>
  by simp

lemma la_cell_first_mem:
  assumes \<open>m < length (snd pr)\<close> and \<open>fst (snd pr ! m) = Nt B\<close> and \<open>br \<in> set (iprods G)\<close> and \<open>fst br = B\<close>
    and \<open>(a, \<sigma>) \<in> set (fscan ft ns (drop (Suc m) (snd pr)))\<close>
  shows \<open>(i, (br, 0), Some a, wcomp (winv (w_of (snd (snd pr ! m)))) (wemb \<sigma>))
           \<in> set (la_cell G ft ns gt sts (i, (pr, m), t, \<tau>))\<close>
  using assms by (force simp: Let_def)

lemma la_cell_inherit_mem:
  assumes \<open>m < length (snd pr)\<close> and \<open>fst (snd pr ! m) = Nt B\<close> and \<open>br \<in> set (iprods G)\<close> and \<open>fst br = B\<close>
    and \<open>list_all (\<lambda>(X, r). nsym ns X) (drop (Suc m) (snd pr))\<close>
  shows \<open>(i, (br, 0), t, wcomp (winv (w_of (snd (snd pr ! m)))) \<tau>)
           \<in> set (la_cell G ft ns gt sts (i, (pr, m), t, \<tau>))\<close>
  using assms by (force simp: Let_def)

lemma tables_ok_cell:
  assumes \<open>tables_ok G Shn sts gt L\<close> and \<open>c \<in> set L\<close>
    and \<open>x \<in> set (la_cell G (ffix G) (nullables G) gt sts c)\<close>
  shows \<open>x \<in> set L\<close>
proof -
  have \<open>x \<in> set (la_step G (ffix G) (nullables G) gt sts L)\<close>
    unfolding la_step_def using assms(2,3) by auto
  then show ?thesis using assms(1) unfolding tables_ok_def by blast
qed

subsection \<open>Frames of the set-anchored machine stay tabulated\<close>

text \<open>The \<^text>\<open>grun_cores\<close> argument transfers to \<^const>\<open>mrun\<close> verbatim:
  \<^text>\<open>set_ccore_lgoto\<close> says the set-valued goto has the same core as
  \<^const>\<open>cgoto\<close>, as \<^text>\<open>set_ccore_xgoto\<close> does for \<^const>\<open>xgoto\<close>.
  So every reachable frame's core is one of \<^const>\<open>lr0_states\<close>, which lets
  the driver's index stack track the frames.\<close>

lemma mstep_cores:
  assumes step: \<open>mstep G (Xs, w) act = Some (Xs', w')\<close>
    and ok: \<open>\<forall>f \<in> set Xs. cores_ok G Shn f\<close>
  shows \<open>\<forall>f \<in> set Xs'. cores_ok G Shn f\<close>
proof (cases act)
  case DShift
  from mstep_shift_shape[OF step[unfolded mstep_def DShift, simplified]]
  obtain a c w'' where w: \<open>w = (a, c) # w''\<close> and ne: \<open>Xs \<noteq> []\<close>
    and Xs': \<open>(Xs', w') = (lgoto (hd (map (xclosure_auto G) Xs)) (Tm a) (FinRep [c]) # Xs, w'')\<close>
    using step unfolding mstep_def DShift by (metis prod.inject)
  have hd_map: \<open>hd (map (xclosure_auto G) Xs) = xclosure_auto G (hd Xs)\<close>
    using ne by (simp add: hd_map)
  have hd_ok: \<open>cores_ok G Shn (hd Xs)\<close> using ok ne by simp
  have \<open>cores_ok G Shn (lgoto (xclosure_auto G (hd Xs)) (Tm a) (FinRep [c]))\<close>
    by (rule cores_ok_goto[OF hd_ok _ set_ccore_lgoto]) (simp add: set_ccore_xclosure_auto)
  then show ?thesis using ok Xs' hd_map by auto
next
  case (DReduce pr)
  let ?k = \<open>length (snd pr)\<close>
  from step[unfolded mstep_def DReduce]
  have k_lt: \<open>?k < length Xs\<close>
    and Xs': \<open>Xs' = lgoto (map (xclosure_auto G) Xs ! ?k) (Nt (fst pr))
                     (red_set (hd (map (xclosure_auto G) Xs)) pr) # drop ?k Xs\<close>
    unfolding mstep_cached_def by (auto simp: Let_def split: if_splits)
  have nth_map: \<open>map (xclosure_auto G) Xs ! ?k = xclosure_auto G (Xs ! ?k)\<close>
    using k_lt by simp
  have nth_ok: \<open>cores_ok G Shn (Xs ! ?k)\<close> using ok k_lt by simp
  have \<open>cores_ok G Shn (lgoto (xclosure_auto G (Xs ! ?k)) (Nt (fst pr))
           (red_set (hd (map (xclosure_auto G) Xs)) pr))\<close>
    by (rule cores_ok_goto[OF nth_ok _ set_ccore_lgoto]) (simp add: set_ccore_xclosure_auto)
  then show ?thesis using ok Xs' nth_map by (auto dest: in_set_dropD)
qed

lemma mreach_cores:
  \<open>mreach G Shn gc \<Longrightarrow> \<forall>f \<in> set (fst gc). cores_ok G Shn f\<close>
proof (induction rule: mreach.induct)
  case (mreach_init w)
  obtain t where \<open>t \<in> set (lr0_states G Shn)\<close> and \<open>set t = set (ccore (xinit G Shn))\<close>
    using lr0_states_start[of G Shn] by blast
  then show ?case unfolding cores_ok_def by auto
next
  case (mreach_step gc act gc')
  show ?case
    using mstep_cores[of G \<open>fst gc\<close> \<open>snd gc\<close> act \<open>fst gc'\<close> \<open>snd gc'\<close> Shn]
      mreach_step.hyps(2) mreach_step.IH by simp
qed

subsection \<open>The driver's index stack tracks the frames\<close>

text \<open>A non-empty set-valued goto witnesses a dotted occurrence of the goto
  symbol in the source frame's core, as \<^text>\<open>dnext_resolve\<close> needs.
  \<^const>\<open>dpick\<close> only commits to \<^const>\<open>dlive\<close> successors, and
  \<^const>\<open>dlive\<close> forces the new frame non-empty, so every driver step supplies
  that witness.\<close>

lemma lgoto_ne_sym:
  assumes \<open>lgoto xs X RA \<noteq> []\<close>
  obtains pr m where \<open>(pr, m) \<in> set (ccore xs)\<close>
    and \<open>m < length (snd pr)\<close> and \<open>fst (snd pr ! m) = X\<close>
proof -
  from assms obtain y where y: \<open>y \<in> set (lgoto xs X RA)\<close> by (cases \<open>lgoto xs X RA\<close>) auto
  from y obtain pr m R where mem: \<open>(pr, m, R) \<in> set xs\<close>
    and lt: \<open>m < length (snd pr)\<close> and Xeq: \<open>fst (snd pr ! m) = X\<close>
    unfolding lgoto_def by auto
  have \<open>(pr, m) \<in> set (ccore xs)\<close> using mem unfolding ccore_def by force
  from that[OF this lt Xeq] show ?thesis .
qed

definition didx_ok :: \<open>('n, 't) is_cfg \<Rightarrow> ('n, 't) citem list list \<Rightarrow>
    ('n, 't) xitem list list \<Rightarrow> nat list \<Rightarrow> bool\<close> where
  \<open>didx_ok G sts Xs istk \<longleftrightarrow> length istk = length Xs \<and>
     (\<forall>k < length Xs. lcore (Xs ! k) \<noteq> {} \<longrightarrow>
        istk ! k < length sts \<and> lcore (Xs ! k) \<subseteq> set (sts ! (istk ! k)))\<close>

lemma didx_okD:
  \<open>didx_ok G sts Xs istk \<Longrightarrow> k < length Xs \<Longrightarrow> lcore (Xs ! k) \<noteq> {} \<Longrightarrow>
     istk ! k < length sts \<and> lcore (Xs ! k) \<subseteq> set (sts ! (istk ! k))\<close>
  unfolding didx_ok_def by blast

lemma didx_ok_len: \<open>didx_ok G sts Xs istk \<Longrightarrow> length istk = length Xs\<close>
  unfolding didx_ok_def by blast

lemma didx_ok_init:
  assumes tab: \<open>tables_ok G Shn sts gt L\<close>
  shows \<open>didx_ok G sts [xinit G Shn] [st_find sts (lr0_start G Shn)]\<close>
proof -
  obtain t where t: \<open>t \<in> set sts\<close> and te: \<open>set t = set (lr0_start G Shn)\<close>
    using tab unfolding tables_ok_def by blast
  from st_find_found[OF t te] have lt: \<open>st_find sts (lr0_start G Shn) < length sts\<close>
    and eq: \<open>set (sts ! st_find sts (lr0_start G Shn)) = set (lr0_start G Shn)\<close> by auto
  show ?thesis unfolding didx_ok_def using lt eq by (simp add: lcore_xinit)
qed

text \<open>The step case: a live item of the goto frame comes from a live item of
  the source closure, which lies in \<^const>\<open>creach\<close> of the tracked state, so
  the lookup resolves and the target state covers the goto frame's live core.\<close>

lemma didx_ok_push:
  assumes tab: \<open>tables_ok G Shn sts gt L\<close>
    and ok: \<open>didx_ok G sts Xs istk\<close>
    and d_lt: \<open>d < length Xs\<close>
  shows \<open>didx_ok G sts (lgoto (xclosure_auto G (Xs ! d)) X RA # drop d Xs)
           (dnext gt sts (istk ! d) X # drop d istk)\<close>
proof -
  let ?F = \<open>lgoto (xclosure_auto G (Xs ! d)) X RA\<close>
  let ?j = \<open>dnext gt sts (istk ! d) X\<close>
  have len: \<open>length istk = length Xs\<close> by (rule didx_ok_len[OF ok])
  have top: \<open>?j < length sts \<and> lcore ?F \<subseteq> set (sts ! ?j)\<close> if live': \<open>lcore ?F \<noteq> {}\<close>
  proof -
    from live' obtain pr\<^sub>0 n\<^sub>0 R\<^sub>0' j\<^sub>0 where
      g0: \<open>(pr\<^sub>0, n\<^sub>0, R\<^sub>0') \<in> set ?F\<close> and j0: \<open>j\<^sub>0 \<in> irep_set R\<^sub>0'\<close>
      unfolding lcore_def by auto
    obtain m\<^sub>0 where n0: \<open>n\<^sub>0 = Suc m\<^sub>0\<close> using lgoto_dot_pos[OF g0] by (cases n\<^sub>0) auto
    from lgoto_kernel_step[OF g0[unfolded n0]] obtain R\<^sub>0 where
      src0: \<open>(pr\<^sub>0, m\<^sub>0, R\<^sub>0) \<in> set (xclosure_auto G (Xs ! d))\<close>
      and m0_lt: \<open>m\<^sub>0 < length (snd pr\<^sub>0)\<close> and X0: \<open>fst (snd pr\<^sub>0 ! m\<^sub>0) = X\<close>
      and R0': \<open>R\<^sub>0' = irep_inter R\<^sub>0 (irep_pre (snd (snd pr\<^sub>0 ! m\<^sub>0)) RA)\<close> .
    have j0R0: \<open>j\<^sub>0 \<in> irep_set R\<^sub>0\<close> using j0 unfolding R0' by auto
    have f_live: \<open>lcore (Xs ! d) \<noteq> {}\<close> by (rule closure_live_kernel[OF src0 j0R0])
    from didx_okD[OF ok d_lt f_live] have p_lt: \<open>istk ! d < length sts\<close>
      and cover: \<open>lcore (Xs ! d) \<subseteq> set (sts ! (istk ! d))\<close> by auto
    have kern: \<open>\<And>pr m R. (pr, m, R) \<in> set (Xs ! d) \<Longrightarrow> irep_nonempty R \<Longrightarrow>
        (pr, m) \<in> set (sts ! (istk ! d))\<close>
      using cover by (fastforce simp: lcore_def)
    have src0_cr: \<open>(pr\<^sub>0, m\<^sub>0) \<in> set (creach G (sts ! (istk ! d)))\<close>
      by (rule xclosure_auto_live_creach[OF kern src0 j0R0])
    have j_lt: \<open>?j < length sts\<close>
      and j_set: \<open>set (sts ! ?j) = set (cgoto (creach G (sts ! (istk ! d))) X)\<close>
      using dnext_resolve[OF tab p_lt src0_cr m0_lt] X0 by auto
    have cov': \<open>lcore ?F \<subseteq> set (sts ! ?j)\<close>
    proof
      fix c assume \<open>c \<in> lcore ?F\<close>
      then obtain pr\<^sub>2 n\<^sub>2 R\<^sub>2' where ceq: \<open>c = (pr\<^sub>2, n\<^sub>2)\<close>
        and g2: \<open>(pr\<^sub>2, n\<^sub>2, R\<^sub>2') \<in> set ?F\<close> and ne2: \<open>irep_nonempty R\<^sub>2'\<close>
        unfolding lcore_def by blast
      obtain j\<^sub>2 where j2: \<open>j\<^sub>2 \<in> irep_set R\<^sub>2'\<close> using ne2 by auto
      obtain m\<^sub>2 where n2: \<open>n\<^sub>2 = Suc m\<^sub>2\<close> using lgoto_dot_pos[OF g2] by (cases n\<^sub>2) auto
      from lgoto_kernel_step[OF g2[unfolded n2]] obtain R\<^sub>2 where
        src2: \<open>(pr\<^sub>2, m\<^sub>2, R\<^sub>2) \<in> set (xclosure_auto G (Xs ! d))\<close>
        and m2_lt: \<open>m\<^sub>2 < length (snd pr\<^sub>2)\<close> and X2: \<open>fst (snd pr\<^sub>2 ! m\<^sub>2) = X\<close>
        and R2': \<open>R\<^sub>2' = irep_inter R\<^sub>2 (irep_pre (snd (snd pr\<^sub>2 ! m\<^sub>2)) RA)\<close> .
      have j2R2: \<open>j\<^sub>2 \<in> irep_set R\<^sub>2\<close> using j2 unfolding R2' by auto
      have \<open>(pr\<^sub>2, m\<^sub>2) \<in> set (creach G (sts ! (istk ! d)))\<close>
        by (rule xclosure_auto_live_creach[OF kern src2 j2R2])
      from cgoto_memI[OF this m2_lt X2] show \<open>c \<in> set (sts ! ?j)\<close>
        unfolding ceq n2 j_set by simp
    qed
    show ?thesis using j_lt cov' by blast
  qed
  show ?thesis
    unfolding didx_ok_def
  proof (rule conjI)
    show \<open>length (?j # drop d istk) = length (?F # drop d Xs)\<close> using len by simp
  next
    show \<open>\<forall>k < length (?F # drop d Xs). lcore ((?F # drop d Xs) ! k) \<noteq> {} \<longrightarrow>
        (?j # drop d istk) ! k < length sts \<and>
        lcore ((?F # drop d Xs) ! k) \<subseteq> set (sts ! ((?j # drop d istk) ! k))\<close>
    proof (intro allI impI)
      fix k assume k_lt: \<open>k < length (?F # drop d Xs)\<close>
        and lv: \<open>lcore ((?F # drop d Xs) ! k) \<noteq> {}\<close>
      show \<open>(?j # drop d istk) ! k < length sts \<and>
          lcore ((?F # drop d Xs) ! k) \<subseteq> set (sts ! ((?j # drop d istk) ! k))\<close>
      proof (cases k)
        case 0
        show ?thesis unfolding 0 using top lv[unfolded 0] by simp
      next
        case (Suc k\<^sub>0)
        have k0: \<open>d + k\<^sub>0 < length Xs\<close> using k_lt Suc d_lt by simp
        have i1: \<open>(?j # drop d istk) ! Suc k\<^sub>0 = istk ! (d + k\<^sub>0)\<close> using k0 len by simp
        have i2: \<open>(?F # drop d Xs) ! Suc k\<^sub>0 = Xs ! (d + k\<^sub>0)\<close> using k0 by simp
        show ?thesis unfolding Suc i1 i2 using didx_okD[OF ok k0] lv Suc i2 by simp
      qed
    qed
  qed
qed

text \<open>A live closure item of the top frame lies in the reachable closure of the
  tracked state, and that state is in range.\<close>

lemma didx_ok_creach:
  assumes ok: \<open>didx_ok G sts Xs istk\<close> and ne: \<open>Xs \<noteq> []\<close>
    and mem: \<open>(pr, m, R) \<in> set (xclosure_auto G (hd Xs))\<close> and jR: \<open>j \<in> irep_set R\<close>
  shows \<open>hd istk < length sts\<close> and \<open>(pr, m) \<in> set (creach G (sts ! hd istk))\<close>
proof -
  have istk_ne: \<open>istk \<noteq> []\<close> using ok ne by (auto dest: didx_ok_len)
  have hd: \<open>istk ! 0 = hd istk\<close> \<open>Xs ! 0 = hd Xs\<close>
    using istk_ne ne by (simp_all add: hd_conv_nth)
  have live: \<open>lcore (hd Xs) \<noteq> {}\<close> by (rule closure_live_kernel[OF mem jR])
  from didx_okD[OF ok, of 0] ne live hd have lt: \<open>hd istk < length sts\<close>
    and cover: \<open>lcore (hd Xs) \<subseteq> set (sts ! hd istk)\<close> by auto
  show \<open>hd istk < length sts\<close> by (rule lt)
  have kern: \<open>\<And>pr' m' R'. (pr', m', R') \<in> set (hd Xs) \<Longrightarrow> irep_nonempty R' \<Longrightarrow>
      (pr', m') \<in> set (sts ! hd istk)\<close>
    using cover by (fastforce simp: lcore_def)
  show \<open>(pr, m) \<in> set (creach G (sts ! hd istk))\<close>
    by (rule xclosure_auto_live_creach[OF kern mem jR])
qed

lemma dlive_lcore: \<open>dlive (X # Xs, w) \<longleftrightarrow> lcore X \<noteq> {}\<close>
  unfolding dlive_def by (simp add: live_lcore)

lemma didx_ok_hd_lt:
  assumes ok: \<open>didx_ok G sts Xs istk\<close> and lv: \<open>dlive (Xs, w)\<close>
  shows \<open>hd istk < length sts\<close>
proof -
  have ne: \<open>Xs \<noteq> []\<close> and live: \<open>lcore (Xs ! 0) \<noteq> {}\<close>
    using lv unfolding dlive_def live_lcore by (auto simp: hd_conv_nth)
  have istk_ne: \<open>istk \<noteq> []\<close> using ok ne by (auto dest: didx_ok_len)
  show ?thesis using didx_okD[OF ok _ live] ne istk_ne by (simp add: hd_conv_nth)
qed

subsection \<open>Cell propagation: down to an item's children\<close>

text \<open>A cell for an item with \<^term>\<open>Nt B\<close> after the dot gives every
  production of \<^term>\<open>B\<close> a dot-0 cell in the same state, re-anchored through
  the occurrence's relation: with the FIRST token of the remaining right-hand
  side, or, when that remainder is nullable, with the parent's own token
  inherited.\<close>

lemma cell_child_first:
  assumes tab: \<open>tables_ok G Shn sts gt L\<close> and cell: \<open>(i, (pr, m), t, \<tau>) \<in> set L\<close>
    and m_lt: \<open>m < length (snd pr)\<close> and nxt: \<open>fst (snd pr ! m) = Nt B\<close>
    and br: \<open>br \<in> set (iprods G)\<close> and brB: \<open>fst br = B\<close>
    and fs: \<open>(a, \<sigma>) \<in> set (fscan (ffix G) (nullables G) (drop (Suc m) (snd pr)))\<close>
  shows \<open>(i, (br, 0), Some a, wcomp (winv (w_of (snd (snd pr ! m)))) (wemb \<sigma>)) \<in> set L\<close>
  by (rule tables_ok_cell[OF tab cell la_cell_first_mem[OF m_lt nxt br brB fs]])

lemma cell_child_inherit:
  assumes tab: \<open>tables_ok G Shn sts gt L\<close> and cell: \<open>(i, (pr, m), t, \<tau>) \<in> set L\<close>
    and m_lt: \<open>m < length (snd pr)\<close> and nxt: \<open>fst (snd pr ! m) = Nt B\<close>
    and br: \<open>br \<in> set (iprods G)\<close> and brB: \<open>fst br = B\<close>
    and nul: \<open>list_all (\<lambda>(X, r). nsym (nullables G) X) (drop (Suc m) (snd pr))\<close>
  shows \<open>(i, (br, 0), t, wcomp (winv (w_of (snd (snd pr ! m)))) \<tau>) \<in> set L\<close>
  by (rule tables_ok_cell[OF tab cell la_cell_inherit_mem[OF m_lt nxt br brB nul]])

text \<open>The relation side of both: composing the occurrence's inverse relation
  with the child-side relation lands the token's column against the child's
  anchor. This packages \<^text>\<open>wcomp_sound\<close>, \<^text>\<open>winv_sound\<close> and
  \<^text>\<open>w_of_sound\<close>.\<close>

lemma wsat_reanchor:
  assumes sat: \<open>irel_sat r j\<^sub>c j\<close> and tj: \<open>wsat \<tau> c j\<close>
  shows \<open>wsat (wcomp (winv (w_of r)) \<tau>) c j\<^sub>c\<close>
  by (rule wcomp_sound[OF tj winv_sound[OF w_of_sound[OF sat]]])

subsection \<open>The index-carrying machine\<close>

type_synonym ('n, 't) icfg = \<open>('n, 't) gconfig \<times> nat list\<close>

definition imstep :: \<open>('n, 't) is_cfg \<Rightarrow> (('n, 't) sym \<times> nat) list list \<Rightarrow> ('n, 't) citem list list \<Rightarrow>
    ('n, 't) icfg \<Rightarrow> ('n, 't) dact \<Rightarrow> ('n, 't) icfg option\<close> where
  \<open>imstep G gt sts ic act = (case ic of ((Xs, w), istk) \<Rightarrow>
     (case mstep G (Xs, w) act of None \<Rightarrow> None
      | Some gc' \<Rightarrow> Some (gc', (case act of
          DShift \<Rightarrow> dnext gt sts (hd istk) (Tm (fst (hd w))) # istk
        | DReduce pr \<Rightarrow> dnext gt sts (istk ! length (snd pr)) (Nt (fst pr))
                         # drop (length (snd pr)) istk))))\<close>

fun imrun :: \<open>('n, 't) is_cfg \<Rightarrow> (('n, 't) sym \<times> nat) list list \<Rightarrow> ('n, 't) citem list list \<Rightarrow>
    ('n, 't) dact list \<Rightarrow> ('n, 't) icfg \<Rightarrow> ('n, 't) icfg option\<close> where
  \<open>imrun G gt sts [] ic = Some ic\<close>
| \<open>imrun G gt sts (act # acts) ic =
     (case imstep G gt sts ic act of None \<Rightarrow> None | Some ic' \<Rightarrow> imrun G gt sts acts ic')\<close>

lemma imrun_append:
  \<open>imrun G gt sts (as @ bs) ic =
     (case imrun G gt sts as ic of None \<Rightarrow> None | Some ic' \<Rightarrow> imrun G gt sts bs ic')\<close>
  by (induction as arbitrary: ic) (auto split: option.splits)

lemma imstep_mstep: \<open>imstep G gt sts ic act = Some ic' \<Longrightarrow> mstep G (fst ic) act = Some (fst ic')\<close>
  unfolding imstep_def by (auto split: prod.splits option.splits)

lemma imrun_mrun: \<open>imrun G gt sts as ic = Some ic' \<Longrightarrow> mrun G as (fst ic) = Some (fst ic')\<close>
  by (induction as arbitrary: ic) (auto split: option.splits dest: imstep_mstep)

subsection \<open>Reachability of the index-carrying machine\<close>

text \<open>The configurations the driver can be in: from the initial frame and the
  start state, by steps whose successor is \<^const>\<open>dlive\<close>.  The determinism
  hypothesis below is stated over these, since the index of a frame is the one
  the driver built, not a function of the frame.\<close>

inductive imreach :: \<open>('n, 't) is_cfg \<Rightarrow> 'n \<Rightarrow> (('n, 't) sym \<times> nat) list list \<Rightarrow>
    ('n, 't) citem list list \<Rightarrow> ('n, 't) icfg \<Rightarrow> bool\<close> for G Shn gt sts where
  imreach_init: \<open>imreach G Shn gt sts (([xinit G Shn], w), [st_find sts (lr0_start G Shn)])\<close>
| imreach_step: \<open>imreach G Shn gt sts ic \<Longrightarrow> imstep G gt sts ic act = Some ic' \<Longrightarrow>
    dlive (fst ic') \<Longrightarrow> imreach G Shn gt sts ic'\<close>

lemma imreach_mreach: \<open>imreach G Shn gt sts ic \<Longrightarrow> mreach G Shn (fst ic)\<close>
  by (induction rule: imreach.induct) (auto intro: mreach_init mreach_step dest: imstep_mstep)

lemma imreach_dlive: \<open>imreach G Shn gt sts ic \<Longrightarrow> dlive (fst ic)\<close>
  by (induction rule: imreach.induct)
     (auto simp: dlive_lcore lcore_xinit lr0_start_def)

text \<open>The index invariant along the machine: each step pushes through
  \<^const>\<open>dnext\<close> from a frame the stack tracks.\<close>

lemma imstep_didx_ok:
  assumes tab: \<open>tables_ok G Shn sts gt L\<close> and ok: \<open>didx_ok G sts Xs istk\<close>
    and step: \<open>imstep G gt sts ((Xs, w), istk) act = Some ((Xs', w'), istk')\<close>
  shows \<open>didx_ok G sts Xs' istk'\<close>
proof (cases act)
  case DShift
  have ms: \<open>mstep G (Xs, w) DShift = Some (Xs', w')\<close>
    using imstep_mstep[OF step] DShift by simp
  from mstep_shift_shape[OF ms[unfolded mstep_def, simplified]]
  obtain a c w'' where w: \<open>w = (a, c) # w''\<close> and ne: \<open>Xs \<noteq> []\<close>
    and Xs': \<open>(Xs', w') = (lgoto (hd (map (xclosure_auto G) Xs)) (Tm a) (FinRep [c]) # Xs, w'')\<close>
    using ms unfolding mstep_def by (metis prod.inject)
  have istk': \<open>istk' = dnext gt sts (hd istk) (Tm a) # istk\<close>
    using step[unfolded imstep_def DShift w] ms[unfolded w] by simp
  have istk_ne: \<open>istk \<noteq> []\<close> using ne didx_ok_len[OF ok] by auto
  have hd0: \<open>Xs ! 0 = hd Xs\<close> and i0: \<open>istk ! 0 = hd istk\<close>
    using ne istk_ne by (simp_all add: hd_conv_nth)
  have \<open>didx_ok G sts (lgoto (xclosure_auto G (Xs ! 0)) (Tm a) (FinRep [c]) # drop 0 Xs)
      (dnext gt sts (istk ! 0) (Tm a) # drop 0 istk)\<close>
    by (rule didx_ok_push[OF tab ok]) (use ne in simp)
  then show ?thesis using Xs' istk' ne hd0 i0 by (simp add: hd_map)
next
  case (DReduce pr)
  let ?k = \<open>length (snd pr)\<close>
  have ms: \<open>mstep G (Xs, w) (DReduce pr) = Some (Xs', w')\<close>
    using imstep_mstep[OF step] DReduce by simp
  from ms[unfolded mstep_def]
  have k_lt: \<open>?k < length Xs\<close>
    and Xs': \<open>Xs' = lgoto (map (xclosure_auto G) Xs ! ?k) (Nt (fst pr))
                     (red_set (hd (map (xclosure_auto G) Xs)) pr) # drop ?k Xs\<close>
    unfolding mstep_cached_def by (auto simp: Let_def split: if_splits)
  have istk': \<open>istk' = dnext gt sts (istk ! ?k) (Nt (fst pr)) # drop ?k istk\<close>
    using step unfolding imstep_def DReduce by (simp add: ms)
  have nth_map: \<open>map (xclosure_auto G) Xs ! ?k = xclosure_auto G (Xs ! ?k)\<close>
    using k_lt by simp
  show ?thesis unfolding Xs' istk' nth_map by (rule didx_ok_push[OF tab ok k_lt])
qed

lemma imreach_didx_ok:
  assumes tab: \<open>tables_ok G Shn sts gt L\<close>
  shows \<open>imreach G Shn gt sts ic \<Longrightarrow> didx_ok G sts (fst (fst ic)) (snd ic)\<close>
proof (induction rule: imreach.induct)
  case (imreach_init w)
  show ?case using didx_ok_init[OF tab] by simp
next
  case (imreach_step ic act ic')
  obtain gc istk where ic: \<open>ic = (gc, istk)\<close> by (cases ic)
  obtain Xs w where gc: \<open>gc = (Xs, w)\<close> by (cases gc)
  obtain gc' istk' where ic': \<open>ic' = (gc', istk')\<close> by (cases ic')
  obtain Xs' w' where gc': \<open>gc' = (Xs', w')\<close> by (cases gc')
  show ?case
    using imstep_didx_ok[OF tab imreach_step.IH[unfolded ic gc, simplified]
        imreach_step.hyps(2)[unfolded ic gc ic' gc']]
    unfolding ic' gc' by simp
qed

subsection \<open>Licensing of the reduces along a run\<close>

definition dlic_L :: \<open>nat \<Rightarrow> ('n, 't) lacell list \<Rightarrow> ('t \<times> nat) list \<Rightarrow> 'n \<times> ('n, 't) rhs \<Rightarrow> indrep \<Rightarrow> bool\<close> where
  \<open>dlic_L i L w pr RS \<longleftrightarrow> (\<exists>t \<tau>. (i, (pr, length (snd pr)), t, \<tau>) \<in> set L \<and>
       (case w of [] \<Rightarrow> t = None | (a, c) # _ \<Rightarrow> t = Some a \<and> irep_ex_wsat \<tau> c RS))\<close>

lemma dlic_buckets:
  assumes i_lt: \<open>i < n\<close>
  shows \<open>dlic i (cell_buckets L n ! i) w pr RS \<longleftrightarrow> dlic_L i L w pr RS\<close>
proof -
  let ?P = \<open>\<lambda>(i', itm, t, \<tau>). i' = i \<and> itm = (pr, length (snd pr)) \<and>
       (case w of [] \<Rightarrow> t = None
                | (a, c) # _ \<Rightarrow> t = Some a \<and> irep_ex_wsat \<tau> c RS)\<close>
  have nth: \<open>cell_buckets L n ! i = filter (\<lambda>(i', itm, t, \<tau>). i' = i)
      (filter (\<lambda>(i, itm, t, \<tau>). snd itm = length (snd (fst itm))) L)\<close>
    unfolding cell_buckets_def Let_def using i_lt by simp
  have keep: \<open>?P c \<Longrightarrow> (case c of (i', itm, t, \<tau>) \<Rightarrow> snd itm = length (snd (fst itm))) \<and>
                      (case c of (i', itm, t, \<tau>) \<Rightarrow> i' = i)\<close> for c
    by (cases c) auto
  have a: \<open>dlic i (cell_buckets L n ! i) w pr RS \<longleftrightarrow> (\<exists>c \<in> set (cell_buckets L n ! i). ?P c)\<close>
    unfolding dlic_def by (simp add: list_ex_iff)
  have b: \<open>(\<exists>c \<in> set (cell_buckets L n ! i). ?P c) \<longleftrightarrow> (\<exists>c \<in> set L. ?P c)\<close>
  proof
    assume \<open>\<exists>c \<in> set (cell_buckets L n ! i). ?P c\<close>
    then obtain cc where \<open>cc \<in> set (cell_buckets L n ! i)\<close> and cp: \<open>?P cc\<close> by blast
    then have \<open>cc \<in> set L\<close> unfolding nth by simp
    with cp show \<open>\<exists>c \<in> set L. ?P c\<close> by blast
  next
    assume \<open>\<exists>c \<in> set L. ?P c\<close>
    then obtain cc where cm: \<open>cc \<in> set L\<close> and cp: \<open>?P cc\<close> by blast
    obtain i' itm t \<tau> where ceq: \<open>cc = (i', itm, t, \<tau>)\<close> by (cases cc)
    from cp ceq have e1: \<open>i' = i\<close> and e2: \<open>itm = (pr, length (snd pr))\<close> by auto
    have \<open>cc \<in> set (cell_buckets L n ! i)\<close>
      unfolding nth using cm ceq e1 e2 by simp
    with cp show \<open>\<exists>c \<in> set (cell_buckets L n ! i). ?P c\<close> by blast
  qed
  have c: \<open>(\<exists>c \<in> set L. ?P c) \<longleftrightarrow> dlic_L i L w pr RS\<close>
  proof
    assume \<open>\<exists>c \<in> set L. ?P c\<close>
    then obtain cc where cm: \<open>cc \<in> set L\<close> and cp: \<open>?P cc\<close> by blast
    obtain i' itm t \<tau> where ceq: \<open>cc = (i', itm, t, \<tau>)\<close> by (cases cc)
    from cp ceq have e1: \<open>i' = i\<close> and e2: \<open>itm = (pr, length (snd pr))\<close>
      and wc: \<open>case w of [] \<Rightarrow> t = None
                       | (a, cl) # _ \<Rightarrow> t = Some a \<and> irep_ex_wsat \<tau> cl RS\<close> by auto
    show \<open>dlic_L i L w pr RS\<close>
      unfolding dlic_L_def using cm ceq e1 e2 wc by auto
  next
    assume \<open>dlic_L i L w pr RS\<close>
    then obtain t \<tau> where m: \<open>(i, (pr, length (snd pr)), t, \<tau>) \<in> set L\<close>
      and wc: \<open>case w of [] \<Rightarrow> t = None
                       | (a, cl) # _ \<Rightarrow> t = Some a \<and> irep_ex_wsat \<tau> cl RS\<close>
      unfolding dlic_L_def by blast
    show \<open>\<exists>c \<in> set L. ?P c\<close>
      by (rule bexI[of _ \<open>(i, (pr, length (snd pr)), t, \<tau>)\<close>]) (use m wc in auto)
  qed
  show ?thesis using a b c by simp
qed

definition lic_at :: \<open>('n, 't) is_cfg \<Rightarrow> ('n, 't) lacell list \<Rightarrow> ('n, 't) citem list list \<Rightarrow>
    ('n, 't) icfg \<Rightarrow> 'n \<times> ('n, 't) rhs \<Rightarrow> bool\<close> where
  \<open>lic_at G L sts ic pr \<longleftrightarrow> (case ic of ((Xs, w), istk) \<Rightarrow>
     hd istk < length sts \<and> dlic_L (hd istk) L w pr (red_set (xclosure_auto G (hd Xs)) pr))\<close>

subsection \<open>Nullability of an empty-yield subtree\<close>

text \<open>A wellformed parse tree with empty yield has a nullable root symbol (via
  \<^text>\<open>derives_iff_ptree\<close> and \<^text>\<open>nullables_complete\<close>); the
  ``all later siblings are nullable'' case of the licensing argument needs this.\<close>

lemma wf_ptree_nullable_root:
  fixes pts :: \<open>('m, 'ch, 'n, 't) ptree list\<close>
  assumes \<open>wf_ptree G (PNode A j pts)\<close> and \<open>pyield (PNode A j pts) = []\<close>
  shows \<open>A \<in> set (nullables G)\<close>
proof -
  have \<open>\<exists>pt. wf_ptree G pt \<and> proot pt = (Nt A, j) \<and> pyield pt = ([] :: ('m, 'ch, 't) tword)\<close>
    using assms by (intro exI[of _ \<open>PNode A j pts\<close>]) simp
  then have \<open>infG G \<turnstile> [Nt (A, j)] \<Rightarrow>* map Tm (tcols ([] :: ('m, 'ch, 't) tword))\<close>
    unfolding derives_iff_ptree by blast
  then obtain n where \<open>infG G \<turnstile> [Nt (A, j)] \<Rightarrow>(n) []\<close>
    by (auto dest!: rtranclp_imp_relpowp)
  from nullables_complete[OF this] show ?thesis .
qed

lemma wf_ptree_nsym_of_empty_yield:
  \<open>wf_ptree G pt \<Longrightarrow> pyield pt = [] \<Longrightarrow> nsym (nullables G) (fst (proot pt))\<close>
  by (cases pt) (auto simp: nsym_def dest: wf_ptree_nullable_root)

subsection \<open>The lookahead of a subtree's continuation\<close>

text \<open>\<^text>\<open>cell_ok G L i pr rest j\<close>: state \<open>i\<close> has a dot-0 cell for \<open>pr\<close>
  whose token is what follows the subtree and whose relation places that
  token's column against the subtree's own anchor \<open>j\<close>. This is the context a
  subtree inherits from its parent and what licenses its reduce.\<close>

definition cell_ok :: \<open>('n, 't) lacell list \<Rightarrow> nat \<Rightarrow> 'n \<times> ('n, 't) rhs \<Rightarrow> nat \<Rightarrow>
    ('t \<times> nat) list \<Rightarrow> nat \<Rightarrow> bool\<close> where
  \<open>cell_ok L i pr m rest j \<longleftrightarrow> (\<exists>\<tau>. (i, (pr, m), tok_of rest, \<tau>) \<in> set L \<and>
     (case rest of [] \<Rightarrow> True | (a, c) # _ \<Rightarrow> wsat \<tau> c j))\<close>

lemma cell_ok_dlic:
  assumes \<open>cell_ok L i pr (length (snd pr)) rest j\<close> and \<open>j \<in> irep_set RS\<close>
  shows \<open>dlic_L i L rest pr RS\<close>
  using assms unfolding cell_ok_def dlic_L_def
  by (cases rest) (auto intro!: bexI[of _ j])

text \<open>Down to a child: the parent's cell for \<open>(pr, m)\<close> gives the child's
  production a dot-0 cell in the same state, with the child's own anchor as
  reference. Case split on whether the material after the child in the parent's
  right-hand side yields a token (FIRST) or is nullable (inherit).\<close>

lemma cell_ok_child:
  assumes tab: \<open>tables_ok G Shn sts gt L\<close>
    and cell: \<open>cell_ok L i pr m rest j\<close>
    and m_lt: \<open>m < length (snd pr)\<close>
    and nxt: \<open>fst (snd pr ! m) = Nt B\<close>
    and br: \<open>br \<in> set (iprods G)\<close> and brB: \<open>fst br = B\<close>
    and sat: \<open>irel_sat (snd (snd pr ! m)) j\<^sub>c j\<close>
    and split: \<open>rest\<^sub>c = suf @ rest\<close>
    and suf_first:
      \<open>suf \<noteq> [] \<Longrightarrow> \<exists>\<sigma>. (fst (hd suf), \<sigma>) \<in> set (fscan (ffix G) (nullables G) (drop (Suc m) (snd pr)))
                       \<and> csat \<sigma> (snd (hd suf)) j\<close>
    and suf_null: \<open>suf = [] \<Longrightarrow> list_all (\<lambda>(X, r). nsym (nullables G) X) (drop (Suc m) (snd pr))\<close>
  shows \<open>cell_ok L i br 0 rest\<^sub>c j\<^sub>c\<close>
proof (cases suf)
  case Nil
  from cell obtain \<tau> where mem: \<open>(i, (pr, m), tok_of rest, \<tau>) \<in> set L\<close>
    and rel: \<open>case rest of [] \<Rightarrow> True | (a, c) # _ \<Rightarrow> wsat \<tau> c j\<close>
    unfolding cell_ok_def by blast
  from cell_child_inherit[OF tab mem m_lt nxt br brB suf_null[OF Nil]]
  have \<open>(i, (br, 0), tok_of rest, wcomp (winv (w_of (snd (snd pr ! m)))) \<tau>) \<in> set L\<close> .
  moreover have \<open>case rest of [] \<Rightarrow> True
      | (a, c) # _ \<Rightarrow> wsat (wcomp (winv (w_of (snd (snd pr ! m)))) \<tau>) c j\<^sub>c\<close>
    using rel wsat_reanchor[OF sat] by (cases rest) auto
  ultimately show ?thesis using split Nil unfolding cell_ok_def by auto
next
  case (Cons x v)
  obtain a c where x: \<open>x = (a, c)\<close> by (cases x)
  from cell obtain \<tau> where mem: \<open>(i, (pr, m), tok_of rest, \<tau>) \<in> set L\<close>
    unfolding cell_ok_def by blast
  from suf_first[OF _] Cons x obtain \<sigma> where
      fs: \<open>(a, \<sigma>) \<in> set (fscan (ffix G) (nullables G) (drop (Suc m) (snd pr)))\<close>
    and cs: \<open>csat \<sigma> c j\<close> by auto
  from cell_child_first[OF tab mem m_lt nxt br brB fs]
  have inL: \<open>(i, (br, 0), Some a, wcomp (winv (w_of (snd (snd pr ! m)))) (wemb \<sigma>)) \<in> set L\<close> .
  have \<open>wsat (wcomp (winv (w_of (snd (snd pr ! m)))) (wemb \<sigma>)) c j\<^sub>c\<close>
    by (rule wsat_reanchor[OF sat wemb_sound[OF cs]])
  moreover have \<open>tok_of rest\<^sub>c = Some a\<close> using split Cons x by simp
  ultimately show ?thesis using inL split Cons x unfolding cell_ok_def by auto
qed

subsection \<open>What \<^const>\<open>dcands\<close> offers\<close>

text \<open>The shift is offered unconditionally while input remains, so the shift
  case of ``the driver follows the trace'' needs no licensing. A reduce is
  offered iff the frame closure completes the production with a non-empty
  anchor set and the cell table licenses it.\<close>

lemma dcands_shift:
  assumes \<open>fst gc \<noteq> []\<close> and \<open>snd gc \<noteq> []\<close>
  shows \<open>DShift \<in> set (dcands G i cells CL gc)\<close>
  using assms unfolding dcands_def by (cases gc) (auto simp: Let_def split: list.splits)

lemma dcands_reduceI:
  assumes ne: \<open>fst gc \<noteq> []\<close>
    and comp: \<open>(pr, length (snd pr), R) \<in> set CL\<close>
    and RS_ne: \<open>irep_nonempty (red_set CL pr)\<close>
    and lic: \<open>dlic i cells (snd gc) pr (red_set CL pr)\<close>
  shows \<open>DReduce pr \<in> set (dcands G i cells CL gc)\<close>
proof -
  obtain Xs w where gc: \<open>gc = (Xs, w)\<close> by (cases gc)
  have \<open>pr \<in> set (remdups (map fst (filter (\<lambda>(pr, m, R). m = length (snd pr)) CL)))\<close>
    using comp by force
  then have \<open>DReduce pr \<in> set (map DReduce (filter (\<lambda>pr. let RS = red_set CL pr in
                  irep_nonempty RS \<and> dlic i cells w pr RS)
                (remdups (map fst (filter (\<lambda>(pr, m, R). m = length (snd pr)) CL)))))\<close>
    using RS_ne lic gc by (simp add: Let_def)
  then show ?thesis
    using ne unfolding dcands_def gc by (cases w) (simp_all add: Let_def)
qed

lemma dcands_reduceD:
  assumes \<open>DReduce pr \<in> set (dcands G i cells CL gc)\<close>
  shows \<open>(\<exists>R. (pr, length (snd pr), R) \<in> set CL) \<and>
         irep_nonempty (red_set CL pr) \<and> dlic i cells (snd gc) pr (red_set CL pr)\<close>
proof -
  obtain Xs w where gc: \<open>gc = (Xs, w)\<close> by (cases gc)
  from assms have ne: \<open>Xs \<noteq> []\<close> unfolding dcands_def gc by (auto split: if_splits)
  from assms have
    \<open>pr \<in> set (filter (\<lambda>pr. let RS = red_set CL pr in
        irep_nonempty RS \<and> dlic i cells w pr RS)
        (remdups (map fst (filter (\<lambda>(pr, m, R). m = length (snd pr)) CL))))\<close>
    unfolding dcands_def gc using ne
    by (cases w) (auto simp: Let_def)
  then show ?thesis unfolding gc by (force simp: Let_def)
qed

subsection \<open>Determinism: the hypothesis \<^const>\<open>dpick\<close> needs\<close>

text \<open>
  The obligation \<^const>\<open>dpick\<close> needs is stated operationally, without
  reference to a static report: at a reachable configuration no two distinct
  candidates may both have live successors. A conflict report is a sufficient
  condition for this, not its definition.
\<close>

definition mdet :: \<open>('n, 't) is_cfg \<Rightarrow> 'n \<Rightarrow> bool\<close> where
  \<open>mdet G Shn \<longleftrightarrow> (\<forall>gc istk i redtab CL a\<^sub>1 a\<^sub>2 gc\<^sub>1 gc\<^sub>2.
      imreach G Shn (pgtab G (pr0_states G Shn)) (pr0_states G Shn) (gc, istk) \<longrightarrow>
      i = hd istk \<longrightarrow>
      redtab = red_buckets G Shn (length (pr0_states G Shn)) ! i \<longrightarrow>
      CL = xclosure_auto G (hd (fst gc)) \<longrightarrow>
      a\<^sub>1 \<in> set (dcands G i redtab CL gc) \<longrightarrow>
      a\<^sub>2 \<in> set (dcands G i redtab CL gc) \<longrightarrow>
      a\<^sub>1 \<noteq> a\<^sub>2 \<longrightarrow>
      mstep G gc a\<^sub>1 = Some gc\<^sub>1 \<longrightarrow> mstep G gc a\<^sub>2 = Some gc\<^sub>2 \<longrightarrow>
      dlive gc\<^sub>1 \<longrightarrow> dlive gc\<^sub>2 \<longrightarrow> False)\<close>

text \<open>Its consequence for \<^const>\<open>dpick\<close>: if the trace's action is offered and
  its successor is live, \<^const>\<open>dpick\<close> commits to that action, since no
  earlier candidate survives the \<^const>\<open>dlive\<close> test.\<close>

lemma dpick_forced:
  assumes det: \<open>mdet G Shn\<close>
    and ireach: \<open>imreach G Shn (pgtab G (pr0_states G Shn)) (pr0_states G Shn) (gc, istk)\<close>
    and ieq: \<open>i = hd istk\<close>
    and req: \<open>redtab = red_buckets G Shn (length (pr0_states G Shn)) ! i\<close>
    and CL: \<open>CL = xclosure_auto G (hd (fst gc))\<close>
    and okc: \<open>cstk = map (xclosure_auto G) (fst gc)\<close>
    and a_mem: \<open>a \<in> set (dcands G i redtab CL gc)\<close>
    and step: \<open>mstep G gc a = Some gc'\<close> and live: \<open>dlive gc'\<close>
  shows \<open>dpick G cstk gc (dcands G i redtab CL gc) = Some (a, gc')\<close>
proof -
  obtain Xs w where gc: \<open>gc = (Xs, w)\<close> by (cases gc)
  have mc: \<open>\<And>act. mstep_cached G cstk gc act = mstep G gc act\<close>
    unfolding okc gc mstep_def by simp
  have aux: \<open>\<And>acts. set acts \<subseteq> set (dcands G i redtab CL gc) \<Longrightarrow> a \<in> set acts \<Longrightarrow>
             dpick G cstk gc acts = Some (a, gc')\<close>
  proof -
    fix acts
    show \<open>set acts \<subseteq> set (dcands G i redtab CL gc) \<Longrightarrow> a \<in> set acts \<Longrightarrow>
          dpick G cstk gc acts = Some (a, gc')\<close>
    proof (induction acts)
      case Nil then show ?case by simp
    next
      case (Cons act' rest)
      from Cons.prems have act'_mem: \<open>act' \<in> set (dcands G i redtab CL gc)\<close>
        and rest_sub: \<open>set rest \<subseteq> set (dcands G i redtab CL gc)\<close> by auto
      show ?case
      proof (cases \<open>act' = a\<close>)
        case True
        then show ?thesis using step live mc by simp
      next
        case ne: False
        with Cons.prems(2) have a_rest: \<open>a \<in> set rest\<close> by simp
        show ?thesis
        proof (cases \<open>mstep_cached G cstk gc act'\<close>)
          case None
          then show ?thesis using Cons.IH[OF rest_sub a_rest] by simp
        next
          case (Some gc'')
          show ?thesis
          proof (cases \<open>dlive gc''\<close>)
            case True
            have \<open>mstep G gc act' = Some gc''\<close> using Some mc by simp
            from det[unfolded mdet_def, rule_format,
                     OF ireach ieq req CL act'_mem a_mem ne this step True live]
            show ?thesis ..
          next
            case False
            then show ?thesis using Some Cons.IH[OF rest_sub a_rest] by simp
          qed
        qed
      qed
    qed
  qed
  show ?thesis by (rule aux[OF subset_refl a_mem])
qed

subsection \<open>Completeness reduces to non-failure\<close>

text \<open>Soundness recovers the \<^const>\<open>ast_of\<close> property of whatever tree comes
  back, so the completeness obligation is only that the driver does not get
  stuck. This removes the tree-stack and \<^const>\<open>realizes\<close> components from
  the remaining induction.\<close>

lemma dparse_complete_of_ne:
  assumes fn: \<open>fresh_name G Shn\<close>
    and ne: \<open>dparse G Shn w \<noteq> None\<close>
  shows \<open>\<exists>t. dparse G Shn w = Some t \<and>
             ast_of G (Nt (istart G)) (istart_ind G) t w\<close>
proof -
  from ne obtain t where p: \<open>dparse G Shn w = Some t\<close> by auto
  from dparse_sound_ast[OF fn p] show ?thesis using p by blast
qed

subsection \<open>The root cell\<close>

text \<open>The base case of the recursion: the start cell
  \<open>(i\<^sub>0, (start_prod, 0), None, WAny)\<close> inherits to every production of
  \<^term>\<open>istart G\<close> with relation \<open>wcomp (winv (w_of Eq)) WAny = WAny\<close>, because
  the material after the dot in \<^const>\<open>start_prod\<close> is empty and hence
  vacuously nullable.\<close>

lemma cell_ok_root:
  assumes tab: \<open>tables_ok G Shn sts gt L\<close>
    and i0: \<open>i\<^sub>0 = st_find sts (lr0_start G Shn)\<close>
    and br: \<open>br \<in> set (iprods G)\<close> and brS: \<open>fst br = istart G\<close>
  shows \<open>cell_ok L i\<^sub>0 br 0 [] j\<close>
proof -
  have start_mem: \<open>(i\<^sub>0, (start_prod G Shn, 0), None, WAny) \<in> set L\<close>
    using tab i0 unfolding tables_ok_def la_start_def by auto
  have m_lt: \<open>0 < length (snd (start_prod G Shn))\<close>
    unfolding start_prod_def by simp
  have nxt: \<open>fst (snd (start_prod G Shn) ! 0) = Nt (istart G)\<close>
    unfolding start_prod_def by simp
  have nul: \<open>list_all (\<lambda>(X, r). nsym (nullables G) X)
        (drop (Suc 0) (snd (start_prod G Shn)))\<close>
    unfolding start_prod_def by simp
  from cell_child_inherit[OF tab start_mem m_lt nxt br brS nul]
  have \<open>(i\<^sub>0, (br, 0), None,
          wcomp (winv (w_of (snd (snd (start_prod G Shn) ! 0)))) WAny) \<in> set L\<close> .
  then have \<open>(i\<^sub>0, (br, 0), None, WAny) \<in> set L\<close>
    unfolding start_prod_def by simp
  then show ?thesis unfolding cell_ok_def by auto
qed

subsection \<open>Semantics of a lookahead cell\<close>

text \<open>A cell \<open>(i, (pr, m), t, \<tau>)\<close> says: in state \<open>i\<close>, when the item \<open>(pr, m)\<close>
  is on top, the token that follows the item's completion is \<open>t\<close>, and its
  column relates to the item's own left-hand-side anchor \<open>j\<close> by \<open>\<tau>\<close>.
  \<^const>\<open>dlic\<close> tests this against the reduce's anchor set.\<close>

definition cell_sat :: \<open>('n, 't) lacell \<Rightarrow> nat \<Rightarrow> ('t \<times> nat) list \<Rightarrow> nat \<Rightarrow> bool\<close> where
  \<open>cell_sat c i w j \<longleftrightarrow> (case c of (i', (pr, m), t, \<tau>) \<Rightarrow> i' = i \<and>
     (case w of [] \<Rightarrow> t = None | (a, cl) # _ \<Rightarrow> t = Some a \<and> wsat \<tau> cl j))\<close>

subsection \<open>A driveable action list\<close>

text \<open>Everything the deterministic driver needs of a machine action list,
  bundled into one predicate: at every position the index-carrying machine
  steps, the successor is \<^const>\<open>dlive\<close>, and a reduce is licensed by the cell
  table. Existence of the run follows (\<open>mdrive_imrun\<close>), so this is the only
  hypothesis the bridge below takes about the trace.\<close>

definition mdrive :: \<open>('n, 't) is_cfg \<Rightarrow> (('n, 't) sym \<times> nat) list list \<Rightarrow>
    ('n, 't) citem list list \<Rightarrow> ('n, 't) lacell list \<Rightarrow> ('n, 't) dact list \<Rightarrow>
    ('n, 't) icfg \<Rightarrow> bool\<close> where
  \<open>mdrive G gt sts L acts ic \<longleftrightarrow>
     (\<forall>p < length acts. \<exists>ic\<^sub>p ic'. imrun G gt sts (take p acts) ic = Some ic\<^sub>p \<and>
        imstep G gt sts ic\<^sub>p (acts ! p) = Some ic' \<and> dlive (fst ic') \<and>
        (\<forall>pr. acts ! p = DReduce pr \<longrightarrow> lic_at G L sts ic\<^sub>p pr))\<close>

lemma mdrive_Nil [simp]: \<open>mdrive G gt sts L [] ic\<close>
  unfolding mdrive_def by simp

lemma mdrive_ConsD:
  assumes \<open>mdrive G gt sts L (act # acts) ic\<close>
  shows \<open>\<exists>ic\<^sub>1. imstep G gt sts ic act = Some ic\<^sub>1 \<and> dlive (fst ic\<^sub>1) \<and>
      (\<forall>pr. act = DReduce pr \<longrightarrow> lic_at G L sts ic pr) \<and>
      mdrive G gt sts L acts ic\<^sub>1\<close>
proof -
  from assms[unfolded mdrive_def, rule_format, of 0] obtain ic\<^sub>1 where
      st: \<open>imstep G gt sts ic act = Some ic\<^sub>1\<close> and lv: \<open>dlive (fst ic\<^sub>1)\<close>
    and lc: \<open>\<forall>pr. act = DReduce pr \<longrightarrow> lic_at G L sts ic pr\<close> by auto
  have \<open>mdrive G gt sts L acts ic\<^sub>1\<close>
    unfolding mdrive_def
  proof (intro allI impI)
    fix p assume p: \<open>p < length acts\<close>
    then have \<open>Suc p < length (act # acts)\<close> by simp
    from assms[unfolded mdrive_def, rule_format, OF this] obtain ic\<^sub>p ic' where
        r: \<open>imrun G gt sts (take (Suc p) (act # acts)) ic = Some ic\<^sub>p\<close>
      and s: \<open>imstep G gt sts ic\<^sub>p ((act # acts) ! Suc p) = Some ic'\<close>
      and l: \<open>dlive (fst ic')\<close>
      and c: \<open>\<forall>pr. (act # acts) ! Suc p = DReduce pr \<longrightarrow> lic_at G L sts ic\<^sub>p pr\<close> by blast
    have r': \<open>imrun G gt sts (take p acts) ic\<^sub>1 = Some ic\<^sub>p\<close> using r st by simp
    have s': \<open>imstep G gt sts ic\<^sub>p (acts ! p) = Some ic'\<close> using s by simp
    have c': \<open>\<forall>pr. acts ! p = DReduce pr \<longrightarrow> lic_at G L sts ic\<^sub>p pr\<close> using c by simp
    show \<open>\<exists>ic\<^sub>p ic'. imrun G gt sts (take p acts) ic\<^sub>1 = Some ic\<^sub>p \<and>
        imstep G gt sts ic\<^sub>p (acts ! p) = Some ic' \<and> dlive (fst ic') \<and>
        (\<forall>pr. acts ! p = DReduce pr \<longrightarrow> lic_at G L sts ic\<^sub>p pr)\<close>
      using r' s' l c' by blast
  qed
  with st lv lc show ?thesis by blast
qed

lemma mdrive_ConsI:
  assumes st: \<open>imstep G gt sts ic act = Some ic\<^sub>1\<close> and lv: \<open>dlive (fst ic\<^sub>1)\<close>
    and lc: \<open>\<forall>pr. act = DReduce pr \<longrightarrow> lic_at G L sts ic pr\<close>
    and rest: \<open>mdrive G gt sts L acts ic\<^sub>1\<close>
  shows \<open>mdrive G gt sts L (act # acts) ic\<close>
  unfolding mdrive_def
proof (intro allI impI)
  fix p assume p: \<open>p < length (act # acts)\<close>
  show \<open>\<exists>ic\<^sub>p ic'. imrun G gt sts (take p (act # acts)) ic = Some ic\<^sub>p \<and>
      imstep G gt sts ic\<^sub>p ((act # acts) ! p) = Some ic' \<and> dlive (fst ic') \<and>
      (\<forall>pr. (act # acts) ! p = DReduce pr \<longrightarrow> lic_at G L sts ic\<^sub>p pr)\<close>
  proof (cases p)
    case 0
    have r\<^sub>0: \<open>imrun G gt sts (take 0 (act # acts)) ic = Some ic\<close> by simp
    have s\<^sub>0: \<open>imstep G gt sts ic ((act # acts) ! 0) = Some ic\<^sub>1\<close> using st by simp
    have c\<^sub>0: \<open>\<forall>pr. (act # acts) ! 0 = DReduce pr \<longrightarrow> lic_at G L sts ic pr\<close> using lc by simp
    show ?thesis unfolding 0 using r\<^sub>0 s\<^sub>0 lv c\<^sub>0 by blast
  next
    case (Suc q)
    then have q: \<open>q < length acts\<close> using p by simp
    from rest[unfolded mdrive_def, rule_format, OF q] obtain ic\<^sub>p ic' where
        r: \<open>imrun G gt sts (take q acts) ic\<^sub>1 = Some ic\<^sub>p\<close>
      and s: \<open>imstep G gt sts ic\<^sub>p (acts ! q) = Some ic'\<close>
      and l: \<open>dlive (fst ic')\<close>
      and c: \<open>\<forall>pr. acts ! q = DReduce pr \<longrightarrow> lic_at G L sts ic\<^sub>p pr\<close> by blast
    have r': \<open>imrun G gt sts (take (Suc q) (act # acts)) ic = Some ic\<^sub>p\<close> using r st by simp
    have s': \<open>imstep G gt sts ic\<^sub>p ((act # acts) ! Suc q) = Some ic'\<close> using s by simp
    have c': \<open>\<forall>pr. (act # acts) ! Suc q = DReduce pr \<longrightarrow> lic_at G L sts ic\<^sub>p pr\<close> using c by simp
    show ?thesis unfolding Suc using r' s' l c' by blast
  qed
qed

lemma mdrive_imrun: \<open>mdrive G gt sts L acts ic \<Longrightarrow> \<exists>ic'. imrun G gt sts acts ic = Some ic'\<close>
proof (induction acts arbitrary: ic)
  case Nil then show ?case by simp
next
  case (Cons act acts)
  from mdrive_ConsD[OF Cons.prems] obtain ic\<^sub>1 where
      st: \<open>imstep G gt sts ic act = Some ic\<^sub>1\<close> and rest: \<open>mdrive G gt sts L acts ic\<^sub>1\<close> by blast
  from Cons.IH[OF rest] show ?case using st by simp
qed

lemma mdrive_append:
  assumes as: \<open>mdrive G gt sts L as ic\<close>
    and run: \<open>imrun G gt sts as ic = Some ic'\<close>
    and bs: \<open>mdrive G gt sts L bs ic'\<close>
  shows \<open>mdrive G gt sts L (as @ bs) ic\<close>
  using as run
proof (induction as arbitrary: ic)
  case Nil then show ?case using bs by simp
next
  case (Cons act as)
  from mdrive_ConsD[OF Cons.prems(1)] obtain ic\<^sub>1 where
      st: \<open>imstep G gt sts ic act = Some ic\<^sub>1\<close> and lv: \<open>dlive (fst ic\<^sub>1)\<close>
    and lc: \<open>\<forall>pr. act = DReduce pr \<longrightarrow> lic_at G L sts ic pr\<close>
    and rest: \<open>mdrive G gt sts L as ic\<^sub>1\<close> by blast
  have \<open>imrun G gt sts as ic\<^sub>1 = Some ic'\<close> using Cons.prems(2) st by simp
  from Cons.IH[OF rest this] show ?case
    by (simp add: mdrive_ConsI[OF st lv lc])
qed
subsection \<open>The driver state tracks the index-carrying machine\<close>

text \<open>The closure cache mirrors the frame stack, the index stack tracks the
  frames (\<^const>\<open>didx_ok\<close>), the spanned input is the raw input's
  \<^const>\<open>tcols\<close>, and the tree stack has one entry per non-initial frame. All
  four are preserved by a step, and all four hold at \<^const>\<open>dinit\<close>.\<close>

definition dfollow_ok :: \<open>('n, 't) is_cfg \<Rightarrow> ('n, 't) citem list list \<Rightarrow>
    ('m, 'ch, 'n, 't) dst \<Rightarrow> bool\<close> where
  \<open>dfollow_ok G sts st \<longleftrightarrow> (case st of ((Xs, w), cstk, istk, v, tstk) \<Rightarrow>
      cstk = map (xclosure_auto G) Xs \<and> didx_ok G sts Xs istk \<and>
      w = tcols v \<and> Suc (length tstk) = length Xs)\<close>

lemma cell_buckets_length [simp]: \<open>length (cell_buckets L n) = n\<close>
  unfolding cell_buckets_def Let_def by simp

lemma red_buckets_length [simp]: \<open>length (red_buckets G Shn n) = n\<close>
  by (simp add: red_buckets_def)

lemma live_nonempty: \<open>live xs \<Longrightarrow> xs \<noteq> []\<close>
  unfolding live_def by auto

text \<open>The remaining input and the tree stack after a step depend only on the
  action: a shift consumes the next token and pushes its leaf, a reduce
  folds the right-hand side.\<close>

fun tstep :: \<open>('n, 't) dact \<Rightarrow> ('m, 'ch, 't) tword \<times> ('m, 'ch, 'n, 't) ast list \<Rightarrow>
    ('m, 'ch, 't) tword \<times> ('m, 'ch, 'n, 't) ast list\<close> where
  \<open>tstep DShift (v, tstk) = (tl v, Leaf (hd v) # tstk)\<close>
| \<open>tstep (DReduce pr) (v, tstk) =
     (v, Node (fst pr) (rev (take (length (snd pr)) tstk)) # drop (length (snd pr)) tstk)\<close>

text \<open>The driver takes the trace's action: it is among the candidates, and
  \<^const>\<open>dpick\<close> commits to it.  The new state is explicit.\<close>

lemma dstep_of_imstep_exact:
  assumes tab: \<open>tables_ok G Shn sts gt L\<close>
    and stc: \<open>sts = pr0_states G Shn\<close>
    and gtc: \<open>gt = pgtab G sts\<close>
    and Lc: \<open>L = la_fix G Shn\<close>
    and rt: \<open>redtab = red_buckets G Shn (length sts)\<close>
    and det: \<open>mdet G Shn\<close>
    and ireach: \<open>imreach G Shn gt sts ((Xs, w), istk)\<close>
    and inv: \<open>dfollow_ok G sts ((Xs, w), cstk, istk, v, tstk)\<close>
    and step: \<open>imstep G gt sts ((Xs, w), istk) act = Some (gc', istk')\<close>
    and live: \<open>dlive gc'\<close>
    and lic: \<open>\<forall>pr. act = DReduce pr \<longrightarrow> lic_at G L sts ((Xs, w), istk) pr\<close>
  shows \<open>act \<in> set (dcands G (hd istk) (redtab ! hd istk) (xclosure_auto G (hd Xs)) (Xs, w)) \<and>
         (\<exists>v' tstk'. (v', tstk') = tstep act (v, tstk) \<and>
            dstep G gt sts redtab ((Xs, w), cstk, istk, v, tstk)
              = Some (gc', map (xclosure_auto G) (fst gc'), istk', v', tstk') \<and>
            dfollow_ok G sts (gc', map (xclosure_auto G) (fst gc'), istk', v', tstk'))\<close>
proof -
  from inv have cstk_eq: \<open>cstk = map (xclosure_auto G) Xs\<close>
    and ok: \<open>didx_ok G sts Xs istk\<close> and vw: \<open>w = tcols v\<close>
    and lens: \<open>Suc (length tstk) = length Xs\<close>
    unfolding dfollow_ok_def by auto
  have len_i: \<open>length istk = length Xs\<close> by (rule didx_ok_len[OF ok])
  have ms: \<open>mstep G (Xs, w) act = Some gc'\<close>
    using imstep_mstep[of G gt sts \<open>((Xs, w), istk)\<close> act \<open>(gc', istk')\<close>] step by simp
  have msc: \<open>mstep_cached G cstk (Xs, w) act = Some gc'\<close>
    using ms unfolding mstep_def cstk_eq by simp
  have Xs_ne: \<open>Xs \<noteq> []\<close>
    using msc unfolding mstep_cached_def
    by (auto split: dact.splits list.splits if_splits)
  then have istk_ne: \<open>istk \<noteq> []\<close> using len_i by auto
  have hd_cstk: \<open>hd cstk = xclosure_auto G (hd Xs)\<close>
    using cstk_eq Xs_ne by (simp add: hd_map)
  have i_lt: \<open>hd istk < length sts\<close>
    using didx_ok_hd_lt[OF ok] imreach_dlive[OF ireach] by simp
  have gc'_ne: \<open>fst gc' \<noteq> []\<close> and gc'_live: \<open>live (hd (fst gc'))\<close>
    using live unfolding dlive_def by (cases gc'; simp)+
  let ?i = \<open>hd istk\<close> and ?CL = \<open>xclosure_auto G (hd Xs)\<close>
  let ?cells = \<open>cell_buckets L (length sts) ! ?i\<close>
  have rt': \<open>redtab = cell_buckets L (length sts)\<close>
    unfolding rt Lc stc by (rule cell_buckets_red_buckets[symmetric])
  have req: \<open>?cells = red_buckets G Shn (length (pr0_states G Shn)) ! ?i\<close>
    unfolding Lc stc by (simp add: cell_buckets_red_buckets)
  have ireach': \<open>imreach G Shn (pgtab G (pr0_states G Shn)) (pr0_states G Shn) ((Xs, w), istk)\<close>
    using ireach unfolding gtc stc .
  have cells_eq: \<open>(if ?i < length redtab then redtab ! ?i else []) = ?cells\<close>
    using i_lt rt' by simp
  have CL_eq: \<open>(case cstk of [] \<Rightarrow> [] | c # _ \<Rightarrow> c) = ?CL\<close>
    using cstk_eq Xs_ne hd_cstk by (cases cstk) auto
  have i_eq: \<open>(case istk of [] \<Rightarrow> length sts | j # _ \<Rightarrow> j) = ?i\<close>
    using istk_ne by (cases istk) auto
  have cstk_eq': \<open>cstk = map (xclosure_auto G) (fst (Xs, w))\<close> using cstk_eq by simp
  have cells_rt: \<open>redtab ! ?i = ?cells\<close> using rt' by simp
  show ?thesis
  proof (cases act)
    case DShift
    have sh: \<open>mstep_cached G cstk (Xs, w) DShift = Some gc'\<close> using msc DShift by simp
    obtain a c w' where w_eq: \<open>w = (a, c) # w'\<close>
      and gc'_eq: \<open>gc' = (lgoto (hd cstk) (Tm a) (FinRep [c]) # Xs, w')\<close>
      using sh unfolding mstep_cached_def by (auto split: list.splits if_splits)
    have v_ne: \<open>v \<noteq> []\<close> using vw w_eq by auto
    then obtain t\<^sub>0 v\<^sub>0 where v_eq: \<open>v = t\<^sub>0 # v\<^sub>0\<close> by (cases v) auto
    have a_eq: \<open>a = tok t\<^sub>0\<close> and w'_eq: \<open>w' = tcols v\<^sub>0\<close>
      using vw w_eq v_eq unfolding tcols_def by auto
    have offered: \<open>DShift \<in> set (dcands G ?i ?cells ?CL (Xs, w))\<close>
      by (rule dcands_shift) (use Xs_ne w_eq in auto)
    have pick: \<open>dpick G cstk (Xs, w) (dcands G ?i ?cells ?CL (Xs, w)) = Some (DShift, gc')\<close>
      by (rule dpick_forced[OF det ireach' refl req _ cstk_eq' offered _ live])
         (use ms DShift in simp_all)
    have dstep_eq: \<open>dstep G gt sts redtab ((Xs, w), cstk, istk, v, tstk) =
        Some (gc', xclosure_auto G (hd (fst gc')) # cstk,
              dnext gt sts ?i (Tm (tok (hd v))) # istk, tl v, Leaf (hd v) # tstk)\<close>
      unfolding dstep_def rt' by (simp add: Let_def i_eq CL_eq i_lt pick)
    have istk'_eq: \<open>istk' = dnext gt sts ?i (Tm a) # istk\<close>
      using step ms unfolding imstep_def DShift by (simp add: w_eq)
    have cstk'_eq: \<open>xclosure_auto G (hd (fst gc')) # cstk = map (xclosure_auto G) (fst gc')\<close>
      using gc'_eq cstk_eq by simp
    have i\<^sub>0: \<open>istk ! 0 = hd istk\<close> using istk_ne by (simp add: hd_conv_nth)
    have x\<^sub>0: \<open>Xs ! 0 = hd Xs\<close> using Xs_ne by (simp add: hd_conv_nth)
    have push: \<open>didx_ok G sts (fst gc') istk'\<close>
      using didx_ok_push[OF tab ok, of 0 \<open>Tm a\<close> \<open>FinRep [c]\<close>] Xs_ne
        gc'_live[unfolded gc'_eq] gc'_eq istk'_eq
      by (simp add: i\<^sub>0 x\<^sub>0 hd_cstk live_nonempty)
    show ?thesis
    proof (intro conjI exI)
      show \<open>act \<in> set (dcands G ?i (redtab ! ?i) ?CL (Xs, w))\<close>
        using offered unfolding DShift cells_rt .
      show \<open>(tl v, Leaf (hd v) # tstk) = tstep act (v, tstk)\<close>
        unfolding DShift by simp
      show \<open>dstep G gt sts redtab ((Xs, w), cstk, istk, v, tstk) =
          Some (gc', map (xclosure_auto G) (fst gc'), istk', tl v, Leaf (hd v) # tstk)\<close>
        unfolding dstep_eq cstk'_eq istk'_eq using a_eq v_eq by simp
      show \<open>dfollow_ok G sts (gc', map (xclosure_auto G) (fst gc'), istk',
              tl v, Leaf (hd v) # tstk)\<close>
        unfolding dfollow_ok_def using push gc'_eq w'_eq v_eq lens by simp
    qed
  next
    case (DReduce pr)
    let ?k = \<open>length (snd pr)\<close>
    have red: \<open>mstep_cached G cstk (Xs, w) (DReduce pr) = Some gc'\<close> using msc DReduce by simp
    have k_lt: \<open>?k < length Xs\<close> and RS_ne: \<open>irep_nonempty (red_set (hd cstk) pr)\<close>
      and gc'_eq: \<open>gc' = (lgoto (cstk ! ?k) (Nt (fst pr)) (red_set (hd cstk) pr) # drop ?k Xs, w)\<close>
      using red unfolding mstep_cached_def by (auto simp: Let_def split: if_splits)
    have RS_ne': \<open>irep_nonempty (red_set ?CL pr)\<close> using RS_ne hd_cstk by simp
    obtain R where compR: \<open>(pr, ?k, R) \<in> set ?CL\<close>
      using RS_ne' unfolding red_set_nonempty_iff by auto
    have dlicL: \<open>dlic_L ?i L w pr (red_set ?CL pr)\<close>
      using lic DReduce unfolding lic_at_def by simp
    have dlic': \<open>dlic ?i ?cells w pr (red_set ?CL pr)\<close>
      by (rule dlic_buckets[OF i_lt, THEN iffD2, OF dlicL])
    have offered: \<open>DReduce pr \<in> set (dcands G ?i ?cells ?CL (Xs, w))\<close>
      by (rule dcands_reduceI[OF _ compR RS_ne']) (use Xs_ne dlic' in auto)
    have pick: \<open>dpick G cstk (Xs, w) (dcands G ?i ?cells ?CL (Xs, w)) = Some (DReduce pr, gc')\<close>
      by (rule dpick_forced[OF det ireach' refl req _ cstk_eq' offered _ live])
         (use ms DReduce in simp_all)
    have dstep_eq: \<open>dstep G gt sts redtab ((Xs, w), cstk, istk, v, tstk) =
        Some (gc', xclosure_auto G (hd (fst gc')) # drop ?k cstk,
              dnext gt sts (istk ! ?k) (Nt (fst pr)) # drop ?k istk, v,
              Node (fst pr) (rev (take ?k tstk)) # drop ?k tstk)\<close>
      unfolding dstep_def rt' by (simp add: Let_def i_eq CL_eq i_lt pick)
    have istk'_eq: \<open>istk' = dnext gt sts (istk ! ?k) (Nt (fst pr)) # drop ?k istk\<close>
      using step ms unfolding imstep_def DReduce by simp
    have cstk'_eq: \<open>xclosure_auto G (hd (fst gc')) # drop ?k cstk =
        map (xclosure_auto G) (fst gc')\<close>
      using gc'_eq cstk_eq by (simp add: drop_map)
    have cstk_k: \<open>cstk ! ?k = xclosure_auto G (Xs ! ?k)\<close> using cstk_eq k_lt by simp
    have push: \<open>didx_ok G sts (fst gc') istk'\<close>
      using didx_ok_push[OF tab ok k_lt, of \<open>Nt (fst pr)\<close> \<open>red_set (hd cstk) pr\<close>]
        gc'_live[unfolded gc'_eq] gc'_eq istk'_eq cstk_k
      by (simp add: live_nonempty)
    show ?thesis
    proof (intro conjI exI)
      show \<open>act \<in> set (dcands G ?i (redtab ! ?i) ?CL (Xs, w))\<close>
        using offered unfolding DReduce cells_rt .
      show \<open>(v, Node (fst pr) (rev (take ?k tstk)) # drop ?k tstk) = tstep act (v, tstk)\<close>
        unfolding DReduce by simp
      show \<open>dstep G gt sts redtab ((Xs, w), cstk, istk, v, tstk) =
          Some (gc', map (xclosure_auto G) (fst gc'), istk', v,
                Node (fst pr) (rev (take ?k tstk)) # drop ?k tstk)\<close>
        unfolding dstep_eq cstk'_eq istk'_eq by simp
      show \<open>dfollow_ok G sts (gc', map (xclosure_auto G) (fst gc'), istk', v,
              Node (fst pr) (rev (take ?k tstk)) # drop ?k tstk)\<close>
        unfolding dfollow_ok_def using push gc'_eq vw lens k_lt by simp
    qed
  qed
qed

lemma dstep_of_imstep:
  assumes tab: \<open>tables_ok G Shn sts gt L\<close>
    and stc: \<open>sts = pr0_states G Shn\<close>
    and gtc: \<open>gt = pgtab G sts\<close>
    and Lc: \<open>L = la_fix G Shn\<close>
    and rt: \<open>redtab = red_buckets G Shn (length sts)\<close>
    and det: \<open>mdet G Shn\<close>
    and ireach: \<open>imreach G Shn gt sts ((Xs, w), istk)\<close>
    and inv: \<open>dfollow_ok G sts ((Xs, w), cstk, istk, v, tstk)\<close>
    and step: \<open>imstep G gt sts ((Xs, w), istk) act = Some (gc', istk')\<close>
    and live: \<open>dlive gc'\<close>
    and lic: \<open>\<forall>pr. act = DReduce pr \<longrightarrow> lic_at G L sts ((Xs, w), istk) pr\<close>
  shows \<open>\<exists>v' tstk'. dstep G gt sts redtab ((Xs, w), cstk, istk, v, tstk)
           = Some (gc', map (xclosure_auto G) (fst gc'), istk', v', tstk')
         \<and> dfollow_ok G sts (gc', map (xclosure_auto G) (fst gc'), istk', v', tstk')\<close>
  using dstep_of_imstep_exact[OF assms] by blast

subsection \<open>Iterating: the driver follows the whole run\<close>

lemma dsteps_of_mdrive:
  assumes tab: \<open>tables_ok G Shn sts gt L\<close>
    and stc: \<open>sts = pr0_states G Shn\<close>
    and gtc: \<open>gt = pgtab G sts\<close>
    and Lc: \<open>L = la_fix G Shn\<close>
    and rt: \<open>redtab = red_buckets G Shn (length sts)\<close>
    and det: \<open>mdet G Shn\<close>
  shows \<open>mdrive G gt sts L acts (gc, istk) \<Longrightarrow> imreach G Shn gt sts (gc, istk) \<Longrightarrow>
     dfollow_ok G sts (gc, cstk, istk, v, tstk) \<Longrightarrow>
     \<exists>gc' istk' v' tstk'. imrun G gt sts acts (gc, istk) = Some (gc', istk') \<and>
        dsteps G gt sts redtab (length acts) (gc, cstk, istk, v, tstk)
          = Some (gc', map (xclosure_auto G) (fst gc'), istk', v', tstk') \<and>
        dfollow_ok G sts (gc', map (xclosure_auto G) (fst gc'), istk', v', tstk')\<close>
proof (induction acts arbitrary: gc istk cstk v tstk)
  case Nil
  obtain Xs w where gc_eq: \<open>gc = (Xs, w)\<close> by (cases gc)
  have \<open>cstk = map (xclosure_auto G) (fst gc)\<close>
    using Nil.prems(3) gc_eq unfolding dfollow_ok_def by simp
  then show ?case using Nil.prems(3) by auto
next
  case (Cons act acts)
  obtain Xs w where gc_eq: \<open>gc = (Xs, w)\<close> by (cases gc)
  from mdrive_ConsD[OF Cons.prems(1)] obtain ic\<^sub>1 where
      st\<^sub>0: \<open>imstep G gt sts (gc, istk) act = Some ic\<^sub>1\<close> and lv\<^sub>0: \<open>dlive (fst ic\<^sub>1)\<close>
    and lc\<^sub>0: \<open>\<forall>pr. act = DReduce pr \<longrightarrow> lic_at G L sts (gc, istk) pr\<close>
    and rest\<^sub>0: \<open>mdrive G gt sts L acts ic\<^sub>1\<close> by blast
  obtain gc\<^sub>1 istk\<^sub>1 where ic\<^sub>1: \<open>ic\<^sub>1 = (gc\<^sub>1, istk\<^sub>1)\<close> by (cases ic\<^sub>1)
  have st: \<open>imstep G gt sts ((Xs, w), istk) act = Some (gc\<^sub>1, istk\<^sub>1)\<close>
    using st\<^sub>0 gc_eq ic\<^sub>1 by simp
  have lv: \<open>dlive gc\<^sub>1\<close> using lv\<^sub>0 ic\<^sub>1 by simp
  have lc: \<open>\<forall>pr. act = DReduce pr \<longrightarrow> lic_at G L sts ((Xs, w), istk) pr\<close>
    using lc\<^sub>0 gc_eq by simp
  have ireach: \<open>imreach G Shn gt sts ((Xs, w), istk)\<close> using Cons.prems(2) gc_eq by simp
  have inv: \<open>dfollow_ok G sts ((Xs, w), cstk, istk, v, tstk)\<close>
    using Cons.prems(3) gc_eq by simp
  from dstep_of_imstep[OF tab stc gtc Lc rt det ireach inv st lv lc] obtain v\<^sub>1 tstk\<^sub>1 where
      ds: \<open>dstep G gt sts redtab ((Xs, w), cstk, istk, v, tstk) =
            Some (gc\<^sub>1, map (xclosure_auto G) (fst gc\<^sub>1), istk\<^sub>1, v\<^sub>1, tstk\<^sub>1)\<close>
    and inv\<^sub>1: \<open>dfollow_ok G sts (gc\<^sub>1, map (xclosure_auto G) (fst gc\<^sub>1), istk\<^sub>1, v\<^sub>1, tstk\<^sub>1)\<close>
    by blast
  have ms: \<open>mstep G gc act = Some gc\<^sub>1\<close>
    using imstep_mstep[of G gt sts \<open>(gc, istk)\<close> act ic\<^sub>1] st\<^sub>0 ic\<^sub>1 by simp
  have ireach\<^sub>1: \<open>imreach G Shn gt sts (gc\<^sub>1, istk\<^sub>1)\<close>
    using imreach_step[OF Cons.prems(2) st\<^sub>0 lv\<^sub>0] ic\<^sub>1 by simp
  have rest: \<open>mdrive G gt sts L acts (gc\<^sub>1, istk\<^sub>1)\<close> using rest\<^sub>0 ic\<^sub>1 by simp
  from Cons.IH[OF rest ireach\<^sub>1 inv\<^sub>1] obtain gc' istk' v' tstk' where
      ir: \<open>imrun G gt sts acts (gc\<^sub>1, istk\<^sub>1) = Some (gc', istk')\<close>
    and dr: \<open>dsteps G gt sts redtab (length acts)
              (gc\<^sub>1, map (xclosure_auto G) (fst gc\<^sub>1), istk\<^sub>1, v\<^sub>1, tstk\<^sub>1) =
                Some (gc', map (xclosure_auto G) (fst gc'), istk', v', tstk')\<close>
    and inv': \<open>dfollow_ok G sts (gc', map (xclosure_auto G) (fst gc'), istk', v', tstk')\<close>
    by blast
  show ?case
  proof (intro exI conjI)
    show \<open>imrun G gt sts (act # acts) (gc, istk) = Some (gc', istk')\<close>
      using st\<^sub>0 ic\<^sub>1 ir by simp
    show \<open>dsteps G gt sts redtab (length (act # acts)) (gc, cstk, istk, v, tstk) =
        Some (gc', map (xclosure_auto G) (fst gc'), istk', v', tstk')\<close>
      using ds dr gc_eq by simp
  qed (rule inv')
qed

subsection \<open>From a completed chain to \<^const>\<open>drun\<^sub>w\<^sub>f\<close>\<close>

text \<open>Every \<^const>\<open>dstep\<close> pushes, so any state the driver reaches has a
  non-empty tree stack. Together with ``the start is not final'' that is all
  \<^const>\<open>drun\<^sub>w\<^sub>f\<close> needs: it may stop at an earlier
  \<^const>\<open>gfinal\<close> than the chain does, but it never returns \<^const>\<open>None\<close>.
  Since completeness reduces to non-failure (\<^text>\<open>dparse_complete_of_ne\<close>),
  that suffices.\<close>

lemma dstep_tstk_ne:
  \<open>dstep G gt sts redtab st = Some st' \<Longrightarrow>
     (case st' of (gc, cstk, istk, v, tstk) \<Rightarrow> tstk) \<noteq> []\<close>
  unfolding dstep_def
  by (auto simp: Let_def split: option.splits prod.splits dact.splits)

lemma drun\<^sub>w\<^sub>f_ne_of_dsteps:
  \<open>dsteps G gt sts redtab n st = Some st' \<Longrightarrow> gfinal G Shn (fst st') \<Longrightarrow>
   \<not> gfinal G Shn (fst st) \<Longrightarrow> drun\<^sub>w\<^sub>f G Shn gt sts redtab st \<noteq> None\<close>
proof (induction n arbitrary: st)
  case 0 then show ?case by simp
next
  case (Suc n)
  from Suc.prems(1) obtain st\<^sub>1 where
      sp: \<open>dstep G gt sts redtab st = Some st\<^sub>1\<close>
    and rn: \<open>dsteps G gt sts redtab n st\<^sub>1 = Some st'\<close>
    by (auto split: option.splits)
  have unf: \<open>drun\<^sub>w\<^sub>f G Shn gt sts redtab st = drun\<^sub>w\<^sub>f G Shn gt sts redtab st\<^sub>1\<close>
    using Suc.prems(3) sp by (cases st) simp
  show ?case
  proof (cases \<open>gfinal G Shn (fst st\<^sub>1)\<close>)
    case True
    have \<open>(case st\<^sub>1 of (gc, cstk, istk, v, tstk) \<Rightarrow> tstk) \<noteq> []\<close>
      by (rule dstep_tstk_ne[OF sp])
    then show ?thesis unfolding unf using True by (cases st\<^sub>1) (auto split: list.splits)
  next
    case False
    from Suc.IH[OF rn Suc.prems(2) False] show ?thesis unfolding unf .
  qed
qed

subsection \<open>The driver is complete for any licensed, deterministic trace\<close>

lemma dfollow_ok_dinit:
  \<open>dfollow_ok G (pr0_states G Shn) (dinit G Shn (pr0_states G Shn) w)\<close>
  unfolding dfollow_ok_def dinit_def using didx_ok_init[OF tables_ok_concrete] by simp

lemma not_gfinal_xinit: \<open>\<not> gfinal G Shn ([xinit G Shn], u)\<close>
  unfolding gfinal_def xinit_def start_prod_def by simp

theorem dparse_ne_of_mdrive:
  assumes det: \<open>mdet G Shn\<close>
    and drv: \<open>mdrive G (pgtab G (pr0_states G Shn)) (pr0_states G Shn) (la_fix G Shn)
                acts (([xinit G Shn], tcols w), [st_find (pr0_states G Shn) (lr0_start G Shn)])\<close>
    and fin: \<open>mcompletes G Shn acts ([xinit G Shn], tcols w)\<close>
  shows \<open>dparse G Shn w \<noteq> None\<close>
proof -
  let ?sts = \<open>pr0_states G Shn\<close> and ?gt = \<open>pgtab G (pr0_states G Shn)\<close>
  let ?L = \<open>la_fix G Shn\<close> and ?redtab = \<open>red_buckets G Shn (length (pr0_states G Shn))\<close>
  have tab: \<open>tables_ok G Shn ?sts ?gt ?L\<close> by (rule tables_ok_concrete)
  have rt: \<open>?redtab = red_buckets G Shn (length ?sts)\<close> by (rule refl)
  let ?ist = \<open>[st_find ?sts (lr0_start G Shn)]\<close>
  have inv: \<open>dfollow_ok G ?sts (([xinit G Shn], tcols w),
      [xclosure_auto G (xinit G Shn)], ?ist, w, [])\<close>
    using dfollow_ok_dinit[of G Shn w] unfolding dinit_def .
  from dsteps_of_mdrive[OF tab refl refl refl rt det drv imreach_init inv]
  obtain gc' istk' v' tstk' where
      ir: \<open>imrun G ?gt ?sts acts (([xinit G Shn], tcols w), ?ist) = Some (gc', istk')\<close>
    and dr: \<open>dsteps G ?gt ?sts ?redtab (length acts)
              (([xinit G Shn], tcols w), [xclosure_auto G (xinit G Shn)], ?ist, w, []) =
                Some (gc', map (xclosure_auto G) (fst gc'), istk', v', tstk')\<close> by blast
  have mr: \<open>mrun G acts ([xinit G Shn], tcols w) = Some gc'\<close>
    using imrun_mrun[OF ir] by simp
  have gf: \<open>gfinal G Shn gc'\<close> using fin mr unfolding mcompletes_def by simp
  have \<open>drun\<^sub>w\<^sub>f G Shn ?gt ?sts ?redtab
      (([xinit G Shn], tcols w), [xclosure_auto G (xinit G Shn)], ?ist, w, []) \<noteq> None\<close>
    by (rule drun\<^sub>w\<^sub>f_ne_of_dsteps[OF dr _ ]) (use gf not_gfinal_xinit in simp_all)
  then show ?thesis unfolding dparse_def dinit_def Let_def by simp
qed

theorem dparse_complete_of_mdrive:
  assumes fn: \<open>fresh_name G Shn\<close> and det: \<open>mdet G Shn\<close>
    and drv: \<open>mdrive G (pgtab G (pr0_states G Shn)) (pr0_states G Shn) (la_fix G Shn)
                acts (([xinit G Shn], tcols w), [st_find (pr0_states G Shn) (lr0_start G Shn)])\<close>
    and fin: \<open>mcompletes G Shn acts ([xinit G Shn], tcols w)\<close>
  shows \<open>\<exists>t. dparse G Shn w = Some t \<and> ast_of G (Nt (istart G)) (istart_ind G) t w\<close>
  by (rule dparse_complete_of_ne[OF fn dparse_ne_of_mdrive[OF det drv fin]])



section \<open>The licensing recursion\<close>

subsection \<open>A subtree list derives its yield\<close>

text \<open>\<^const>\<open>anntree\<close> turns a \<^const>\<open>wf_ptree\<close> into a \<^const>\<open>parse_tree\<close> of
  \<^const>\<open>infG\<close>, so \<^text>\<open>derives_fringe_if_parse_tree\<close> gives the derivation of
  its yield; \<^text>\<open>derives_concat\<close> lifts that to a list of siblings.\<close>

lemma wf_ptree_derives:
  \<open>wf_ptree G pt \<Longrightarrow> infG G \<turnstile> [annsym (proot pt)] \<Rightarrow>* map Tm (tcols (pyield pt))\<close>
  using derives_fringe_if_parse_tree[of \<open>infG G\<close> \<open>anntree pt\<close>] by simp

lemma wf_ptree_list_derives:
  assumes \<open>\<forall>pt \<in> set pts. wf_ptree G pt\<close>
  shows \<open>infG G \<turnstile> map (\<lambda>pt. annsym (proot pt)) pts \<Rightarrow>*
           map Tm (tcols (concat (map pyield pts)))\<close>
proof -
  have e\<^sub>1: \<open>concat (map (\<lambda>pt. [annsym (proot pt)]) pts) = map (\<lambda>pt. annsym (proot pt)) pts\<close>
    by (induction pts) auto
  have e\<^sub>2: \<open>concat (map (\<lambda>pt. map Tm (tcols (pyield pt))) pts) =
      map Tm (tcols (concat (map pyield pts)))\<close>
    by (induction pts) auto
  have \<open>infG G \<turnstile> concat (map (\<lambda>pt. [annsym (proot pt)]) pts) \<Rightarrow>*
        concat (map (\<lambda>pt. map Tm (tcols (pyield pt))) pts)\<close>
    by (rule derives_concat) (use assms wf_ptree_derives in blast)
  then show ?thesis unfolding e\<^sub>1 e\<^sub>2 .
qed

text \<open>The roots of the siblings annotate the right-hand-side suffix they were
  matched against.\<close>

lemma annotates_of_kids:
  assumes \<open>list_all2 (\<lambda>Xr pt. fst (proot pt) = fst Xr \<and>
      irel_sat (snd Xr) (snd (proot pt)) j) sfx pts\<close>
  shows \<open>annotates j sfx (map (\<lambda>pt. annsym (proot pt)) pts)\<close>
  unfolding annotates_def using assms
proof (induction rule: list_all2_induct)
  case Nil
  show ?case by simp
next
  case (Cons Xr sfx' pt pts')
  obtain X r where Xr: \<open>Xr = (X, r)\<close> by (cases Xr)
  have \<open>annsym (proot pt) = annsym (X, snd (proot pt))\<close>
    using Cons.hyps(1) Xr by (cases \<open>proot pt\<close>) simp
  then show ?case using Cons.hyps(1) Cons.IH Xr by auto
qed

subsection \<open>The two cases of \<^text>\<open>cell_ok_child\<close>, supplied from the siblings\<close>

lemma kids_first:
  assumes kids: \<open>list_all2 (\<lambda>Xr pt. fst (proot pt) = fst Xr \<and>
        irel_sat (snd Xr) (snd (proot pt)) j) sfx pts\<close>
    and wf: \<open>\<forall>pt \<in> set pts. wf_ptree G pt\<close>
    and yield: \<open>tcols (concat (map pyield pts)) = (a, cl) # V\<close>
  shows \<open>\<exists>\<sigma>. (a, \<sigma>) \<in> set (fscan (ffix G) (nullables G) sfx) \<and> csat \<sigma> cl j\<close>
proof -
  have ann: \<open>annotates j sfx (map (\<lambda>pt. annsym (proot pt)) pts)\<close>
    by (rule annotates_of_kids[OF kids])
  have \<open>infG G \<turnstile> map (\<lambda>pt. annsym (proot pt)) pts \<Rightarrow>* map Tm (tcols (concat (map pyield pts)))\<close>
    by (rule wf_ptree_list_derives[OF wf])
  then have \<open>infG G \<turnstile> map (\<lambda>pt. annsym (proot pt)) pts \<Rightarrow>* Tm (a, cl) # map Tm V\<close>
    unfolding yield by simp
  then obtain n where \<open>infG G \<turnstile> map (\<lambda>pt. annsym (proot pt)) pts \<Rightarrow>(n) Tm (a, cl) # map Tm V\<close>
    by (auto simp: rtranclp_power)
  from fscan_complete[OF this ann] show ?thesis .
qed

lemma kids_null:
  assumes kids: \<open>list_all2 (\<lambda>Xr pt. fst (proot pt) = fst Xr \<and>
        irel_sat (snd Xr) (snd (proot pt)) j) sfx pts\<close>
    and wf: \<open>\<forall>pt \<in> set pts. wf_ptree G pt\<close>
    and yield: \<open>concat (map pyield pts) = []\<close>
  shows \<open>list_all (\<lambda>(X, r). nsym (nullables G) X) sfx\<close>
proof -
  have len: \<open>length pts = length sfx\<close> using kids by (simp add: list_all2_lengthD)
  have \<open>\<forall>p < length sfx. nsym (nullables G) (fst (sfx ! p))\<close>
  proof (intro allI impI)
    fix p assume p: \<open>p < length sfx\<close>
    then have mem: \<open>pts ! p \<in> set pts\<close> using len by simp
    have \<open>pyield (pts ! p) = []\<close> using yield p len by simp
    from wf_ptree_nsym_of_empty_yield[OF _ this] wf mem
    have \<open>nsym (nullables G) (fst (proot (pts ! p)))\<close> by blast
    then show \<open>nsym (nullables G) (fst (sfx ! p))\<close>
      using list_all2_nthD[OF kids p] by simp
  qed
  then show ?thesis by (simp add: list_all_length case_prod_beta)
qed

subsection \<open>A frame slot for a symbol: what makes the pushed frame live\<close>

text \<open>The pushed frame \<^term>\<open>lgoto CL X RA\<close> is \<^const>\<open>live\<close> iff the
  source frame closure has an item with \<open>X\<close> after the dot whose anchor is
  compatible with some anchor of \<^term>\<open>RA\<close>. That witness is available at every
  push the tree recursion makes: for a child it is the parent's own item, and
  for the root it is the start item of \<^const>\<open>xinit\<close>.\<close>

definition slot_ok :: \<open>('n, 't) xitem list \<Rightarrow> ('n, 't) sym \<Rightarrow> nat \<Rightarrow> bool\<close> where
  \<open>slot_ok CL X j \<longleftrightarrow> (\<exists>pr m R j'. (pr, m, R) \<in> set CL \<and> m < length (snd pr) \<and>
      fst (snd pr ! m) = X \<and> j' \<in> irep_set R \<and> irel_sat (snd (snd pr ! m)) j j')\<close>

lemma slot_okI:
  \<open>(pr, m, R) \<in> set CL \<Longrightarrow> m < length (snd pr) \<Longrightarrow> fst (snd pr ! m) = X \<Longrightarrow>
   j' \<in> irep_set R \<Longrightarrow> irel_sat (snd (snd pr ! m)) j j' \<Longrightarrow> slot_ok CL X j\<close>
  unfolding slot_ok_def by blast

lemma slot_ok_live:
  assumes slot: \<open>slot_ok CL X j\<close> and j: \<open>j \<in> irep_set RA\<close>
  shows \<open>live (lgoto CL X RA)\<close>
proof -
  from slot obtain pr m R j' where
      mem: \<open>(pr, m, R) \<in> set CL\<close> and m_lt: \<open>m < length (snd pr)\<close>
    and Xeq: \<open>fst (snd pr ! m) = X\<close> and j'R: \<open>j' \<in> irep_set R\<close>
    and sat: \<open>irel_sat (snd (snd pr ! m)) j j'\<close> unfolding slot_ok_def by blast
  let ?R' = \<open>irep_inter R (irep_pre (snd (snd pr ! m)) RA)\<close>
  have inl: \<open>(pr, Suc m, ?R') \<in> set (lgoto CL X RA)\<close>
    by (rule lgoto_memI[OF mem m_lt Xeq])
  have ne: \<open>irep_nonempty ?R'\<close> using j'R j sat by auto
  show ?thesis unfolding live_def list_ex_iff
    by (intro bexI[of _ \<open>(pr, Suc m, ?R')\<close>]) (use inl ne in auto)
qed

lemma slot_ok_dlive:
  \<open>slot_ok CL X j \<Longrightarrow> j \<in> irep_set RA \<Longrightarrow> dlive (lgoto CL X RA # Ys, u)\<close>
  unfolding dlive_def by (simp add: slot_ok_live)

subsection \<open>Moving the cell along with the index stack\<close>

lemma cell_ok_step:
  assumes tab: \<open>tables_ok G Shn sts gt L\<close>
    and cell: \<open>cell_ok L i pr m rest j\<close>
    and m_lt: \<open>m < length (snd pr)\<close>
  shows \<open>cell_ok L (la_next gt sts i (fst (snd pr ! m))) pr (Suc m) rest j\<close>
proof -
  from cell obtain \<tau> where mem: \<open>(i, (pr, m), tok_of rest, \<tau>) \<in> set L\<close>
    and rel: \<open>case rest of [] \<Rightarrow> True | (a, c) # _ \<Rightarrow> wsat \<tau> c j\<close>
    unfolding cell_ok_def by auto
  have step: \<open>(la_next gt sts i (fst (snd pr ! m)), (pr, Suc m), tok_of rest, \<tau>)
        \<in> set (la_cell G (ffix G) (nullables G) gt sts (i, (pr, m), tok_of rest, \<tau>))\<close>
    by (rule la_cell_goto_mem[OF m_lt])
  from tables_ok_cell[OF tab mem step]
  have \<open>(la_next gt sts i (fst (snd pr ! m)), (pr, Suc m), tok_of rest, \<tau>) \<in> set L\<close> .
  then show ?thesis using rel unfolding cell_ok_def by auto
qed

subsection \<open>The context a subtree inherits, with the slot witness\<close>

text \<open>\<open>nctx\<close> is the context a subtree inherits: besides the machine-side
  context (the closure of the top frame holds the node's production at dot 0,
  admitting the node's anchor) and the cell-side context, it carries the
  \<^const>\<open>slot_ok\<close> witness that makes the frame the subtree pushes
  \<^const>\<open>live\<close>.\<close>

definition nctx :: \<open>('n, 't) is_cfg \<Rightarrow> ('n, 't) lacell list \<Rightarrow> nat \<Rightarrow>
    ('m, 'ch, 'n, 't) ptree \<Rightarrow> ('n, 't) dact list \<Rightarrow>
    ('n, 't) xitem list list \<Rightarrow> ('t \<times> nat) list \<Rightarrow> bool\<close> where
  \<open>nctx G L i pt acts Xs rest \<longleftrightarrow>
     slot_ok (xclosure_auto G (hd Xs)) (fst (proot pt)) (snd (proot pt)) \<and>
     (\<forall>A j pts. pt = PNode A j pts \<longrightarrow>
        (\<exists>pr R\<^sub>0. acts \<noteq> [] \<and> last acts = DReduce pr \<and>
           (pr, 0, R\<^sub>0) \<in> set (xclosure_auto G (hd Xs)) \<and> j \<in> irep_set R\<^sub>0 \<and>
           cell_ok L i pr 0 rest j))\<close>

lemma nctx_slot: \<open>nctx G L i pt acts Xs rest \<Longrightarrow>
    slot_ok (xclosure_auto G (hd Xs)) (fst (proot pt)) (snd (proot pt))\<close>
  unfolding nctx_def by simp

lemma nctx_node:
  assumes \<open>nctx G L i (PNode A j pts) acts Xs rest\<close>
  shows \<open>\<exists>pr R\<^sub>0. acts \<noteq> [] \<and> last acts = DReduce pr \<and>
      (pr, 0, R\<^sub>0) \<in> set (xclosure_auto G (hd Xs)) \<and> j \<in> irep_set R\<^sub>0 \<and>
      cell_ok L i pr 0 rest j\<close>
  using assms unfolding nctx_def by simp

subsection \<open>The licensing recursion\<close>

text \<open>Running the first \<open>c\<close> children of a node: the index stack grows in
  lockstep with the frame stack, the node's item advances to dot \<open>c\<close>, and
  its cell moves with the index.\<close>

lemma mtrace_mdrive_kids:
  assumes tab: \<open>tables_ok G Shn sts gt L\<close>
    and kids: \<open>list_all2 (\<lambda>Xr pt. fst (proot pt) = fst Xr \<and>
      irel_sat (snd Xr) (snd (proot pt)) i) rhs pts\<close>
    and kids_tr: \<open>list_all2 (mtrace G) pts trs\<close>
    and wf_kids: \<open>\<forall>q \<in> set pts. wf_ptree G q\<close>
    and IH: \<open>\<And>c Xs' istk' rest'. c < length pts \<Longrightarrow> wf_ptree G (pts ! c) \<Longrightarrow> Xs' \<noteq> [] \<Longrightarrow>
       didx_ok G sts Xs' istk' \<Longrightarrow> nctx G L (hd istk') (pts ! c) (trs ! c) Xs' rest' \<Longrightarrow>
       \<exists>RA. snd (proot (pts ! c)) \<in> irep_set RA \<and>
         mdrive G gt sts L (trs ! c) ((Xs', tcols (pyield (pts ! c)) @ rest'), istk') \<and>
         imrun G gt sts (trs ! c) ((Xs', tcols (pyield (pts ! c)) @ rest'), istk') =
           Some ((lgoto (xclosure_auto G (hd Xs')) (fst (proot (pts ! c))) RA # Xs', rest'),
                 dnext gt sts (hd istk') (fst (proot (pts ! c))) # istk')\<close>
    and Xs_ne: \<open>Xs \<noteq> []\<close> and ok\<^sub>0: \<open>didx_ok G sts Xs istk\<close>
    and item\<^sub>0: \<open>((A, rhs), 0, R\<^sub>0) \<in> set (xclosure_auto G (hd Xs))\<close>
    and i\<^sub>0: \<open>i \<in> irep_set R\<^sub>0\<close>
    and cell\<^sub>0: \<open>cell_ok L (hd istk) (A, rhs) 0 rest i\<close>
    and c_le: \<open>c \<le> length pts\<close>
  shows \<open>\<exists>Xs\<^sub>c istk\<^sub>c R\<^sub>c.
        imrun G gt sts (concat (take c trs))
            ((Xs, tcols (concat (map pyield pts)) @ rest), istk) =
          Some ((Xs\<^sub>c, tcols (concat (map pyield (drop c pts))) @ rest), istk\<^sub>c) \<and>
        mdrive G gt sts L (concat (take c trs))
            ((Xs, tcols (concat (map pyield pts)) @ rest), istk) \<and>
        drop c Xs\<^sub>c = Xs \<and> length Xs\<^sub>c = c + length Xs \<and>
        drop c istk\<^sub>c = istk \<and> length istk\<^sub>c = c + length istk \<and>
        didx_ok G sts Xs\<^sub>c istk\<^sub>c \<and>
        ((A, rhs), c, R\<^sub>c) \<in> set (xclosure_auto G (hd Xs\<^sub>c)) \<and> i \<in> irep_set R\<^sub>c \<and>
        cell_ok L (hd istk\<^sub>c) (A, rhs) c rest i\<close>
proof -
  have len_pr: \<open>length pts = length rhs\<close> using kids by (simp add: list_all2_lengthD)
  have len_tr: \<open>length trs = length pts\<close> using kids_tr by (simp add: list_all2_lengthD)
  show ?thesis using c_le
  proof (induction c)
    case 0
    show ?case
      by (intro exI[of _ Xs] exI[of _ istk] exI[of _ R\<^sub>0])
         (use item\<^sub>0 i\<^sub>0 cell\<^sub>0 ok\<^sub>0 in simp)
  next
    case (Suc c)
    then have c_lt: \<open>c < length pts\<close> by simp
    from Suc.IH[OF Suc_leD[OF Suc.prems]] obtain Xs\<^sub>c istk\<^sub>c R\<^sub>c where
        run_c: \<open>imrun G gt sts (concat (take c trs))
            ((Xs, tcols (concat (map pyield pts)) @ rest), istk) =
          Some ((Xs\<^sub>c, tcols (concat (map pyield (drop c pts))) @ rest), istk\<^sub>c)\<close>
      and drv_c: \<open>mdrive G gt sts L (concat (take c trs))
            ((Xs, tcols (concat (map pyield pts)) @ rest), istk)\<close>
      and drop_c: \<open>drop c Xs\<^sub>c = Xs\<close> and len_c: \<open>length Xs\<^sub>c = c + length Xs\<close>
      and dropi_c: \<open>drop c istk\<^sub>c = istk\<close> and leni_c: \<open>length istk\<^sub>c = c + length istk\<close>
      and ok_c: \<open>didx_ok G sts Xs\<^sub>c istk\<^sub>c\<close>
      and item_c: \<open>((A, rhs), c, R\<^sub>c) \<in> set (xclosure_auto G (hd Xs\<^sub>c))\<close>
      and i_c: \<open>i \<in> irep_set R\<^sub>c\<close>
      and cell_c: \<open>cell_ok L (hd istk\<^sub>c) (A, rhs) c rest i\<close> by blast
    have Xsc_ne: \<open>Xs\<^sub>c \<noteq> []\<close> using len_c Xs_ne by auto
    have istkc_ne: \<open>istk\<^sub>c \<noteq> []\<close> using Xsc_ne ok_c by (auto dest: didx_ok_len)
    let ?pt = \<open>pts ! c\<close> and ?tr = \<open>trs ! c\<close>
    have kid_c: \<open>fst (proot ?pt) = fst (rhs ! c) \<and> irel_sat (snd (rhs ! c)) (snd (proot ?pt)) i\<close>
      using list_all2_nthD[OF kids, of c] c_lt len_pr by auto
    have c_rhs: \<open>c < length (snd (A, rhs))\<close> using c_lt len_pr by simp
    have wf_c: \<open>wf_ptree G ?pt\<close> using wf_kids c_lt by simp
    let ?suf = \<open>tcols (concat (map pyield (drop (Suc c) pts)))\<close>
    let ?rest_c = \<open>?suf @ rest\<close>
    \<comment> \<open>the slot witness for the child\<close>
    have slot_c: \<open>slot_ok (xclosure_auto G (hd Xs\<^sub>c)) (fst (proot ?pt)) (snd (proot ?pt))\<close>
      by (rule slot_okI[OF item_c c_rhs _ i_c]) (use kid_c in simp_all)
    \<comment> \<open>the cell for the child, both cases\<close>
    have kids_sfx: \<open>list_all2 (\<lambda>Xr q. fst (proot q) = fst Xr \<and>
          irel_sat (snd Xr) (snd (proot q)) i) (drop (Suc c) rhs) (drop (Suc c) pts)\<close>
      using kids by (rule list_all2_dropI)
    have wf_sfx: \<open>\<forall>q \<in> set (drop (Suc c) pts). wf_ptree G q\<close>
      using wf_kids by (meson in_set_dropD)
    have first_c: \<open>?suf \<noteq> [] \<Longrightarrow> \<exists>\<sigma>. (fst (hd ?suf), \<sigma>)
          \<in> set (fscan (ffix G) (nullables G) (drop (Suc c) (snd (A, rhs))))
          \<and> csat \<sigma> (snd (hd ?suf)) i\<close>
    proof -
      assume ne: \<open>?suf \<noteq> []\<close>
      obtain a cl V where sf: \<open>?suf = (a, cl) # V\<close> using ne by (cases ?suf) auto
      from kids_first[OF kids_sfx wf_sfx sf] show ?thesis using sf by simp
    qed
    have null_c: \<open>?suf = [] \<Longrightarrow>
        list_all (\<lambda>(X, r). nsym (nullables G) X) (drop (Suc c) (snd (A, rhs)))\<close>
    proof -
      assume e: \<open>?suf = []\<close>
      then have \<open>concat (map pyield (drop (Suc c) pts)) = []\<close> unfolding tcols_def by simp
      from kids_null[OF kids_sfx wf_sfx this] show ?thesis by simp
    qed
    have ctx_c: \<open>nctx G L (hd istk\<^sub>c) ?pt ?tr Xs\<^sub>c ?rest_c\<close>
      unfolding nctx_def
    proof (intro conjI allI impI)
      show \<open>slot_ok (xclosure_auto G (hd Xs\<^sub>c)) (fst (proot ?pt)) (snd (proot ?pt))\<close>
        by (rule slot_c)
    next
      fix B jc pts' assume pt_eq: \<open>?pt = PNode B jc pts'\<close>
      have tr_c: \<open>mtrace G ?pt ?tr\<close> using kids_tr c_lt by (auto simp: list_all2_conv_all_nth)
      from mtrace_node_last[OF tr_c[unfolded pt_eq]] obtain brhs trs' where
          tr_eq: \<open>?tr = concat trs' @ [DReduce (B, brhs)]\<close>
        and brhs: \<open>(B, brhs) \<in> set (iprods G)\<close> by blast
      have nxt: \<open>fst (snd (A, rhs) ! c) = Nt B\<close> using kid_c pt_eq by simp
      have sat: \<open>irel_sat (snd (snd (A, rhs) ! c)) jc i\<close> using kid_c pt_eq by simp
      from xclosure_auto_slot[OF item_c c_rhs nxt brhs i_c sat]
      obtain R' where R': \<open>((B, brhs), 0, R') \<in> set (xclosure_auto G (hd Xs\<^sub>c))\<close>
        and jcR': \<open>jc \<in> irep_set R'\<close> by blast
      have cell_kid: \<open>cell_ok L (hd istk\<^sub>c) (B, brhs) 0 ?rest_c jc\<close>
        by (rule cell_ok_child[OF tab cell_c c_rhs nxt brhs _ sat refl first_c null_c]) simp
      show \<open>\<exists>pr R\<^sub>0. ?tr \<noteq> [] \<and> last ?tr = DReduce pr \<and>
          (pr, 0, R\<^sub>0) \<in> set (xclosure_auto G (hd Xs\<^sub>c)) \<and> jc \<in> irep_set R\<^sub>0 \<and>
          cell_ok L (hd istk\<^sub>c) pr 0 ?rest_c jc\<close>
        using tr_eq R' jcR' cell_kid by auto
    qed
    from IH[OF c_lt wf_c Xsc_ne ok_c ctx_c] obtain RA where
        jc_RA: \<open>snd (proot ?pt) \<in> irep_set RA\<close>
      and drv_kid: \<open>mdrive G gt sts L ?tr ((Xs\<^sub>c, tcols (pyield ?pt) @ ?rest_c), istk\<^sub>c)\<close>
      and run_kid: \<open>imrun G gt sts ?tr ((Xs\<^sub>c, tcols (pyield ?pt) @ ?rest_c), istk\<^sub>c) =
          Some ((lgoto (xclosure_auto G (hd Xs\<^sub>c)) (fst (proot ?pt)) RA # Xs\<^sub>c, ?rest_c),
                dnext gt sts (hd istk\<^sub>c) (fst (proot ?pt)) # istk\<^sub>c)\<close> by blast
    let ?F = \<open>lgoto (xclosure_auto G (hd Xs\<^sub>c)) (fst (proot ?pt)) RA\<close>
    let ?j = \<open>dnext gt sts (hd istk\<^sub>c) (fst (proot ?pt))\<close>
    have yield_split: \<open>tcols (concat (map pyield (drop c pts))) @ rest =
        tcols (pyield ?pt) @ ?rest_c\<close>
      using c_lt by (simp add: Cons_nth_drop_Suc[symmetric])
    have take_Suc: \<open>concat (take (Suc c) trs) = concat (take c trs) @ ?tr\<close>
      using c_lt len_tr by (simp add: take_Suc_conv_app_nth)
    have run': \<open>imrun G gt sts (concat (take (Suc c) trs))
        ((Xs, tcols (concat (map pyield pts)) @ rest), istk) = Some ((?F # Xs\<^sub>c, ?rest_c), ?j # istk\<^sub>c)\<close>
      by (simp only: take_Suc imrun_append run_c option.case yield_split run_kid)
    have drv': \<open>mdrive G gt sts L (concat (take (Suc c) trs))
        ((Xs, tcols (concat (map pyield pts)) @ rest), istk)\<close>
      unfolding take_Suc by (rule mdrive_append[OF drv_c run_c drv_kid[unfolded yield_split[symmetric]]])
    have item': \<open>((A, rhs), Suc c, irep_inter R\<^sub>c (irep_pre (snd (snd (A, rhs) ! c)) RA))
        \<in> set ?F\<close>
      using lgoto_memI[OF item_c, of \<open>fst (proot ?pt)\<close> RA] c_rhs kid_c by simp
    have i': \<open>i \<in> irep_set (irep_inter R\<^sub>c (irep_pre (snd (snd (A, rhs) ! c)) RA))\<close>
      using i_c jc_RA kid_c by auto
    have F_ne: \<open>?F \<noteq> []\<close> using item' by auto
    have x\<^sub>0: \<open>Xs\<^sub>c ! 0 = hd Xs\<^sub>c\<close> and iq\<^sub>0: \<open>istk\<^sub>c ! 0 = hd istk\<^sub>c\<close>
      using Xsc_ne istkc_ne by (simp_all add: hd_conv_nth)
    have push: \<open>didx_ok G sts (?F # Xs\<^sub>c) (?j # istk\<^sub>c)\<close>
      using didx_ok_push[OF tab ok_c, of 0 \<open>fst (proot ?pt)\<close> RA] Xsc_ne F_ne x\<^sub>0 iq\<^sub>0 by simp
    \<comment> \<open>the cell moves with the index\<close>
    have i_lt_c: \<open>hd istk\<^sub>c < length sts\<close>
      by (rule didx_ok_creach(1)[OF ok_c Xsc_ne item_c i_c])
    have core_c: \<open>((A, rhs), c) \<in> set (creach G (sts ! hd istk\<^sub>c))\<close>
      by (rule didx_ok_creach(2)[OF ok_c Xsc_ne item_c i_c])
    have dn: \<open>?j = la_next gt sts (hd istk\<^sub>c) (fst (snd (A, rhs) ! c))\<close>
      using dnext_resolve(3)[OF tab i_lt_c core_c c_rhs] kid_c by simp
    have cell': \<open>cell_ok L ?j (A, rhs) (Suc c) rest i\<close>
      unfolding dn by (rule cell_ok_step[OF tab cell_c c_rhs])
    have item'': \<open>((A, rhs), Suc c, irep_inter R\<^sub>c (irep_pre (snd (snd (A, rhs) ! c)) RA))
        \<in> set (xclosure_auto G ?F)\<close>
      using item' xclosure_auto_kernel_sub[of ?F G] by blast
    show ?case
      by (intro exI[of _ \<open>?F # Xs\<^sub>c\<close>] exI[of _ \<open>?j # istk\<^sub>c\<close>]
                exI[of _ \<open>irep_inter R\<^sub>c (irep_pre (snd (snd (A, rhs) ! c)) RA)\<close>])
         (use run' drv' drop_c len_c dropi_c leni_c push item'' i' cell' in simp)
  qed
qed

lemma mtrace_mdrive:
  assumes tab: \<open>tables_ok G Shn sts gt L\<close>
  shows \<open>mtrace G pt acts \<Longrightarrow> wf_ptree G pt \<Longrightarrow> Xs \<noteq> [] \<Longrightarrow> didx_ok G sts Xs istk \<Longrightarrow>
     nctx G L (hd istk) pt acts Xs rest \<Longrightarrow>
     \<exists>RA. snd (proot pt) \<in> irep_set RA \<and>
       mdrive G gt sts L acts ((Xs, tcols (pyield pt) @ rest), istk) \<and>
       imrun G gt sts acts ((Xs, tcols (pyield pt) @ rest), istk) =
         Some ((lgoto (xclosure_auto G (hd Xs)) (fst (proot pt)) RA # Xs, rest),
               dnext gt sts (hd istk) (fst (proot pt)) # istk)\<close>
proof (induction arbitrary: Xs istk rest rule: mtrace.induct)
  case (mt_leaf t)
  let ?c = \<open>s_col (token.span t)\<close>
  let ?RA = \<open>FinRep [?c]\<close>
  have istk_ne: \<open>istk \<noteq> []\<close> using mt_leaf.prems(2,3) by (auto dest: didx_ok_len)
  have w: \<open>tcols (pyield (PLeaf t)) @ rest = (tok t, ?c) # rest\<close>
    unfolding tcols_def by simp
  have ms: \<open>mstep G (Xs, (tok t, ?c) # rest) DShift =
      Some (lgoto (xclosure_auto G (hd Xs)) (Tm (tok t)) ?RA # Xs, rest)\<close>
    unfolding mstep_def mstep_cached_def using mt_leaf.prems(2) by (simp add: hd_map)
  have im: \<open>imstep G gt sts ((Xs, (tok t, ?c) # rest), istk) DShift =
      Some ((lgoto (xclosure_auto G (hd Xs)) (Tm (tok t)) ?RA # Xs, rest),
            dnext gt sts (hd istk) (Tm (tok t)) # istk)\<close>
    unfolding imstep_def by (simp add: ms)
  have slot: \<open>slot_ok (xclosure_auto G (hd Xs)) (Tm (tok t)) ?c\<close>
    using nctx_slot[OF mt_leaf.prems(4)] by simp
  have live: \<open>dlive (fst ((lgoto (xclosure_auto G (hd Xs)) (Tm (tok t)) ?RA # Xs, rest),
      dnext gt sts (hd istk) (Tm (tok t)) # istk))\<close>
    using slot_ok_dlive[OF slot, of ?RA] by simp
  have drv: \<open>mdrive G gt sts L [DShift] ((Xs, (tok t, ?c) # rest), istk)\<close>
    by (rule mdrive_ConsI[OF im live _ mdrive_Nil]) simp
  show ?case
    by (intro exI[of _ ?RA]) (use drv im w in simp)
next
  case (mt_node A rhs i pts trs)
  note prod = mt_node.hyps(1) and kids = mt_node.hyps(2)
  note wf = mt_node.prems(1) and Xs_ne = mt_node.prems(2)
    and ok\<^sub>0 = mt_node.prems(3) and ctx = mt_node.prems(4)
  have kids_tr: \<open>list_all2 (mtrace G) pts trs\<close>
    using mt_node.IH by (auto simp: list_all2_conv_all_nth)
  have len_pr: \<open>length pts = length rhs\<close> using kids by (simp add: list_all2_lengthD)
  have len_tr: \<open>length trs = length pts\<close> using kids_tr by (simp add: list_all2_lengthD)
  have wf_kids: \<open>\<forall>q \<in> set pts. wf_ptree G q\<close>
    using wf by (auto elim!: wf_ptree.cases simp: list_all2_conv_all_nth set_conv_nth)
  have IH: \<open>\<And>c Xs' istk' rest'. c < length pts \<Longrightarrow> wf_ptree G (pts ! c) \<Longrightarrow> Xs' \<noteq> [] \<Longrightarrow>
       didx_ok G sts Xs' istk' \<Longrightarrow> nctx G L (hd istk') (pts ! c) (trs ! c) Xs' rest' \<Longrightarrow>
       \<exists>RA. snd (proot (pts ! c)) \<in> irep_set RA \<and>
         mdrive G gt sts L (trs ! c) ((Xs', tcols (pyield (pts ! c)) @ rest'), istk') \<and>
         imrun G gt sts (trs ! c) ((Xs', tcols (pyield (pts ! c)) @ rest'), istk') =
           Some ((lgoto (xclosure_auto G (hd Xs')) (fst (proot (pts ! c))) RA # Xs', rest'),
                 dnext gt sts (hd istk') (fst (proot (pts ! c))) # istk')\<close>
    using mt_node.IH by (auto simp: list_all2_conv_all_nth)
  have istk\<^sub>0_ne: \<open>istk \<noteq> []\<close> using Xs_ne ok\<^sub>0 by (auto dest: didx_ok_len)
  have slot\<^sub>0: \<open>slot_ok (xclosure_auto G (hd Xs)) (Nt A) i\<close>
    using nctx_slot[OF ctx] by simp
  from nctx_node[OF ctx] obtain pr R\<^sub>0 where
      last_pr: \<open>last (concat trs @ [DReduce (A, rhs)]) = DReduce pr\<close>
    and item\<^sub>0': \<open>(pr, 0, R\<^sub>0) \<in> set (xclosure_auto G (hd Xs))\<close> and i\<^sub>0: \<open>i \<in> irep_set R\<^sub>0\<close>
    and cell\<^sub>0': \<open>cell_ok L (hd istk) pr 0 rest i\<close> by blast
  have pr_eq: \<open>pr = (A, rhs)\<close> using last_pr by simp
  note item\<^sub>0 = item\<^sub>0'[unfolded pr_eq] and cell\<^sub>0 = cell\<^sub>0'[unfolded pr_eq]
  from mtrace_mdrive_kids[OF tab kids kids_tr wf_kids IH Xs_ne ok\<^sub>0 item\<^sub>0 i\<^sub>0 cell\<^sub>0 order.refl]
  obtain Xs\<^sub>n istk\<^sub>n R\<^sub>n where
      run_n: \<open>imrun G gt sts (concat trs) ((Xs, tcols (concat (map pyield pts)) @ rest), istk) =
        Some ((Xs\<^sub>n, rest), istk\<^sub>n)\<close>
    and drv_n: \<open>mdrive G gt sts L (concat trs)
        ((Xs, tcols (concat (map pyield pts)) @ rest), istk)\<close>
    and drop_n: \<open>drop (length pts) Xs\<^sub>n = Xs\<close> and len_n: \<open>length Xs\<^sub>n = length pts + length Xs\<close>
    and dropi_n: \<open>drop (length pts) istk\<^sub>n = istk\<close>
    and leni_n: \<open>length istk\<^sub>n = length pts + length istk\<close>
    and ok_n: \<open>didx_ok G sts Xs\<^sub>n istk\<^sub>n\<close>
    and item_n: \<open>((A, rhs), length pts, R\<^sub>n) \<in> set (xclosure_auto G (hd Xs\<^sub>n))\<close>
    and i_n: \<open>i \<in> irep_set R\<^sub>n\<close>
    and cell_n: \<open>cell_ok L (hd istk\<^sub>n) (A, rhs) (length pts) rest i\<close>
    using len_tr by auto
  have Xsn_ne: \<open>Xs\<^sub>n \<noteq> []\<close> using len_n Xs_ne by auto
  have istkn_ne: \<open>istk\<^sub>n \<noteq> []\<close> using Xsn_ne ok_n by (auto dest: didx_ok_len)
  have k_lt: \<open>length rhs < length Xs\<^sub>n\<close> using len_n len_pr Xs_ne by simp
  let ?RS = \<open>red_set (xclosure_auto G (hd Xs\<^sub>n)) (A, rhs)\<close>
  have RS_i: \<open>i \<in> irep_set ?RS\<close>
    using item_n i_n len_pr by (auto simp: red_set_correct)
  then have RS_ne: \<open>irep_nonempty ?RS\<close> by auto
  have nth_n: \<open>Xs\<^sub>n ! length rhs = hd Xs\<close>
    using drop_n len_pr Xs_ne by (metis hd_drop_conv_nth k_lt)
  have ki_lt: \<open>length rhs < length istk\<^sub>n\<close> using leni_n len_pr istk\<^sub>0_ne by simp
  have dropi_n': \<open>drop (length rhs) istk\<^sub>n = istk\<close> using dropi_n len_pr by simp
  have nthi_n: \<open>istk\<^sub>n ! length rhs = hd istk\<close>
    using dropi_n' istk\<^sub>0_ne by (metis hd_drop_conv_nth ki_lt)
  have red: \<open>mstep G (Xs\<^sub>n, rest) (DReduce (A, rhs)) =
      Some (lgoto (xclosure_auto G (hd Xs)) (Nt A) ?RS # Xs, rest)\<close>
    unfolding mstep_def mstep_cached_def using k_lt RS_ne Xsn_ne nth_n drop_n len_pr
    by (simp add: Let_def hd_map)
  have imred: \<open>imstep G gt sts ((Xs\<^sub>n, rest), istk\<^sub>n) (DReduce (A, rhs)) =
      Some ((lgoto (xclosure_auto G (hd Xs)) (Nt A) ?RS # Xs, rest),
            dnext gt sts (hd istk) (Nt A) # istk)\<close>
    unfolding imstep_def by (simp add: red nthi_n dropi_n')
  have live: \<open>dlive (fst ((lgoto (xclosure_auto G (hd Xs)) (Nt A) ?RS # Xs, rest),
      dnext gt sts (hd istk) (Nt A) # istk))\<close>
    using slot_ok_dlive[OF slot\<^sub>0 RS_i] by simp
  have in_lt: \<open>hd istk\<^sub>n < length sts\<close>
    by (rule didx_ok_creach(1)[OF ok_n Xsn_ne item_n i_n])
  have cell_n': \<open>cell_ok L (hd istk\<^sub>n) (A, rhs) (length (snd (A, rhs))) rest i\<close>
    using cell_n len_pr by simp
  have lic: \<open>lic_at G L sts ((Xs\<^sub>n, rest), istk\<^sub>n) (A, rhs)\<close>
    unfolding lic_at_def using in_lt cell_ok_dlic[OF cell_n' RS_i] by simp
  have drv_red: \<open>mdrive G gt sts L [DReduce (A, rhs)] ((Xs\<^sub>n, rest), istk\<^sub>n)\<close>
    by (rule mdrive_ConsI[OF imred live _ mdrive_Nil]) (use lic in simp)
  have drv_all: \<open>mdrive G gt sts L (concat trs @ [DReduce (A, rhs)])
      ((Xs, tcols (concat (map pyield pts)) @ rest), istk)\<close>
    by (rule mdrive_append[OF drv_n run_n drv_red])
  have run_all: \<open>imrun G gt sts (concat trs @ [DReduce (A, rhs)])
      ((Xs, tcols (concat (map pyield pts)) @ rest), istk) =
        Some ((lgoto (xclosure_auto G (hd Xs)) (Nt A) ?RS # Xs, rest),
              dnext gt sts (hd istk) (Nt A) # istk)\<close>
    by (simp only: imrun_append run_n option.case imrun.simps imred)
  show ?case
    by (intro exI[of _ ?RS]) (use drv_all run_all RS_i in simp)
qed

subsection \<open>The root context, and completeness of \<^const>\<open>dparse\<close>\<close>



lemma slot_ok_xinit: \<open>slot_ok (xclosure_auto G (xinit G Shn)) (Nt (istart G)) (istart_ind G)\<close>
proof -
  have \<open>(start_prod G Shn, 0, FinRep [istart_ind G]) \<in> set (xclosure_auto G (xinit G Shn))\<close>
    using xclosure_auto_kernel_sub[of \<open>xinit G Shn\<close> G]
    unfolding xinit_def start_prod_def by auto
  then show ?thesis
    by (rule slot_okI) (simp_all add: start_prod_def)
qed

text \<open>At the root, the context is the start item's dot-0 slot of the initial
  frame with the root cell; the trace then drives the machine from the
  initial configuration to the accepting one.\<close>

lemma mtrace_root:
  assumes wf: \<open>wf_ptree G pt\<close> and rt: \<open>proot pt = (Nt (istart G), istart_ind G)\<close>
    and tr: \<open>mtrace G pt acts\<close>
  shows \<open>\<exists>RA. istart_ind G \<in> irep_set RA \<and>
    mdrive G (pgtab G (pr0_states G Shn)) (pr0_states G Shn) (la_fix G Shn) acts
      (([xinit G Shn], tcols (pyield pt)), [st_find (pr0_states G Shn) (lr0_start G Shn)]) \<and>
    imrun G (pgtab G (pr0_states G Shn)) (pr0_states G Shn) acts
      (([xinit G Shn], tcols (pyield pt)), [st_find (pr0_states G Shn) (lr0_start G Shn)]) =
      Some ((lgoto (xclosure_auto G (xinit G Shn)) (Nt (istart G)) RA # [xinit G Shn], []),
            dnext (pgtab G (pr0_states G Shn)) (pr0_states G Shn)
              (st_find (pr0_states G Shn) (lr0_start G Shn)) (Nt (istart G))
            # [st_find (pr0_states G Shn) (lr0_start G Shn)])\<close>
proof -
  let ?sts = \<open>pr0_states G Shn\<close> and ?gt = \<open>pgtab G (pr0_states G Shn)\<close>
  let ?L = \<open>la_fix G Shn\<close> and ?i\<^sub>0 = \<open>st_find (pr0_states G Shn) (lr0_start G Shn)\<close>
  have tab: \<open>tables_ok G Shn ?sts ?gt ?L\<close> by (rule tables_ok_concrete)
  obtain pts where pt: \<open>pt = PNode (istart G) (istart_ind G) pts\<close>
    using rt by (cases pt) auto
  from mtrace_node_last[OF tr[unfolded pt]] obtain rhs trs where
      acts_eq: \<open>acts = concat trs @ [DReduce (istart G, rhs)]\<close>
    and prod: \<open>(istart G, rhs) \<in> set (iprods G)\<close> by blast
  have xinit_item: \<open>((start_prod G Shn, 0, FinRep [istart_ind G])) \<in> set (xclosure_auto G (xinit G Shn))\<close>
    using xclosure_auto_kernel_sub[of \<open>xinit G Shn\<close> G] unfolding xinit_def start_prod_def by auto
  have ctx: \<open>nctx G ?L ?i\<^sub>0 pt acts [xinit G Shn] []\<close>
    unfolding nctx_def
  proof (intro conjI allI impI)
    show \<open>slot_ok (xclosure_auto G (hd [xinit G Shn])) (fst (proot pt)) (snd (proot pt))\<close>
      using slot_ok_xinit rt by simp
  next
    fix A j pts' assume \<open>pt = PNode A j pts'\<close>
    then have A: \<open>A = istart G\<close> and j: \<open>j = istart_ind G\<close> using pt by auto
    from xclosure_auto_slot[OF xinit_item _ _ prod, of \<open>istart_ind G\<close> \<open>istart_ind G\<close>]
    obtain R' where R': \<open>((istart G, rhs), 0, R') \<in> set (xclosure_auto G (xinit G Shn))\<close>
      and jR': \<open>istart_ind G \<in> irep_set R'\<close> unfolding start_prod_def by auto
    have cell: \<open>cell_ok ?L ?i\<^sub>0 (istart G, rhs) 0 [] (istart_ind G)\<close>
      by (rule cell_ok_root[OF tab refl prod]) simp
    show \<open>\<exists>pr R\<^sub>0. acts \<noteq> [] \<and> last acts = DReduce pr \<and>
        (pr, 0, R\<^sub>0) \<in> set (xclosure_auto G (hd [xinit G Shn])) \<and> j \<in> irep_set R\<^sub>0 \<and>
        cell_ok ?L ?i\<^sub>0 pr 0 [] j\<close>
      using acts_eq R' jR' cell j by auto
  qed
  have ne: \<open>[xinit G Shn] \<noteq> []\<close> by simp
  have ok\<^sub>0: \<open>didx_ok G ?sts [xinit G Shn] [?i\<^sub>0]\<close> by (rule didx_ok_init[OF tab])
  have ctx': \<open>nctx G ?L (hd [?i\<^sub>0]) pt acts [xinit G Shn] []\<close> using ctx by simp
  from mtrace_mdrive[OF tab tr wf ne ok\<^sub>0 ctx'] show ?thesis using rt by simp
qed

lemma mdrive_root:
  assumes wf: \<open>wf_ptree G pt\<close> and rt: \<open>proot pt = (Nt (istart G), istart_ind G)\<close>
    and tr: \<open>mtrace G pt acts\<close>
  shows \<open>mdrive G (pgtab G (pr0_states G Shn)) (pr0_states G Shn) (la_fix G Shn) acts
           (([xinit G Shn], tcols (pyield pt)), [st_find (pr0_states G Shn) (lr0_start G Shn)])\<close>
  using mtrace_root[OF wf rt tr] by blast

theorem mtrace_completes:
  assumes wf: \<open>wf_ptree G pt\<close> and tr: \<open>mtrace G pt acts\<close>
    and rt: \<open>proot pt = (Nt (istart G), istart_ind G)\<close>
  shows \<open>mcompletes G Shn acts ([xinit G Shn], tcols (pyield pt))\<close>
proof -
  from mtrace_root[OF wf rt tr] obtain RA where
      i0: \<open>istart_ind G \<in> irep_set RA\<close>
    and run': \<open>imrun G (pgtab G (pr0_states G Shn)) (pr0_states G Shn) acts
      (([xinit G Shn], tcols (pyield pt)), [st_find (pr0_states G Shn) (lr0_start G Shn)]) =
      Some ((lgoto (xclosure_auto G (xinit G Shn)) (Nt (istart G)) RA # [xinit G Shn], []),
            dnext (pgtab G (pr0_states G Shn)) (pr0_states G Shn)
              (st_find (pr0_states G Shn) (lr0_start G Shn)) (Nt (istart G))
            # [st_find (pr0_states G Shn) (lr0_start G Shn)])\<close> by blast
  have run: \<open>mrun G acts ([xinit G Shn], tcols (pyield pt)) =
      Some (lgoto (xclosure_auto G (xinit G Shn)) (Nt (istart G)) RA # [xinit G Shn], [])\<close>
    using imrun_mrun[OF run'] by simp
  have xinit_item: \<open>((start_prod G Shn, 0, FinRep [istart_ind G])) \<in> set (xclosure_auto G (xinit G Shn))\<close>
    using xclosure_auto_kernel_sub[of \<open>xinit G Shn\<close> G] unfolding xinit_def start_prod_def by auto
  have fin_item: \<open>((start_prod G Shn, Suc 0,
      irep_inter (FinRep [istart_ind G]) (irep_pre Eq RA)))
      \<in> set (lgoto (xclosure_auto G (xinit G Shn)) (Nt (istart G)) RA)\<close>
    using lgoto_memI[OF xinit_item, of \<open>Nt (istart G)\<close> RA] unfolding start_prod_def by simp
  have \<open>gfinal G Shn (lgoto (xclosure_auto G (xinit G Shn)) (Nt (istart G)) RA # [xinit G Shn], [])\<close>
    unfolding gfinal_def using fin_item i0
    by (auto simp: list_ex_iff start_prod_def intro!: bexI[where x = \<open>(start_prod G Shn, Suc 0,
      irep_inter (FinRep [istart_ind G]) (irep_pre Eq RA))\<close>])
  then show ?thesis unfolding mcompletes_def run by simp
qed

theorem dparse_complete:
  assumes fn: \<open>fresh_name G Shn\<close> and det: \<open>mdet G Shn\<close>
    and wf: \<open>wf_ptree G pt\<close> and rt: \<open>proot pt = (Nt (istart G), istart_ind G)\<close>
  shows \<open>\<exists>t. dparse G Shn (pyield pt) = Some t \<and>
             ast_of G (Nt (istart G)) (istart_ind G) t (pyield pt)\<close>
proof -
  from mtrace_ex[OF wf] obtain acts where tr: \<open>mtrace G pt acts\<close> by blast
  show ?thesis
    by (rule dparse_complete_of_mdrive[OF fn det mdrive_root[OF wf rt tr] mtrace_completes[OF wf tr rt]])
qed

corollary dparse_complete_lang:
  assumes fn: \<open>fresh_name G Shn\<close> and det: \<open>mdet G Shn\<close> and w: \<open>w \<in> ilang G\<close>
  shows \<open>\<exists>t. dparse G Shn w = Some t \<and> ast_of G (Nt (istart G)) (istart_ind G) t w\<close>
proof -
  from w have \<open>infG G \<turnstile> [Nt (istart G, istart_ind G)] \<Rightarrow>* map Tm (tcols w)\<close>
    unfolding ilang_derives .
  from iffD1[OF derives_iff_ptree this] obtain pt where
      wf: \<open>wf_ptree G pt\<close> and rt: \<open>proot pt = (Nt (istart G), istart_ind G)\<close>
    and y: \<open>pyield pt = w\<close> by blast
  from dparse_complete[OF fn det wf rt] show ?thesis unfolding y .
qed

corollary dparse_iff_lang:
  assumes fn: \<open>fresh_name G Shn\<close> and det: \<open>mdet G Shn\<close>
  shows \<open>dparse G Shn w \<noteq> None \<longleftrightarrow> w \<in> ilang G\<close>
proof
  assume \<open>dparse G Shn w \<noteq> None\<close>
  then obtain t where \<open>dparse G Shn w = Some t\<close> by auto
  from dparse_sound[OF fn this] show \<open>w \<in> ilang G\<close> .
next
  assume \<open>w \<in> ilang G\<close>
  from dparse_complete_lang[OF fn det this] show \<open>dparse G Shn w \<noteq> None\<close> by auto
qed


section \<open>Summary\<close>

text \<open>\<^const>\<open>dparse\<close> is sound unconditionally and complete under
  \<^const>\<open>fresh_name\<close> and \<^const>\<open>mdet\<close>:
  \<^item> \<^text>\<open>dparse_sound_ast\<close> / \<^text>\<open>dparse_sound\<close>
  \<^item> \<^text>\<open>dparse_complete\<close> / \<^text>\<open>dparse_complete_lang\<close>
  \<^item> \<^text>\<open>dparse_iff_lang\<close>: \<open>dparse G Shn w \<noteq> None \<longleftrightarrow> w \<in> ilang G\<close>

  The static sufficient condition for \<^const>\<open>mdet\<close> from a conflict
  report is the subject of
  \<^text>\<open>LR_Det\<close>; the backend \<^text>\<open>LR_Parser\<close> uses
  \<^const>\<open>dparse\<close> through \<^text>\<open>dparse_via_tables\<close>.\<close>


end
