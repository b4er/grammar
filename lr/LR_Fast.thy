theory LR_Fast
  imports LR_Driver
begin

section \<open>A faster closure for the set-anchored driver\<close>

text \<open>Profiling the generated CaraML parser puts nearly all of a step's time
  in \<^const>\<open>xclosure_auto\<close>, the closure of the frame a step pushes.  Its
  rounds (\<^const>\<open>xround\<close>) fold every slot of the round into the
  accumulator of the previous round, so each round unions the previous
  representation again and the \<^const>\<open>FinRep\<close> lists grow with duplicates.
  \<^text>\<open>dclosure\<close> runs the same rounds from a fresh accumulator and
  stops when a round adds nothing.  Its items equal those of
  \<^const>\<open>xclosure_auto\<close> up to the sets their anchor representations
  denote (\<^text>\<open>xeq\<close>), and every driver operation only looks at those
  sets, so a driver that caches \<^text>\<open>dclosure\<close> (\<^text>\<open>drun_nh_c\<close>)
  returns what \<^const>\<open>drun_nh\<close> returns.\<close>

subsection \<open>Item lists equal up to anchor sets\<close>

definition xrel :: \<open>(nat set \<Rightarrow> nat set \<Rightarrow> bool) \<Rightarrow> ('n, 't) xitem list \<Rightarrow> ('n, 't) xitem list \<Rightarrow> bool\<close> where
  \<open>xrel P xs ys \<longleftrightarrow> list_all2 (\<lambda>(p, m, R) (p', m', R'). p = p' \<and> m = m' \<and> P (irep_set R) (irep_set R')) xs ys\<close>

abbreviation xeq :: \<open>('n, 't) xitem list \<Rightarrow> ('n, 't) xitem list \<Rightarrow> bool\<close> where
  \<open>xeq \<equiv> xrel (=)\<close>

lemma xrel_refl: \<open>(\<And>S. P S S) \<Longrightarrow> xrel P xs xs\<close>
  unfolding xrel_def by (induction xs) auto

lemma xeq_refl [simp]: \<open>xeq xs xs\<close>
  by (rule xrel_refl) simp

lemma xeq_sym: \<open>xeq xs ys \<Longrightarrow> xeq ys xs\<close>
  unfolding xrel_def by (induction rule: list_all2_induct) (auto split: prod.split_asm)

lemma xrel_mono: \<open>xrel P xs ys \<Longrightarrow> (\<And>S T. P S T \<Longrightarrow> Q S T) \<Longrightarrow> xrel Q xs ys\<close>
  unfolding xrel_def by (erule list_all2_mono) (auto split: prod.split_asm)

lemma ximg_mono: \<open>irep_set R \<subseteq> irep_set R' \<Longrightarrow> ximg pr (p, m, R) \<subseteq> ximg pr (p, m, R')\<close>
  by (cases p) auto

lemma xrel_ximg:
  \<open>xrel (\<subseteq>) xs ys \<Longrightarrow> \<Union> (ximg pr ` set xs) \<subseteq> \<Union> (ximg pr ` set ys)\<close>
  unfolding xrel_def
proof (induction rule: list_all2_induct)
  case (Cons x xs y ys)
  obtain p m R p' m' R' where \<open>x = (p, m, R)\<close> \<open>y = (p', m', R')\<close> by (metis prod.collapse)
  with Cons.hyps(1) ximg_mono[of R R' pr p m] have \<open>ximg pr x \<subseteq> ximg pr y\<close> by simp
  with Cons.IH show ?case by auto
qed simp

lemma xeq_ximg: \<open>xeq xs ys \<Longrightarrow> \<Union> (ximg pr ` set xs) = \<Union> (ximg pr ` set ys)\<close>
  by (intro equalityI xrel_ximg) (auto elim: xrel_mono dest: xeq_sym)

lemma xslots_xrel:
  assumes \<open>xrel P xs ys\<close> and \<open>list_all2 (\<lambda>a b. P (irep_set a) (irep_set b)) cls cls'\<close>
  shows \<open>xrel P (xslots G xs cls) (xslots G ys cls')\<close>
proof -
  have \<open>list_all2 (\<lambda>(p, m, R) (p', m', R'). p = p' \<and> m = m' \<and> P (irep_set R) (irep_set R'))
      (map2 (\<lambda>pr R. (pr, 0, R)) (iprods G) cls) (map2 (\<lambda>pr R. (pr, 0, R)) (iprods G) cls')\<close>
    using assms(2) by (auto simp: list_all2_conv_all_nth)
  with assms(1) show ?thesis unfolding xrel_def xslots_def by (rule list_all2_appendI)
qed

subsection \<open>Rounds from a fresh accumulator\<close>

definition dround :: \<open>('n, 't) is_cfg \<Rightarrow> ('n, 't) xitem list \<Rightarrow> indrep list \<Rightarrow> indrep list\<close> where
  \<open>dround G xs cls = map (\<lambda>pr. fold (xcontrib pr) (xslots G xs cls) (FinRep [])) (iprods G)\<close>

fun diter :: \<open>('n, 't) is_cfg \<Rightarrow> ('n, 't) xitem list \<Rightarrow> nat \<Rightarrow> indrep list\<close> where
  \<open>diter G xs 0 = map (\<lambda>_. FinRep []) (iprods G)\<close>
| \<open>diter G xs (Suc s) = dround G xs (diter G xs s)\<close>

lemma diter_length [simp]: \<open>length (diter G xs s) = length (iprods G)\<close>
  by (cases s) (simp_all add: dround_def)

lemma xiter_mono:
  \<open>p < length (iprods G) \<Longrightarrow> irep_set (xiter G xs s ! p) \<subseteq> irep_set (xiter G xs (Suc s) ! p)\<close>
  by (simp only: xiter.simps(2) xround_nth[OF xiter_length] fold_xcontrib_set) blast

lemma xiter_Suc_set:
  \<open>p < length (iprods G) \<Longrightarrow>
   irep_set (xiter G xs (Suc s) ! p) = \<Union> (ximg (iprods G ! p) ` set (xslots G xs (xiter G xs s)))\<close>
proof (induction s arbitrary: p)
  case 0
  then show ?case by (simp only: xiter.simps(2) xround_nth[OF xiter_length] fold_xcontrib_set) simp
next
  case (Suc s)
  have \<open>list_all2 (\<lambda>a b. irep_set a \<subseteq> irep_set b) (xiter G xs s) (xiter G xs (Suc s))\<close>
    using xiter_mono[of _ G xs s] by (simp only: list_all2_conv_all_nth xiter_length) blast
  then have \<open>xrel (\<subseteq>) (xslots G xs (xiter G xs s)) (xslots G xs (xiter G xs (Suc s)))\<close>
    by (rule xslots_xrel[OF xrel_refl, rotated]) simp  from xrel_ximg[OF this, of \<open>iprods G ! p\<close>] Suc.IH[OF Suc.prems] show ?case
    by (simp only: xiter.simps(2)[of G xs \<open>Suc s\<close>] xround_nth[OF xiter_length Suc.prems] fold_xcontrib_set) blast
qed

lemma xiter_diter:
  assumes \<open>xeq f f'\<close>
  shows \<open>list_all2 (\<lambda>a b. irep_set a = irep_set b) (xiter G f s) (diter G f' s)\<close>
proof (induction s)
  case 0
  then show ?case by (simp add: list_all2_conv_all_nth)
next
  case (Suc s)
  have eq: \<open>\<Union> (ximg pr ` set (xslots G f (xiter G f s))) = \<Union> (ximg pr ` set (xslots G f' (diter G f' s)))\<close> for pr
    by (rule xeq_ximg[OF xslots_xrel[OF assms Suc.IH]])
  show ?case
    unfolding list_all2_conv_all_nth
  proof (intro conjI allI impI)
    fix p assume \<open>p < length (xiter G f (Suc s))\<close>
    then have p: \<open>p < length (iprods G)\<close> by (simp only: xiter_length)
    show \<open>irep_set (xiter G f (Suc s) ! p) = irep_set (diter G f' (Suc s) ! p)\<close>
      using p by (simp only: xiter_Suc_set[OF p] eq diter.simps dround_def nth_map fold_xcontrib_set) simp
  qed (simp only: xiter_length diter_length)qed

definition dclosure :: \<open>('n, 't) is_cfg \<Rightarrow> ('n, 't) xitem list \<Rightarrow> ('n, 't) xitem list\<close> where
  \<open>dclosure G xs = xslots G xs (diter G xs (xfuel G xs))\<close>

lemma xstable_diter:
  assumes \<open>xeq f f'\<close>
  shows \<open>xstable G f (xiter G f t) \<longleftrightarrow> list_all2 irep_subset (diter G f' (Suc t)) (diter G f' t)\<close>
proof -
  have a: \<open>list_all2 (\<lambda>a b. irep_set a = irep_set b) (xiter G f t) (diter G f' t)\<close>
    and b: \<open>list_all2 (\<lambda>a b. irep_set a = irep_set b) (xiter G f (Suc t)) (diter G f' (Suc t))\<close>
    by (rule xiter_diter[OF assms])+
  have \<open>xstable G f (xiter G f t) \<longleftrightarrow> list_all2 irep_subset (xiter G f (Suc t)) (xiter G f t)\<close>
    by (simp only: xstable_def xiter.simps(2))
  also have \<open>\<dots> \<longleftrightarrow> list_all2 irep_subset (diter G f' (Suc t)) (diter G f' t)\<close>
    using a b by (simp only: list_all2_conv_all_nth irep_subset_correct xiter_length diter_length) auto
  finally show ?thesis .
qed

lemma xfuel_xeq: \<open>xeq f f' \<Longrightarrow> xfuel G f = xfuel G f'\<close>
  unfolding xfuel_def using xstable_diter[of f f'] xstable_diter[of f' f'] by simp

lemma xclosure_auto_dclosure: \<open>xeq f f' \<Longrightarrow> xeq (xclosure_auto G f) (dclosure G f')\<close>
  unfolding xclosure_auto_def xclosure_def dclosure_def
  by (simp only: xfuel_xeq[of f f']) (rule xslots_xrel[OF _ xiter_diter])

text \<open>Executably, the rounds are iterated once, as for \<^const>\<open>xclosure_auto\<close>.\<close>

lemma dclosure_code [code]:
  \<open>dclosure G xs = xslots G xs (fst (the (while_option
     (\<lambda>(cls, nxt). \<not> list_all2 irep_subset nxt cls) (\<lambda>(cls, nxt). (nxt, dround G xs nxt))
     (diter G xs 0, dround G xs (diter G xs 0)))))\<close>
proof -
  obtain k where \<open>xstable G xs (xiter G xs k)\<close>
    using xcls_stable_ex by blast
  then have \<open>while_option (\<lambda>t. \<not> xstable G xs (xiter G xs t)) Suc 0 = Some (xfuel G xs)\<close>
    unfolding xfuel_def by (rule nat_search_Some)
  moreover have
    \<open>map_option (\<lambda>t. (diter G xs t, diter G xs (Suc t)))
       (while_option (\<lambda>t. \<not> xstable G xs (xiter G xs t)) Suc 0) =
     while_option (\<lambda>(cls, nxt). \<not> list_all2 irep_subset nxt cls) (\<lambda>(cls, nxt). (nxt, dround G xs nxt))
       (diter G xs 0, diter G xs (Suc 0))\<close>
    by (rule while_option_commute
        [where f = \<open>\<lambda>t. (diter G xs t, diter G xs (Suc t))\<close> and s = 0])
      (simp_all add: xstable_diter[OF xeq_refl])
  ultimately have
    \<open>Some (diter G xs (xfuel G xs), diter G xs (Suc (xfuel G xs))) =
     while_option (\<lambda>(cls, nxt). \<not> list_all2 irep_subset nxt cls) (\<lambda>(cls, nxt). (nxt, dround G xs nxt))
       (diter G xs 0, dround G xs (diter G xs 0))\<close>
    by simp
  from this[symmetric] show ?thesis
    by (simp add: dclosure_def)
qed

text \<open>For the code, a round builds the slot list once and keeps of it only the
  items before a nonterminal, with their images; each production then folds
  over the images for its left-hand side.\<close>

definition dnx :: \<open>('n, 't) xitem list \<Rightarrow> ('n \<times> indrep) list\<close> where
  \<open>dnx sl = List.map_filter (\<lambda>((A, rhs), m, R).
     if m < length rhs then (case rhs ! m of (Nt B, r) \<Rightarrow> Some (B, irep_img r R) | _ \<Rightarrow> None)
     else None) sl\<close>

lemma fold_xcontrib_dnx:
  \<open>fold (xcontrib pr) sl acc =
   fold (\<lambda>(B, I) acc. if B = fst pr then irep_union I acc else acc) (dnx sl) acc\<close>
  by (induction sl arbitrary: acc)
     (auto simp: dnx_def split: sym.splits prod.splits)

lemma dround_code [code]:
  \<open>dround G xs cls = (let nx = dnx (xslots G xs cls) in
     map (\<lambda>pr. fold (\<lambda>(B, I) acc. if B = fst pr then irep_union I acc else acc) nx (FinRep []))
       (iprods G))\<close>
  unfolding dround_def Let_def by (simp add: fold_xcontrib_dnx)

subsection \<open>Nonterminals as numbers\<close>

text \<open>The left-hand sides of a round are compared as numbers: a nonterminal is
  numbered by its first position among the left-hand sides of the productions,
  the per-production numbers are a table (\<^text>\<open>dtab\<close>) that the
  \<^text>\<open>parser\<close> command evaluates once, and the numbers of the kernel's
  successors are computed once per closure (\<^text>\<open>dkn\<close>).\<close>

fun ntidx :: \<open>'n list \<Rightarrow> 'n \<Rightarrow> nat\<close> where
  \<open>ntidx [] B = 0\<close>
| \<open>ntidx (A # As) B = (if A = B then 0 else Suc (ntidx As B))\<close>

lemma ntidx_eq_iff: \<open>A \<in> set As \<Longrightarrow> ntidx As B = ntidx As A \<longleftrightarrow> B = A\<close>
  by (induction As) auto

definition dtab_of :: \<open>'n list \<Rightarrow> 'n \<times> ('n, 't) rhs \<Rightarrow> nat \<times> nat option\<close> where
  \<open>dtab_of ns = (\<lambda>(A, rhs). (ntidx ns A,
     case rhs of (Nt B, _) # _ \<Rightarrow> Some (ntidx ns B) | _ \<Rightarrow> None))\<close>

definition dtab :: \<open>('n, 't) is_cfg \<Rightarrow> (nat \<times> nat option) list\<close> where
  \<open>dtab G = map (dtab_of (map fst (iprods G))) (iprods G)\<close>

definition dkn :: \<open>('n, 't) is_cfg \<Rightarrow> ('n, 't) xitem list \<Rightarrow> (nat \<times> indrep) list\<close> where
  \<open>dkn G xs = map (\<lambda>(B, I). (ntidx (map fst (iprods G)) B, I)) (dnx xs)\<close>

definition dround_t :: \<open>('n, 't) is_cfg \<Rightarrow> (nat \<times> nat option) list \<Rightarrow> (nat \<times> indrep) list \<Rightarrow>
    indrep list \<Rightarrow> indrep list\<close> where
  \<open>dround_t G dt kn cls = (let
     nx = filter (\<lambda>(_, I). I \<noteq> FinRep []) (kn @ List.map_filter (\<lambda>(((l, f), (A, rhs)), R).
            case f of None \<Rightarrow> None
            | Some b \<Rightarrow> (case rhs of (_, r) # _ \<Rightarrow> Some (b, irep_img r R) | [] \<Rightarrow> None))
          (zip (zip dt (iprods G)) cls))
   in map (\<lambda>(l, f). fold (\<lambda>(b, I) acc. if b = l then irep_union I acc else acc) nx (FinRep [])) dt)\<close>

lemma dnx_append: \<open>dnx (xs @ ys) = dnx xs @ dnx ys\<close>
  unfolding dnx_def by (induction xs) (simp_all split: option.split)

lemma dnx_slots:
  \<open>map (\<lambda>(B, I). (ntidx ns B, I)) (dnx (map2 (\<lambda>pr R. (pr, 0, R)) ps cls)) =
   List.map_filter (\<lambda>(((l, f), (A, rhs)), R). case f of None \<Rightarrow> None
       | Some b \<Rightarrow> (case rhs of (_, r) # _ \<Rightarrow> Some (b, irep_img r R) | [] \<Rightarrow> None))
     (zip (zip (map (dtab_of ns) ps) ps) cls)\<close>
proof (induction ps arbitrary: cls)
  case (Cons pr ps)
  then show ?case
    by (cases cls) (auto simp: dnx_def dtab_of_def split: list.splits sym.splits prod.splits)
qed (simp add: dnx_def)

lemma fold_ntidx:
  assumes \<open>A \<in> set ns\<close>
  shows \<open>fold (\<lambda>(b, I) acc. if b = ntidx ns A then irep_union I acc else acc)
           (map (\<lambda>(B, I). (ntidx ns B, I)) nx) acc =
         fold (\<lambda>(B, I) acc. if B = A then irep_union I acc else acc) nx acc\<close>
  by (induction nx arbitrary: acc) (auto simp: ntidx_eq_iff[OF assms])

text \<open>Images that are empty as representations are dropped: a union with them
  changes nothing, not even the representation.\<close>

lemma fold_union_filter:
  \<open>fold (\<lambda>(b, I) acc. if b = l then irep_union I acc else acc) (filter (\<lambda>(_, I). I \<noteq> FinRep []) nx) acc =
   fold (\<lambda>(b, I) acc. if b = l then irep_union I acc else acc) nx acc\<close>
proof (induction nx arbitrary: acc)
  case (Cons x nx)
  have \<open>irep_union (FinRep []) acc = acc\<close> for acc by (cases acc) simp_all
  with Cons show ?case by (cases x) auto
qed simp

lemma dround_t_dround: \<open>dround_t G (dtab G) (dkn G xs) cls = dround G xs cls\<close>
proof -
  let ?ns = \<open>map fst (iprods G)\<close>
  let ?h = \<open>\<lambda>(B, I). (ntidx ?ns B, I)\<close>
  have nx: \<open>dkn G xs @ List.map_filter (\<lambda>(((l, f), (A, rhs)), R). case f of None \<Rightarrow> None
            | Some b \<Rightarrow> (case rhs of (_, r) # _ \<Rightarrow> Some (b, irep_img r R) | [] \<Rightarrow> None))
          (zip (zip (dtab G) (iprods G)) cls) = map ?h (dnx (xslots G xs cls))\<close>
    unfolding dkn_def dtab_def xslots_def dnx_append map_append dnx_slots ..
  have fe: \<open>fold (\<lambda>(b, I) acc. if b = fst (dtab_of ?ns pr) then irep_union I acc else acc)
          (map ?h (dnx (xslots G xs cls))) (FinRep []) =
        fold (\<lambda>(B, I) acc. if B = fst pr then irep_union I acc else acc)
          (dnx (xslots G xs cls)) (FinRep [])\<close> if \<open>pr \<in> set (iprods G)\<close> for pr
  proof -
    have \<open>fst pr \<in> set ?ns\<close> using that by simp
    moreover have \<open>fst (dtab_of ?ns pr) = ntidx ?ns (fst pr)\<close> by (simp add: dtab_of_def split: prod.split)
    ultimately show ?thesis by (simp only: fold_ntidx)
  qed
  show ?thesis
    unfolding dround_t_def dround_code Let_def nx unfolding dtab_def map_map
    by (intro map_cong refl) (simp only: comp_apply case_prod_beta fold_union_filter fe)
qed

definition dclosure_t :: \<open>('n, 't) is_cfg \<Rightarrow> (nat \<times> nat option) list \<Rightarrow>
    ('n, 't) xitem list \<Rightarrow> ('n, 't) xitem list\<close> where
  \<open>dclosure_t G dt xs = (let kn = dkn G xs in xslots G xs (fst (the (while_option
     (\<lambda>(cls, nxt). \<not> list_all2 irep_subset nxt cls) (\<lambda>(cls, nxt). (nxt, dround_t G dt kn nxt))
     (map (\<lambda>_. FinRep []) dt, dround_t G dt kn (map (\<lambda>_. FinRep []) dt))))))\<close>

lemma dclosure_t_eq: \<open>dclosure_t G (dtab G) xs = dclosure G xs\<close>
proof -
  have \<open>map (\<lambda>_. FinRep []) (dtab G) = diter G xs 0\<close> by (simp add: dtab_def)
  then show ?thesis
    unfolding dclosure_t_def dclosure_code Let_def dround_t_dround by simp
qed

subsection \<open>The driver operations respect set-equality\<close>

lemma list_all2_nth_refl:
  \<open>list_all2 R xs ys \<Longrightarrow> (\<And>x. R x x) \<Longrightarrow> R (xs ! k) (ys ! k)\<close>
proof (induction arbitrary: k rule: list_all2_induct)
  case Nil then show ?case by simp
next
  case (Cons x xs y ys) then show ?case by (cases k) simp_all
qed

lemma list_all2_hd_refl: \<open>list_all2 R xs ys \<Longrightarrow> (\<And>x. R x x) \<Longrightarrow> R (hd xs) (hd ys)\<close>
  using list_all2_nth_refl[of R xs ys 0] by (cases xs; cases ys) simp_all

lemma lgoto_xeq:
  \<open>xeq xs ys \<Longrightarrow> irep_set RA = irep_set RB \<Longrightarrow> xeq (lgoto xs X RA) (lgoto ys X RB)\<close>
  unfolding xrel_def lgoto_def
  by (induction rule: list_all2_induct) (auto split: prod.split_asm)

lemma red_set_xeq: \<open>xeq xs ys \<Longrightarrow> irep_set (red_set xs pr) = irep_set (red_set ys pr)\<close>
  unfolding xrel_def red_set_def
  by (induction rule: list_all2_induct) (auto split: prod.split_asm)

lemma comps_xeq:
  \<open>xeq xs ys \<Longrightarrow> map fst (filter (\<lambda>(pr, m, R). m = length (snd pr)) xs) =
                map fst (filter (\<lambda>(pr, m, R). m = length (snd pr)) ys)\<close>
  unfolding xrel_def by (induction rule: list_all2_induct) (auto split: prod.split_asm)

lemma dlic_cong: \<open>irep_set RS = irep_set RS' \<Longrightarrow> dlic i cells w pr RS = dlic i cells w pr RS'\<close>
  unfolding dlic_def by (simp split: list.splits)
lemma dcands_xeq:
  assumes a: \<open>xeq CL CL'\<close>
  shows \<open>dcands G i cells CL gc = dcands G i cells CL' gc\<close>
proof -
  have eq: \<open>(\<lambda>pr. irep_nonempty (red_set CL pr) \<and> dlic i cells w pr (red_set CL pr)) =
        (\<lambda>pr. irep_nonempty (red_set CL' pr) \<and> dlic i cells w pr (red_set CL' pr))\<close> for w
    by (rule ext) (metis red_set_xeq[OF a] dlic_cong irep_nonempty_correct)
  show ?thesis unfolding dcands_def Let_def comps_xeq[OF a] eq ..
qed

lemma live_xeq: \<open>xeq xs ys \<Longrightarrow> live xs = live ys\<close>
  unfolding xrel_def live_def
  by (induction rule: list_all2_induct) (auto split: prod.split_asm)

lemma gfinal_xeq:
  \<open>list_all2 xeq Ys Ys' \<Longrightarrow> gfinal G Shn (Ys, v) = gfinal G Shn (Ys', v)\<close>
proof -
  assume a: \<open>list_all2 xeq Ys Ys'\<close>
  have \<open>xeq (hd Ys) (hd Ys')\<close> by (rule list_all2_hd_refl[OF a]) simp
  then have \<open>list_ex (\<lambda>(pr, m, R). fst pr = Shn \<and> m = Suc 0 \<and> irep_mem (istart_ind G) R) (hd Ys) =
             list_ex (\<lambda>(pr, m, R). fst pr = Shn \<and> m = Suc 0 \<and> irep_mem (istart_ind G) R) (hd Ys')\<close>
    unfolding xrel_def by (induction rule: list_all2_induct) (auto split: prod.split_asm)
  moreover have \<open>Ys = [] \<longleftrightarrow> Ys' = []\<close> using a by (auto dest: list_all2_lengthD)
  ultimately show ?thesis unfolding gfinal_def by simp
qed

definition gxeq :: \<open>('n, 't) gconfig \<Rightarrow> ('n, 't) gconfig \<Rightarrow> bool\<close> where
  \<open>gxeq gc gc' \<longleftrightarrow> list_all2 xeq (fst gc) (fst gc') \<and> snd gc = snd gc'\<close>

lemma mstep_cached_xeq:
  assumes c: \<open>list_all2 xeq cstk cstk'\<close> and g: \<open>gxeq gc gc'\<close>
  shows \<open>rel_option gxeq (mstep_cached G cstk gc act) (mstep_cached G cstk' gc' act)\<close>
proof -
  obtain Xs w Xs' where gc: \<open>gc = (Xs, w)\<close> \<open>gc' = (Xs', w)\<close> and x: \<open>list_all2 xeq Xs Xs'\<close>
    using g unfolding gxeq_def by (cases gc; cases gc') auto
  have len: \<open>length Xs = length Xs'\<close> using x by (rule list_all2_lengthD)
  have hd: \<open>xeq (hd cstk) (hd cstk')\<close> by (rule list_all2_hd_refl[OF c]) simp
  have nth: \<open>xeq (cstk ! k) (cstk' ! k)\<close> for k by (rule list_all2_nth_refl[OF c]) simp
  have dr: \<open>list_all2 xeq (drop k Xs) (drop k Xs')\<close> for k using x by (rule list_all2_dropI)
  show ?thesis
  proof (cases act)
    case DShift
    then show ?thesis
      using lgoto_xeq[OF hd] x len unfolding gc by (auto simp: mstep_cached_def gxeq_def split: list.splits)
  next
    case (DReduce pr)
    have rs: \<open>irep_set (red_set (hd cstk) pr) = irep_set (red_set (hd cstk') pr)\<close>
      by (rule red_set_xeq[OF hd])
    then show ?thesis
      using DReduce lgoto_xeq[OF nth rs] dr len unfolding gc
      by (auto simp: mstep_cached_def gxeq_def Let_def)
  qed
qed

lemma dlive_xeq: \<open>gxeq gc gc' \<Longrightarrow> dlive gc = dlive gc'\<close>
proof -
  assume g: \<open>gxeq gc gc'\<close>
  then have x: \<open>list_all2 xeq (fst gc) (fst gc')\<close> unfolding gxeq_def by simp
  have \<open>xeq (hd (fst gc)) (hd (fst gc'))\<close> by (rule list_all2_hd_refl[OF x]) simp
  moreover have \<open>fst gc = [] \<longleftrightarrow> fst gc' = []\<close> using x by (auto dest: list_all2_lengthD)
  ultimately show ?thesis unfolding dlive_def by (auto split: prod.splits dest: live_xeq)
qed

lemma dpick_xeq:
  assumes c: \<open>list_all2 xeq cstk cstk'\<close> and g: \<open>gxeq gc gc'\<close>
  shows \<open>rel_option (\<lambda>(a, g) (a', g'). a = a' \<and> gxeq g g') (dpick G cstk gc acts) (dpick G cstk' gc' acts)\<close>
proof (induction acts)
  case (Cons act acts)
  show ?case
  proof (cases \<open>mstep_cached G cstk gc act\<close>)
    case None
    with mstep_cached_xeq[OF c g, of G act] have \<open>mstep_cached G cstk' gc' act = None\<close>
      by (cases \<open>mstep_cached G cstk' gc' act\<close>) simp_all
    with None Cons.IH show ?thesis by simp
  next
    case (Some g1)
    with mstep_cached_xeq[OF c g, of G act] obtain g1' where
      \<open>mstep_cached G cstk' gc' act = Some g1'\<close> and r: \<open>gxeq g1 g1'\<close>
      by (cases \<open>mstep_cached G cstk' gc' act\<close>) simp_all
    with Some Cons.IH dlive_xeq[OF r] show ?thesis by simp
  qed
qed simp

subsection \<open>The driver over \<^text>\<open>dclosure\<close>\<close>

lemma dcands_gxeq: \<open>gxeq gc gc' \<Longrightarrow> dcands G i cells CL gc = dcands G i cells CL gc'\<close>
  unfolding gxeq_def dcands_def by (cases gc; cases gc') (auto dest: list_all2_lengthD)

definition dstep_c :: \<open>('n, 't) is_cfg \<Rightarrow> (('n, 't) sym \<times> nat) list list \<Rightarrow>
    ('n, 't) citem list list \<Rightarrow> ('n, 't) lacell list list \<Rightarrow> (nat \<times> nat option) list \<Rightarrow>
    ('m, 'ch, 'n, 't) dst \<Rightarrow> ('m, 'ch, 'n, 't) dst option\<close> where
  \<open>dstep_c G gt sts redtab dt st = (case st of (gc, cstk, istk, v, tstk) \<Rightarrow>
     let i = (case istk of [] \<Rightarrow> length sts | j # _ \<Rightarrow> j);
         cells = (if i < length redtab then redtab ! i else []);
         CL = (case cstk of [] \<Rightarrow> [] | c # _ \<Rightarrow> c)
     in (case dpick G cstk gc (dcands G i cells CL gc) of
        None \<Rightarrow> None
      | Some (act, gc') \<Rightarrow> Some (case act of
          DShift \<Rightarrow> (gc',
              dclosure_t G dt (hd (fst gc')) # cstk,
              dnext gt sts i (Tm (tok (hd v))) # istk,
              tl v,
              Leaf (hd v) # tstk)
        | DReduce pr \<Rightarrow> (gc',
              dclosure_t G dt (hd (fst gc')) # drop (length (snd pr)) cstk,
              dnext gt sts (istk ! length (snd pr)) (Nt (fst pr))
                # drop (length (snd pr)) istk,
              v,
              Node (fst pr) (rev (take (length (snd pr)) tstk))
                # drop (length (snd pr)) tstk))))\<close>

definition dst_rel :: \<open>('m, 'ch, 'n, 't) dst \<Rightarrow> ('m, 'ch, 'n, 't) dst \<Rightarrow> bool\<close> where
  \<open>dst_rel st st' \<longleftrightarrow> gxeq (fst st) (fst st') \<and>
     list_all2 xeq (fst (snd st)) (fst (snd st')) \<and> snd (snd st) = snd (snd st')\<close>

lemma dstep_xeq:
  assumes r: \<open>dst_rel st st'\<close>
  shows \<open>rel_option dst_rel (dstep G gt sts redtab st) (dstep_c G gt sts redtab (dtab G) st')\<close>
proof -
  obtain gc cstk istk v tstk gc' cstk' where
    st: \<open>st = (gc, cstk, istk, v, tstk)\<close> \<open>st' = (gc', cstk', istk, v, tstk)\<close> and
    g: \<open>gxeq gc gc'\<close> and c: \<open>list_all2 xeq cstk cstk'\<close>
    using r unfolding dst_rel_def by (cases st; cases st') auto
  have cl: \<open>xeq (case cstk of [] \<Rightarrow> [] | c # _ \<Rightarrow> c) (case cstk' of [] \<Rightarrow> [] | c # _ \<Rightarrow> c)\<close>
    using c by (cases cstk; cases cstk') auto
  define i where \<open>i = (case istk of [] \<Rightarrow> length sts | j # _ \<Rightarrow> j)\<close>
  define cells where \<open>cells = (if i < length redtab then redtab ! i else [])\<close>
  define acts where \<open>acts = dcands G i cells (case cstk of [] \<Rightarrow> [] | c # _ \<Rightarrow> c) gc\<close>
  have acts': \<open>dcands G i cells (case cstk' of [] \<Rightarrow> [] | c # _ \<Rightarrow> c) gc' = acts\<close>
    unfolding acts_def dcands_xeq[OF cl] dcands_gxeq[OF g] ..
  have p: \<open>rel_option (\<lambda>(a, g) (a', g'). a = a' \<and> gxeq g g') (dpick G cstk gc acts) (dpick G cstk' gc' acts)\<close>
    by (rule dpick_xeq[OF c g])
  have u: \<open>dcands G (case istk of [] \<Rightarrow> length sts | j # _ \<Rightarrow> j)
      (if (case istk of [] \<Rightarrow> length sts | j # _ \<Rightarrow> j) < length redtab
       then redtab ! (case istk of [] \<Rightarrow> length sts | j # _ \<Rightarrow> j) else [])
      (case cstk of [] \<Rightarrow> [] | c # _ \<Rightarrow> c) gc = acts\<close>
    \<open>dcands G (case istk of [] \<Rightarrow> length sts | j # _ \<Rightarrow> j)
      (if (case istk of [] \<Rightarrow> length sts | j # _ \<Rightarrow> j) < length redtab
       then redtab ! (case istk of [] \<Rightarrow> length sts | j # _ \<Rightarrow> j) else [])
      (case cstk' of [] \<Rightarrow> [] | c # _ \<Rightarrow> c) gc' = acts\<close>
    using acts' unfolding acts_def cells_def i_def by simp_all
  show ?thesis
  proof (cases \<open>dpick G cstk gc acts\<close>)
    case None
    with p have \<open>dpick G cstk' gc' acts = None\<close> by (cases \<open>dpick G cstk' gc' acts\<close>) auto
    with None show ?thesis
      unfolding st dstep_def dstep_c_def Let_def prod.case u by simp
  next
    case (Some p1)
    then obtain act g1 where p1: \<open>dpick G cstk gc acts = Some (act, g1)\<close> by (cases p1) auto
    with p obtain g1' where p1': \<open>dpick G cstk' gc' acts = Some (act, g1')\<close> and g1: \<open>gxeq g1 g1'\<close>
      by (cases \<open>dpick G cstk' gc' acts\<close>) auto
    have x1: \<open>list_all2 xeq (fst g1) (fst g1')\<close> using g1 unfolding gxeq_def by simp
    have h: \<open>xeq (xclosure_auto G (hd (fst g1))) (dclosure_t G (dtab G) (hd (fst g1')))\<close>
      unfolding dclosure_t_eq by (rule xclosure_auto_dclosure, rule list_all2_hd_refl[OF x1]) simp
    have \<open>list_all2 xeq (drop k cstk) (drop k cstk')\<close> for k using c by (rule list_all2_dropI)
    with h g1 c show ?thesis
      unfolding st dstep_def dstep_c_def Let_def prod.case u
      by (simp add: p1 p1' dst_rel_def split: dact.splits)
  qed
qed

lemma gfinal_gxeq: \<open>gxeq gc gc' \<Longrightarrow> gfinal G Shn gc = gfinal G Shn gc'\<close>
  unfolding gxeq_def by (cases gc; cases gc') (auto dest: gfinal_xeq)

partial_function (option) drun_nh_c ::
  \<open>('n, 't) is_cfg \<Rightarrow> 'n \<Rightarrow> (('n, 't) sym \<times> nat) list list \<Rightarrow>
    ('n, 't) citem list list \<Rightarrow> ('n, 't) lacell list list \<Rightarrow> (nat \<times> nat option) list \<Rightarrow>
    ('m, 'ch, 'n, 't) dst \<Rightarrow> ('m, 'ch, 'n, 't) ast option\<close>
  where
  \<open>drun_nh_c G Shn gt sts redtab dt st =
     (case st of (gc, cstk, istk, v, tstk) \<Rightarrow>
        if gfinal G Shn gc then (case tstk of t # _ \<Rightarrow> Some t | [] \<Rightarrow> None)
        else Option.bind (dstep_c G gt sts redtab dt st) (drun_nh_c G Shn gt sts redtab dt))\<close>

lemmas drun_nh_c_simps [code] = drun_nh_c.simps

lemma drun_nh_imp_c:
  assumes \<open>drun_nh G Shn gt sts redtab st = Some t\<close>
  shows \<open>\<forall>st'. dst_rel st st' \<longrightarrow> drun_nh_c G Shn gt sts redtab (dtab G) st' = Some t\<close>
proof (rule drun_nh.raw_induct[OF _ assms], goal_cases)
  case (1 f G Shn gt sts redtab st t)
  show ?case
  proof (intro allI impI)
    fix st' assume r: \<open>dst_rel st st'\<close>
    obtain gc cstk istk v tstk gc' cstk' where
      st: \<open>st = (gc, cstk, istk, v, tstk)\<close> \<open>st' = (gc', cstk', istk, v, tstk)\<close> and g: \<open>gxeq gc gc'\<close>
      using r unfolding dst_rel_def by (cases st; cases st') auto
    show \<open>drun_nh_c G Shn gt sts redtab (dtab G) st' = Some t\<close>
    proof (cases \<open>gfinal G Shn gc\<close>)
      case True
      with "1"(2) gfinal_gxeq[OF g] show ?thesis
        unfolding st by (subst drun_nh_c.simps) simp
    next
      case False
      with "1"(2) obtain st\<^sub>1 where sp: \<open>dstep G gt sts redtab st = Some st\<^sub>1\<close>
        and rec: \<open>f G Shn gt sts redtab st\<^sub>1 = Some t\<close>
        unfolding st by (auto simp: bind_eq_Some_conv)
      from dstep_xeq[OF r, of G gt sts redtab] sp obtain st\<^sub>1' where
        sp': \<open>dstep_c G gt sts redtab (dtab G) st' = Some st\<^sub>1'\<close> and r1: \<open>dst_rel st\<^sub>1 st\<^sub>1'\<close>
        by (cases \<open>dstep_c G gt sts redtab (dtab G) st'\<close>) auto
      from "1"(1)[OF rec] r1 have \<open>drun_nh_c G Shn gt sts redtab (dtab G) st\<^sub>1' = Some t\<close> by blast
      with False gfinal_gxeq[OF g] sp' show ?thesis
        unfolding st by (subst drun_nh_c.simps) simp
    qed
  qed
qed

lemma drun_nh_c_imp:
  assumes \<open>drun_nh_c G Shn gt sts redtab dt st' = Some t\<close>
  shows \<open>dt = dtab G \<longrightarrow> (\<forall>st. dst_rel st st' \<longrightarrow> drun_nh G Shn gt sts redtab st = Some t)\<close>
proof (rule drun_nh_c.raw_induct[OF _ assms], goal_cases)
  case (1 f G Shn gt sts redtab dt st' t)
  show ?case
  proof (intro allI impI)
    fix st assume d: \<open>dt = dtab G\<close> and r: \<open>dst_rel st st'\<close>
    note prem = "1"(2)[unfolded d]
    obtain gc cstk istk v tstk gc' cstk' where
      st: \<open>st = (gc, cstk, istk, v, tstk)\<close> \<open>st' = (gc', cstk', istk, v, tstk)\<close> and g: \<open>gxeq gc gc'\<close>
      using r unfolding dst_rel_def by (cases st; cases st') auto
    show \<open>drun_nh G Shn gt sts redtab st = Some t\<close>
    proof (cases \<open>gfinal G Shn gc\<close>)
      case True
      with prem gfinal_gxeq[OF g] show ?thesis
        unfolding st by (subst drun_nh.simps) simp
    next
      case False
      with prem gfinal_gxeq[OF g] obtain st\<^sub>1' where sp': \<open>dstep_c G gt sts redtab (dtab G) st' = Some st\<^sub>1'\<close>
        and rec: \<open>f G Shn gt sts redtab (dtab G) st\<^sub>1' = Some t\<close>
        unfolding st by (auto simp: bind_eq_Some_conv)
      from dstep_xeq[OF r, of G gt sts redtab] sp' obtain st\<^sub>1 where
        sp: \<open>dstep G gt sts redtab st = Some st\<^sub>1\<close> and r1: \<open>dst_rel st\<^sub>1 st\<^sub>1'\<close>
        by (cases \<open>dstep G gt sts redtab st\<close>) auto
      from "1"(1)[OF rec] r1 have \<open>drun_nh G Shn gt sts redtab st\<^sub>1 = Some t\<close> by blast
      with False sp show ?thesis
        unfolding st by (subst drun_nh.simps) simp
    qed
  qed
qed

lemma drun_nh_eq_c:
  \<open>dst_rel st st' \<Longrightarrow> drun_nh G Shn gt sts redtab st = drun_nh_c G Shn gt sts redtab (dtab G) st'\<close>
  using drun_nh_imp_c[of G Shn gt sts redtab st] drun_nh_c_imp[of G Shn gt sts redtab \<open>dtab G\<close> st']
  by (metis not_Some_eq)

lemma dparse_via_tables_nh_c:
  assumes st:  \<open>pr0_states G Shn = sts\<close>
    and   gt:  \<open>pgtab G sts = gtab\<close>
    and   rt:  \<open>red_buckets G Shn (length sts) = redtab\<close>
    and   xi:  \<open>xinit G Shn = xin\<close>
    and   xc:  \<open>dclosure G xin = xclos\<close>
    and   i0:  \<open>st_find sts (lr0_start G Shn) = i\<^sub>0\<close>
    and   dt:  \<open>dtab G = dtb\<close>
  shows \<open>dparse G Shn w =
     drun_nh_c G Shn gtab sts redtab dtb (([xin], tcols w), [xclos], [i\<^sub>0], w, [])\<close>
proof -
  have \<open>dst_rel (([xin], tcols w), [xclosure_auto G xin], [i\<^sub>0], w, [])
                (([xin], tcols w), [xclos], [i\<^sub>0], w, [])\<close>
    using xclosure_auto_dclosure[OF xeq_refl, of G xin] unfolding xc dst_rel_def gxeq_def by simp
  then show ?thesis
    unfolding dparse_via_tables_nh[OF st gt rt xi refl i0] dt[symmetric] by (rule drun_nh_eq_c)
qed

text \<open>\<^const>\<open>dstep_act\<close> over \<^text>\<open>dclosure\<close>, for drivers that need the
  action (the error diagnostics).\<close>

definition dstep_act_c :: \<open>('n, 't) is_cfg \<Rightarrow> (('n, 't) sym \<times> nat) list list \<Rightarrow>
    ('n, 't) citem list list \<Rightarrow> ('n, 't) lacell list list \<Rightarrow> (nat \<times> nat option) list \<Rightarrow>
    ('m, 'ch, 'n, 't) dst \<Rightarrow> (('n, 't) dact \<times> ('m, 'ch, 'n, 't) dst) option\<close> where
  \<open>dstep_act_c G gt sts redtab dt st = (case st of (gc, cstk, istk, v, tstk) \<Rightarrow>
     let i = (case istk of [] \<Rightarrow> length sts | j # _ \<Rightarrow> j);
         cells = (if i < length redtab then redtab ! i else []);
         CL = (case cstk of [] \<Rightarrow> [] | c # _ \<Rightarrow> c)
     in (case dpick G cstk gc (dcands G i cells CL gc) of
        None \<Rightarrow> None
      | Some (act, gc') \<Rightarrow> Some (act, case act of
          DShift \<Rightarrow> (gc',
              dclosure_t G dt (hd (fst gc')) # cstk,
              dnext gt sts i (Tm (tok (hd v))) # istk,
              tl v,
              Leaf (hd v) # tstk)
        | DReduce pr \<Rightarrow> (gc',
              dclosure_t G dt (hd (fst gc')) # drop (length (snd pr)) cstk,
              dnext gt sts (istk ! length (snd pr)) (Nt (fst pr))
                # drop (length (snd pr)) istk,
              v,
              Node (fst pr) (rev (take (length (snd pr)) tstk))
                # drop (length (snd pr)) tstk))))\<close>

lemma dstep_c_eq_dstep_act_c:
  \<open>dstep_c G gt sts redtab (dtab G) st = map_option snd (dstep_act_c G gt sts redtab (dtab G) st)\<close>
  unfolding dstep_c_def dstep_act_c_def
  by (auto simp: Let_def split: prod.splits option.splits dact.splits)

lemma dstep_act_xeq:
  assumes r: \<open>dst_rel st st'\<close>
  shows \<open>rel_option (\<lambda>(a, s) (a', s'). a = a' \<and> dst_rel s s')
           (dstep_act G gt sts redtab st) (dstep_act_c G gt sts redtab (dtab G) st')\<close>
proof -
  obtain gc cstk istk v tstk gc' cstk' where
    st: \<open>st = (gc, cstk, istk, v, tstk)\<close> \<open>st' = (gc', cstk', istk, v, tstk)\<close> and
    g: \<open>gxeq gc gc'\<close> and c: \<open>list_all2 xeq cstk cstk'\<close>
    using r unfolding dst_rel_def by (cases st; cases st') auto
  have cl: \<open>xeq (case cstk of [] \<Rightarrow> [] | c # _ \<Rightarrow> c) (case cstk' of [] \<Rightarrow> [] | c # _ \<Rightarrow> c)\<close>
    using c by (cases cstk; cases cstk') auto
  define i where \<open>i = (case istk of [] \<Rightarrow> length sts | j # _ \<Rightarrow> j)\<close>
  define cells where \<open>cells = (if i < length redtab then redtab ! i else [])\<close>
  define acts where \<open>acts = dcands G i cells (case cstk of [] \<Rightarrow> [] | c # _ \<Rightarrow> c) gc\<close>
  have acts': \<open>dcands G i cells (case cstk' of [] \<Rightarrow> [] | c # _ \<Rightarrow> c) gc' = acts\<close>
    unfolding acts_def dcands_xeq[OF cl] dcands_gxeq[OF g] ..
  have p: \<open>rel_option (\<lambda>(a, g) (a', g'). a = a' \<and> gxeq g g') (dpick G cstk gc acts) (dpick G cstk' gc' acts)\<close>
    by (rule dpick_xeq[OF c g])
  have u: \<open>dcands G (case istk of [] \<Rightarrow> length sts | j # _ \<Rightarrow> j)
      (if (case istk of [] \<Rightarrow> length sts | j # _ \<Rightarrow> j) < length redtab
       then redtab ! (case istk of [] \<Rightarrow> length sts | j # _ \<Rightarrow> j) else [])
      (case cstk of [] \<Rightarrow> [] | c # _ \<Rightarrow> c) gc = acts\<close>
    \<open>dcands G (case istk of [] \<Rightarrow> length sts | j # _ \<Rightarrow> j)
      (if (case istk of [] \<Rightarrow> length sts | j # _ \<Rightarrow> j) < length redtab
       then redtab ! (case istk of [] \<Rightarrow> length sts | j # _ \<Rightarrow> j) else [])
      (case cstk' of [] \<Rightarrow> [] | c # _ \<Rightarrow> c) gc' = acts\<close>
    using acts' unfolding acts_def cells_def i_def by simp_all
  show ?thesis
  proof (cases \<open>dpick G cstk gc acts\<close>)
    case None
    with p have \<open>dpick G cstk' gc' acts = None\<close> by (cases \<open>dpick G cstk' gc' acts\<close>) auto
    with None show ?thesis
      unfolding st dstep_act_def dstep_act_c_def Let_def prod.case u by simp
  next
    case (Some p1)
    then obtain act g1 where p1: \<open>dpick G cstk gc acts = Some (act, g1)\<close> by (cases p1) auto
    with p obtain g1' where p1': \<open>dpick G cstk' gc' acts = Some (act, g1')\<close> and g1: \<open>gxeq g1 g1'\<close>
      by (cases \<open>dpick G cstk' gc' acts\<close>) auto
    have x1: \<open>list_all2 xeq (fst g1) (fst g1')\<close> using g1 unfolding gxeq_def by simp
    have h: \<open>xeq (xclosure_auto G (hd (fst g1))) (dclosure_t G (dtab G) (hd (fst g1')))\<close>
      unfolding dclosure_t_eq by (rule xclosure_auto_dclosure, rule list_all2_hd_refl[OF x1]) simp
    have \<open>list_all2 xeq (drop k cstk) (drop k cstk')\<close> for k using c by (rule list_all2_dropI)
    with h g1 c show ?thesis
      unfolding st dstep_act_def dstep_act_c_def Let_def prod.case u
      by (simp add: p1 p1' dst_rel_def split: dact.splits)
  qed
qed

end
