(* Author: Basil Fürer *)

theory LR_Vec_Fuse
  imports LR_Vec LR_Fuse
begin

section \<open>Integer labels and fused actions for the state-indexed driver\<close>

text \<open>The driver for grammars with layout (\<^const>\<open>vrun_k\<close>, whose code is
  \<^const>\<open>ivr_run\<close>) builds trees over the names of the nonterminals, and the decoders
  compare names. As for the simple driver (LR_Lab, LR_Fuse), its candidate table is
  relabelled by the positions of the names (\<open>vklab\<close>), and the run is
  generalised over what it pushes for a token and a reduction (\<open>ivr_grun\<close>): with
  \<^const>\<open>Leaf\<close> and \<^const>\<open>Node\<close> it is \<^const>\<open>ivr_run\<close>, and with the actions on values
  it computes the decoders' result directly. Only the candidate table mentions
  nonterminals, so relabelling the tables changes nothing else. The fallback to the
  sparse driver keeps its trees and the decoder.\<close>

subsection \<open>Relabelled tables\<close>

definition cp_lab :: \<open>('n \<Rightarrow> 'l) \<Rightarrow> nat \<times> nat \<times> ('n \<times> ('n, 't) rhs) \<Rightarrow> nat \<times> nat \<times> ('l \<times> ('l, 't) rhs)\<close> where
  \<open>cp_lab h c = (case c of (s, b, pr) \<Rightarrow> (s, b, pr_lab h pr))\<close>

definition vlab :: \<open>('n \<Rightarrow> 'l) \<Rightarrow> ('n, 't) vtab \<Rightarrow> ('l, 't) vtab\<close> where
  \<open>vlab h V = VTab (v_lal V) (v_miss V) (v_sh V) (v_go V) (v_ct V)
     (IArray (map (map (cp_lab h)) (IArray.list_of (v_cp V))))
     (v_cl V) (v_ce V) (v_fin V) (v_av0 V) (v_ind0 V)\<close>

definition vklab :: \<open>('n \<Rightarrow> 'l) \<Rightarrow> ('n, 't) vktab \<Rightarrow> ('l, 't) vktab\<close> where
  \<open>vklab h K = VKTab (vlab h (k_v K)) (k_sh K) (k_go K)\<close>

lemma vklab_sel [simp]:
  \<open>k_sh (vklab h K) = k_sh K\<close> \<open>k_go (vklab h K) = k_go K\<close>
  \<open>v_ce (k_v (vklab h K)) = v_ce (k_v K)\<close> \<open>v_cl (k_v (vklab h K)) = v_cl (k_v K)\<close>
  \<open>v_fin (k_v (vklab h K)) = v_fin (k_v K)\<close> \<open>v_ind0 (k_v (vklab h K)) = v_ind0 (k_v K)\<close>
  by (simp_all add: vklab_def vlab_def)

lemma iget_cp_vklab:
  \<open>iget (v_cp (k_v (vklab h K))) j [] = map (cp_lab h) (iget (v_cp (k_v K)) j [])\<close>
  by (simp add: vklab_def vlab_def iget_def)

lemma cp_lab_simp: \<open>cp_lab h (s, b, pr) = (s, b, pr_lab h pr)\<close>
  by (simp add: cp_lab_def)

lemma cp_lab_comp: \<open>cp_lab h (cp_lab g c) = cp_lab (h \<circ> g) c\<close>
  by (cases c) (simp add: cp_lab_def pr_lab_comp)

lemma vklab_comp: \<open>vklab h (vklab g K) = vklab (h \<circ> g) K\<close>
proof -
  have \<open>map (map (cp_lab h)) (map (map (cp_lab g)) css) = map (map (cp_lab (h \<circ> g))) css\<close> for css
    by (simp add: cp_lab_comp)
  then show ?thesis by (simp add: vklab_def vlab_def)
qed

text \<open>The candidates of the tables, and the names they mention.\<close>

definition vkcands :: \<open>('n, 't) vktab \<Rightarrow> (nat \<times> nat \<times> ('n \<times> ('n, 't) rhs)) list\<close> where
  \<open>vkcands K = concat (IArray.list_of (v_cp (k_v K)))\<close>

definition vklabels :: \<open>('n, 't) vktab \<Rightarrow> 'n list\<close> where
  \<open>vklabels K = fold (\<lambda>c. fold addn (pr_names (snd (snd c)))) (vkcands K) []\<close>

lemma vklabels_mem:
  assumes c: \<open>c \<in> set (vkcands K)\<close> and n: \<open>n \<in> set (pr_names (snd (snd c)))\<close>
  shows \<open>n \<in> set (vklabels K)\<close>
proof -
  have keep: \<open>set acc \<subseteq> set (fold (\<lambda>c. fold addn (pr_names (snd (snd c)))) cs acc)\<close> for cs acc
  proof (induction cs arbitrary: acc)
    case (Cons c cs)
    from Cons.IH[of \<open>fold addn (pr_names (snd (snd c))) acc\<close>] show ?case by (auto simp: set_fold_addn)
  qed simp
  have \<open>c \<in> set cs \<Longrightarrow> n \<in> set (fold (\<lambda>c. fold addn (pr_names (snd (snd c)))) cs acc)\<close> for cs acc
  proof (induction cs arbitrary: acc)
    case (Cons c' cs)
    show ?case
    proof (cases \<open>c' = c\<close>)
      case True
      with n keep[of \<open>fold addn (pr_names (snd (snd c))) acc\<close> cs] show ?thesis
        by (auto simp: set_fold_addn)
    next
      case False
      with Cons show ?thesis by simp
    qed
  qed simp
  from this[OF c] show ?thesis by (simp add: vklabels_def)
qed

lemma vklab_cong:
  assumes \<open>\<And>c. c \<in> set (vkcands K) \<Longrightarrow> cp_lab f c = cp_lab g c\<close>
  shows \<open>vklab f K = vklab g K\<close>
proof -
  have \<open>map (map (cp_lab f)) (IArray.list_of (v_cp (k_v K))) =
      map (map (cp_lab g)) (IArray.list_of (v_cp (k_v K)))\<close>
  proof (intro map_cong refl)
    fix cs c assume \<open>cs \<in> set (IArray.list_of (v_cp (k_v K)))\<close> \<open>c \<in> set cs\<close>
    then show \<open>cp_lab f c = cp_lab g c\<close> by (intro assms) (auto simp: vkcands_def)
  qed
  then show ?thesis by (simp add: vklab_def vlab_def)
qed

lemma vklab_id: \<open>vklab id K = K\<close>
proof -
  have c: \<open>cp_lab id = id\<close> by (auto simp: cp_lab_def pr_lab_id split: prod.split)
  have m: \<open>map (map (cp_lab id)) xs = xs\<close> for xs by (simp add: c)
  have a: \<open>IArray (IArray.list_of a) = a\<close> for a :: \<open>'x iarray\<close> by (cases a) simp
  obtain V s g where K: \<open>K = VKTab V s g\<close> by (cases K)
  show ?thesis by (cases V) (simp add: K vklab_def vlab_def m a)
qed

lemma vklab_back:
  assumes ns: \<open>remdups (vklabels K @ ds) = ns\<close>
  shows \<open>vklab (lnm ns) (vklab (lix ns) K) = K\<close>
proof -
  have \<open>vklab (lnm ns) (vklab (lix ns) K) = vklab (lnm ns \<circ> lix ns) K\<close> by (rule vklab_comp)
  also have \<open>\<dots> = vklab id K\<close>
  proof (rule vklab_cong)
    fix c assume c: \<open>c \<in> set (vkcands K)\<close>
    obtain s b pr where cs: \<open>c = (s, b, pr)\<close> by (cases c)
    have \<open>n \<in> set ns\<close> if \<open>n \<in> set (pr_names pr)\<close> for n
      using vklabels_mem[OF c] cs ns that by auto
    then have \<open>pr_lab (lnm ns \<circ> lix ns) pr = pr_lab id pr\<close>
      by (intro pr_lab_cong) (simp add: lnm_lix)
    then show \<open>cp_lab (lnm ns \<circ> lix ns) c = cp_lab id c\<close> by (simp add: cs cp_lab_def)
  qed
  finally show ?thesis by (simp add: vklab_id)
qed

subsection \<open>The steps over relabelled tables\<close>

lemma ivr_live_vklab: \<open>ivr_live (vklab h K) = ivr_live K\<close>
  unfolding ivr_live_def[abs_def] ivr_lic_def[abs_def] vklab_def vlab_def vktab.sel vtab.sel ..

lemma ivr_red_vklab: \<open>ivr_red (vklab h K) gs g s b (pr_lab h pr) = ivr_red K gs g s b pr\<close>
  unfolding ivr_red_def pr_lab_def vklab_def vktab.sel snd_conv length_rhs_lab ..

lemma ivr_shift_vklab: \<open>ivr_shift (vklab h K) = ivr_shift K\<close>
  unfolding ivr_shift_def[abs_def] vklab_def vktab.sel ..

primrec ivs_lab :: \<open>('n \<Rightarrow> 'l) \<Rightarrow> ('n, 't) ivsres \<Rightarrow> ('l, 't) ivsres\<close> where
  \<open>ivs_lab h IvConf = IvConf\<close>
| \<open>ivs_lab h IvRej = IvRej\<close>
| \<open>ivs_lab h (IvRed pr gs) = IvRed (pr_lab h pr) gs\<close>

lemma ivr_scan_vklab:
  \<open>ivr_scan (vklab h K) gs w j g (map (cp_lab h) cs) = ivs_lab h (ivr_scan K gs w j g cs)\<close>
proof (induction cs)
  case (Cons c cs)
  obtain s b pr where c: \<open>c = (s, b, pr)\<close> by (cases c)
  have pt: \<open>(case cp_lab h c of (s, b, pr) \<Rightarrow> ivr_live K j g w s \<and> ivr_red (vklab h K) gs g s b pr \<noteq> None) =
      (case c of (s, b, pr) \<Rightarrow> ivr_live K j g w s \<and> ivr_red K gs g s b pr \<noteq> None)\<close> for c
    by (cases c) (simp only: cp_lab_simp prod.case ivr_red_vklab)
  have ex: \<open>list_ex (\<lambda>(s, b, pr). ivr_live K j g w s \<and> ivr_red (vklab h K) gs g s b pr \<noteq> None)
      (map (cp_lab h) cs) = list_ex (\<lambda>(s, b, pr). ivr_live K j g w s \<and> ivr_red K gs g s b pr \<noteq> None) cs\<close>
    by (induction cs) (simp_all only: list.map list_ex_Nil_iff list_ex_Cons_iff pt)
  show ?case
    unfolding c list.map cp_lab_simp ivr_scan.simps ivr_live_vklab ex ivr_red_vklab Cons.IH
    by (auto split: option.split)
qed simp

subsection \<open>The run, generic over what it pushes\<close>

partial_function (option) ivr_grun ::
  \<open>('l, 't) vktab \<Rightarrow> (('t, 'ch, 'm) token_scheme \<Rightarrow> 'u) \<Rightarrow> ('l \<Rightarrow> 'u list \<Rightarrow> 'u) \<Rightarrow>
    (nat \<times> ivf) list \<Rightarrow> (nat \<times> nat) list \<Rightarrow> ('m, 'ch, 't) tword \<Rightarrow> 'u list \<Rightarrow> 'u option option\<close>
  where
  \<open>ivr_grun K Lf Nd gs w v us = (if w = [] \<and> (case gs of [] \<Rightarrow> False
       | (j, g) # _ \<Rightarrow> ivr_mem (v_ind0 (k_v K)) (ivf_get g (iget (v_fin (k_v K)) j 0)))
     then Some (case us of u # _ \<Rightarrow> Some u | [] \<Rightarrow> None)
     else (case gs of [] \<Rightarrow> Some None | (j, g) # _ \<Rightarrow>
       (case ivr_shift K j g w of
          Some h \<Rightarrow> ivr_grun K Lf Nd (h # gs) (tl w) (tl v) (Lf (hd v) # us)
        | None \<Rightarrow> (case ivr_scan K gs w j g (iget (v_cp (k_v K)) j []) of
            IvConf \<Rightarrow> None
          | IvRej \<Rightarrow> Some None
          | IvRed pr gs' \<Rightarrow> ivr_grun K Lf Nd gs' w v
              (Nd (fst pr) (rev (take (length (snd pr)) us)) # drop (length (snd pr)) us)))))\<close>

lemmas ivr_grun_simps [code] = ivr_grun.simps

context
  fixes U :: \<open>('m, 'ch, 'n, 't) ast \<Rightarrow> 'u\<close>
    and Lf :: \<open>('t, 'ch, 'm) token_scheme \<Rightarrow> 'u\<close>
    and Nd :: \<open>'l \<Rightarrow> 'u list \<Rightarrow> 'u\<close>
    and h :: \<open>'n \<Rightarrow> 'l\<close>
  assumes U_leaf: \<open>\<And>t. U (Leaf t) = Lf t\<close>
    and U_node: \<open>\<And>n cs. U (Node n cs) = Nd (h n) (map U cs)\<close>
begin

lemma red_map:
  \<open>Nd (fst (pr_lab h pr)) (rev (take (length (snd (pr_lab h pr))) (map U ts))) #
      drop (length (snd (pr_lab h pr))) (map U ts) =
    map U (Node (fst pr) (rev (take (length (snd pr)) ts)) # drop (length (snd pr)) ts)\<close>
  by (simp add: pr_lab_def U_node take_map drop_map rev_map)

lemma ivr_grun_one:
  assumes run: \<open>ivr_run K gs w v ts = Some r\<close>
  shows \<open>ivr_grun (vklab h K) Lf Nd gs w v (map U ts) = Some (map_option U r)\<close>
proof -
  have \<open>ivr_grun (vklab h K) Lf Nd gs w v (map U ts) = Some (map_option U r)\<close>
  proof (rule ivr_run.raw_induct[where P = \<open>\<lambda>K gs w v ts r.
        ivr_grun (vklab h K) Lf Nd gs w v (map U ts) = Some (map_option U r)\<close>, OF _ run], goal_cases)
    case (1 vr K gs w v ts r)
    let ?F = \<open>w = [] \<and> (case gs of [] \<Rightarrow> False
      | (j, g) # _ \<Rightarrow> ivr_mem (v_ind0 (k_v K)) (ivf_get g (iget (v_fin (k_v K)) j 0)))\<close>
    have finK: \<open>(w = [] \<and> (case gs of [] \<Rightarrow> False
      | (j, g) # _ \<Rightarrow> ivr_mem (v_ind0 (k_v (vklab h K))) (ivf_get g (iget (v_fin (k_v (vklab h K))) j 0)))) = ?F\<close>
      unfolding vklab_sel ..
    show ?case
    proof (cases ?F)
      case True
      from "1"(2)[unfolded if_P[OF True]] have r: \<open>r = (case ts of t # _ \<Rightarrow> Some t | [] \<Rightarrow> None)\<close> by simp
      show ?thesis
        by (subst ivr_grun.simps, subst finK, subst if_P[OF True]) (simp add: r split: list.split)
    next
      case fin: False
      note body = "1"(2)[unfolded if_not_P[OF fin]]
      have gstep: \<open>ivr_grun (vklab h K) Lf Nd gs w v us = (case gs of [] \<Rightarrow> Some None | (j, g) # _ \<Rightarrow>
         (case ivr_shift K j g w of
            Some h' \<Rightarrow> ivr_grun (vklab h K) Lf Nd (h' # gs) (tl w) (tl v) (Lf (hd v) # us)
          | None \<Rightarrow> (case ivr_scan (vklab h K) gs w j g (iget (v_cp (k_v (vklab h K))) j []) of
              IvConf \<Rightarrow> None
            | IvRej \<Rightarrow> Some None
            | IvRed pr gs' \<Rightarrow> ivr_grun (vklab h K) Lf Nd gs' w v
                (Nd (fst pr) (rev (take (length (snd pr)) us)) # drop (length (snd pr)) us))))\<close> for us
        by (subst ivr_grun.simps, subst finK, subst if_not_P[OF fin]) (simp only: ivr_shift_vklab)
      show ?thesis
      proof (cases gs)
        case Nil
        with body gstep show ?thesis by simp
      next
        case (Cons gr gs\<^sub>1)
        obtain j g where gr: \<open>gr = (j, g)\<close> by (cases gr)
        note body' = body[unfolded Cons gr list.case prod.case, folded gr, folded Cons]
        note gst = gstep[unfolded Cons gr list.case prod.case, folded gr, folded Cons]
        show ?thesis
        proof (cases \<open>ivr_shift K j g w\<close>)
          case (Some h')
          from body' Some have rec: \<open>vr K (h' # gs) (tl w) (tl v) (Leaf (hd v) # ts) = Some r\<close>
            by simp
          from "1"(1)[OF rec] Some show ?thesis by (simp add: gst U_leaf)
        next
          case sh: None
          have scan: \<open>ivr_scan (vklab h K) gs w j g (iget (v_cp (k_v (vklab h K))) j []) =
              ivs_lab h (ivr_scan K gs w j g (iget (v_cp (k_v K)) j []))\<close>
            unfolding iget_cp_vklab by (rule ivr_scan_vklab)
          show ?thesis
          proof (cases \<open>ivr_scan K gs w j g (iget (v_cp (k_v K)) j [])\<close>)
            case IvConf
            with body' sh show ?thesis by simp
          next
            case IvRej
            with body' sh have \<open>r = None\<close> by simp
            with IvRej sh scan show ?thesis by (simp add: gst)
          next
            case (IvRed pr gs')
            with body' sh have rec: \<open>vr K gs' w v
                (Node (fst pr) (rev (take (length (snd pr)) ts)) # drop (length (snd pr)) ts) = Some r\<close>
              by simp
            from "1"(1)[OF rec] IvRed sh scan show ?thesis
              by (simp only: gst option.case ivsres.case ivs_lab.simps red_map)
          qed
        qed
      qed
    qed
  qed
  then show ?thesis .
qed

lemma ivr_grun_two:
  assumes run: \<open>ivr_grun K' Lf Nd gs w v us = Some r\<close>
  shows \<open>Lf = Lf \<longrightarrow> Nd = Nd \<longrightarrow> (\<forall>K ts. K' = vklab h K \<longrightarrow> us = map U ts \<longrightarrow>
    (\<exists>r'. r = map_option U r' \<and> ivr_run K gs w v ts = Some r'))\<close>
proof (rule ivr_grun.raw_induct[where P = \<open>\<lambda>K' Lf' Nd' gs w v us r. Lf' = Lf \<longrightarrow> Nd' = Nd \<longrightarrow>
      (\<forall>K ts. K' = vklab h K \<longrightarrow> us = map U ts \<longrightarrow>
        (\<exists>r'. r = map_option U r' \<and> ivr_run K gs w v ts = Some r'))\<close>, OF _ run], goal_cases)
  case (1 gr K' Lf' Nd' gs w v us r)
  show ?case
  proof (intro impI allI)
    fix K ts
    assume l: \<open>Lf' = Lf\<close> and n: \<open>Nd' = Nd\<close> and K': \<open>K' = vklab h K\<close> and us: \<open>us = map U ts\<close>
    let ?F = \<open>w = [] \<and> (case gs of [] \<Rightarrow> False
      | (j, g) # _ \<Rightarrow> ivr_mem (v_ind0 (k_v K)) (ivf_get g (iget (v_fin (k_v K)) j 0)))\<close>
    have finK: \<open>(w = [] \<and> (case gs of [] \<Rightarrow> False
      | (j, g) # _ \<Rightarrow> ivr_mem (v_ind0 (k_v K')) (ivf_get g (iget (v_fin (k_v K')) j 0)))) = ?F\<close>
      unfolding K' vklab_sel ..
    note body0 = "1"(2)[unfolded finK]
    show \<open>\<exists>r'. r = map_option U r' \<and> ivr_run K gs w v ts = Some r'\<close>
    proof (cases ?F)
      case True
      from body0[unfolded if_P[OF True]] have r: \<open>r = (case us of u # _ \<Rightarrow> Some u | [] \<Rightarrow> None)\<close> by simp
      have \<open>ivr_run K gs w v ts = Some (case ts of t # _ \<Rightarrow> Some t | [] \<Rightarrow> None)\<close>
        by (subst ivr_run.simps, subst if_P[OF True]) (rule refl)
      then show ?thesis by (simp add: r us split: list.split)
    next
      case fin: False
      note body = body0[unfolded if_not_P[OF fin] K' ivr_shift_vklab us l n]
      have rstep: \<open>ivr_run K gs w v ts = (case gs of [] \<Rightarrow> Some None | (j, g) # _ \<Rightarrow>
         (case ivr_shift K j g w of
            Some h \<Rightarrow> ivr_run K (h # gs) (tl w) (tl v) (Leaf (hd v) # ts)
          | None \<Rightarrow> (case ivr_scan K gs w j g (iget (v_cp (k_v K)) j []) of
              IvConf \<Rightarrow> None
            | IvRej \<Rightarrow> Some None
            | IvRed pr gs' \<Rightarrow> ivr_run K gs' w v
                (Node (fst pr) (rev (take (length (snd pr)) ts)) # drop (length (snd pr)) ts))))\<close>
        by (subst ivr_run.simps, subst if_not_P[OF fin]) (rule refl)
      show ?thesis
      proof (cases gs)
        case Nil
        with body rstep show ?thesis by simp
      next
        case (Cons gq gs\<^sub>1)
        obtain j g where gq: \<open>gq = (j, g)\<close> by (cases gq)
        note body' = body[unfolded Cons gq list.case prod.case, folded gq, folded Cons]
        note rst = rstep[unfolded Cons gq list.case prod.case, folded gq, folded Cons]
        show ?thesis
        proof (cases \<open>ivr_shift K j g w\<close>)
          case (Some h')
          from body' Some have rec: \<open>gr (vklab h K) Lf Nd (h' # gs) (tl w) (tl v)
              (map U (Leaf (hd v) # ts)) = Some r\<close>
            by (simp add: U_leaf)
          from "1"(1)[OF rec, rule_format, OF refl refl refl refl] Some show ?thesis
            by (simp add: rst)
        next
          case sh: None
          have scan: \<open>ivr_scan (vklab h K) gs w j g (iget (v_cp (k_v (vklab h K))) j []) =
              ivs_lab h (ivr_scan K gs w j g (iget (v_cp (k_v K)) j []))\<close>
            unfolding iget_cp_vklab by (rule ivr_scan_vklab)
          note body'' = body'[unfolded sh option.case scan]
          show ?thesis
          proof (cases \<open>ivr_scan K gs w j g (iget (v_cp (k_v K)) j [])\<close>)
            case IvConf
            with body'' show ?thesis by simp
          next
            case IvRej
            with body'' sh show ?thesis by (simp add: rst)
          next
            case (IvRed pr gs')
            from body''[unfolded IvRed ivs_lab.simps ivsres.case red_map] have rec: \<open>gr (vklab h K) Lf Nd gs' w v
                (map U (Node (fst pr) (rev (take (length (snd pr)) ts)) # drop (length (snd pr)) ts)) = Some r\<close> .
            from "1"(1)[OF rec, rule_format, OF refl refl refl refl] IvRed sh show ?thesis
              by (simp add: rst)
          qed
        qed
      qed
    qed
  qed
qed

theorem ivr_grun_map:
  \<open>ivr_grun (vklab h K) Lf Nd gs w v (map U ts) = map_option (map_option U) (ivr_run K gs w v ts)\<close>
proof (cases \<open>ivr_run K gs w v ts\<close>)
  case None
  show ?thesis
  proof (cases \<open>ivr_grun (vklab h K) Lf Nd gs w v (map U ts)\<close>)
    case (Some r)
    from ivr_grun_two[OF Some, rule_format, OF refl refl refl refl] None show ?thesis by auto
  qed (simp add: None)
next
  case (Some r)
  then show ?thesis using ivr_grun_one[OF Some] by simp
qed

end

lemma ivr_grun_run: \<open>ivr_grun K Leaf Node gs w v ts = ivr_run K gs w v ts\<close>
  using ivr_grun_map[of id Leaf Node id K gs w v ts] by (simp add: vklab_id option.map_id0)

subsection \<open>The code equations\<close>

text \<open>The frames of the code: those of \<open>vrun_k_code_iv\<close>.\<close>

definition ivr_init :: \<open>vframes \<Rightarrow> (nat \<times> ivf) list\<close> where
  \<open>ivr_init fs = map (\<lambda>(j, av). (j, IvEager (map ivr_of av))) fs\<close>

text \<open>The run on names followed by a decoder: the run on integers followed by the
  decoder over integer trees; the fallback is untouched.\<close>

theorem bind_vrun_lab:
  assumes ns: \<open>remdups (vklabels K @ ds) = ns\<close> and K': \<open>vklab (lix ns) K = K'\<close>
    and nd: \<open>d \<circ> relab (lnm ns) = nd\<close>
  shows \<open>Option.bind (case vrun_k K fs w v [] of Some r \<Rightarrow> r | None \<Rightarrow> S) d =
    (case ivr_grun K' Leaf Node (ivr_init fs) w v [] of
       Some r \<Rightarrow> Option.bind r nd | None \<Rightarrow> Option.bind S d)\<close>
proof -
  have K: \<open>vklab (lnm ns) K' = K\<close> using vklab_back[OF ns] K' by simp
  have \<open>vrun_k K fs w v [] = ivr_run K (ivr_init fs) w v []\<close>
    unfolding vrun_k_code_iv ivr_init_def ..
  also have \<open>\<dots> = ivr_grun (vklab (lnm ns) K') Leaf Node (ivr_init fs) w v (map (relab (lnm ns)) [])\<close>
    by (simp add: K ivr_grun_run)
  also have \<open>\<dots> = map_option (map_option (relab (lnm ns))) (ivr_grun K' Leaf Node (ivr_init fs) w v [])\<close>
    by (subst ivr_grun_map[where Lf = Leaf and Nd = Node]) (simp_all add: ivr_grun_run)
  finally have e: \<open>vrun_k K fs w v [] = map_option (map_option (relab (lnm ns)))
      (ivr_grun K' Leaf Node (ivr_init fs) w v [])\<close> .
  show ?thesis
    unfolding e using nd[symmetric]
    by (cases \<open>ivr_grun K' Leaf Node (ivr_init fs) w v []\<close>) (simp_all add: bind_map_option comp_def)
qed

text \<open>The run on integer trees followed by the start's decoder: the run on values
  followed by the projection to the start's carrier (the assumptions of
  \<open>bind_frun\<close>).\<close>

theorem bind_vfrun:
  assumes V: \<open>\<And>t. vof dl t = afold Kf t\<close> and L: \<open>\<And>c. fproj ix pj (vof dl c) = nd c\<close>
    and N: \<open>\<And>i us. N i us = FNode i (Kf i us)\<close>
  shows \<open>(case ivr_grun K Leaf Node gs w v [] of Some r \<Rightarrow> Option.bind r nd | None \<Rightarrow> X) =
    (case ivr_grun K FLeaf N gs w v [] of Some r \<Rightarrow> Option.bind r (fproj ix pj) | None \<Rightarrow> X)\<close>
proof -
  have \<open>ivr_grun (vklab id K) FLeaf N gs w v (map (afold Kf) []) =
      map_option (map_option (afold Kf)) (ivr_run K gs w v [])\<close>
    by (rule ivr_grun_map) (simp_all add: N)
  then have e: \<open>ivr_grun K FLeaf N gs w v [] =
      map_option (map_option (afold Kf)) (ivr_grun K Leaf Node gs w v [])\<close>
    by (simp add: vklab_id ivr_grun_run)
  have p: \<open>fproj ix pj (afold Kf t) = nd t\<close> for t using L[of t] V[of t] by simp
  show ?thesis
    unfolding e by (cases \<open>ivr_grun K Leaf Node gs w v []\<close>) (simp_all add: bind_map_option comp_def p)
qed

end
