theory LR_Sparse
  imports LR_Fast "HOL-Library.IArray"
begin

section \<open>Sparse closures for the set-anchored driver\<close>

text \<open>A closure of \<^const>\<open>dclosure\<close> has one slot per production, but on
  CaraML only about nine of its 286 items have a non-empty anchor set.  No
  driver operation observes the empty ones: \<^const>\<open>live\<close> and
  \<^const>\<open>gfinal\<close> look at non-empty items only, \<^const>\<open>red_set\<close> unions
  anchor sets, \<^const>\<open>lgoto\<close> maps an empty item to an empty one, and a
  round's image of an empty set is empty.  The sparse driver keeps only the
  non-empty items, computes a closure's rounds per nonterminal instead of per
  production, and refers to productions and symbols by numbers.

  The one observation that could depend on empty items is the order of the
  reduce candidates (\<^const>\<open>dcands\<close>: \<^const>\<open>remdups\<close> keeps the last
  occurrence).  It does not, because the closures the driver builds are
  \<^emph>\<open>coherent\<close>: items with the same production and dot have the same anchor
  set (\<open>coh\<close>), so a production that has a non-empty complete item has only
  non-empty ones.  Coherence needs the start production to be no production of
  the grammar, which \<^const>\<open>fresh_name\<close> provides.\<close>

subsection \<open>Productions as records\<close>

text \<open>The productions of the grammar and the start production, in one list;
  the start production gets the last position.\<close>

definition eprods :: \<open>('n, 't) is_cfg \<Rightarrow> 'n \<Rightarrow> ('n \<times> ('n, 't) rhs) list\<close> where
  \<open>eprods G Shn = iprods G @ [(Shn, [(Nt (istart G), Eq)])]\<close>

fun symid :: \<open>'n list \<Rightarrow> ('n, 't) sym \<Rightarrow> (nat, 't) sym\<close> where
  \<open>symid ns (Nt B) = Nt (ntidx ns B)\<close>
| \<open>symid ns (Tm a) = Tm a\<close>

text \<open>A production's record: its number (the first position of the production),
  the number of its left-hand side (the first position of a production with that
  left-hand side), its right-hand side over numbered nonterminals, and the
  production itself, for the tree and the reduce cells.\<close>

type_synonym ('n, 't) prec = \<open>nat \<times> nat \<times> ((nat, 't) sym \<times> irel) list \<times> 'n \<times> ('n, 't) rhs\<close>

type_synonym ('n, 't) sitem = \<open>('n, 't) prec \<times> nat \<times> indrep\<close>

definition mkrec :: \<open>('n \<times> ('n, 't) rhs) list \<Rightarrow> 'n \<times> ('n, 't) rhs \<Rightarrow> ('n, 't) prec\<close> where
  \<open>mkrec ps p = (ntidx ps p, ntidx (map fst ps) (fst p),
     map (\<lambda>(X, r). (symid (map fst ps) X, r)) (snd p), p)\<close>

definition rpid :: \<open>('n, 't) prec \<Rightarrow> nat\<close> where \<open>rpid r = fst r\<close>
definition rlhs :: \<open>('n, 't) prec \<Rightarrow> nat\<close> where \<open>rlhs r = fst (snd r)\<close>
definition rrhs :: \<open>('n, 't) prec \<Rightarrow> ((nat, 't) sym \<times> irel) list\<close> where \<open>rrhs r = fst (snd (snd r))\<close>
definition rprod :: \<open>('n, 't) prec \<Rightarrow> 'n \<times> ('n, 't) rhs\<close> where \<open>rprod r = snd (snd (snd r))\<close>

lemma mkrec_sel [simp]:
  \<open>rpid (mkrec ps p) = ntidx ps p\<close>
  \<open>rlhs (mkrec ps p) = ntidx (map fst ps) (fst p)\<close>
  \<open>rrhs (mkrec ps p) = map (\<lambda>(X, r). (symid (map fst ps) X, r)) (snd p)\<close>
  \<open>rprod (mkrec ps p) = p\<close>
  by (simp_all add: mkrec_def rpid_def rlhs_def rrhs_def rprod_def)

fun sdec :: \<open>('n, 't) sitem \<Rightarrow> ('n, 't) xitem\<close> where
  \<open>sdec (r, m, R) = (rprod r, m, R)\<close>

text \<open>Every record of a sparse item list is a table record.\<close>

definition swf :: \<open>('n \<times> ('n, 't) rhs) list \<Rightarrow> ('n, 't) sitem list \<Rightarrow> bool\<close> where
  \<open>swf ps xs \<longleftrightarrow> (\<forall>(r, m, R) \<in> set xs. r \<in> mkrec ps ` set ps)\<close>

subsubsection \<open>Numbering\<close>

lemma ntidx_less: \<open>ntidx xs x < length xs \<longleftrightarrow> x \<in> set xs\<close>
  by (induction xs) auto

lemma ntidx_le: \<open>ntidx xs x \<le> length xs\<close>
  by (induction xs) auto

lemma ntidx_nth: \<open>x \<in> set xs \<Longrightarrow> xs ! ntidx xs x = x\<close>
  by (induction xs) auto

lemma ntidx_notin: \<open>x \<notin> set xs \<Longrightarrow> ntidx xs x = length xs\<close>
  by (induction xs) auto

lemma ntidx_append_in: \<open>x \<in> set xs \<Longrightarrow> ntidx (xs @ ys) x = ntidx xs x\<close>
  by (induction xs) auto

lemma ntidx_append_notin: \<open>x \<notin> set xs \<Longrightarrow> ntidx (xs @ ys) x = length xs + ntidx ys x\<close>
  by (induction xs) auto

lemma ntidx_nth_le: \<open>k < length xs \<Longrightarrow> ntidx xs (xs ! k) \<le> k\<close>
proof (induction xs arbitrary: k)
  case (Cons a xs)
  then show ?case by (cases k) auto
qed simp

lemma symid_eq_Nt: \<open>A \<in> set ns \<Longrightarrow> symid ns Y = Nt (ntidx ns A) \<longleftrightarrow> Y = Nt A\<close>
  by (cases Y) (auto simp: ntidx_eq_iff)

lemma symid_eq_Tm: \<open>symid ns Y = Tm a \<longleftrightarrow> Y = Tm a\<close>
  by (cases Y) auto

subsection \<open>The tables\<close>

text \<open>Per grammar: the records by position, for each nonterminal number the
  positions of its productions, the number of productions, the goto table and the
  reduce cells over numbered symbols and productions, and the number of
  states.\<close>

datatype ('n, 't) stab = STab
  (s_recs: \<open>('n, 't) prec iarray\<close>)
  (s_ntab: \<open>nat list iarray\<close>)
  (s_np: nat)
  (s_gt: \<open>((nat, 't) sym \<times> nat) list iarray\<close>)
  (s_rt: \<open>(nat \<times> (nat \<times> nat) \<times> 't option \<times> wrel) list iarray\<close>)
  (s_ns: nat)
  (s_i0: nat)

definition lids :: \<open>('n, 't) is_cfg \<Rightarrow> 'n \<Rightarrow> nat list\<close> where
  \<open>lids G Shn = map (\<lambda>p. ntidx (map fst (eprods G Shn)) (fst p)) (iprods G)\<close>

definition mk_stab :: \<open>('n, 't) is_cfg \<Rightarrow> 'n \<Rightarrow> (('n, 't) sym \<times> nat) list list \<Rightarrow>
    ('n, 't) citem list list \<Rightarrow> ('n, 't) lacell list list \<Rightarrow> ('n, 't) stab\<close> where
  \<open>mk_stab G Shn gt sts redtab = (let ps = eprods G Shn; ns = map fst ps;
       np = length (iprods G); ls = lids G Shn in
     STab (IArray (map (mkrec ps) ps))
       (IArray (map (\<lambda>a. map fst (filter (\<lambda>(k, l). l = a) (zip [0..<np] ls))) [0..<np]))
       np
       (IArray (map (map (\<lambda>(X, j). (symid ns X, j))) gt))
       (IArray (map (map (\<lambda>(i', (pr, n), t, \<tau>). (i', (ntidx ps pr, n), t, \<tau>))) redtab))
       (length sts) (istart_ind G))\<close>

definition ntl :: \<open>('n, 't) stab \<Rightarrow> nat \<Rightarrow> nat list\<close> where
  \<open>ntl T a = (if a < IArray.length (s_ntab T) then s_ntab T !! a else [])\<close>

subsection \<open>Closure rounds per nonterminal\<close>

text \<open>An item's contribution to a round: the nonterminal after its dot, if the
  grammar has productions for it, with the image of its anchor set.\<close>

definition sitem_nx :: \<open>nat \<Rightarrow> ('n, 't) sitem \<Rightarrow> (nat \<times> indrep) option\<close> where
  \<open>sitem_nx np = (\<lambda>(r, m, R). if m < length (rrhs r) then
     (case rrhs r ! m of (Nt b, q) \<Rightarrow> if b < np then Some (b, irep_img q R) else None | _ \<Rightarrow> None)
     else None)\<close>

definition skn :: \<open>('n, 't) stab \<Rightarrow> ('n, 't) sitem list \<Rightarrow> (nat \<times> indrep) list\<close> where
  \<open>skn T K = filter (\<lambda>(_, I). I \<noteq> FinRep []) (List.map_filter (sitem_nx (s_np T)) K)\<close>

definition sslot_nx :: \<open>('n, 't) stab \<Rightarrow> nat \<Rightarrow> indrep \<Rightarrow> (nat \<times> indrep) list\<close> where
  \<open>sslot_nx T a R = List.map_filter (\<lambda>k. sitem_nx (s_np T) (s_recs T !! k, 0, R)) (ntl T a)\<close>

text \<open>The anchor sets of a round, per nonterminal number, as an association list
  with distinct keys and non-empty values.\<close>

fun sins :: \<open>nat \<times> indrep \<Rightarrow> (nat \<times> indrep) list \<Rightarrow> (nat \<times> indrep) list\<close> where
  \<open>sins (b, I) [] = [(b, I)]\<close>
| \<open>sins (b, I) ((c, J) # N) = (if b = c then (c, irep_union I J) # N else (c, J) # sins (b, I) N)\<close>

definition slk :: \<open>(nat \<times> indrep) list \<Rightarrow> nat \<Rightarrow> indrep\<close> where
  \<open>slk N a = (case map_of N a of Some R \<Rightarrow> R | None \<Rightarrow> FinRep [])\<close>

definition sround :: \<open>('n, 't) stab \<Rightarrow> (nat \<times> indrep) list \<Rightarrow> (nat \<times> indrep) list \<Rightarrow>
    (nat \<times> indrep) list\<close> where
  \<open>sround T kn N = fold sins (kn @ filter (\<lambda>(_, I). I \<noteq> FinRep [])
     (concat (map (\<lambda>(a, R). sslot_nx T a R) N))) []\<close>

definition ssub :: \<open>(nat \<times> indrep) list \<Rightarrow> (nat \<times> indrep) list \<Rightarrow> bool\<close> where
  \<open>ssub N' N \<longleftrightarrow> list_all (\<lambda>(a, R). irep_subset R (slk N a)) N'\<close>

definition sfix :: \<open>('n, 't) stab \<Rightarrow> (nat \<times> indrep) list \<Rightarrow> (nat \<times> indrep) list\<close> where
  \<open>sfix T kn = fst (the (while_option (\<lambda>(N, N'). \<not> ssub N' N)
     (\<lambda>(N, N'). (N', sround T kn N')) ([], sround T kn [])))\<close>

text \<open>The closure: the kernel's non-empty items, then the non-empty slots in the
  order of the productions.\<close>

definition sclosure :: \<open>('n, 't) stab \<Rightarrow> ('n, 't) sitem list \<Rightarrow> ('n, 't) sitem list\<close> where
  \<open>sclosure T K = (let N = sfix T (skn T K) in
     filter (\<lambda>(_, _, R). irep_nonempty R) K @
     map (\<lambda>k. (s_recs T !! k, 0, slk N (rlhs (s_recs T !! k))))
       (sort (concat (map (\<lambda>(a, _). ntl T a) N))))\<close>

subsubsection \<open>Grouping\<close>

lemma sins_set:
  \<open>irep_set (slk (sins (b, I) N) a) = irep_set (slk N a) \<union> (if a = b then irep_set I else {})\<close>
proof (induction N)
  case (Cons x N)
  obtain c J where x: \<open>x = (c, J)\<close> by (cases x)
  show ?case
  proof (cases \<open>b = c\<close>)
    case True
    then show ?thesis by (cases \<open>a = b\<close>) (simp_all add: x slk_def Un_commute)
  next
    case False
    with Cons.IH show ?thesis by (cases \<open>a = c\<close>) (simp_all add: x slk_def)
  qed
qed (simp add: slk_def)

lemma sins_keys: \<open>fst ` set (sins (b, I) N) = insert b (fst ` set N)\<close>
  by (induction \<open>(b, I)\<close> N rule: sins.induct) auto

lemma sins_distinct: \<open>distinct (map fst N) \<Longrightarrow> distinct (map fst (sins (b, I) N))\<close>
  by (induction \<open>(b, I)\<close> N rule: sins.induct) (auto simp: sins_keys)

lemma sins_nonempty:
  \<open>irep_nonempty I \<Longrightarrow> \<forall>(a, R) \<in> set N. irep_nonempty R \<Longrightarrow>
   \<forall>(a, R) \<in> set (sins (b, I) N). irep_nonempty R\<close>
  by (induction \<open>(b, I)\<close> N rule: sins.induct) auto

definition kset :: \<open>nat \<Rightarrow> (nat \<times> indrep) list \<Rightarrow> nat set\<close> where
  \<open>kset a xs = \<Union> {irep_set I |I. (a, I) \<in> set xs}\<close>

lemma kset_simps [simp]:
  \<open>kset a [] = {}\<close>
  \<open>kset a ((b, I) # xs) = (if b = a then irep_set I else {}) \<union> kset a xs\<close>
  by (auto simp: kset_def)

lemma kset_append [simp]: \<open>kset a (xs @ ys) = kset a xs \<union> kset a ys\<close>
  by (auto simp: kset_def)

lemma kset_concat: \<open>kset a (concat xss) = \<Union> (kset a ` set xss)\<close>
  by (auto simp: kset_def)

lemma kset_filter_ne: \<open>kset a (filter (\<lambda>(_, I). I \<noteq> FinRep []) xs) = kset a xs\<close>
proof (induction xs)
  case (Cons x xs)
  then show ?case by (cases x) simp
qed simp

lemma kset_concat_map: \<open>kset a (concat (map (\<lambda>(b, R). f b R) N)) = (\<Union>(b, R) \<in> set N. kset a (f b R))\<close>
  by (auto simp: kset_concat)

lemma fold_sins_set:
  \<open>irep_set (slk (fold sins xs N) a) = irep_set (slk N a) \<union> kset a xs\<close>proof (induction xs arbitrary: N)
  case (Cons x xs)
  then show ?case by (cases x) (auto simp: sins_set)
qed simp

lemma fold_sins_keys: \<open>fst ` set (fold sins xs N) = fst ` set N \<union> fst ` set xs\<close>
proof (induction xs arbitrary: N)
  case (Cons x xs)
  then show ?case by (cases x) (auto simp: sins_keys)
qed simp

lemma fold_sins_distinct: \<open>distinct (map fst N) \<Longrightarrow> distinct (map fst (fold sins xs N))\<close>
  by (induction xs arbitrary: N) (auto simp: sins_distinct)

lemma fold_sins_nonempty:
  \<open>\<forall>(b, I) \<in> set xs. irep_nonempty I \<Longrightarrow> \<forall>(a, R) \<in> set N. irep_nonempty R \<Longrightarrow>
   \<forall>(a, R) \<in> set (fold sins xs N). irep_nonempty R\<close>
proof (induction xs arbitrary: N)
  case (Cons x xs)
  obtain b I where x: \<open>x = (b, I)\<close> by (cases x)
  have I: \<open>irep_nonempty I\<close> and xs: \<open>\<forall>(b, I) \<in> set xs. irep_nonempty I\<close>
    using Cons.prems(1) x by (simp_all del: irep_nonempty_correct)
  have \<open>\<forall>(a, R) \<in> set (sins (b, I) N). irep_nonempty R\<close>
    by (rule sins_nonempty[OF I Cons.prems(2)])
  from Cons.IH[OF xs this] show ?case by (simp add: x)
qed simp

lemma slk_in: \<open>distinct (map fst N) \<Longrightarrow> (a, R) \<in> set N \<Longrightarrow> slk N a = R\<close>
  by (simp add: slk_def)

lemma slk_Nil [simp]: \<open>slk [] a = FinRep []\<close>
  by (simp add: slk_def)

lemma slk_notin: \<open>a \<notin> fst ` set N \<Longrightarrow> slk N a = FinRep []\<close>
proof -
  assume \<open>a \<notin> fst ` set N\<close>
  then have \<open>map_of N a = None\<close> by (simp add: map_of_eq_None_iff)
  then show ?thesis by (simp add: slk_def)
qed

subsubsection \<open>What the tables hold\<close>

lemma length_eprods [simp]: \<open>length (eprods G Shn) = Suc (length (iprods G))\<close>
  by (simp add: eprods_def)

lemma eprods_nth: \<open>k < length (iprods G) \<Longrightarrow> eprods G Shn ! k = iprods G ! k\<close>
  by (simp add: eprods_def nth_append)

lemma lhs_id_less:
  \<open>ntidx (map fst (eprods G Shn)) B < length (iprods G) \<longleftrightarrow> B \<in> fst ` set (iprods G)\<close>
proof (cases \<open>B \<in> fst ` set (iprods G)\<close>)
  case True
  then have \<open>B \<in> set (map fst (iprods G))\<close> by simp
  then show ?thesis using True ntidx_less[of \<open>map fst (iprods G)\<close> B]
    by (simp add: eprods_def ntidx_append_in del: set_map)
next
  case False
  then have \<open>B \<notin> set (map fst (iprods G))\<close> by simp
  then show ?thesis using False
    by (simp add: eprods_def ntidx_append_notin del: set_map)
qed

lemma length_lids [simp]: \<open>length (lids G Shn) = length (iprods G)\<close>
  by (simp add: lids_def)

lemma lids_nth:
  \<open>k < length (iprods G) \<Longrightarrow> lids G Shn ! k = ntidx (map fst (eprods G Shn)) (fst (iprods G ! k))\<close>
  by (simp add: lids_def)

lemma lids_nth_le: \<open>k < length (iprods G) \<Longrightarrow> lids G Shn ! k \<le> k\<close>
  using ntidx_nth_le[of k \<open>map fst (eprods G Shn)\<close>] by (simp add: lids_nth eprods_nth)

lemma set_lids:
  \<open>b \<in> set (lids G Shn) \<longleftrightarrow> (\<exists>B \<in> fst ` set (iprods G). b = ntidx (map fst (eprods G Shn)) B)\<close>
  by (auto simp: lids_def)

lemma zip_upt_nth: \<open>length ls = n \<Longrightarrow> zip [0..<n] ls = map (\<lambda>k. (k, ls ! k)) [0..<n]\<close>
  by (rule nth_equalityI) simp_all

lemma mk_stab_sel [simp]:
  \<open>s_np (mk_stab G Shn gt sts redtab) = length (iprods G)\<close>
  \<open>s_ns (mk_stab G Shn gt sts redtab) = length sts\<close>
  \<open>s_i0 (mk_stab G Shn gt sts redtab) = istart_ind G\<close>
  \<open>s_recs (mk_stab G Shn gt sts redtab) = IArray (map (mkrec (eprods G Shn)) (eprods G Shn))\<close>
  \<open>s_gt (mk_stab G Shn gt sts redtab) =
     IArray (map (map (\<lambda>(X, j). (symid (map fst (eprods G Shn)) X, j))) gt)\<close>
  \<open>s_rt (mk_stab G Shn gt sts redtab) =
     IArray (map (map (\<lambda>(i', (pr, n), t, \<tau>). (i', (ntidx (eprods G Shn) pr, n), t, \<tau>))) redtab)\<close>
  by (simp_all add: mk_stab_def Let_def)

lemma ntl_mk_stab:
  \<open>ntl (mk_stab G Shn gt sts redtab) a = filter (\<lambda>k. lids G Shn ! k = a) [0..<length (iprods G)]\<close>
proof (cases \<open>a < length (iprods G)\<close>)
  case True
  then show ?thesis
    by (simp add: ntl_def mk_stab_def Let_def zip_upt_nth filter_map o_def)
next
  case False
  have \<open>filter (\<lambda>k. lids G Shn ! k = a) [0..<length (iprods G)] = []\<close>
    by (rule filter_False) (use False lids_nth_le[of _ G Shn] in fastforce)
  with False show ?thesis by (simp add: ntl_def mk_stab_def Let_def)
qed

lemma recs_mk_stab:
  \<open>k < length (iprods G) \<Longrightarrow>
   s_recs (mk_stab G Shn gt sts redtab) !! k = mkrec (eprods G Shn) (iprods G ! k)\<close>
  by (simp add: eprods_nth)

subsubsection \<open>An item's contribution\<close>

definition nx_set :: \<open>nat \<Rightarrow> nat \<Rightarrow> ('n, 't) sitem \<Rightarrow> nat set\<close> where
  \<open>nx_set np a s = (case sitem_nx np s of Some (b, I) \<Rightarrow> if b = a then irep_set I else {} | None \<Rightarrow> {})\<close>

lemma map_filter_nx_set:
  \<open>kset a (List.map_filter (sitem_nx np) xs) = \<Union> (nx_set np a ` set xs)\<close>
proof (induction xs)
  case (Cons x xs)
  then show ?case by (cases \<open>sitem_nx np x\<close>) (auto simp: nx_set_def)
qed simp

lemma ximg_nx_set:
  assumes p: \<open>p \<in> set (eprods G Shn)\<close> and A: \<open>A \<in> fst ` set (iprods G)\<close>
  shows \<open>ximg (A, x) (sdec (mkrec (eprods G Shn) p, m, R)) =
    nx_set (length (iprods G)) (ntidx (map fst (eprods G Shn)) A) (mkrec (eprods G Shn) p, m, R)\<close>
proof -
  let ?ns = \<open>map fst (eprods G Shn)\<close>
  have An: \<open>A \<in> set ?ns\<close> using A by (force simp: eprods_def)
  have Al: \<open>ntidx ?ns A < length (iprods G)\<close> using lhs_id_less[of G Shn A] A by simp
  show ?thesis
  proof (cases \<open>m < length (snd p)\<close>)
    case True
    obtain X q where Xq: \<open>snd p ! m = (X, q)\<close> by (cases \<open>snd p ! m\<close>)
    show ?thesis
    proof (cases X)
      case (Nt B)
      have \<open>ntidx ?ns B = ntidx ?ns A \<longleftrightarrow> B = A\<close> by (rule ntidx_eq_iff[OF An])
      with True Xq Nt Al show ?thesis
        by (cases p) (auto simp: nx_set_def sitem_nx_def)
    qed (use True Xq in \<open>cases p, auto simp: nx_set_def sitem_nx_def\<close>)
  qed (cases p, auto simp: nx_set_def sitem_nx_def)
qed

lemma sitem_nx_key:
  assumes \<open>p \<in> set (eprods G Shn)\<close>
    and \<open>sitem_nx (length (iprods G)) (mkrec (eprods G Shn) p, m, R) = Some (b, I)\<close>
  shows \<open>b \<in> set (lids G Shn)\<close>
proof -
  let ?ns = \<open>map fst (eprods G Shn)\<close>
  from assms(2) obtain X q where Xq: \<open>rrhs (mkrec (eprods G Shn) p) ! m = (symid ?ns X, q)\<close>
      and s: \<open>symid ?ns X = Nt b\<close> and bl: \<open>b < length (iprods G)\<close>
    by (auto simp: sitem_nx_def split: if_splits sym.splits prod.splits)
  then obtain B where \<open>X = Nt B\<close> by (cases X) auto
  with s bl lhs_id_less[of G Shn B] show ?thesis by (force simp: set_lids)
qed

subsection \<open>The rounds agree\<close>

definition ine :: \<open>'p \<times> nat \<times> indrep \<Rightarrow> bool\<close> where
  \<open>ine x \<longleftrightarrow> irep_nonempty (snd (snd x))\<close>

lemma ine_simp [simp]: \<open>ine (p, m, R) \<longleftrightarrow> irep_nonempty R\<close>
  by (simp add: ine_def)

lemma irep_nonempty_iff: \<open>irep_nonempty I \<longleftrightarrow> I \<noteq> FinRep []\<close>
  by (cases I) auto

lemma ximg_cong: \<open>irep_set R = irep_set R' \<Longrightarrow> ximg pr (p, m, R) = ximg pr (p, m, R')\<close>
  by (cases p) simp

lemma ximg_emptyR: \<open>irep_set R = {} \<Longrightarrow> ximg pr (p, m, R) = {}\<close>
  by (cases p) simp

lemma ximg_fst: \<open>ximg (A, x) it = ximg (A, y) it\<close>
proof -
  obtain B rhs m R where \<open>it = ((B, rhs), m, R)\<close> by (metis prod.collapse)
  then show ?thesis by simp
qed
lemma ximg_filter_ine: \<open>\<Union> (ximg pr ` set (filter ine xs)) = \<Union> (ximg pr ` set xs)\<close>
proof (induction xs)
  case (Cons x xs)
  obtain p m R where x: \<open>x = (p, m, R)\<close> by (cases x)
  show ?case
  proof (cases \<open>ine x\<close>)
    case False
    then have \<open>ximg pr x = {}\<close> by (simp add: x ximg_emptyR)
    with False Cons.IH show ?thesis by simp
  qed (use Cons.IH in simp)
qed simp

lemma map_sdec_filter: \<open>map sdec (filter ine xs) = filter ine (map sdec xs)\<close>
  by (induction xs) (auto simp: ine_def)

text \<open>A sparse kernel stands for a kernel when its records are table records and
  their non-empty items agree.\<close>

definition skrel :: \<open>('n, 't) is_cfg \<Rightarrow> 'n \<Rightarrow> ('n, 't) xitem list \<Rightarrow> ('n, 't) sitem list \<Rightarrow> bool\<close> where
  \<open>skrel G Shn K Ks \<longleftrightarrow> swf (eprods G Shn) Ks \<and> xeq (filter ine K) (filter ine (map sdec Ks))\<close>

lemma swf_nx_set:
  assumes \<open>swf (eprods G Shn) Ks\<close> and \<open>A \<in> fst ` set (iprods G)\<close>
  shows \<open>\<Union> (nx_set (length (iprods G)) (ntidx (map fst (eprods G Shn)) A) ` set Ks) =
         \<Union> (ximg (A, x) ` set (map sdec Ks))\<close>
proof -
  have \<open>nx_set (length (iprods G)) (ntidx (map fst (eprods G Shn)) A) s = ximg (A, x) (sdec s)\<close>
    if \<open>s \<in> set Ks\<close> for s
  proof -
    obtain r m R where s: \<open>s = (r, m, R)\<close> by (cases s)
    with that assms(1) obtain p where \<open>p \<in> set (eprods G Shn)\<close> \<open>r = mkrec (eprods G Shn) p\<close>
      unfolding swf_def by fast
    with s ximg_nx_set[OF _ assms(2)] show ?thesis by metis
  qed
  then show ?thesis by simp
qed

lemma skn_kset:
  assumes T: \<open>T = mk_stab G Shn gt sts redtab\<close> and r: \<open>skrel G Shn K Ks\<close>
    and A: \<open>A \<in> fst ` set (iprods G)\<close>
  shows \<open>kset (ntidx (map fst (eprods G Shn)) A) (skn T Ks) = \<Union> (ximg (A, x) ` set K)\<close>
proof -
  have \<open>kset (ntidx (map fst (eprods G Shn)) A) (skn T Ks) = \<Union> (ximg (A, x) ` set (map sdec Ks))\<close>
    using r A unfolding skrel_def skn_def T kset_filter_ne
    by (simp only: map_filter_nx_set mk_stab_sel swf_nx_set)
  also have \<open>\<dots> = \<Union> (ximg (A, x) ` set (filter ine (map sdec Ks)))\<close>
    by (rule ximg_filter_ine[symmetric])
  also have \<open>\<dots> = \<Union> (ximg (A, x) ` set (filter ine K))\<close>
    using r unfolding skrel_def by (metis xeq_ximg)
  also have \<open>\<dots> = \<Union> (ximg (A, x) ` set K)\<close>
    by (rule ximg_filter_ine)
  finally show ?thesis .
qed

lemma map_filter_map: \<open>List.map_filter f (map g xs) = List.map_filter (f \<circ> g) xs\<close>
  by (induction xs) (auto split: option.split)

lemma sslot_kset:
  assumes T: \<open>T = mk_stab G Shn gt sts redtab\<close> and A: \<open>A \<in> fst ` set (iprods G)\<close>
  shows \<open>kset (ntidx (map fst (eprods G Shn)) A) (sslot_nx T a R) =
    \<Union> ((\<lambda>q. ximg (A, x) (iprods G ! q, 0, R)) ` {q. q < length (iprods G) \<and> lids G Shn ! q = a})\<close>
proof -
  have eq: \<open>nx_set (length (iprods G)) (ntidx (map fst (eprods G Shn)) A) (s_recs T !! q, 0, R) =
        ximg (A, x) (iprods G ! q, 0, R)\<close> if \<open>q < length (iprods G)\<close> for q
  proof -
    have \<open>iprods G ! q \<in> set (eprods G Shn)\<close> using that by (simp add: eprods_def)
    from ximg_nx_set[OF this A, of x 0 R] that show ?thesis by (simp add: T recs_mk_stab eprods_nth)
  qed
  have m: \<open>sslot_nx T a R = List.map_filter (sitem_nx (s_np T)) (map (\<lambda>k. (s_recs T !! k, 0, R)) (ntl T a))\<close>
    by (simp add: sslot_nx_def map_filter_map comp_def)
  have s: \<open>set (ntl T a) = {q. q < length (iprods G) \<and> lids G Shn ! q = a}\<close>
    by (auto simp: T ntl_mk_stab)
  have np: \<open>s_np T = length (iprods G)\<close> by (simp add: T)
  show ?thesis
    unfolding m np map_filter_nx_set set_map image_image s
    by (rule SUP_cong[OF refl]) (metis (no_types, lifting) eq mem_Collect_eq)
qed

lemma in_map_filter: \<open>y \<in> set (List.map_filter f xs) \<longleftrightarrow> (\<exists>x \<in> set xs. f x = Some y)\<close>
  by (induction xs) (auto split: option.split)

definition sinv :: \<open>('n, 't) is_cfg \<Rightarrow> 'n \<Rightarrow> (nat \<times> indrep) list \<Rightarrow> bool\<close> where
  \<open>sinv G Shn N \<longleftrightarrow> distinct (map fst N) \<and> fst ` set N \<subseteq> set (lids G Shn) \<and>
     (\<forall>(a, R) \<in> set N. irep_nonempty R)\<close>

definition siter :: \<open>('n, 't) stab \<Rightarrow> (nat \<times> indrep) list \<Rightarrow> nat \<Rightarrow> (nat \<times> indrep) list\<close> where
  \<open>siter T kn t = (sround T kn ^^ t) []\<close>

lemma siter_simps [simp]:
  \<open>siter T kn 0 = []\<close>
  \<open>siter T kn (Suc t) = sround T kn (siter T kn t)\<close>
  by (simp_all add: siter_def)

lemma skrel_swf: \<open>skrel G Shn K Ks \<Longrightarrow> swf (eprods G Shn) Ks\<close>
  by (simp add: skrel_def)

lemma skn_keys:
  assumes T: \<open>T = mk_stab G Shn gt sts redtab\<close> and w: \<open>swf (eprods G Shn) Ks\<close>
  shows \<open>fst ` set (skn T Ks) \<subseteq> set (lids G Shn)\<close>
proof
  fix b assume \<open>b \<in> fst ` set (skn T Ks)\<close>
  then obtain I s where s: \<open>s \<in> set Ks\<close> \<open>sitem_nx (length (iprods G)) s = Some (b, I)\<close>
    by (auto simp: skn_def T in_map_filter)
  obtain r m R where s': \<open>s = (r, m, R)\<close> by (cases s)
  with s(1) w obtain p where \<open>p \<in> set (eprods G Shn)\<close> \<open>r = mkrec (eprods G Shn) p\<close>
    unfolding swf_def by fast
  with s s' show \<open>b \<in> set (lids G Shn)\<close> by (metis sitem_nx_key)
qed

lemma sslot_keys:
  assumes T: \<open>T = mk_stab G Shn gt sts redtab\<close>
  shows \<open>fst ` set (sslot_nx T a R) \<subseteq> set (lids G Shn)\<close>
proof
  fix b assume b: \<open>b \<in> fst ` set (sslot_nx T a R)\<close>
  have np: \<open>s_np T = length (iprods G)\<close> by (simp add: T)
  from b obtain I where \<open>(b, I) \<in> set (sslot_nx T a R)\<close> by force
  then obtain k where k: \<open>k \<in> set (ntl T a)\<close>
      and ks: \<open>sitem_nx (length (iprods G)) (s_recs T !! k, 0, R) = Some (b, I)\<close>
    unfolding sslot_nx_def np in_map_filter by blast
  from k have kl: \<open>k < length (iprods G)\<close> by (simp add: T ntl_mk_stab)
  then have p: \<open>iprods G ! k \<in> set (eprods G Shn)\<close> by (simp add: eprods_def)
  from ks have \<open>sitem_nx (length (iprods G)) (mkrec (eprods G Shn) (iprods G ! k), 0, R) = Some (b, I)\<close>
    by (simp only: T recs_mk_stab[OF kl])
  with p show \<open>b \<in> set (lids G Shn)\<close> by (rule sitem_nx_key)
qed

lemma sround_inv:
  assumes T: \<open>T = mk_stab G Shn gt sts redtab\<close> and w: \<open>swf (eprods G Shn) Ks\<close>
  shows \<open>sinv G Shn (sround T (skn T Ks) N)\<close>
proof -
  let ?xs = \<open>skn T Ks @ filter (\<lambda>(_, I). I \<noteq> FinRep []) (concat (map (\<lambda>(a, R). sslot_nx T a R) N))\<close>
  have k: \<open>fst ` set ?xs \<subseteq> set (lids G Shn)\<close>
    using skn_keys[OF T w] sslot_keys[OF T] by fastforce
  have ne: \<open>\<forall>(b, I) \<in> set ?xs. irep_nonempty I\<close>
    by (auto simp: skn_def irep_nonempty_iff simp del: irep_nonempty_correct)
  show ?thesis
    unfolding sinv_def sround_def
    using fold_sins_distinct[of \<open>[]\<close> ?xs] fold_sins_keys[of ?xs \<open>[]\<close>] fold_sins_nonempty[OF ne, of \<open>[]\<close>] k
    by auto
qed

lemma siter_inv:
  assumes T: \<open>T = mk_stab G Shn gt sts redtab\<close> and w: \<open>swf (eprods G Shn) Ks\<close>
  shows \<open>sinv G Shn (siter T (skn T Ks) t)\<close>
proof (cases t)
  case 0
  then show ?thesis by (simp add: sinv_def)
next
  case (Suc n)
  then show ?thesis using sround_inv[OF T w] by simp
qed

lemma sinv_slk: \<open>sinv G Shn N \<Longrightarrow> (b, R) \<in> set N \<Longrightarrow> slk N b = R\<close>
  by (simp add: sinv_def slk_in)

lemma set_slots:
  assumes \<open>length cls = length (iprods G)\<close>
  shows \<open>set (map (\<lambda>(pr, R). (pr, 0::nat, R)) (zip (iprods G) cls)) =
    (\<lambda>q. (iprods G ! q, 0, cls ! q)) ` {0..<length (iprods G)}\<close>
proof -
  have \<open>zip (iprods G) cls = map (\<lambda>q. (iprods G ! q, cls ! q)) [0..<length (iprods G)]\<close>
    using assms by (intro nth_equalityI) simp_all
  then show ?thesis by (simp add: image_image)
qed

text \<open>The lockstep: after \<open>t\<close> rounds, the dense slot of a production and the
  sparse entry of its left-hand side hold the same anchor set.\<close>

lemma lockstep:
  assumes T: \<open>T = mk_stab G Shn gt sts redtab\<close> and r: \<open>skrel G Shn K Ks\<close>
    and q: \<open>q < length (iprods G)\<close>
  shows \<open>irep_set (diter G K t ! q) = irep_set (slk (siter T (skn T Ks) t) (lids G Shn ! q))\<close>
  using q
proof (induction t arbitrary: q)
  case 0
  then show ?case by (simp add: slk_def)
next
  case (Suc t)
  let ?N = \<open>siter T (skn T Ks) t\<close>
  let ?n = \<open>length (iprods G)\<close>
  have inv: \<open>sinv G Shn ?N\<close> by (rule siter_inv[OF T skrel_swf[OF r]])
  obtain A rhs where pr: \<open>iprods G ! q = (A, rhs)\<close> by fastforce
  have A: \<open>A \<in> fst ` set (iprods G)\<close> using Suc.prems pr by (metis fst_conv image_eqI nth_mem)
  have a: \<open>lids G Shn ! q = ntidx (map fst (eprods G Shn)) A\<close> using lids_nth[OF Suc.prems] pr by simp
  have IH: \<open>ximg (A, rhs) (iprods G ! q', 0, diter G K t ! q') =
      ximg (A, rhs) (iprods G ! q', 0, slk ?N (lids G Shn ! q'))\<close> if \<open>q' < ?n\<close> for q'
    by (rule ximg_cong[OF Suc.IH[OF that]])
  have slots: \<open>(\<Union>q' \<in> {0..<?n}. ximg (A, rhs) (iprods G ! q', 0, diter G K t ! q')) =
      (\<Union>(b, R) \<in> set ?N. \<Union>q' \<in> {q'. q' < ?n \<and> lids G Shn ! q' = b}. ximg (A, rhs) (iprods G ! q', 0, R))\<close>
  proof (intro equalityI subsetI)
    fix j assume \<open>j \<in> (\<Union>q' \<in> {0..<?n}. ximg (A, rhs) (iprods G ! q', 0, diter G K t ! q'))\<close>
    then obtain q' where q': \<open>q' < ?n\<close> and j0: \<open>j \<in> ximg (A, rhs) (iprods G ! q', 0, diter G K t ! q')\<close>
      by auto
    from j0 have j: \<open>j \<in> ximg (A, rhs) (iprods G ! q', 0, slk ?N (lids G Shn ! q'))\<close>
      by (simp only: IH[OF q'])
    show \<open>j \<in> (\<Union>(b, R) \<in> set ?N. \<Union>q' \<in> {q'. q' < ?n \<and> lids G Shn ! q' = b}. ximg (A, rhs) (iprods G ! q', 0, R))\<close>
    proof (cases \<open>lids G Shn ! q' \<in> fst ` set ?N\<close>)
      case True
      then obtain R where R: \<open>(lids G Shn ! q', R) \<in> set ?N\<close> by force
      with j sinv_slk[OF inv R] q' show ?thesis by fastforce
    next
      case False
      with j show ?thesis by (simp add: slk_notin ximg_emptyR)
    qed
  next
    fix j assume \<open>j \<in> (\<Union>(b, R) \<in> set ?N. \<Union>q' \<in> {q'. q' < ?n \<and> lids G Shn ! q' = b}. ximg (A, rhs) (iprods G ! q', 0, R))\<close>
    then obtain b R q' where R: \<open>(b, R) \<in> set ?N\<close> and q': \<open>q' < ?n\<close> \<open>lids G Shn ! q' = b\<close>
      and j: \<open>j \<in> ximg (A, rhs) (iprods G ! q', 0, R)\<close> by blast
    have \<open>j \<in> ximg (A, rhs) (iprods G ! q', 0, diter G K t ! q')\<close>
      using j sinv_slk[OF inv R] q'(2) IH[OF q'(1)] by simp
    with q'(1) show \<open>j \<in> (\<Union>q' \<in> {0..<?n}. ximg (A, rhs) (iprods G ! q', 0, diter G K t ! q'))\<close>
      by auto
  qed
  have dense: \<open>irep_set (diter G K (Suc t) ! q) =
      \<Union> (ximg (A, rhs) ` set K) \<union> (\<Union>q' \<in> {0..<?n}. ximg (A, rhs) (iprods G ! q', 0, diter G K t ! q'))\<close>
  proof -
    have \<open>irep_set (diter G K (Suc t) ! q) = \<Union> (ximg (A, rhs) ` set (xslots G K (diter G K t)))\<close>
      using Suc.prems pr by (simp add: dround_def fold_xcontrib_set)
    then show ?thesis
      by (simp only: xslots_def set_append set_slots[OF diter_length] image_Un Union_Un_distrib image_image)
  qed
  have sparse: \<open>irep_set (slk (siter T (skn T Ks) (Suc t)) (lids G Shn ! q)) =
      \<Union> (ximg (A, rhs) ` set K) \<union>
      (\<Union>(b, R) \<in> set ?N. \<Union>q' \<in> {q'. q' < ?n \<and> lids G Shn ! q' = b}. ximg (A, rhs) (iprods G ! q', 0, R))\<close>
  proof -
    have \<open>irep_set (slk (siter T (skn T Ks) (Suc t)) (lids G Shn ! q)) =
        kset (lids G Shn ! q) (skn T Ks) \<union> (\<Union>(b, R) \<in> set ?N. kset (lids G Shn ! q) (sslot_nx T b R))\<close>
      by (simp add: sround_def fold_sins_set kset_filter_ne kset_concat_map)
    also have \<open>\<dots> = \<Union> (ximg (A, rhs) ` set K) \<union>
        (\<Union>(b, R) \<in> set ?N. \<Union>q' \<in> {q'. q' < ?n \<and> lids G Shn ! q' = b}. ximg (A, rhs) (iprods G ! q', 0, R))\<close>
      unfolding a skn_kset[OF T r A, where x = rhs] sslot_kset[OF T A, where x = rhs] ..
    finally show ?thesis .
  qed
  show ?case by (simp only: dense sparse slots)
qed

text \<open>So the sparse loop stops when the dense one does.\<close>

lemma ssub_lockstep:
  assumes T: \<open>T = mk_stab G Shn gt sts redtab\<close> and r: \<open>skrel G Shn K Ks\<close>
  shows \<open>ssub (siter T (skn T Ks) (Suc t)) (siter T (skn T Ks) t) \<longleftrightarrow>
    list_all2 irep_subset (diter G K (Suc t)) (diter G K t)\<close>
proof -
  let ?N = \<open>siter T (skn T Ks) t\<close>
  let ?N' = \<open>siter T (skn T Ks) (Suc t)\<close>
  let ?n = \<open>length (iprods G)\<close>
  have inv': \<open>sinv G Shn ?N'\<close> by (rule siter_inv[OF T skrel_swf[OF r]])
  have \<open>ssub ?N' ?N \<longleftrightarrow> (\<forall>q < ?n. irep_set (slk ?N' (lids G Shn ! q)) \<subseteq> irep_set (slk ?N (lids G Shn ! q)))\<close>
  proof
    assume s: \<open>ssub ?N' ?N\<close>
    show \<open>\<forall>q < ?n. irep_set (slk ?N' (lids G Shn ! q)) \<subseteq> irep_set (slk ?N (lids G Shn ! q))\<close>
    proof (intro allI impI)
      fix q assume \<open>q < ?n\<close>
      show \<open>irep_set (slk ?N' (lids G Shn ! q)) \<subseteq> irep_set (slk ?N (lids G Shn ! q))\<close>
      proof (cases \<open>lids G Shn ! q \<in> fst ` set ?N'\<close>)
        case True
        then obtain R where R: \<open>(lids G Shn ! q, R) \<in> set ?N'\<close> by force
        with s sinv_slk[OF inv' R] show ?thesis by (auto simp: ssub_def list_all_iff)
      next
        case False
        then show ?thesis by (simp add: slk_notin)
      qed
    qed
  next
    assume a: \<open>\<forall>q < ?n. irep_set (slk ?N' (lids G Shn ! q)) \<subseteq> irep_set (slk ?N (lids G Shn ! q))\<close>
    have \<open>irep_subset R (slk ?N b)\<close> if b: \<open>(b, R) \<in> set ?N'\<close> for b R
    proof -
      from b inv' have \<open>b \<in> set (lids G Shn)\<close> by (force simp: sinv_def)
      then obtain q where q: \<open>q < ?n\<close> and bq: \<open>b = lids G Shn ! q\<close> by (auto simp: in_set_conv_nth)
      from a q have \<open>irep_set (slk ?N' (lids G Shn ! q)) \<subseteq> irep_set (slk ?N (lids G Shn ! q))\<close> by blast
      with bq sinv_slk[OF inv' b] show ?thesis by simp
    qed
    then show \<open>ssub ?N' ?N\<close> by (auto simp: ssub_def list_all_iff)
  qed
  also have \<open>\<dots> \<longleftrightarrow> list_all2 irep_subset (diter G K (Suc t)) (diter G K t)\<close>
    unfolding list_all2_conv_all_nth diter_length
    using lockstep[OF T r, where t = t] lockstep[OF T r, where t = \<open>Suc t\<close>] by auto
  finally show ?thesis .
qed

lemma sfix_siter:
  assumes T: \<open>T = mk_stab G Shn gt sts redtab\<close> and r: \<open>skrel G Shn K Ks\<close>
  shows \<open>sfix T (skn T Ks) = siter T (skn T Ks) (xfuel G K)\<close>
proof -
  let ?kn = \<open>skn T Ks\<close>
  obtain k where \<open>xstable G K (xiter G K k)\<close>
    using xcls_stable_ex by blast
  then have \<open>while_option (\<lambda>t. \<not> xstable G K (xiter G K t)) Suc 0 = Some (xfuel G K)\<close>
    unfolding xfuel_def by (rule nat_search_Some)
  moreover have
    \<open>map_option (\<lambda>t. (siter T ?kn t, siter T ?kn (Suc t)))
       (while_option (\<lambda>t. \<not> xstable G K (xiter G K t)) Suc 0) =
     while_option (\<lambda>(N, N'). \<not> ssub N' N) (\<lambda>(N, N'). (N', sround T ?kn N'))
       (siter T ?kn 0, siter T ?kn (Suc 0))\<close>
    by (rule while_option_commute[where f = \<open>\<lambda>t. (siter T ?kn t, siter T ?kn (Suc t))\<close> and s = 0])
      (simp_all only: xstable_diter[OF xeq_refl] ssub_lockstep[OF T r, simplified siter_simps] siter_simps case_prod_conv)
  ultimately have
    \<open>while_option (\<lambda>(N, N'). \<not> ssub N' N) (\<lambda>(N, N'). (N', sround T ?kn N')) ([], sround T ?kn []) =
     Some (siter T ?kn (xfuel G K), siter T ?kn (Suc (xfuel G K)))\<close>
    by simp
  then show ?thesis by (simp add: sfix_def)
qed

subsection \<open>The closures agree\<close>

lemma set_ntl:
  \<open>T = mk_stab G Shn gt sts redtab \<Longrightarrow> set (ntl T a) = {k. k < length (iprods G) \<and> lids G Shn ! k = a}\<close>
  by (auto simp: ntl_mk_stab)

lemma distinct_ntl: \<open>T = mk_stab G Shn gt sts redtab \<Longrightarrow> distinct (ntl T a)\<close>
  by (simp add: ntl_mk_stab)

lemma ntl_concat:
  assumes T: \<open>T = mk_stab G Shn gt sts redtab\<close> and d: \<open>distinct (map fst N)\<close>
  shows \<open>sort (concat (map (\<lambda>(a, _). ntl T a) N)) =
    filter (\<lambda>k. lids G Shn ! k \<in> fst ` set N) [0..<length (iprods G)]\<close>
proof (rule sorted_distinct_set_unique)
  have \<open>distinct (concat (map (\<lambda>(a, _). ntl T a) N))\<close> using d
  proof (induction N)
    case (Cons x N)
    obtain a R where x: \<open>x = (a, R)\<close> by (cases x)
    from Cons.prems x have \<open>a \<notin> fst ` set N\<close> by simp
    then have \<open>set (ntl T a) \<inter> set (concat (map (\<lambda>(a, _). ntl T a) N)) = {}\<close>
      by (force simp: set_ntl[OF T])
    with Cons x show ?case by (simp add: distinct_ntl[OF T])
  qed simp
  then show \<open>distinct (sort (concat (map (\<lambda>(a, _). ntl T a) N)))\<close> by simp
  show \<open>set (sort (concat (map (\<lambda>(a, _). ntl T a) N))) =
      set (filter (\<lambda>k. lids G Shn ! k \<in> fst ` set N) [0..<length (iprods G)])\<close>
    by (force simp: set_ntl[OF T])
qed (simp_all add: sorted_wrt_filter)

lemma list_all2_map_same:
  \<open>(\<And>x. x \<in> set xs \<Longrightarrow> P (f x) (g x)) \<Longrightarrow> list_all2 P (map f xs) (map g xs)\<close>
  by (induction xs) auto

lemma recs_sel:
  assumes T: \<open>T = mk_stab G Shn gt sts redtab\<close> and k: \<open>k < length (iprods G)\<close>
  shows \<open>rprod (s_recs T !! k) = iprods G ! k\<close> \<open>rlhs (s_recs T !! k) = lids G Shn ! k\<close>
  by (simp_all only: T recs_mk_stab[OF k] mkrec_sel lids_nth[OF k])

text \<open>A sparse closure stands for the non-empty items of the dense closure.\<close>

lemma sclosure_rel:
  assumes T: \<open>T = mk_stab G Shn gt sts redtab\<close> and r: \<open>skrel G Shn K Ks\<close>
  shows \<open>xeq (filter ine (dclosure G K)) (map sdec (sclosure T Ks))\<close>
proof -
  let ?n = \<open>length (iprods G)\<close>
  let ?cls = \<open>diter G K (xfuel G K)\<close>
  let ?N = \<open>sfix T (skn T Ks)\<close>
  let ?ks = \<open>filter (\<lambda>k. lids G Shn ! k \<in> fst ` set ?N) [0..<?n]\<close>
  have N: \<open>?N = siter T (skn T Ks) (xfuel G K)\<close> by (rule sfix_siter[OF T r])
  have inv: \<open>sinv G Shn ?N\<close> unfolding N by (rule siter_inv[OF T skrel_swf[OF r]])
  have lk: \<open>irep_set (?cls ! q) = irep_set (slk ?N (lids G Shn ! q))\<close> if \<open>q < ?n\<close> for q
    unfolding N by (rule lockstep[OF T r that])
  have ne: \<open>irep_set (slk ?N b) \<noteq> {} \<longleftrightarrow> b \<in> fst ` set ?N\<close> for b
  proof (cases \<open>b \<in> fst ` set ?N\<close>)
    case True
    then obtain R where R: \<open>(b, R) \<in> set ?N\<close> by force
    with inv have \<open>irep_nonempty R\<close> by (force simp: sinv_def simp del: irep_nonempty_correct)
    with True sinv_slk[OF inv R] show ?thesis by simp
  next
    case False
    then show ?thesis by (simp add: slk_notin)
  qed
  have zip: \<open>zip (iprods G) ?cls = map (\<lambda>q. (iprods G ! q, ?cls ! q)) [0..<?n]\<close>
    by (intro nth_equalityI) simp_all
  have dense: \<open>filter ine (dclosure G K) =
      filter ine K @ map (\<lambda>q. (iprods G ! q, 0, ?cls ! q)) ?ks\<close>
  proof -
    have fk: \<open>filter (\<lambda>q. irep_set (?cls ! q) \<noteq> {}) [0..<?n] = ?ks\<close>
      by (rule filter_cong[OF refl]) (simp add: lk ne)
    show ?thesis by (simp add: dclosure_def xslots_def zip filter_map o_def fk)
  qed
  have fne: \<open>filter (\<lambda>(_, _, R). irep_nonempty R) Ks = filter ine Ks\<close>
    by (rule filter_cong) (auto simp: ine_def simp del: irep_nonempty_correct)
  have sparse: \<open>map sdec (sclosure T Ks) =
      map sdec (filter ine Ks) @ map (\<lambda>k. (iprods G ! k, 0, slk ?N (lids G Shn ! k))) ?ks\<close>
    using inv unfolding sclosure_def Let_def fne sinv_def
    by (simp add: ntl_concat[OF T] recs_sel[OF T] del: IArray.sub_def cong: map_cong)
  have kern: \<open>xeq (filter ine K) (map sdec (filter ine Ks))\<close>
    using r by (simp add: skrel_def map_sdec_filter)
  have slots: \<open>xeq (map (\<lambda>q. (iprods G ! q, 0, ?cls ! q)) ?ks)
      (map (\<lambda>k. (iprods G ! k, 0, slk ?N (lids G Shn ! k))) ?ks)\<close>
    unfolding xrel_def by (rule list_all2_map_same) (simp add: lk)
  show ?thesis
    unfolding dense sparse using kern slots by (simp add: xrel_def list_all2_appendI)
qed

lemma sclosure_swf:
  assumes T: \<open>T = mk_stab G Shn gt sts redtab\<close> and w: \<open>swf (eprods G Shn) Ks\<close>
  shows \<open>swf (eprods G Shn) (sclosure T Ks)\<close>
proof -
  have \<open>s_recs T !! k \<in> mkrec (eprods G Shn) ` set (eprods G Shn)\<close> if \<open>k < length (iprods G)\<close> for k
    using that by (auto simp: T intro!: imageI nth_mem)
  with w show ?thesis
    by (auto simp: swf_def sclosure_def Let_def set_ntl[OF T] simp del: IArray.sub_def)
qed

subsection \<open>Coherence: the candidate order survives sparsity\<close>

text \<open>A list of items is coherent when items with the same production and dot
  have the same anchor set. The closures the driver builds are coherent, so a
  production with a non-empty complete item has only non-empty complete items,
  and the last occurrence that \<^const>\<open>remdups\<close> keeps in \<^const>\<open>dcands\<close> is
  a non-empty one.\<close>

definition coh :: \<open>('n, 't) xitem list \<Rightarrow> bool\<close> where
  \<open>coh xs \<longleftrightarrow> (\<forall>p m R R'. (p, m, R) \<in> set xs \<longrightarrow> (p, m, R') \<in> set xs \<longrightarrow> irep_set R = irep_set R')\<close>

definition kinv :: \<open>('n, 't) is_cfg \<Rightarrow> ('n, 't) xitem list \<Rightarrow> bool\<close> where
  \<open>kinv G K \<longleftrightarrow> coh K \<and> (\<forall>p R. (p, 0, R) \<in> set K \<longrightarrow> p \<notin> set (iprods G))\<close>

lemma xiter_slot_eq:
  assumes \<open>q < length (iprods G)\<close> \<open>q' < length (iprods G)\<close> \<open>iprods G ! q = iprods G ! q'\<close>
  shows \<open>irep_set (xiter G xs s ! q) = irep_set (xiter G xs s ! q')\<close>
  using assms by (cases s) (simp_all only: xiter_Suc_set, simp)

lemma coh_xclosure:
  assumes k: \<open>kinv G K\<close>
  shows \<open>coh (xclosure_auto G K)\<close>
proof -
  let ?cls = \<open>xiter G K (xfuel G K)\<close>
  have c: \<open>coh K\<close> and k0: \<open>\<And>p R. (p, 0, R) \<in> set K \<Longrightarrow> p \<notin> set (iprods G)\<close>
    using k by (auto simp: kinv_def)
  have S: \<open>set (xclosure_auto G K) = set K \<union> (\<lambda>q. (iprods G ! q, 0, ?cls ! q)) ` {0..<length (iprods G)}\<close>
    by (simp only: xclosure_auto_def xclosure_def xslots_def set_append set_slots[OF xiter_length])
  show ?thesis
    unfolding coh_def S
  proof (intro allI impI)
    fix p m R R'
    assume a: \<open>(p, m, R) \<in> set K \<union> (\<lambda>q. (iprods G ! q, 0, ?cls ! q)) ` {0..<length (iprods G)}\<close>
      and b: \<open>(p, m, R') \<in> set K \<union> (\<lambda>q. (iprods G ! q, 0, ?cls ! q)) ` {0..<length (iprods G)}\<close>
    show \<open>irep_set R = irep_set R'\<close>
    proof (cases \<open>(p, m, R) \<in> set K\<close>)
      case aK: True
      show ?thesis
      proof (cases \<open>(p, m, R') \<in> set K\<close>)
        case True
        with aK c show ?thesis unfolding coh_def by blast
      next
        case False
        with b obtain q where \<open>q < length (iprods G)\<close> \<open>p = iprods G ! q\<close> \<open>m = 0\<close> by auto
        with aK k0 have False by (metis nth_mem)
        then show ?thesis ..
      qed
    next
      case False
      with a obtain q where q: \<open>q < length (iprods G)\<close> \<open>p = iprods G ! q\<close> \<open>m = 0\<close> \<open>R = ?cls ! q\<close>
        by auto
      show ?thesis
      proof (cases \<open>(p, m, R') \<in> set K\<close>)
        case True
        with q k0 have False by (metis nth_mem)
        then show ?thesis ..
      next
        case False
        with b obtain q' where q': \<open>q' < length (iprods G)\<close> \<open>p = iprods G ! q'\<close> \<open>R' = ?cls ! q'\<close>
          by auto
        from q q' show ?thesis by (metis xiter_slot_eq)
      qed
    qed
  qed
qed
lemma coh_lgoto:
  assumes c: \<open>coh xs\<close>
  shows \<open>coh (lgoto xs X RA)\<close>
  unfolding coh_def
proof (intro allI impI)
  fix p m R R'
  assume a: \<open>(p, m, R) \<in> set (lgoto xs X RA)\<close> and b: \<open>(p, m, R') \<in> set (lgoto xs X RA)\<close>
  from lgoto_dot_pos[OF a] obtain k where m: \<open>m = Suc k\<close> by (metis gr0_conv_Suc)
  obtain R0 where R0: \<open>(p, k, R0) \<in> set xs\<close> \<open>R = irep_inter R0 (irep_pre (snd (snd p ! k)) RA)\<close>
    using a unfolding m by (rule lgoto_kernel_step)
  obtain R0' where R0': \<open>(p, k, R0') \<in> set xs\<close> \<open>R' = irep_inter R0' (irep_pre (snd (snd p ! k)) RA)\<close>
    using b unfolding m by (rule lgoto_kernel_step)
  from R0(1) R0'(1) c have \<open>irep_set R0 = irep_set R0'\<close> unfolding coh_def by blast
  with R0(2) R0'(2) show \<open>irep_set R = irep_set R'\<close> by simp
qed

lemma kinv_lgoto: \<open>coh xs \<Longrightarrow> kinv G (lgoto xs X RA)\<close>
  unfolding kinv_def using coh_lgoto lgoto_dot_pos by blast

lemma kinv_xinit: \<open>fresh_name G Shn \<Longrightarrow> kinv G (xinit G Shn)\<close>
  by (force simp: kinv_def coh_def xinit_def fresh_name_def)

lemma filter_remdups_map:
  assumes \<open>\<And>x. x \<in> set xs \<Longrightarrow> P (f x) \<Longrightarrow> Q x\<close>
  shows \<open>filter P (remdups (map f xs)) = filter P (remdups (map f (filter Q xs)))\<close>
  using assms
proof (induction xs)
  case (Cons x xs)
  then have IH: \<open>filter P (remdups (map f xs)) = filter P (remdups (map f (filter Q xs)))\<close> by simp
  have eq: \<open>f x \<in> f ` set xs \<longleftrightarrow> f x \<in> f ` set (filter Q xs)\<close> if \<open>P (f x)\<close>
    using that Cons.prems by force
  show ?case
    using IH eq Cons.prems[of x] by (cases \<open>P (f x)\<close>) auto
qed simp

lemma red_set_filter_ine: \<open>irep_set (red_set (filter ine CL) pr) = irep_set (red_set CL pr)\<close>
  by (auto simp: red_set_correct ine_def)

lemma dcands_coh:
  assumes c: \<open>coh CL\<close>
  shows \<open>dcands G i cells CL gc = dcands G i cells (filter ine CL) gc\<close>
proof -
  let ?cmp = \<open>\<lambda>(pr, m, R). m = length (snd pr)\<close>
  have eq: \<open>(\<lambda>pr. irep_nonempty (red_set (filter ine CL) pr) \<and> dlic i cells w pr (red_set (filter ine CL) pr)) =
        (\<lambda>pr. irep_nonempty (red_set CL pr) \<and> dlic i cells w pr (red_set CL pr))\<close> for w
    by (rule ext) (simp only: irep_nonempty_correct red_set_filter_ine dlic_cong[OF red_set_filter_ine])
  have ff: \<open>filter ?cmp (filter ine CL) = filter ine (filter ?cmp CL)\<close>
    by (simp add: conj_commute)
  have comps: \<open>filter (\<lambda>pr. irep_nonempty (red_set CL pr) \<and> dlic i cells w pr (red_set CL pr))
        (remdups (map fst (filter ?cmp CL))) =
      filter (\<lambda>pr. irep_nonempty (red_set CL pr) \<and> dlic i cells w pr (red_set CL pr))
        (remdups (map fst (filter ine (filter ?cmp CL))))\<close> for w
  proof (rule filter_remdups_map)
    fix x assume x: \<open>x \<in> set (filter ?cmp CL)\<close>
      and P: \<open>irep_nonempty (red_set CL (fst x)) \<and> dlic i cells w (fst x) (red_set CL (fst x))\<close>
    obtain p m R where xp: \<open>x = (p, m, R)\<close> by (cases x)
    obtain R' where R': \<open>(p, length (snd p), R') \<in> set CL\<close> \<open>irep_nonempty R'\<close>
      using P[unfolded xp fst_conv] red_set_nonempty_iff by blast
    from x xp have \<open>(p, length (snd p), R) \<in> set CL\<close> by auto
    with R' c have \<open>irep_set R = irep_set R'\<close> unfolding coh_def by blast
    with R'(2) show \<open>ine x\<close> by (simp add: xp)
  qed
  show ?thesis unfolding dcands_def Let_def eq ff comps ..
qed

subsection \<open>The driver's operations on sparse items\<close>

text \<open>Each operation decodes to its dense counterpart: symbols are compared as
  numbers, productions by their number.\<close>

definition slgoto :: \<open>('n, 't) sitem list \<Rightarrow> (nat, 't) sym \<Rightarrow> indrep \<Rightarrow> ('n, 't) sitem list\<close> where
  \<open>slgoto xs X RA =
     map (\<lambda>(r, m, R). (r, Suc m, irep_inter R (irep_pre (snd (rrhs r ! m)) RA)))
       (filter (\<lambda>(r, m, R). m < length (rrhs r) \<and> fst (rrhs r ! m) = X) xs)\<close>

definition sred :: \<open>('n, 't) sitem list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> indrep\<close> where
  \<open>sred xs k n = foldr (\<lambda>(r, m, R) acc. if rpid r = k \<and> m = n then irep_union R acc else acc)
     xs (FinRep [])\<close>

definition sdlic :: \<open>nat \<Rightarrow> (nat \<times> (nat \<times> nat) \<times> 't option \<times> wrel) list \<Rightarrow> ('t \<times> nat) list \<Rightarrow>
    nat \<Rightarrow> nat \<Rightarrow> indrep \<Rightarrow> bool\<close> where
  \<open>sdlic i cells w k n RS \<longleftrightarrow> list_ex (\<lambda>(i', itm, t, \<tau>).
       i' = i \<and> itm = (k, n) \<and>
       (case w of [] \<Rightarrow> t = None | (a, c) # _ \<Rightarrow> t = Some a \<and> irep_ex_wsat \<tau> c RS)) cells\<close>

definition slive :: \<open>('n, 't) sitem list \<Rightarrow> bool\<close> where
  \<open>slive xs = list_ex (\<lambda>(r, m, R). irep_nonempty R) xs\<close>

definition sgfinal :: \<open>('n, 't) stab \<Rightarrow> ('n, 't) sitem list list \<times> ('t \<times> nat) list \<Rightarrow> bool\<close> where
  \<open>sgfinal T gc \<longleftrightarrow> (case gc of (Ys, v) \<Rightarrow> v = [] \<and> Ys \<noteq> [] \<and>
      list_ex (\<lambda>(r, m, R). rlhs r = s_np T \<and> m = Suc 0 \<and> irep_mem (s_i0 T) R) (hd Ys))\<close>

definition sdnext :: \<open>('n, 't) stab \<Rightarrow> nat \<Rightarrow> (nat, 't) sym \<Rightarrow> nat\<close> where
  \<open>sdnext T i X = (if i < IArray.length (s_gt T)
     then min (case map_of (s_gt T !! i) X of Some j \<Rightarrow> j | None \<Rightarrow> s_ns T) (s_ns T)
     else s_ns T)\<close>

definition scells :: \<open>('n \<times> ('n, 't) rhs) list \<Rightarrow> ('n, 't) lacell list \<Rightarrow>
    (nat \<times> (nat \<times> nat) \<times> 't option \<times> wrel) list\<close> where
  \<open>scells ps cells = map (\<lambda>(i', (pr, n), t, \<tau>). (i', (ntidx ps pr, n), t, \<tau>)) cells\<close>

lemma rt_mk_stab: \<open>s_rt (mk_stab G Shn gt sts redtab) = IArray (map (scells (eprods G Shn)) redtab)\<close>
  by (simp add: scells_def)

text \<open>A symbol is told apart by its number when no other symbol has it: the
  terminals, and the nonterminals with productions.\<close>

definition sgood :: \<open>'n list \<Rightarrow> ('n, 't) sym \<Rightarrow> bool\<close> where
  \<open>sgood ns X \<longleftrightarrow> (\<forall>Y. symid ns Y = symid ns X \<longrightarrow> Y = X)\<close>

lemma sgood_Tm [simp]: \<open>sgood ns (Tm a)\<close>
  unfolding sgood_def by (intro allI impI, case_tac Y) auto

lemma sgood_Nt: \<open>B \<in> set ns \<Longrightarrow> sgood ns (Nt B)\<close>
  unfolding sgood_def by (intro allI impI, case_tac Y) (auto simp: ntidx_eq_iff)

lemma rrhs_nth:
  \<open>m < length (snd p) \<Longrightarrow> rrhs (mkrec ps p) ! m = (symid (map fst ps) (fst (snd p ! m)), snd (snd p ! m))\<close>
  by (simp add: split_beta)

lemma swf_ConsD:
  assumes \<open>swf ps ((r, m, R) # xs)\<close>
  obtains p where \<open>r = mkrec ps p\<close> \<open>p \<in> set ps\<close> \<open>swf ps xs\<close>
  using assms unfolding swf_def by auto

lemma slgoto_dec:
  assumes w: \<open>swf ps xs\<close> and g: \<open>sgood (map fst ps) X\<close>
  shows \<open>map sdec (slgoto xs (symid (map fst ps) X) RA) = lgoto (map sdec xs) X RA\<close>
  using w
proof (induction xs)
  case (Cons x xs)
  obtain r m R where x: \<open>x = (r, m, R)\<close> by (cases x)
  from Cons.prems obtain p where r: \<open>r = mkrec ps p\<close> and w': \<open>swf ps xs\<close>
    unfolding x by (rule swf_ConsD)
  have IH: \<open>map sdec (slgoto xs (symid (map fst ps) X) RA) = lgoto (map sdec xs) X RA\<close>
    by (rule Cons.IH[OF w'])
  show ?case
  proof (cases \<open>m < length (snd p)\<close>)
    case True
    obtain Y I where yi: \<open>snd p ! m = (Y, I)\<close> by (cases \<open>snd p ! m\<close>)
    have \<open>symid (map fst ps) Y = symid (map fst ps) X \<longleftrightarrow> Y = X\<close>
      using g unfolding sgood_def by auto
    with True IH show ?thesis
      by (simp add: x r slgoto_def lgoto_def yi)
  next
    case False
    with IH show ?thesis by (simp add: x r slgoto_def lgoto_def)
  qed
qed (simp add: slgoto_def lgoto_def)

lemma slgoto_swf: \<open>swf ps xs \<Longrightarrow> swf ps (slgoto xs X RA)\<close>
  unfolding swf_def slgoto_def by auto

lemma sred_dec:
  assumes w: \<open>swf ps xs\<close> and p: \<open>pr \<in> set ps\<close>
  shows \<open>sred xs (ntidx ps pr) (length (snd pr)) = red_set (map sdec xs) pr\<close>
  using w
proof (induction xs)
  case (Cons x xs)
  obtain r m R where x: \<open>x = (r, m, R)\<close> by (cases x)
  from Cons.prems obtain q where r: \<open>r = mkrec ps q\<close> and w': \<open>swf ps xs\<close>
    unfolding x by (rule swf_ConsD)
  have \<open>ntidx ps q = ntidx ps pr \<longleftrightarrow> q = pr\<close> by (rule ntidx_eq_iff[OF p])
  with Cons.IH[OF w'] show ?case by (simp add: x r sred_def red_set_def)
qed (simp add: sred_def red_set_def)

lemma sdlic_dec:
  assumes p: \<open>pr \<in> set ps\<close>
  shows \<open>sdlic i (scells ps cells) w (ntidx ps pr) (length (snd pr)) RS = dlic i cells w pr RS\<close>
proof -
  have e: \<open>ntidx ps q = ntidx ps pr \<longleftrightarrow> q = pr\<close> for q by (rule ntidx_eq_iff[OF p])
  show ?thesis
    by (induction cells) (auto simp: sdlic_def dlic_def scells_def e)
qed

lemma live_filter_ine: \<open>live (filter ine xs) = live xs\<close>
  by (induction xs) (auto simp: live_def ine_def)

lemma slive_dec: \<open>slive xs = live (map sdec xs)\<close>
  by (induction xs) (auto simp: slive_def live_def)

lemma skrel_live: \<open>skrel G Shn K Ks \<Longrightarrow> live K = slive Ks\<close>
  unfolding skrel_def slive_dec by (metis live_filter_ine live_xeq)

lemma lhs_id_start:
  assumes fr: \<open>fresh_name G Shn\<close> and p: \<open>p \<in> set (eprods G Shn)\<close>
  shows \<open>ntidx (map fst (eprods G Shn)) (fst p) = length (iprods G) \<longleftrightarrow> fst p = Shn\<close>
proof (cases \<open>fst p = Shn\<close>)
  case True
  have \<open>Shn \<notin> set (map fst (iprods G))\<close> using fr by (auto simp: fresh_name_def)
  with True show ?thesis by (simp add: eprods_def ntidx_append_notin)
next
  case False
  with p have \<open>fst p \<in> fst ` set (iprods G)\<close> by (force simp: eprods_def)
  with False lhs_id_less[of G Shn \<open>fst p\<close>] show ?thesis by simp
qed

lemma map_of_map_key:
  \<open>(\<forall>Y. f Y = f X \<longrightarrow> Y = X) \<Longrightarrow> map_of (map (\<lambda>(k, v). (f k, v)) l) (f X) = map_of l X\<close>
  by (induction l) auto

lemma sdnext_dec:
  assumes T: \<open>T = mk_stab G Shn gt sts redtab\<close> and g: \<open>sgood (map fst (eprods G Shn)) X\<close>
  shows \<open>sdnext T i (symid (map fst (eprods G Shn)) X) = dnext gt sts i X\<close>
proof -
  have m: \<open>map_of (map (\<lambda>(k, v). (symid (map fst (eprods G Shn)) k, v)) l)
      (symid (map fst (eprods G Shn)) X) = map_of l X\<close> for l :: \<open>(_ \<times> nat) list\<close>
    by (rule map_of_map_key) (use g in \<open>simp add: sgood_def\<close>)
  show ?thesis by (simp add: T sdnext_def dnext_def la_next_def m split: option.split)
qed

subsection \<open>Sparse closures against dense ones\<close>

lemma xeq_trans: \<open>xeq xs ys \<Longrightarrow> xeq ys zs \<Longrightarrow> xeq xs zs\<close>
  unfolding xrel_def by (rule list_all2_trans[rotated], assumption, assumption) (auto split: prod.splits)

lemma xeq_filter_ine: \<open>xeq xs ys \<Longrightarrow> xeq (filter ine xs) (filter ine ys)\<close>
  unfolding xrel_def by (induction rule: list_all2_induct) (auto split: prod.split_asm)

lemma lgoto_filter_ine: \<open>filter ine (lgoto (filter ine xs) X RA) = filter ine (lgoto xs X RA)\<close>
proof (induction xs)
  case (Cons x xs)
  obtain p m R where x: \<open>x = (p, m, R)\<close> by (cases x)
  with Cons.IH show ?case by (auto simp: lgoto_def)
qed (simp add: lgoto_def)

text \<open>A cached dense closure and its sparse counterpart.\<close>

definition screl :: \<open>('n, 't) is_cfg \<Rightarrow> 'n \<Rightarrow> ('n, 't) xitem list \<Rightarrow> ('n, 't) sitem list \<Rightarrow> bool\<close> where
  \<open>screl G Shn CL CLs \<longleftrightarrow> coh CL \<and> swf (eprods G Shn) CLs \<and> xeq (filter ine CL) (map sdec CLs)\<close>

lemma screl_Nil [simp]: \<open>screl G Shn [] []\<close>
  by (simp add: screl_def coh_def swf_def xrel_def)

lemma screl_lgoto:
  assumes c: \<open>screl G Shn CL CLs\<close> and g: \<open>sgood (map fst (eprods G Shn)) X\<close>
    and RA: \<open>irep_set RA = irep_set RB\<close>
  shows \<open>skrel G Shn (lgoto CL X RA) (slgoto CLs (symid (map fst (eprods G Shn)) X) RB)\<close>
    and \<open>kinv G (lgoto CL X RA)\<close>
proof -
  have w: \<open>swf (eprods G Shn) CLs\<close> and x: \<open>xeq (filter ine CL) (map sdec CLs)\<close> and h: \<open>coh CL\<close>
    using c unfolding screl_def by simp_all
  have \<open>xeq (filter ine (lgoto (filter ine CL) X RA)) (filter ine (lgoto (map sdec CLs) X RB))\<close>
    by (rule xeq_filter_ine, rule lgoto_xeq[OF x RA])
  then show \<open>skrel G Shn (lgoto CL X RA) (slgoto CLs (symid (map fst (eprods G Shn)) X) RB)\<close>
    unfolding skrel_def lgoto_filter_ine slgoto_dec[OF w g] using slgoto_swf[OF w] by simp
  show \<open>kinv G (lgoto CL X RA)\<close> by (rule kinv_lgoto[OF h])
qed

lemma screl_closure:
  assumes T: \<open>T = mk_stab G Shn gt sts redtab\<close> and r: \<open>skrel G Shn K Ks\<close> and k: \<open>kinv G K\<close>
  shows \<open>screl G Shn (xclosure_auto G K) (sclosure T Ks)\<close>
  unfolding screl_def
  using coh_xclosure[OF k] sclosure_swf[OF T skrel_swf[OF r]]
    xeq_trans[OF xeq_filter_ine[OF xclosure_auto_dclosure[OF xeq_refl]] sclosure_rel[OF T r]]
  by simp

lemma screl_red:
  assumes c: \<open>screl G Shn CL CLs\<close> and p: \<open>pr \<in> set (eprods G Shn)\<close>
  shows \<open>irep_set (sred CLs (ntidx (eprods G Shn) pr) (length (snd pr))) = irep_set (red_set CL pr)\<close>
proof -
  have w: \<open>swf (eprods G Shn) CLs\<close> and x: \<open>xeq (filter ine CL) (map sdec CLs)\<close>
    using c unfolding screl_def by simp_all
  show ?thesis
    unfolding sred_dec[OF w p] using red_set_xeq[OF x, of pr] red_set_filter_ine[of CL pr] by simp
qed

lemma recs_ntidx:
  assumes T: \<open>T = mk_stab G Shn gt sts redtab\<close> and p: \<open>p \<in> set (eprods G Shn)\<close>
  shows \<open>s_recs T !! ntidx (eprods G Shn) p = mkrec (eprods G Shn) p\<close>
proof -
  have \<open>ntidx (eprods G Shn) p < length (eprods G Shn)\<close> using p by (simp only: ntidx_less)
  with p show ?thesis by (simp add: T ntidx_nth)
qed

subsection \<open>The sparse driver\<close>

datatype ('n, 't) sact = SShift | SReduce \<open>('n, 't) prec\<close>

fun sdec_act :: \<open>('n, 't) sact \<Rightarrow> ('n, 't) dact\<close> where
  \<open>sdec_act SShift = DShift\<close>
| \<open>sdec_act (SReduce r) = DReduce (rprod r)\<close>

type_synonym ('n, 't) sgconfig = \<open>('n, 't) sitem list list \<times> ('t \<times> nat) list\<close>

definition sdcands :: \<open>('n, 't) stab \<Rightarrow> nat \<Rightarrow> (nat \<times> (nat \<times> nat) \<times> 't option \<times> wrel) list \<Rightarrow>
    ('n, 't) sitem list \<Rightarrow> ('n, 't) sgconfig \<Rightarrow> ('n, 't) sact list\<close> where
  \<open>sdcands T i cells CL gc = (case gc of (Xs, w) \<Rightarrow>
     if Xs = [] then [] else
     let comps = remdups (map (\<lambda>(r, m, R). rpid r) (filter (\<lambda>(r, m, R). m = length (rrhs r)) CL));
         reds = map (\<lambda>k. SReduce (s_recs T !! k)) (filter (\<lambda>k. let n = length (rrhs (s_recs T !! k));
                    RS = sred CL k n in irep_nonempty RS \<and> sdlic i cells w k n RS) comps)
     in (case w of [] \<Rightarrow> reds | _ \<Rightarrow> SShift # reds))\<close>

lemma remdups_map_inj: \<open>inj_on f (set xs) \<Longrightarrow> remdups (map f xs) = map f (remdups xs)\<close>
  by (induction xs) (auto simp: inj_on_def)

lemma sdcands_dec:
  assumes T: \<open>T = mk_stab G Shn gt sts redtab\<close> and w: \<open>swf (eprods G Shn) CLs\<close>
    and e: \<open>Ks = [] \<longleftrightarrow> Xs = []\<close>
  shows \<open>map sdec_act (sdcands T i (scells (eprods G Shn) cells) CLs (Ks, v)) =
         dcands G i cells (map sdec CLs) (Xs, v)\<close>
proof -
  let ?ps = \<open>eprods G Shn\<close>
  let ?C = \<open>map fst (filter (\<lambda>(pr, m, R). m = length (snd pr)) (map sdec CLs))\<close>
  have C: \<open>set ?C \<subseteq> set ?ps\<close> using w by (auto simp: swf_def)
  have \<open>map (\<lambda>(r, m, R). rpid r) (filter (\<lambda>(r, m, R). m = length (rrhs r)) CLs) = map (ntidx ?ps) ?C\<close>
    using w
  proof (induction CLs)
    case (Cons x xs)
    obtain r m R where x: \<open>x = (r, m, R)\<close> by (cases x)
    from Cons.prems obtain p where \<open>r = mkrec ?ps p\<close> \<open>swf ?ps xs\<close> unfolding x by (rule swf_ConsD)
    with Cons.IH show ?case by (simp add: x)
  qed simp
  moreover have inj: \<open>inj_on (ntidx ?ps) (set ?C)\<close>
  proof (rule inj_onI)
    fix x y assume \<open>x \<in> set ?C\<close> \<open>y \<in> set ?C\<close> \<open>ntidx ?ps x = ntidx ?ps y\<close>
    with C ntidx_eq_iff[of y ?ps x] show \<open>x = y\<close> by blast
  qed
  ultimately have comps: \<open>remdups (map (\<lambda>(r, m, R). rpid r) (filter (\<lambda>(r, m, R). m = length (rrhs r)) CLs)) =
      map (ntidx ?ps) (remdups ?C)\<close>
    by (simp only: remdups_map_inj[OF inj])
  have P: \<open>(irep_nonempty (sred CLs (ntidx ?ps p) (length (snd p))) \<and>
        sdlic i (scells ?ps cells) u (ntidx ?ps p) (length (snd p)) (sred CLs (ntidx ?ps p) (length (snd p)))) \<longleftrightarrow>
      (irep_nonempty (red_set (map sdec CLs) p) \<and> dlic i cells u p (red_set (map sdec CLs) p))\<close>
    if \<open>p \<in> set ?ps\<close> for p u
    using that by (simp add: sred_dec[OF w] sdlic_dec del: irep_nonempty_correct)
  have red: \<open>set L \<subseteq> set ?ps \<Longrightarrow>
      map (sdec_act \<circ> (\<lambda>k. SReduce (s_recs T !! k))) (filter (\<lambda>k.
          irep_nonempty (sred CLs k (length (rrhs (s_recs T !! k)))) \<and>
          sdlic i (scells ?ps cells) u k (length (rrhs (s_recs T !! k)))
            (sred CLs k (length (rrhs (s_recs T !! k))))) (map (ntidx ?ps) L)) =
      map DReduce (filter (\<lambda>pr. irep_nonempty (red_set (map sdec CLs) pr) \<and>
          dlic i cells u pr (red_set (map sdec CLs) pr)) L)\<close> for L u
    by (induction L) (simp_all add: P recs_ntidx[OF T] del: IArray.sub_def irep_nonempty_correct)
  have sub: \<open>set (remdups ?C) \<subseteq> set ?ps\<close> using C by simp
  show ?thesis
    unfolding sdcands_def dcands_def Let_def comps
    by (simp add: e red[OF sub] split: list.split del: IArray.sub_def irep_nonempty_correct)
qed

definition sgood_act :: \<open>('n, 't) is_cfg \<Rightarrow> 'n \<Rightarrow> ('n, 't) sact \<Rightarrow> bool\<close> where
  \<open>sgood_act G Shn a \<longleftrightarrow> (case a of SShift \<Rightarrow> True
     | SReduce r \<Rightarrow> r \<in> mkrec (eprods G Shn) ` set (eprods G Shn))\<close>

lemma sdcands_good:
  assumes T: \<open>T = mk_stab G Shn gt sts redtab\<close> and w: \<open>swf (eprods G Shn) CL\<close>
  shows \<open>\<forall>act \<in> set (sdcands T i cells CL gc). sgood_act G Shn act\<close>
proof -
  have r: \<open>sgood_act G Shn (SReduce (s_recs T !! rpid r))\<close>
    if \<open>(r, m, R) \<in> set CL\<close> for r m R
  proof -
    from w that obtain p where \<open>p \<in> set (eprods G Shn)\<close> \<open>r = mkrec (eprods G Shn) p\<close>
      unfolding swf_def by blast
    then show ?thesis using recs_ntidx[OF T] by (simp add: sgood_act_def del: IArray.sub_def)
  qed
  obtain Xs w where gc: \<open>gc = (Xs, w)\<close> by (cases gc)
  let ?f = \<open>\<lambda>k. SReduce (s_recs T !! k)\<close> and ?g = \<open>\<lambda>(r :: ('n, 't) prec, m :: nat, R :: indrep). rpid r\<close>
  have sub: \<open>set (map ?f (filter P (remdups (map ?g (filter Q CL))))) \<subseteq> ?f ` ?g ` set CL\<close> for P Q
    unfolding set_map
    by (rule image_mono, rule order_trans[OF filter_is_subset], simp only: set_remdups set_map,
        rule image_mono, rule filter_is_subset)
  have S: \<open>set (sdcands T i cells CL gc) \<subseteq> insert SShift (?f ` ?g ` set CL)\<close>
  proof (cases \<open>Xs = []\<close>)
    case False
    show ?thesis
    proof (cases w)
      case Nil
      show ?thesis unfolding sdcands_def Let_def gc prod.case if_not_P[OF False] Nil list.case
        by (rule subset_insertI2[OF sub])
    next
      case (Cons a w')
      show ?thesis unfolding sdcands_def Let_def gc prod.case if_not_P[OF False] Cons list.case list.set
        by (rule insert_mono[OF sub])
    qed
  qed (simp add: sdcands_def gc)
  show ?thesis
  proof
    fix act assume \<open>act \<in> set (sdcands T i cells CL gc)\<close>
    with S obtain x where \<open>act = SShift \<or> (x \<in> set CL \<and> act = ?f (?g x))\<close> by blast
    then show \<open>sgood_act G Shn act\<close>
    proof
      assume \<open>act = SShift\<close>
      then show ?thesis by (simp add: sgood_act_def)
    next
      assume a: \<open>x \<in> set CL \<and> act = ?f (?g x)\<close>
      obtain r m R where x: \<open>x = (r, m, R)\<close> by (cases x)
      from a r[of r m R] show ?thesis by (simp add: x del: IArray.sub_def)
    qed
  qed
qed

definition smstep :: \<open>('n, 't) sitem list list \<Rightarrow> ('n, 't) sgconfig \<Rightarrow> ('n, 't) sact \<Rightarrow>
    ('n, 't) sgconfig option\<close> where
  \<open>smstep cstk gc act = (case gc of (Xs, w) \<Rightarrow> (case act of
      SShift \<Rightarrow> (case w of [] \<Rightarrow> None | (a, c) # w' \<Rightarrow>
        (if Xs = [] then None else Some (slgoto (hd cstk) (Tm a) (FinRep [c]) # Xs, w')))
    | SReduce r \<Rightarrow> (let n = length (rrhs r) in
        if drop n Xs = [] then None
        else let R = sred (hd cstk) (rpid r) n in
          if irep_nonempty R then Some (slgoto (cstk ! n) (Nt (rlhs r)) R # drop n Xs, w)
          else None)))\<close>

definition sdlive :: \<open>('n, 't) sgconfig \<Rightarrow> bool\<close> where
  \<open>sdlive gc = (case gc of (Xs, w) \<Rightarrow> Xs \<noteq> [] \<and> slive (hd Xs))\<close>

fun sdpick :: \<open>('n, 't) sitem list list \<Rightarrow> ('n, 't) sgconfig \<Rightarrow> ('n, 't) sact list \<Rightarrow>
    (('n, 't) sact \<times> ('n, 't) sgconfig) option\<close> where
  \<open>sdpick cstk gc [] = None\<close>
| \<open>sdpick cstk gc (act # acts) =
     (case smstep cstk gc act of
        Some gc' \<Rightarrow> (if sdlive gc' then Some (act, gc') else sdpick cstk gc acts)
      | None \<Rightarrow> sdpick cstk gc acts)\<close>

text \<open>A dense configuration and its sparse counterpart: related kernels, the
  dense ones coherent, the same input.\<close>

definition sgrel :: \<open>('n, 't) is_cfg \<Rightarrow> 'n \<Rightarrow> ('n, 't) gconfig \<Rightarrow> ('n, 't) sgconfig \<Rightarrow> bool\<close> where
  \<open>sgrel G Shn gc gs \<longleftrightarrow> list_all2 (skrel G Shn) (fst gc) (fst gs) \<and>
     (\<forall>K \<in> set (fst gc). kinv G K) \<and> snd gc = snd gs\<close>

lemma smstep_rel:
  assumes c: \<open>list_all2 (screl G Shn) cstk cstks\<close> and l: \<open>length cstk = length (fst gc)\<close>
    and g: \<open>sgrel G Shn gc gs\<close> and a: \<open>sgood_act G Shn act\<close>
  shows \<open>rel_option (sgrel G Shn) (mstep_cached G cstk gc (sdec_act act)) (smstep cstks gs act)\<close>
proof -
  obtain Xs w Ks where gc: \<open>gc = (Xs, w)\<close> \<open>gs = (Ks, w)\<close> and x: \<open>list_all2 (skrel G Shn) Xs Ks\<close>
    and kv: \<open>\<forall>K \<in> set Xs. kinv G K\<close>
    using g unfolding sgrel_def by (cases gc; cases gs) auto
  have len: \<open>length Ks = length Xs\<close> using x by (simp add: list_all2_lengthD)
  have lc: \<open>length cstks = length cstk\<close> using c by (simp add: list_all2_lengthD)
  have nth: \<open>screl G Shn (cstk ! k) (cstks ! k)\<close> if \<open>k < length Xs\<close> for k
    using c that l gc by (simp add: list_all2_nthD)
  have h: \<open>screl G Shn (hd cstk) (hd cstks)\<close> if \<open>Xs \<noteq> []\<close>
  proof -
    have \<open>cstk \<noteq> []\<close> \<open>cstks \<noteq> []\<close> using that l lc gc by auto
    with nth[of 0] that show ?thesis by (simp add: hd_conv_nth)
  qed
  show ?thesis
  proof (cases act)
    case SShift
    show ?thesis
    proof (cases w)
      case Nil
      then show ?thesis by (simp add: SShift gc mstep_cached_code smstep_def)
    next
      case (Cons ac w')
      obtain a cc where ac: \<open>ac = (a, cc)\<close> by (cases ac)
      show ?thesis
      proof (cases \<open>Xs = []\<close>)
        case True
        then show ?thesis using len by (simp add: SShift gc Cons ac mstep_cached_code smstep_def)
      next
        case False
        have ks: \<open>Ks \<noteq> []\<close> using False len by auto
        from screl_lgoto[OF h[OF False] sgood_Tm[of _ a], where RA = \<open>FinRep [cc]\<close> and RB = \<open>FinRep [cc]\<close>]
        have \<open>skrel G Shn (lgoto (hd cstk) (Tm a) (FinRep [cc])) (slgoto (hd cstks) (Tm a) (FinRep [cc]))\<close>
          \<open>kinv G (lgoto (hd cstk) (Tm a) (FinRep [cc]))\<close>
          by simp_all
        with False ks x kv show ?thesis
          by (simp add: SShift gc Cons ac mstep_cached_code smstep_def sgrel_def)
      qed
    qed
  next
    case (SReduce r)
    from a obtain p where r: \<open>r = mkrec (eprods G Shn) p\<close> and p: \<open>p \<in> set (eprods G Shn)\<close>
      unfolding SReduce sgood_act_def by auto
    let ?n = \<open>length (snd p)\<close>
    have rn: \<open>length (rrhs r) = ?n\<close> and rp: \<open>rprod r = p\<close> by (simp_all add: r)
    show ?thesis
    proof (cases \<open>drop ?n Xs = []\<close>)
      case True
      then have \<open>drop ?n Ks = []\<close> using len by simp
      with True show ?thesis by (simp add: SReduce gc mstep_cached_code smstep_def rn rp Let_def)
    next
      case False
      then have n: \<open>?n < length Xs\<close> and ne: \<open>Xs \<noteq> []\<close> by auto
      have rs: \<open>irep_set (sred (hd cstks) (rpid r) ?n) = irep_set (red_set (hd cstk) p)\<close>
        unfolding r mkrec_sel by (rule screl_red[OF h[OF ne] p])
      have pn: \<open>fst p \<in> set (map fst (eprods G Shn))\<close> using p by force
      have sy: \<open>symid (map fst (eprods G Shn)) (Nt (fst p)) = Nt (rlhs r)\<close> by (simp add: r)
      from screl_lgoto[OF nth[OF n] sgood_Nt[OF pn], of \<open>red_set (hd cstk) p\<close> \<open>sred (hd cstks) (rpid r) ?n\<close>] rs sy
      have k: \<open>skrel G Shn (lgoto (cstk ! ?n) (Nt (fst p)) (red_set (hd cstk) p))
          (slgoto (cstks ! ?n) (Nt (rlhs r)) (sred (hd cstks) (rpid r) ?n))\<close>
        \<open>kinv G (lgoto (cstk ! ?n) (Nt (fst p)) (red_set (hd cstk) p))\<close>
        by simp_all
      have \<open>list_all2 (skrel G Shn) (drop ?n Xs) (drop ?n Ks)\<close> using x by (rule list_all2_dropI)
      moreover have \<open>\<forall>K \<in> set (drop ?n Xs). kinv G K\<close> using kv by (meson in_set_dropD)
      moreover have \<open>drop ?n Ks \<noteq> []\<close> using False len by simp
      ultimately show ?thesis using False k rs
        by (simp add: SReduce gc mstep_cached_code smstep_def rn rp Let_def sgrel_def)
    qed
  qed
qed

lemma sgrel_dlive: \<open>sgrel G Shn gc gs \<Longrightarrow> dlive gc = sdlive gs\<close>
proof -
  assume g: \<open>sgrel G Shn gc gs\<close>
  obtain Xs w Ks where gc: \<open>gc = (Xs, w)\<close> \<open>gs = (Ks, w)\<close> and x: \<open>list_all2 (skrel G Shn) Xs Ks\<close>
    using g unfolding sgrel_def by (cases gc; cases gs) auto
  show ?thesis
  proof (cases Xs)
    case Nil
    with x show ?thesis by (simp add: gc dlive_def sdlive_def)
  next
    case (Cons K Xs')
    with x obtain K' Ks' where \<open>Ks = K' # Ks'\<close> \<open>skrel G Shn K K'\<close> by (auto simp: list_all2_Cons1)
    with Cons show ?thesis by (simp add: gc dlive_def sdlive_def skrel_live)
  qed
qed

lemma sdpick_rel:
  assumes c: \<open>list_all2 (screl G Shn) cstk cstks\<close> and l: \<open>length cstk = length (fst gc)\<close>
    and g: \<open>sgrel G Shn gc gs\<close>
  shows \<open>\<forall>act \<in> set acts. sgood_act G Shn act \<Longrightarrow>
    rel_option (\<lambda>(a, g) (a', g'). a = sdec_act a' \<and> sgood_act G Shn a' \<and> sgrel G Shn g g')
      (dpick G cstk gc (map sdec_act acts)) (sdpick cstks gs acts)\<close>
proof (induction acts)
  case (Cons act acts)
  from Cons.prems have ga: \<open>sgood_act G Shn act\<close> and as: \<open>\<forall>act \<in> set acts. sgood_act G Shn act\<close>
    by simp_all
  note IH = Cons.IH[OF as]
  have m: \<open>rel_option (sgrel G Shn) (mstep_cached G cstk gc (sdec_act act)) (smstep cstks gs act)\<close>
    by (rule smstep_rel[OF c l g ga])
  show ?case
  proof (cases \<open>mstep_cached G cstk gc (sdec_act act)\<close>)
    case None
    with m have \<open>smstep cstks gs act = None\<close> by (cases \<open>smstep cstks gs act\<close>) simp_all
    with None IH show ?thesis by simp
  next
    case (Some g1)
    with m obtain g1' where s: \<open>smstep cstks gs act = Some g1'\<close> and r: \<open>sgrel G Shn g1 g1'\<close>
      by (cases \<open>smstep cstks gs act\<close>) simp_all
    with Some IH ga sgrel_dlive[OF r] show ?thesis by simp
  qed
qed simp

type_synonym ('m, 'ch, 'n, 't) sdst =
  \<open>('n, 't) sgconfig \<times> ('n, 't) sitem list list \<times> nat list \<times> ('m, 'ch, 't) tword \<times>
   ('m, 'ch, 'n, 't) ast list\<close>

definition sdstep_act :: \<open>('n, 't) stab \<Rightarrow> ('m, 'ch, 'n, 't) sdst \<Rightarrow>
    (('n, 't) sact \<times> ('m, 'ch, 'n, 't) sdst) option\<close> where
  \<open>sdstep_act T st = (case st of (gc, cstk, istk, v, tstk) \<Rightarrow>
     let i = (case istk of [] \<Rightarrow> s_ns T | j # _ \<Rightarrow> j);
         cells = (if i < IArray.length (s_rt T) then s_rt T !! i else []);
         CL = (case cstk of [] \<Rightarrow> [] | c # _ \<Rightarrow> c)
     in (case sdpick cstk gc (sdcands T i cells CL gc) of
        None \<Rightarrow> None
      | Some (act, gc') \<Rightarrow> Some (act, case act of
          SShift \<Rightarrow> (gc',
              sclosure T (hd (fst gc')) # cstk,
              sdnext T i (Tm (tok (hd v))) # istk,
              tl v,
              Leaf (hd v) # tstk)
        | SReduce r \<Rightarrow> (gc',
              sclosure T (hd (fst gc')) # drop (length (rrhs r)) cstk,
              sdnext T (istk ! length (rrhs r)) (Nt (rlhs r)) # drop (length (rrhs r)) istk,
              v,
              Node (fst (rprod r)) (rev (take (length (rrhs r)) tstk))
                # drop (length (rrhs r)) tstk))))\<close>

definition sdstep :: \<open>('n, 't) stab \<Rightarrow> ('m, 'ch, 'n, 't) sdst \<Rightarrow> ('m, 'ch, 'n, 't) sdst option\<close> where
  \<open>sdstep T st = map_option snd (sdstep_act T st)\<close>

partial_function (option) sdrun :: \<open>('n, 't) stab \<Rightarrow> ('m, 'ch, 'n, 't) sdst \<Rightarrow> ('m, 'ch, 'n, 't) ast option\<close>
  where
  \<open>sdrun T st =
     (case st of (gc, cstk, istk, v, tstk) \<Rightarrow>
        if sgfinal T gc then (case tstk of t # _ \<Rightarrow> Some t | [] \<Rightarrow> None)
        else Option.bind (sdstep T st) (sdrun T))\<close>

lemmas sdrun_simps [code] = sdrun.simps

definition sinit :: \<open>('n, 't) stab \<Rightarrow> ('n, 't) sitem list\<close> where
  \<open>sinit T = [(s_recs T !! s_np T, 0, FinRep [s_i0 T])]\<close>

subsection \<open>The sparse driver runs the dense one\<close>

definition sst_rel :: \<open>('n, 't) is_cfg \<Rightarrow> 'n \<Rightarrow> ('m, 'ch, 'n, 't) dst \<Rightarrow> ('m, 'ch, 'n, 't) sdst \<Rightarrow> bool\<close> where
  \<open>sst_rel G Shn st sst \<longleftrightarrow> sgrel G Shn (fst st) (fst sst) \<and>
     list_all2 (screl G Shn) (fst (snd st)) (fst (snd sst)) \<and>
     length (fst (snd st)) = length (fst (fst st)) \<and> snd (snd st) = snd (snd sst)\<close>

lemma scells_sel:
  assumes T: \<open>T = mk_stab G Shn gt sts redtab\<close>
  shows \<open>(if i < IArray.length (s_rt T) then s_rt T !! i else []) =
         scells (eprods G Shn) (if i < length redtab then redtab ! i else [])\<close>
  by (simp add: T scells_def)

lemma sdstep_act_rel:
  assumes T: \<open>T = mk_stab G Shn gt sts redtab\<close> and r: \<open>sst_rel G Shn st sst\<close>
  shows \<open>rel_option (\<lambda>(a, s) (a', s'). a = sdec_act a' \<and> sst_rel G Shn s s')
           (dstep_act G gt sts redtab st) (sdstep_act T sst)\<close>
proof -
  let ?ps = \<open>eprods G Shn\<close>
  obtain gc cstk istk v tstk gs cstks where
    st: \<open>st = (gc, cstk, istk, v, tstk)\<close> \<open>sst = (gs, cstks, istk, v, tstk)\<close> and
    g: \<open>sgrel G Shn gc gs\<close> and c: \<open>list_all2 (screl G Shn) cstk cstks\<close> and
    l: \<open>length cstk = length (fst gc)\<close>
    using r unfolding sst_rel_def by (cases st; cases sst) auto
  obtain Xs w Ks where gc: \<open>gc = (Xs, w)\<close> \<open>gs = (Ks, w)\<close> and x: \<open>list_all2 (skrel G Shn) Xs Ks\<close>
    using g unfolding sgrel_def by (cases gc; cases gs) auto
  have e: \<open>Ks = [] \<longleftrightarrow> Xs = []\<close> using x by auto
  define i where \<open>i = (case istk of [] \<Rightarrow> length sts | j # _ \<Rightarrow> j)\<close>
  define cells where \<open>cells = (if i < length redtab then redtab ! i else [])\<close>
  define CL where \<open>CL = (case cstk of [] \<Rightarrow> [] | c # _ \<Rightarrow> c)\<close>
  define CLs where \<open>CLs = (case cstks of [] \<Rightarrow> [] | c # _ \<Rightarrow> c)\<close>
  have cl: \<open>screl G Shn CL CLs\<close> using c unfolding CL_def CLs_def by (cases cstk; cases cstks) auto
  have ns: \<open>s_ns T = length sts\<close> by (simp add: T)
  have i': \<open>(case istk of [] \<Rightarrow> s_ns T | j # _ \<Rightarrow> j) = i\<close> unfolding ns i_def ..
  have i'': \<open>(case istk of [] \<Rightarrow> length sts | j # _ \<Rightarrow> j) = i\<close> unfolding i_def ..
  have cells': \<open>(if i < IArray.length (s_rt T) then s_rt T !! i else []) = scells ?ps cells\<close>
    unfolding cells_def by (rule scells_sel[OF T])
  define acts where \<open>acts = sdcands T i (scells ?ps cells) CLs gs\<close>
  have \<open>dcands G i cells CL gc = dcands G i cells (filter ine CL) gc\<close>
    using cl unfolding screl_def by (simp add: dcands_coh)
  also have \<open>\<dots> = dcands G i cells (map sdec CLs) gc\<close>
    using cl unfolding screl_def by (blast intro: dcands_xeq)
  also have \<open>\<dots> = map sdec_act acts\<close>
    unfolding acts_def gc using sdcands_dec[OF T _ e] cl unfolding screl_def by simp
  finally have da: \<open>dcands G i cells CL gc = map sdec_act acts\<close> .
  have u: \<open>dcands G (case istk of [] \<Rightarrow> length sts | j # _ \<Rightarrow> j)
      (if (case istk of [] \<Rightarrow> length sts | j # _ \<Rightarrow> j) < length redtab
       then redtab ! (case istk of [] \<Rightarrow> length sts | j # _ \<Rightarrow> j) else [])
      (case cstk of [] \<Rightarrow> [] | c # _ \<Rightarrow> c) gc = map sdec_act acts\<close>
    using da unfolding i_def cells_def CL_def .
  have us: \<open>sdcands T (case istk of [] \<Rightarrow> s_ns T | j # _ \<Rightarrow> j)
      (if (case istk of [] \<Rightarrow> s_ns T | j # _ \<Rightarrow> j) < IArray.length (s_rt T)
       then s_rt T !! (case istk of [] \<Rightarrow> s_ns T | j # _ \<Rightarrow> j) else [])
      (case cstks of [] \<Rightarrow> [] | c # _ \<Rightarrow> c) gs = acts\<close>
    unfolding acts_def CLs_def by (simp only: i' cells')
  have ga: \<open>\<forall>act \<in> set acts. sgood_act G Shn act\<close>
    unfolding acts_def by (rule sdcands_good[OF T]) (use cl in \<open>simp add: screl_def\<close>)
  have pk: \<open>rel_option (\<lambda>(a, g) (a', g'). a = sdec_act a' \<and> sgood_act G Shn a' \<and> sgrel G Shn g g')
      (dpick G cstk gc (map sdec_act acts)) (sdpick cstks gs acts)\<close>
    by (rule sdpick_rel[OF c l g ga])
  show ?thesis
  proof (cases \<open>dpick G cstk gc (map sdec_act acts)\<close>)
    case None
    with pk have \<open>sdpick cstks gs acts = None\<close> by (cases \<open>sdpick cstks gs acts\<close>) auto
    with None show ?thesis
      unfolding st dstep_act_def sdstep_act_def Let_def prod.case u us by simp
  next
    case (Some p1)
    then obtain act g1 where p1: \<open>dpick G cstk gc (map sdec_act acts) = Some (act, g1)\<close>
      by (cases p1) auto
    with pk obtain act' g1' where p1': \<open>sdpick cstks gs acts = Some (act', g1')\<close>
      and aa: \<open>act = sdec_act act'\<close> and ga': \<open>sgood_act G Shn act'\<close> and g1: \<open>sgrel G Shn g1 g1'\<close>
      by (cases \<open>sdpick cstks gs acts\<close>) auto
    from dpick_sound[OF p1] have ms: \<open>mstep_cached G cstk gc act = Some g1\<close> and lv: \<open>dlive g1\<close>
      by simp_all
    obtain Ys w1 Ks1 where g1s: \<open>g1 = (Ys, w1)\<close> \<open>g1' = (Ks1, w1)\<close>
      and y: \<open>list_all2 (skrel G Shn) Ys Ks1\<close> and yk: \<open>\<forall>K \<in> set Ys. kinv G K\<close>
      using g1 unfolding sgrel_def by (cases g1; cases g1') auto
    from lv obtain Y Ys' where Ys: \<open>Ys = Y # Ys'\<close> by (cases Ys) (auto simp: dlive_def g1s)
    with y obtain K1 Ks1' where Ks1: \<open>Ks1 = K1 # Ks1'\<close> and yk1: \<open>skrel G Shn Y K1\<close>
      by (auto simp: list_all2_Cons1)
    have hr: \<open>screl G Shn (xclosure_auto G (hd (fst g1))) (sclosure T (hd (fst g1')))\<close>
      using screl_closure[OF T yk1] yk by (simp add: g1s Ys Ks1)
    show ?thesis
    proof (cases act')
      case SShift
      then have act: \<open>act = DShift\<close> using aa by simp
      from ms[unfolded act gc] obtain a cc w' where \<open>Xs \<noteq> []\<close>
        and g1e: \<open>g1 = (lgoto (hd cstk) (Tm a) (FinRep [cc]) # Xs, w')\<close>
        by (rule mstep_shift_shape)
      then have len1: \<open>length (fst g1) = Suc (length cstk)\<close> using l gc by simp
      have nx: \<open>sdnext T j (Tm b) = dnext gt sts j (Tm b)\<close> for j b
        using sdnext_dec[OF T sgood_Tm[of _ b], where i = j] by simp
      show ?thesis
        unfolding st dstep_act_def sdstep_act_def Let_def prod.case u us
        using p1 p1' act SShift hr c len1 g1
        by (simp add: sst_rel_def nx i' i'')
    next
      case (SReduce r)
      from ga' obtain p where r: \<open>r = mkrec ?ps p\<close> and p: \<open>p \<in> set ?ps\<close>
        unfolding SReduce sgood_act_def by auto
      have rn: \<open>length (rrhs r) = length (snd p)\<close> and rp: \<open>rprod r = p\<close> by (simp_all add: r)
      have act: \<open>act = DReduce p\<close> using aa SReduce rp by simp
      from ms[unfolded act gc] obtain n: \<open>length (snd p) < length Xs\<close>
        and \<open>irep_nonempty (red_set (hd cstk) p)\<close>
        and g1e: \<open>g1 = (lgoto (cstk ! length (snd p)) (Nt (fst p)) (red_set (hd cstk) p)
                # drop (length (snd p)) Xs, w)\<close>
        by (rule mstep_reduce_shape)
      then have len1: \<open>length (fst g1) = Suc (length (drop (length (snd p)) cstk))\<close> using l gc by simp
      have pn: \<open>fst p \<in> set (map fst ?ps)\<close> using p by force
      have nx: \<open>sdnext T j (Nt (rlhs r)) = dnext gt sts j (Nt (fst p))\<close> for j
        using sdnext_dec[OF T sgood_Nt[OF pn], of j] by (simp add: r)
      have cd: \<open>list_all2 (screl G Shn) (drop (length (snd p)) cstk) (drop (length (snd p)) cstks)\<close>
        using c by (rule list_all2_dropI)
      show ?thesis
        unfolding st dstep_act_def sdstep_act_def Let_def prod.case u us
        using p1 p1' act SReduce hr cd len1 g1
        by (simp add: sst_rel_def nx rn rp i' i'')
    qed
  qed
qed

lemma sdstep_rel:
  assumes T: \<open>T = mk_stab G Shn gt sts redtab\<close> and r: \<open>sst_rel G Shn st sst\<close>
  shows \<open>rel_option (sst_rel G Shn) (dstep G gt sts redtab st) (sdstep T sst)\<close>
  using sdstep_act_rel[OF T r] unfolding dstep_eq_dstep_act sdstep_def
  by (cases \<open>dstep_act G gt sts redtab st\<close>; cases \<open>sdstep_act T sst\<close>) auto

lemma list_ex_filter_ine: \<open>(\<And>x. P x \<Longrightarrow> ine x) \<Longrightarrow> list_ex P (filter ine xs) = list_ex P xs\<close>
  by (induction xs) auto

lemma sgfinal_rel:
  fixes G :: \<open>('n, 't) is_cfg\<close>
  assumes T: \<open>T = mk_stab G Shn gt sts redtab\<close> and fr: \<open>fresh_name G Shn\<close> and g: \<open>sgrel G Shn gc gs\<close>
  shows \<open>gfinal G Shn gc = sgfinal T gs\<close>
proof -
  let ?ps = \<open>eprods G Shn\<close>
  let ?P = \<open>\<lambda>(pr :: 'n \<times> ('n, 't) rhs, m :: nat, R). fst pr = Shn \<and> m = Suc 0 \<and> irep_mem (istart_ind G) R\<close>
  let ?Q = \<open>\<lambda>(r :: ('n, 't) prec, m :: nat, R). rlhs r = s_np T \<and> m = Suc 0 \<and> irep_mem (s_i0 T) R\<close>
  obtain Xs w Ks where gc: \<open>gc = (Xs, w)\<close> \<open>gs = (Ks, w)\<close> and x: \<open>list_all2 (skrel G Shn) Xs Ks\<close>
    using g unfolding sgrel_def by (cases gc; cases gs) auto
  show ?thesis
  proof (cases Xs)
    case Nil
    with x show ?thesis by (simp add: gc gfinal_def sgfinal_def)
  next
    case (Cons K Xs')
    with x obtain K1 Ks' where Ks: \<open>Ks = K1 # Ks'\<close> and k: \<open>skrel G Shn K K1\<close>
      by (auto simp: list_all2_Cons1)
    from k have w: \<open>swf ?ps K1\<close> and xk: \<open>xeq (filter ine K) (filter ine (map sdec K1))\<close>
      unfolding skrel_def by simp_all
    have Pi: \<open>?P x \<Longrightarrow> ine x\<close> for x by (cases x) auto
    have \<open>list_ex ?P K = list_ex ?P (filter ine K)\<close> by (simp add: list_ex_filter_ine Pi)
    also have \<open>\<dots> = list_ex ?P (filter ine (map sdec K1))\<close>
      using xk unfolding xrel_def by (induction rule: list_all2_induct) (auto split: prod.split_asm)
    also have \<open>\<dots> = list_ex ?P (map sdec K1)\<close> by (simp add: list_ex_filter_ine Pi)
    also have \<open>\<dots> = list_ex ?Q K1\<close>
      using w
    proof (induction K1)
      case (Cons y ys)
      obtain r m R where y: \<open>y = (r, m, R)\<close> by (cases y)
      from Cons.prems obtain q where r: \<open>r = mkrec ?ps q\<close> and q: \<open>q \<in> set ?ps\<close> and w': \<open>swf ?ps ys\<close>
        unfolding y swf_def by auto
      have \<open>rlhs r = s_np T \<longleftrightarrow> fst q = Shn\<close> using lhs_id_start[OF fr q] by (simp add: T r)
      with Cons.IH[OF w'] show ?case by (simp add: y r T)
    qed simp
    finally show ?thesis by (simp add: gc Cons Ks gfinal_def sgfinal_def)
  qed
qed

lemma sst_rel_gfinal:
  assumes T: \<open>T = mk_stab G Shn gt sts redtab\<close> and fr: \<open>fresh_name G Shn\<close>
    and r: \<open>sst_rel G Shn st sst\<close>
  obtains gc cstk istk v tstk gs cstks where
    \<open>st = (gc, cstk, istk, v, tstk)\<close> \<open>sst = (gs, cstks, istk, v, tstk)\<close>
    \<open>gfinal G Shn gc = sgfinal T gs\<close>
  using r sgfinal_rel[OF T fr] unfolding sst_rel_def by (cases st; cases sst) auto

lemma drun_nh_imp_s:
  assumes run: \<open>drun_nh G Shn gt sts redtab st = Some t\<close>
  shows \<open>T = mk_stab G Shn gt sts redtab \<longrightarrow> fresh_name G Shn \<longrightarrow>
    (\<forall>sst. sst_rel G Shn st sst \<longrightarrow> sdrun T sst = Some t)\<close>
proof (rule drun_nh.raw_induct[OF _ run], goal_cases)
  case (1 f G Shn gt sts redtab st t)
  show ?case
  proof (intro impI allI)
    fix sst assume T: \<open>T = mk_stab G Shn gt sts redtab\<close> and fr: \<open>fresh_name G Shn\<close>
      and r: \<open>sst_rel G Shn st sst\<close>
    obtain gc cstk istk v tstk gs cstks where
      st: \<open>st = (gc, cstk, istk, v, tstk)\<close> \<open>sst = (gs, cstks, istk, v, tstk)\<close> and
      gf: \<open>gfinal G Shn gc = sgfinal T gs\<close>
      by (rule sst_rel_gfinal[OF T fr r])
    show \<open>sdrun T sst = Some t\<close>
    proof (cases \<open>gfinal G Shn gc\<close>)
      case True
      with "1"(2) gf show ?thesis unfolding st by (subst sdrun.simps) simp
    next
      case False
      with "1"(2) obtain st\<^sub>1 where sp: \<open>dstep G gt sts redtab st = Some st\<^sub>1\<close>
        and rec: \<open>f G Shn gt sts redtab st\<^sub>1 = Some t\<close>
        unfolding st by (auto simp: bind_eq_Some_conv)
      from sdstep_rel[OF T r] sp obtain sst\<^sub>1 where
        sp': \<open>sdstep T sst = Some sst\<^sub>1\<close> and r1: \<open>sst_rel G Shn st\<^sub>1 sst\<^sub>1\<close>
        by (cases \<open>sdstep T sst\<close>) auto
      from "1"(1)[OF rec] T fr r1 have \<open>sdrun T sst\<^sub>1 = Some t\<close> by blast
      with False gf sp' show ?thesis unfolding st by (subst sdrun.simps) simp
    qed
  qed
qed

lemma sdrun_imp_nh:
  assumes run: \<open>sdrun T sst = Some t\<close>
  shows \<open>T = mk_stab G Shn gt sts redtab \<longrightarrow> fresh_name G Shn \<longrightarrow>
    (\<forall>st. sst_rel G Shn st sst \<longrightarrow> drun_nh G Shn gt sts redtab st = Some t)\<close>
proof (rule sdrun.raw_induct[OF _ run], goal_cases)
  case (1 f T sst t)
  show ?case
  proof (intro impI allI)
    fix st assume T: \<open>T = mk_stab G Shn gt sts redtab\<close> and fr: \<open>fresh_name G Shn\<close>
      and r: \<open>sst_rel G Shn st sst\<close>
    obtain gc cstk istk v tstk gs cstks where
      st: \<open>st = (gc, cstk, istk, v, tstk)\<close> \<open>sst = (gs, cstks, istk, v, tstk)\<close> and
      gf: \<open>gfinal G Shn gc = sgfinal T gs\<close>
      by (rule sst_rel_gfinal[OF T fr r])
    show \<open>drun_nh G Shn gt sts redtab st = Some t\<close>
    proof (cases \<open>sgfinal T gs\<close>)
      case True
      with "1"(2) gf show ?thesis unfolding st by (subst drun_nh.simps) simp
    next
      case False
      with "1"(2) obtain sst\<^sub>1 where sp': \<open>sdstep T sst = Some sst\<^sub>1\<close>
        and rec: \<open>f T sst\<^sub>1 = Some t\<close>
        unfolding st by (auto simp: bind_eq_Some_conv)
      from sdstep_rel[OF T r] sp' obtain st\<^sub>1 where
        sp: \<open>dstep G gt sts redtab st = Some st\<^sub>1\<close> and r1: \<open>sst_rel G Shn st\<^sub>1 sst\<^sub>1\<close>
        by (cases \<open>dstep G gt sts redtab st\<close>) auto
      from "1"(1)[OF rec] T fr r1 have \<open>drun_nh G Shn gt sts redtab st\<^sub>1 = Some t\<close> by blast
      with False gf sp show ?thesis unfolding st by (subst drun_nh.simps) simp
    qed
  qed
qed

lemma drun_nh_eq_s:
  assumes T: \<open>T = mk_stab G Shn gt sts redtab\<close> and fr: \<open>fresh_name G Shn\<close>
    and r: \<open>sst_rel G Shn st sst\<close>
  shows \<open>drun_nh G Shn gt sts redtab st = sdrun T sst\<close>
proof (cases \<open>drun_nh G Shn gt sts redtab st\<close>)
  case None
  show ?thesis
  proof (rule ccontr)
    assume \<open>drun_nh G Shn gt sts redtab st \<noteq> sdrun T sst\<close>
    with None obtain t where \<open>sdrun T sst = Some t\<close> by (cases \<open>sdrun T sst\<close>) auto
    from sdrun_imp_nh[OF this, rule_format, OF T fr r] None show False by simp
  qed
next
  case (Some t)
  from drun_nh_imp_s[OF this, rule_format, OF T fr r] Some show ?thesis by simp
qed

lemma sinit_dec:
  assumes T: \<open>T = mk_stab G Shn gt sts redtab\<close> and fr: \<open>fresh_name G Shn\<close>
  shows \<open>skrel G Shn (xinit G Shn) (sinit T)\<close>
proof -
  let ?p = \<open>(Shn, [(Nt (istart G), Eq)])\<close>
  have \<open>s_recs T !! s_np T = mkrec (eprods G Shn) ?p\<close>
    by (simp add: T eprods_def nth_append)
  moreover have \<open>?p \<in> set (eprods G Shn)\<close> by (simp add: eprods_def)
  ultimately show ?thesis
    by (simp add: skrel_def sinit_def xinit_def swf_def T del: IArray.sub_def)
qed

text \<open>The parser over the sparse driver: \<^const>\<open>dparse\<close> as a run of
  \<^const>\<open>sdrun\<close> over the table bundle, the initial kernel and its closure,
  each a constant the generated code computes once.\<close>

lemma dparse_via_tables_s:
  assumes st:  \<open>pr0_states G Shn = sts\<close>
    and   gt:  \<open>pgtab G sts = gtab\<close>
    and   rt:  \<open>red_buckets G Shn (length sts) = redtab\<close>
    and   i0:  \<open>st_find sts (lr0_start G Shn) = i\<^sub>0\<close>
    and   fr:  \<open>fresh_name G Shn\<close>
    and   tb:  \<open>mk_stab G Shn gtab sts redtab = stb\<close>
    and   ki:  \<open>sinit stb = kin\<close>
    and   kc:  \<open>sclosure stb kin = kcl\<close>
  shows \<open>dparse G Shn w = sdrun stb (([kin], tcols w), [kcl], [i\<^sub>0], w, [])\<close>
proof -
  have T: \<open>stb = mk_stab G Shn gtab sts redtab\<close> using tb by simp
  have k: \<open>skrel G Shn (xinit G Shn) kin\<close> using sinit_dec[OF T fr] ki by simp
  have kv: \<open>kinv G (xinit G Shn)\<close> by (rule kinv_xinit[OF fr])
  have \<open>screl G Shn (xclosure_auto G (xinit G Shn)) kcl\<close>
    using screl_closure[OF T k kv] kc by simp
  with k kv have \<open>sst_rel G Shn (([xinit G Shn], tcols w), [xclosure_auto G (xinit G Shn)], [i\<^sub>0], w, [])
      (([kin], tcols w), [kcl], [i\<^sub>0], w, [])\<close>
    by (simp add: sst_rel_def sgrel_def)
  then show ?thesis
    unfolding dparse_via_tables_nh[OF st gt rt refl refl i0] by (rule drun_nh_eq_s[OF T fr])
qed

end
