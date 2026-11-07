theory LR_Prec
  imports LR_Restrict
begin

section \<open>Declarations\<close>

datatype fkind = FDirect | FRight | FLeft
datatype passoc = ALeft | ARight | ANon | AOpen | AList

type_synonym ('n, 't) forbid = \<open>('n, 't) alt \<times> nat \<times> fkind \<times> ('n, 't) alt\<close>

text \<open>A level holds alternatives with a strictness flag, and \<open>dlevels\<close> is a list of
  chains of levels, loosest first: two levels are ordered only if they share a chain, so a
  partial order is several chains. \<open>dforbids\<close> are the restrictions a level table cannot
  express. A forbid \<open>(p, k, FDirect, c)\<close> keeps \<open>c\<close> from being child
  \<open>k\<close> of \<open>p\<close>; \<open>FRight\<close> and \<open>FLeft\<close> keep it off the whole right or left spine of that child.\<close>

record ('n, 't) prec_decl =
  dlevels :: \<open>(passoc \<times> (('n, 't) alt \<times> bool) list) list list\<close>
  dforbids :: \<open>('n, 't) forbid list\<close>

section \<open>Spines\<close>

fun sym_null :: \<open>'n list \<Rightarrow> ('n, 't) sym \<Rightarrow> bool\<close> where
  \<open>sym_null ns (Nt x) = (x \<in> set ns)\<close>
| \<open>sym_null ns (Tm t) = False\<close>

definition nstep :: \<open>('n, 't) is_cfg \<Rightarrow> 'n list \<Rightarrow> 'n list\<close> where
  \<open>nstep G ns = remdups (map fst (filter (\<lambda>p. list_all (\<lambda>a. sym_null ns (fst a)) (snd p)) (iprods G)))\<close>

fun nfix :: \<open>('n, 't) is_cfg \<Rightarrow> nat \<Rightarrow> 'n list \<Rightarrow> 'n list\<close> where
  \<open>nfix G 0 ns = ns\<close>
| \<open>nfix G (Suc f) ns = (let ns' = nstep G ns in if ns' = ns then ns else nfix G f ns')\<close>

definition nulls :: \<open>('n, 't) is_cfg \<Rightarrow> 'n list\<close> where
  \<open>nulls G = nfix G (Suc (length (iprods G))) []\<close>

fun is_nt :: \<open>('n, 't) sym \<Rightarrow> bool\<close> where
  \<open>is_nt (Nt x) = True\<close>
| \<open>is_nt (Tm t) = False\<close>

text \<open>A top-down automaton cannot see whether a subtree is empty, so a position is on the
  spine when everything beyond it is nullable in the grammar. Stopping at closed productions
  is the special case of a terminal beyond the position.\<close>

definition rpos :: \<open>'n list \<Rightarrow> ('n, 't) rhs \<Rightarrow> nat \<Rightarrow> bool\<close> where
  \<open>rpos ns r k \<longleftrightarrow> k < length r \<and> is_nt (fst (r ! k)) \<and>
     list_all (\<lambda>a. sym_null ns (fst a)) (drop (Suc k) r)\<close>

definition lpos :: \<open>'n list \<Rightarrow> ('n, 't) rhs \<Rightarrow> nat \<Rightarrow> bool\<close> where
  \<open>lpos ns r k \<longleftrightarrow> k < length r \<and> is_nt (fst (r ! k)) \<and>
     list_all (\<lambda>a. sym_null ns (fst a)) (take k r)\<close>

definition fb :: \<open>('n, 't) forbid list \<Rightarrow> fkind \<Rightarrow> ('n, 't) alt \<Rightarrow> nat \<Rightarrow> ('n, 't) alt list\<close> where
  \<open>fb F kd p k = map (\<lambda>f. snd (snd (snd f)))
     (filter (\<lambda>f. fst f = p \<and> fst (snd f) = k \<and> fst (snd (snd f)) = kd) F)\<close>

section \<open>The tree predicate\<close>

inductive pk ::
  \<open>('n, 't) is_cfg \<Rightarrow> 'n list \<Rightarrow> ('n, 't) forbid list \<Rightarrow> ('n, 't) alt set \<Rightarrow> ('n, 't) alt set \<Rightarrow>
   ('n, 't) alt set \<Rightarrow> ('m, 'ch, 'n, 't) ptree \<Rightarrow> bool\<close>
  for G ns F where
  pk_leaf: \<open>pk G ns F D R L (PLeaf t)\<close>
| pk_node: \<open>(n, r) \<in> set (iprods G) \<Longrightarrow> (n, r) \<notin> D \<Longrightarrow> (n, r) \<notin> R \<Longrightarrow> (n, r) \<notin> L \<Longrightarrow>
    length ts = length r \<Longrightarrow>
    (\<And>k. k < length r \<Longrightarrow> fst (proot (ts ! k)) = fst (r ! k) \<and>
      irel_sat (snd (r ! k)) (snd (proot (ts ! k))) i \<and>
      pk G ns F (set (fb F FDirect (n, r) k))
        (set (fb F FRight (n, r) k) \<union> (if rpos ns r k then R else {}))
        (set (fb F FLeft (n, r) k) \<union> (if lpos ns r k then L else {})) (ts ! k)) \<Longrightarrow>
    pk G ns F D R L (PNode n i ts)\<close>

section \<open>The automaton\<close>

type_synonym ('n, 't) pstate = \<open>'n \<times> ('n, 't) alt list \<times> ('n, 't) alt list \<times> ('n, 't) alt list\<close>

definition canon :: \<open>('n, 't) is_cfg \<Rightarrow> ('n \<Rightarrow> ('n, 't) alt list) \<Rightarrow> ('n \<Rightarrow> ('n, 't) alt list) \<Rightarrow> 'n \<Rightarrow>
    ('n, 't) alt list \<Rightarrow> ('n, 't) alt list \<Rightarrow> ('n, 't) alt list \<Rightarrow> ('n, 't) pstate\<close> where
  \<open>canon G rt lt N D R L =
    (let R' = filter (\<lambda>p. p \<in> set R) (rt N);
         L' = filter (\<lambda>p. p \<in> set L) (lt N)
     in (N, filter (\<lambda>p. fst p = N \<and> (p \<in> set D \<or> p \<in> set R' \<or> p \<in> set L')) (iprods G), R', L'))\<close>

definition pok :: \<open>('n, 't) pstate \<Rightarrow> ('n, 't) alt \<Rightarrow> bool\<close> where
  \<open>pok q p \<longleftrightarrow> p \<notin> set (fst (snd q))\<close>

definition pstep :: \<open>('n, 't) is_cfg \<Rightarrow> 'n list \<Rightarrow> ('n, 't) forbid list \<Rightarrow>
    ('n \<Rightarrow> ('n, 't) alt list) \<Rightarrow> ('n \<Rightarrow> ('n, 't) alt list) \<Rightarrow>
    ('n, 't) pstate \<Rightarrow> ('n, 't) alt \<Rightarrow> nat \<Rightarrow> ('n, 't) pstate\<close> where
  \<open>pstep G ns F rt lt q p k =
    canon G rt lt (case fst (snd p ! k) of Nt x \<Rightarrow> x | Tm _ \<Rightarrow> fst q) (fb F FDirect p k)
      (fb F FRight p k @ (if rpos ns (snd p) k then fst (snd (snd q)) else []))
      (fb F FLeft p k @ (if lpos ns (snd p) k then snd (snd (snd q)) else []))\<close>

definition paut :: \<open>('n, 't) is_cfg \<Rightarrow> 'n list \<Rightarrow> ('n, 't) forbid list \<Rightarrow>
    ('n \<Rightarrow> ('n, 't) alt list) \<Rightarrow> ('n \<Rightarrow> ('n, 't) alt list) \<Rightarrow>
    ('n, 't, ('n, 't) pstate) prec_aut\<close> where
  \<open>paut G ns F rt lt = \<lparr>ok = pok, step = pstep G ns F rt lt\<rparr>\<close>

locale spined =
  fixes G :: \<open>('n, 't) is_cfg\<close> and ns :: \<open>'n list\<close> and F :: \<open>('n, 't) forbid list\<close>
    and rt lt :: \<open>'n \<Rightarrow> ('n, 't) alt list\<close>
  assumes rt_self: \<open>p \<in> set (iprods G) \<Longrightarrow> p \<in> set (rt (fst p))\<close>
    and lt_self: \<open>p \<in> set (iprods G) \<Longrightarrow> p \<in> set (lt (fst p))\<close>
    and rt_step: \<open>(n, r) \<in> set (iprods G) \<Longrightarrow> rpos ns r k \<Longrightarrow> fst (r ! k) = Nt x \<Longrightarrow>
        set (rt x) \<subseteq> set (rt n)\<close>
    and lt_step: \<open>(n, r) \<in> set (iprods G) \<Longrightarrow> lpos ns r k \<Longrightarrow> fst (r ! k) = Nt x \<Longrightarrow>
        set (lt x) \<subseteq> set (lt n)\<close>
begin

abbreviation \<open>A \<equiv> paut G ns F rt lt\<close>

lemma canon_cong:
  assumes \<open>\<And>p. p \<in> set (rt N) \<Longrightarrow> p \<in> set R1 \<longleftrightarrow> p \<in> set R2\<close>
    and \<open>\<And>p. p \<in> set (lt N) \<Longrightarrow> p \<in> set L1 \<longleftrightarrow> p \<in> set L2\<close>
  shows \<open>canon G rt lt N D R1 L1 = canon G rt lt N D R2 L2\<close>
proof -
  have \<open>filter (\<lambda>p. p \<in> set R1) (rt N) = filter (\<lambda>p. p \<in> set R2) (rt N)\<close>
    \<open>filter (\<lambda>p. p \<in> set L1) (lt N) = filter (\<lambda>p. p \<in> set L2) (lt N)\<close>
    using assms by (auto intro: filter_cong)
  then show ?thesis by (simp add: canon_def Let_def)
qed

lemma step_canon:
  assumes p: \<open>(N, r) \<in> set (iprods G)\<close> and x: \<open>fst (r ! k) = Nt x\<close>
  shows \<open>step A (canon G rt lt N D R L) (N, r) k = canon G rt lt x (fb F FDirect (N, r) k)
      (fb F FRight (N, r) k @ (if rpos ns r k then R else []))
      (fb F FLeft (N, r) k @ (if lpos ns r k then L else []))\<close>
proof -
  have *: \<open>canon G rt lt x (fb F FDirect (N, r) k)
      (fb F FRight (N, r) k @ (if rpos ns r k then filter (\<lambda>p. p \<in> set R) (rt N) else []))
      (fb F FLeft (N, r) k @ (if lpos ns r k then filter (\<lambda>p. p \<in> set L) (lt N) else [])) =
    canon G rt lt x (fb F FDirect (N, r) k)
      (fb F FRight (N, r) k @ (if rpos ns r k then R else []))
      (fb F FLeft (N, r) k @ (if lpos ns r k then L else []))\<close>
  proof (rule canon_cong)
    show \<open>p \<in> set (fb F FRight (N, r) k @ (if rpos ns r k then filter (\<lambda>p. p \<in> set R) (rt N) else [])) \<longleftrightarrow>
        p \<in> set (fb F FRight (N, r) k @ (if rpos ns r k then R else []))\<close> if \<open>p \<in> set (rt x)\<close> for p
      using that rt_step[OF p _ x] by auto
    show \<open>p \<in> set (fb F FLeft (N, r) k @ (if lpos ns r k then filter (\<lambda>p. p \<in> set L) (lt N) else [])) \<longleftrightarrow>
        p \<in> set (fb F FLeft (N, r) k @ (if lpos ns r k then L else []))\<close> if \<open>p \<in> set (lt x)\<close> for p
      using that lt_step[OF p _ x] by auto
  qed
  show ?thesis using x by (simp add: paut_def pstep_def canon_def[of G rt lt N D R L] Let_def * [symmetric])
qed

lemma ok_canon:
  assumes p: \<open>(N, r) \<in> set (iprods G)\<close>
  shows \<open>ok A (canon G rt lt N D R L) (N, r) \<longleftrightarrow>
    (N, r) \<notin> set D \<and> (N, r) \<notin> set R \<and> (N, r) \<notin> set L\<close>
  using p rt_self[OF p] lt_self[OF p] by (auto simp: paut_def pok_def canon_def Let_def)

lemma canon_of_run:
  \<open>prec_run G A q t \<Longrightarrow> q = canon G rt lt N D R L \<Longrightarrow> (\<And>n i ts. t = PNode n i ts \<Longrightarrow> n = N) \<Longrightarrow>
   pk G ns F (set D) (set R) (set L) t\<close>
proof (induction arbitrary: N D R L rule: prec_run.induct)
  case (prec_leaf q t)
  show ?case by (rule pk_leaf)
next
  case (prec_node n r q ts i)
  have n: \<open>n = N\<close> using prec_node.prems(2) by simp
  note p = prec_node.hyps(1)[unfolded n]
  have o: \<open>(N, r) \<notin> set D\<close> \<open>(N, r) \<notin> set R\<close> \<open>(N, r) \<notin> set L\<close>
    using prec_node.hyps(2) ok_canon[OF p] by (simp_all add: n prec_node.prems(1))
  show ?case unfolding n
  proof (rule pk_node[OF p o prec_node.hyps(3)])
    fix k assume k: \<open>k < length r\<close>
    note h = prec_node.IH[OF k]
    have \<open>pk G ns F (set (fb F FDirect (N, r) k))
        (set (fb F FRight (N, r) k) \<union> (if rpos ns r k then set R else {}))
        (set (fb F FLeft (N, r) k) \<union> (if lpos ns r k then set L else {})) (ts ! k)\<close>
    proof (cases \<open>ts ! k\<close>)
      case (PLeaf t)
      then show ?thesis by (simp add: pk_leaf)
    next
      case (PNode m j us)
      then have x: \<open>fst (r ! k) = Nt m\<close> using h by simp
      have \<open>pk G ns F (set (fb F FDirect (N, r) k))
          (set (fb F FRight (N, r) k @ (if rpos ns r k then R else [])))
          (set (fb F FLeft (N, r) k @ (if lpos ns r k then L else []))) (ts ! k)\<close>
      proof (rule h[THEN conjunct2, THEN conjunct2, THEN conjunct2, rule_format])
        show \<open>step A q (n, r) k = canon G rt lt m (fb F FDirect (N, r) k)
            (fb F FRight (N, r) k @ (if rpos ns r k then R else []))
            (fb F FLeft (N, r) k @ (if lpos ns r k then L else []))\<close>
          unfolding n prec_node.prems(1) by (rule step_canon[OF p x])
      qed (simp add: PNode)
      then show ?thesis by (auto elim!: back_subst[where P = \<open>\<lambda>S. pk G ns F _ S _ _\<close>]
            back_subst[where P = \<open>\<lambda>S. pk G ns F _ _ S _\<close>])
    qed
    with h show \<open>fst (proot (ts ! k)) = fst (r ! k) \<and> irel_sat (snd (r ! k)) (snd (proot (ts ! k))) i \<and>
        pk G ns F (set (fb F FDirect (N, r) k))
        (set (fb F FRight (N, r) k) \<union> (if rpos ns r k then set R else {}))
        (set (fb F FLeft (N, r) k) \<union> (if lpos ns r k then set L else {})) (ts ! k)\<close> by blast
  qed
qed

lemma run_of_pk:
  \<open>pk G ns F SD SR SL t \<Longrightarrow> SD = set D \<Longrightarrow> SR = set R \<Longrightarrow> SL = set L \<Longrightarrow>
   (\<And>n i ts. t = PNode n i ts \<Longrightarrow> n = N) \<Longrightarrow> prec_run G A (canon G rt lt N D R L) t\<close>
proof (induction arbitrary: N D R L rule: pk.induct)
  case (pk_leaf D R L t)
  show ?case by (rule prec_leaf)
next
  case (pk_node n r SD SR SL ts i)
  have n: \<open>n = N\<close> using pk_node.prems(4) by simp
  note p = pk_node.hyps(1)[unfolded n]
  have o: \<open>ok A (canon G rt lt N D R L) (N, r)\<close>
    using pk_node.hyps(2-4) ok_canon[OF p] by (simp add: n pk_node.prems)
  show ?case unfolding n
  proof (rule prec_node[OF p o pk_node.hyps(5)])
    fix k assume k: \<open>k < length r\<close>
    note h = pk_node.IH[OF k, unfolded n]
    have \<open>prec_run G A (step A (canon G rt lt N D R L) (N, r) k) (ts ! k)\<close>
    proof (cases \<open>ts ! k\<close>)
      case (PLeaf t)
      then show ?thesis by (simp add: prec_leaf)
    next
      case (PNode m j us)
      then have x: \<open>fst (r ! k) = Nt m\<close> using h by simp
      have \<open>prec_run G A (canon G rt lt m (fb F FDirect (N, r) k)
          (fb F FRight (N, r) k @ (if rpos ns r k then R else []))
          (fb F FLeft (N, r) k @ (if lpos ns r k then L else []))) (ts ! k)\<close>
        by (rule h[THEN conjunct2, THEN conjunct2, THEN conjunct2, rule_format])
          (auto simp: PNode pk_node.prems)
      with step_canon[OF p x] show ?thesis by simp
    qed
    with h show \<open>fst (proot (ts ! k)) = fst (r ! k) \<and> irel_sat (snd (r ! k)) (snd (proot (ts ! k))) i \<and>
        prec_run G A (step A (canon G rt lt N D R L) (N, r) k) (ts ! k)\<close> by blast
  qed
qed

theorem run_iff_pk:
  assumes \<open>\<And>n i ts. t = PNode n i ts \<Longrightarrow> n = N\<close>
  shows \<open>prec_run G A (canon G rt lt N D R L) t \<longleftrightarrow> pk G ns F (set D) (set R) (set L) t\<close>
proof
  assume a: \<open>prec_run G A (canon G rt lt N D R L) t\<close>
  show \<open>pk G ns F (set D) (set R) (set L) t\<close> by (rule canon_of_run[OF a refl]) (rule assms)
next
  assume a: \<open>pk G ns F (set D) (set R) (set L) t\<close>
  show \<open>prec_run G A (canon G rt lt N D R L) t\<close> by (rule run_of_pk[OF a refl refl refl]) (rule assms)
qed

end

section \<open>Spine tables\<close>

definition snext :: \<open>('n, 't) is_cfg \<Rightarrow> (('n, 't) rhs \<Rightarrow> nat \<Rightarrow> bool) \<Rightarrow> 'n \<Rightarrow> 'n list\<close> where
  \<open>snext G pos N = concat (map (\<lambda>p. if fst p = N then concat (map (\<lambda>k.
       if pos (snd p) k then (case fst (snd p ! k) of Nt x \<Rightarrow> [x] | Tm _ \<Rightarrow> []) else [])
     [0..<length (snd p)]) else []) (iprods G))\<close>

definition spn :: \<open>('n, 't) is_cfg \<Rightarrow> (('n, 't) rhs \<Rightarrow> nat \<Rightarrow> bool) \<Rightarrow> 'n \<Rightarrow> ('n, 't) alt list\<close> where
  \<open>spn G pos N = filter (\<lambda>p. fst p \<in> set (reach (snext G pos) N)) (iprods G)\<close>

definition stab :: \<open>('n, 't) is_cfg \<Rightarrow> (('n, 't) rhs \<Rightarrow> nat \<Rightarrow> bool) \<Rightarrow> ('n \<times> ('n, 't) alt list) list\<close> where
  \<open>stab G pos = map (\<lambda>N. (N, spn G pos N)) (remdups (map fst (iprods G)))\<close>

definition lk :: \<open>('a \<times> 'b list) list \<Rightarrow> 'a \<Rightarrow> 'b list\<close> where
  \<open>lk tb N = (case map_of tb N of Some x \<Rightarrow> x | None \<Rightarrow> [])\<close>

definition syms :: \<open>('n, 't) is_cfg \<Rightarrow> 'n set\<close> where
  \<open>syms G = {x. \<exists>p \<in> set (iprods G). \<exists>a \<in> set (snd p). fst a = Nt x}\<close>

lemma finite_syms: \<open>finite (syms G)\<close>
proof -
  have \<open>syms G \<subseteq> (\<Union>p \<in> set (iprods G). \<Union>a \<in> set (snd p). case fst a of Nt x \<Rightarrow> {x} | Tm _ \<Rightarrow> {})\<close>
    by (force simp: syms_def)
  moreover have \<open>finite (\<Union>p \<in> set (iprods G). \<Union>a \<in> set (snd p). case fst a of Nt x \<Rightarrow> {x} | Tm _ \<Rightarrow> {})\<close>
    by (auto split: sym.split)
  ultimately show ?thesis by (rule finite_subset)
qed

lemma in_syms: \<open>p \<in> set (iprods G) \<Longrightarrow> k < length (snd p) \<Longrightarrow> fst (snd p ! k) = Nt x \<Longrightarrow> x \<in> syms G\<close>
  unfolding syms_def using nth_mem by fastforce

lemma snext_syms: \<open>set (snext G pos N) \<subseteq> syms G\<close>
  by (force simp: snext_def in_syms split: sym.splits if_splits)

lemma snext_fin: \<open>finite ((steps (snext G pos))\<^sup>* `` {N})\<close>
  by (rule reach_within(2)[of \<open>insert N (syms G)\<close>]) (auto simp: finite_syms dest: snext_syms[of G pos, THEN subsetD])

lemma snext_step:
  assumes \<open>(n, r) \<in> set (iprods G)\<close> \<open>pos r k\<close> \<open>k < length r\<close> \<open>fst (r ! k) = Nt x\<close>
  shows \<open>x \<in> set (snext G pos n)\<close>
proof -
  have \<open>x \<in> set (concat (map (\<lambda>k. if pos r k then (case fst (r ! k) of Nt x \<Rightarrow> [x] | Tm _ \<Rightarrow> []) else [])
      [0..<length r]))\<close>
    using assms(2-4) by (auto intro!: bexI[of _ k])
  with assms(1) show ?thesis by (auto simp: snext_def intro!: bexI[of _ \<open>(n, r)\<close>])
qed

lemma reach_mono:
  assumes fin: \<open>finite ((steps f)\<^sup>* `` {n})\<close> \<open>finite ((steps f)\<^sup>* `` {x})\<close>
    and x: \<open>x \<in> set (reach f n)\<close>
  shows \<open>set (reach f x) \<subseteq> set (reach f n)\<close>
proof
  fix y assume \<open>y \<in> set (reach f x)\<close>
  with reach_spec(3)[OF fin(2)] have \<open>(x, y) \<in> (steps f)\<^sup>*\<close> by blast
  then show \<open>y \<in> set (reach f n)\<close>
  proof (induction rule: rtrancl_induct)
    case base
    from x show ?case .
  next
    case (step y z)
    with reach_spec(2)[OF fin(1)] show ?case by (auto simp: steps_def)
  qed
qed

lemma spn_self: \<open>p \<in> set (iprods G) \<Longrightarrow> p \<in> set (spn G pos (fst p))\<close>
  using reach_spec(1)[OF snext_fin] by (auto simp: spn_def)

lemma spn_step:
  assumes \<open>(n, r) \<in> set (iprods G)\<close> \<open>pos r k\<close> \<open>k < length r\<close> \<open>fst (r ! k) = Nt x\<close>
  shows \<open>set (spn G pos x) \<subseteq> set (spn G pos n)\<close>
proof -
  have \<open>x \<in> set (reach (snext G pos) n)\<close>
    using reach_spec(2)[OF snext_fin reach_spec(1)[OF snext_fin] snext_step[where pos = pos, OF assms]] .
  from reach_mono[OF snext_fin snext_fin this] show ?thesis by (auto simp: spn_def)
qed

lemma lk_map: \<open>lk (map (\<lambda>N. (N, f N)) xs) N = (if N \<in> set xs then f N else [])\<close>
  by (induction xs) (auto simp: lk_def)

lemma lk_stab: \<open>lk (stab G pos) N = (if N \<in> set (map fst (iprods G)) then spn G pos N else [])\<close>
  unfolding stab_def lk_map by simp

lemma lk_shape: \<open>\<exists>g. lk (stab G pos) N = filter g (iprods G)\<close>
  unfolding lk_stab spn_def by (cases \<open>N \<in> set (map fst (iprods G))\<close>)
    (auto intro: exI[of _ \<open>\<lambda>_. False\<close>])

lemma lk_self: \<open>p \<in> set (iprods G) \<Longrightarrow> p \<in> set (lk (stab G pos) (fst p))\<close>
proof -
  assume p: \<open>p \<in> set (iprods G)\<close>
  then have \<open>fst p \<in> set (map fst (iprods G))\<close> by simp
  with spn_self[OF p] show ?thesis unfolding lk_stab by simp
qed

lemma lk_step:
  assumes \<open>(n, r) \<in> set (iprods G)\<close> \<open>pos r k\<close> \<open>k < length r\<close> \<open>fst (r ! k) = Nt x\<close>
  shows \<open>set (lk (stab G pos) x) \<subseteq> set (lk (stab G pos) n)\<close>
proof -
  have \<open>n \<in> set (map fst (iprods G))\<close> using assms(1) by force
  then show ?thesis unfolding lk_stab using spn_step[where pos = pos, OF assms] by auto
qed

section \<open>Levels to forbids\<close>

definition pick0 :: \<open>('n, 't) rhs \<Rightarrow> nat \<Rightarrow> bool\<close> where \<open>pick0 r k \<longleftrightarrow> k = 0\<close>
definition pickl :: \<open>('n, 't) rhs \<Rightarrow> nat \<Rightarrow> bool\<close> where \<open>pickl r k \<longleftrightarrow> Suc k = length r\<close>

definition opens :: \<open>('n, 't) is_cfg \<Rightarrow> (('n, 't) rhs \<Rightarrow> nat \<Rightarrow> bool) \<Rightarrow> ('n, 't) sym \<Rightarrow> 'n \<Rightarrow> bool\<close> where
  \<open>opens G pos X T = (case X of Nt x \<Rightarrow> T \<in> set (reach (snext G pos) x) | Tm _ \<Rightarrow> False)\<close>

definition lopen :: \<open>('n, 't) is_cfg \<Rightarrow> ('n, 't) alt \<Rightarrow> 'n \<Rightarrow> bool\<close> where
  \<open>lopen G c T \<longleftrightarrow> snd c \<noteq> [] \<and> opens G pick0 (fst (hd (snd c))) T\<close>

definition ropen :: \<open>('n, 't) is_cfg \<Rightarrow> ('n, 't) alt \<Rightarrow> 'n \<Rightarrow> bool\<close> where
  \<open>ropen G c T \<longleftrightarrow> snd c \<noteq> [] \<and> opens G pickl (fst (last (snd c))) T\<close>

type_synonym ('n, 't) ltab = \<open>(('n, 't) alt \<times> nat \<times> passoc \<times> bool) list\<close>

definition lvl_tab :: \<open>(passoc \<times> (('n, 't) alt \<times> bool) list) list \<Rightarrow> ('n, 't) ltab\<close> where
  \<open>lvl_tab lvs = concat (map (\<lambda>(i, a, cs). map (\<lambda>(c, s). (c, i, a, s)) cs) (List.enumerate 0 lvs))\<close>

definition lside :: \<open>('n, 't) is_cfg \<Rightarrow> ('n, 't) ltab \<Rightarrow> ('n, 't) alt \<Rightarrow> nat \<Rightarrow> passoc \<Rightarrow> 'n \<Rightarrow> ('n, 't) forbid list\<close> where
  \<open>lside G tb p lp ap X = (if ap = AOpen then [] else concat (map (\<lambda>c.
     case map_of tb c of None \<Rightarrow> []
     | Some (lc, ac, _) \<Rightarrow>
        if ap = AList \<and> ac = AList \<and> fst p = X then [] else
        if lc < lp \<or> (lc = lp \<and> ap \<noteq> ALeft) then
          (if lopen G c X then [(p, 0, FDirect, c)] else []) @
          (if ropen G c X then [(p, 0, FRight, c)] else [])
        else []) (filter (\<lambda>c. fst c = X) (iprods G))))\<close>

definition rside :: \<open>('n, 't) is_cfg \<Rightarrow> ('n, 't) ltab \<Rightarrow> ('n, 't) alt \<Rightarrow> nat \<Rightarrow> passoc \<Rightarrow> 'n \<Rightarrow> ('n, 't) forbid list\<close> where
  \<open>rside G tb p lp ap X = concat (map (\<lambda>c.
     case map_of tb c of None \<Rightarrow> []
     | Some (lc, ac, sc) \<Rightarrow>
        if ap = AList \<and> ac = AList \<and> fst p = X then [] else
        if (lc < lp \<or> (lc = lp \<and> ap \<noteq> ARight)) \<and> (lopen G c X \<or> sc)
        then [(p, length (snd p) - 1, FDirect, c)] else []) (filter (\<lambda>c. fst c = X) (iprods G)))\<close>

definition level_forbids :: \<open>('n, 't) is_cfg \<Rightarrow> (passoc \<times> (('n, 't) alt \<times> bool) list) list \<Rightarrow> ('n, 't) forbid list\<close> where
  \<open>level_forbids G lvs = (let tb = lvl_tab lvs in concat (map (\<lambda>(p, lp, ap, _).
     if length (snd p) \<le> 1 then [] else
       (case fst (hd (snd p)) of Nt X \<Rightarrow> lside G tb p lp ap X | Tm _ \<Rightarrow> []) @
       (case fst (last (snd p)) of Nt X \<Rightarrow> rside G tb p lp ap X | Tm _ \<Rightarrow> [])) tb))\<close>

definition forbids :: \<open>('n, 't) is_cfg \<Rightarrow> ('n, 't) prec_decl \<Rightarrow> ('n, 't) forbid list\<close> where
  \<open>forbids G d = dforbids d @ concat (map (level_forbids G) (dlevels d))\<close>

section \<open>Top level\<close>

definition prec_ok :: \<open>('n, 't) is_cfg \<Rightarrow> ('n, 't) prec_decl \<Rightarrow> ('m, 'ch, 'n, 't) ptree \<Rightarrow> bool\<close> where
  \<open>prec_ok G d t \<longleftrightarrow> pk G (nulls G) (forbids G d) {} {} {} t\<close>

definition compile :: \<open>('n, 't) is_cfg \<Rightarrow> ('n, 't) prec_decl \<Rightarrow> ('n, 't, ('n, 't) pstate) prec_aut\<close> where
  \<open>compile G d = (let ns = nulls G; rb = stab G (rpos ns); lb = stab G (lpos ns)
     in paut G ns (forbids G d) (lk rb) (lk lb))\<close>

definition pq0 :: \<open>('n, 't) is_cfg \<Rightarrow> ('n, 't) pstate\<close> where
  \<open>pq0 G = (let ns = nulls G; rb = stab G (rpos ns); lb = stab G (lpos ns)
     in canon G (lk rb) (lk lb) (istart G) [] [] [])\<close>

definition restrict :: \<open>(string, 't) is_cfg \<Rightarrow> (string, 't) prec_decl \<Rightarrow> (string, 't) is_cfg\<close> where
  \<open>restrict G d = (let ns = nulls G; rb = stab G (rpos ns); lb = stab G (lpos ns)
     in restrict_gen G (paut G ns (forbids G d) (lk rb) (lk lb)) fst
          (canon G (lk rb) (lk lb) (istart G) [] [] []))\<close>

lemma restrict_alt: \<open>restrict G d = restrict_gen G (compile G d) fst (pq0 G)\<close>
  by (simp add: restrict_def compile_def pq0_def Let_def)

interpretation prec_sp: spined G ns F \<open>lk (stab G (rpos ns))\<close> \<open>lk (stab G (lpos ns))\<close> for G ns F
proof
  show \<open>p \<in> set (lk (stab G (rpos ns)) (fst p))\<close> if \<open>p \<in> set (iprods G)\<close> for p
    using lk_self[OF that] .
  show \<open>p \<in> set (lk (stab G (lpos ns)) (fst p))\<close> if \<open>p \<in> set (iprods G)\<close> for p
    using lk_self[OF that] .
  show \<open>set (lk (stab G (rpos ns)) x) \<subseteq> set (lk (stab G (rpos ns)) n)\<close>
    if \<open>(n, r) \<in> set (iprods G)\<close> \<open>rpos ns r k\<close> \<open>fst (r ! k) = Nt x\<close> for n r k x
    by (rule lk_step[where pos = \<open>rpos ns\<close>, OF that(1,2) _ that(3)]) (use that(2) in \<open>simp add: rpos_def\<close>)
  show \<open>set (lk (stab G (lpos ns)) x) \<subseteq> set (lk (stab G (lpos ns)) n)\<close>
    if \<open>(n, r) \<in> set (iprods G)\<close> \<open>lpos ns r k\<close> \<open>fst (r ! k) = Nt x\<close> for n r k x
    by (rule lk_step[where pos = \<open>lpos ns\<close>, OF that(1,2) _ that(3)]) (use that(2) in \<open>simp add: lpos_def\<close>)
qed

theorem accepts_iff_prec_ok:
  assumes \<open>\<And>n i ts. t = PNode n i ts \<Longrightarrow> n = istart G\<close>
  shows \<open>prec_run G (compile G d) (pq0 G) t \<longleftrightarrow> prec_ok G d t\<close>
  using prec_sp.run_iff_pk[where ns = \<open>nulls G\<close> and F = \<open>forbids G d\<close> and D = \<open>[]\<close> and R = \<open>[]\<close>
      and L = \<open>[]\<close>, OF assms]
  by (simp add: compile_def pq0_def prec_ok_def Let_def)

section \<open>Finitely many states\<close>

definition subs :: \<open>'a list \<Rightarrow> 'a list set\<close> where
  \<open>subs P = (\<lambda>S. filter (\<lambda>p. p \<in> S) P) ` Pow (set P)\<close>

lemma finite_subs: \<open>finite (subs P)\<close>
  by (simp add: subs_def)

lemma filter_subs: \<open>filter g P \<in> subs P\<close>
proof -
  have \<open>filter g P = filter (\<lambda>p. p \<in> {p \<in> set P. g p}) P\<close> by (rule filter_cong) auto
  then show ?thesis unfolding subs_def by blast
qed

definition pspace :: \<open>('n, 't) is_cfg \<Rightarrow> ('n, 't) pstate set\<close> where
  \<open>pspace G = insert (istart G) (syms G) \<times> subs (iprods G) \<times> subs (iprods G) \<times> subs (iprods G)\<close>

lemma finite_pspace: \<open>finite (pspace G)\<close>
  by (simp add: pspace_def finite_syms finite_subs)

lemma canon_space:
  assumes \<open>N \<in> insert (istart G) (syms G)\<close>
  shows \<open>canon G (lk (stab G p1)) (lk (stab G p2)) N D R L \<in> pspace G\<close>
proof -
  obtain g1 g2 where g: \<open>lk (stab G p1) N = filter g1 (iprods G)\<close> \<open>lk (stab G p2) N = filter g2 (iprods G)\<close>
    using lk_shape by metis
  show ?thesis using assms
    by (simp add: canon_def Let_def pspace_def g filter_subs)
qed

lemma mem_concat_map: \<open>y \<in> set (concat (map f xs)) \<Longrightarrow> \<exists>x\<in>set xs. y \<in> set (f x)\<close>
  by auto

lemma rsucc_mem:
  assumes \<open>z \<in> set (rsucc G A nt q)\<close>
  obtains l k x where \<open>l < length (iprods G)\<close> \<open>k < length (snd (iprods G ! l))\<close>
    \<open>fst (snd (iprods G ! l) ! k) = Nt x\<close> \<open>z = step A q (iprods G ! l) k\<close>
proof -
  obtain l where l: \<open>l \<in> set (ralts G A nt q)\<close> and
    z: \<open>z \<in> set (concat (map (\<lambda>k. case fst (snd (iprods G ! l) ! k) of
        Nt _ \<Rightarrow> [step A q (iprods G ! l) k] | Tm _ \<Rightarrow> []) [0..<length (snd (iprods G ! l))]))\<close>
    using mem_concat_map[OF assms[unfolded rsucc_def]] by blast
  obtain k where k0: \<open>k \<in> set [0..<length (snd (iprods G ! l))]\<close> and
    y: \<open>z \<in> set (case fst (snd (iprods G ! l) ! k) of
        Nt _ \<Rightarrow> [step A q (iprods G ! l) k] | Tm _ \<Rightarrow> [])\<close>
    using mem_concat_map[OF z] by blast
  have k: \<open>k < length (snd (iprods G ! l))\<close> using k0 by simp
  show ?thesis
  proof (cases \<open>fst (snd (iprods G ! l) ! k)\<close>)
    case (Nt x)
    with l k y that[of l k x] show ?thesis by (simp add: set_ralts)
  next
    case (Tm t)
    with y show ?thesis by simp
  qed
qed

lemma rsucc_space:
  \<open>set (rsucc G (paut G ns F (lk (stab G p1)) (lk (stab G p2))) fst q) \<subseteq> pspace G\<close>
proof
  fix z assume \<open>z \<in> set (rsucc G (paut G ns F (lk (stab G p1)) (lk (stab G p2))) fst q)\<close>
  then obtain l k x where l: \<open>l < length (iprods G)\<close> \<open>k < length (snd (iprods G ! l))\<close>
    \<open>fst (snd (iprods G ! l) ! k) = Nt x\<close>
    \<open>z = step (paut G ns F (lk (stab G p1)) (lk (stab G p2))) q (iprods G ! l) k\<close>
    by (rule rsucc_mem)
  have \<open>x \<in> insert (istart G) (syms G)\<close> using in_syms[OF nth_mem[OF l(1)] l(2,3)] by simp
  from canon_space[OF this] l show \<open>z \<in> pspace G\<close>
    by (simp add: paut_def pstep_def)
qed

theorem restrict_correct:
  assumes \<open>no_self_unit G\<close>
  shows \<open>\<exists>Q (cls :: _ \<Rightarrow> string). restrict_ok G (compile G d) (pq0 G) Q cls (restrict G d) orig_name\<close>
  unfolding restrict_alt
proof (rule restrict_gen_correct[OF _ _ assms])
  have q: \<open>pq0 G \<in> pspace G\<close> unfolding pq0_def Let_def by (rule canon_space) simp
  show \<open>finite ((steps (rsucc G (compile G d) fst))\<^sup>* `` {pq0 G})\<close>
    by (rule reach_within(2)[OF finite_pspace q])
      (simp add: compile_def Let_def rsucc_space)
  show \<open>fst (pq0 G) = istart G\<close> by (simp add: pq0_def canon_def Let_def)
qed (simp add: compile_def paut_def pstep_def canon_def Let_def)

end
