theory LR_Restrict
  imports TIGER_Grammar.Grammar_Base "HOL-Library.While_Combinator"
begin

type_synonym ('n, 't) alt = \<open>'n \<times> ('n, 't) rhs\<close>

record ('n, 't, 'q) prec_aut =
  ok   :: \<open>'q \<Rightarrow> ('n, 't) alt \<Rightarrow> bool\<close>
  step :: \<open>'q \<Rightarrow> ('n, 't) alt \<Rightarrow> nat \<Rightarrow> 'q\<close>

inductive prec_run ::
  \<open>('n, 't) is_cfg \<Rightarrow> ('n, 't, 'q) prec_aut \<Rightarrow> 'q \<Rightarrow> ('m, 'ch, 'n, 't) ptree \<Rightarrow> bool\<close>
  for G A where
  prec_leaf: \<open>prec_run G A q (PLeaf t)\<close>
| prec_node: \<open>(n, r) \<in> set (iprods G) \<Longrightarrow> ok A q (n, r) \<Longrightarrow>
    length ts = length r \<Longrightarrow>
    (\<And>k. k < length r \<Longrightarrow> fst (proot (ts ! k)) = fst (r ! k) \<and>
      irel_sat (snd (r ! k)) (snd (proot (ts ! k))) i \<and>
      prec_run G A (step A q (n, r) k) (ts ! k)) \<Longrightarrow>
    prec_run G A q (PNode n i ts)\<close>

fun usym :: \<open>('n' \<Rightarrow> 'n) \<Rightarrow> ('n', 't) sym \<Rightarrow> ('n, 't) sym\<close> where
  \<open>usym orig (Nt n) = Nt (orig n)\<close>
| \<open>usym orig (Tm t) = Tm t\<close>

definition urhs :: \<open>('n' \<Rightarrow> 'n) \<Rightarrow> ('n', 't) rhs \<Rightarrow> ('n, 't) rhs\<close> where
  \<open>urhs orig = map (\<lambda>(X, r). (usym orig X, r))\<close>

definition unit_alt :: \<open>('n' \<Rightarrow> 'n) \<Rightarrow> ('n', 't) alt \<Rightarrow> 'n' \<Rightarrow> bool\<close> where
  \<open>unit_alt orig p m \<longleftrightarrow> snd p = [(Nt m, Eq)] \<and> orig m = orig (fst p)\<close>

definition units :: \<open>('n', 't) is_cfg \<Rightarrow> ('n' \<Rightarrow> 'n) \<Rightarrow> 'n' \<Rightarrow> 'n' \<Rightarrow> bool\<close> where
  \<open>units G' orig n m \<longleftrightarrow> (\<exists>r. (n, r) \<in> set (iprods G') \<and> unit_alt orig (n, r) m)\<close>

abbreviation units_star where \<open>units_star G' orig \<equiv> (units G' orig)\<^sup>*\<^sup>*\<close>

fun plain :: \<open>('n' \<Rightarrow> 'n) \<Rightarrow> ('m, 'ch, 'n', 't) ptree \<Rightarrow> ('m, 'ch, 'n, 't) ptree\<close> where
  \<open>plain orig (PLeaf t) = PLeaf t\<close>
| \<open>plain orig (PNode n i [PNode m j us]) =
     (if orig m = orig n then plain orig (PNode m j us)
      else PNode (orig n) i [plain orig (PNode m j us)])\<close>
| \<open>plain orig (PNode n i ts) = PNode (orig n) i (map (plain orig) ts)\<close>

fun plain_ast :: \<open>('n' \<Rightarrow> 'n) \<Rightarrow> ('m, 'ch, 'n', 't) ast \<Rightarrow> ('m, 'ch, 'n, 't) ast\<close> where
  \<open>plain_ast orig (Leaf t) = Leaf t\<close>
| \<open>plain_ast orig (Node n [Node m us]) =
     (if orig m = orig n then plain_ast orig (Node m us)
      else Node (orig n) [plain_ast orig (Node m us)])\<close>
| \<open>plain_ast orig (Node n ts) = Node (orig n) (map (plain_ast orig) ts)\<close>

lemma pyield_plain[simp]: \<open>pyield (plain orig t) = pyield t\<close>
  by (induction orig t rule: plain.induct) (auto intro!: arg_cong[of _ _ concat])

lemma erase_plain: \<open>erase (plain orig t) = plain_ast orig (erase t)\<close>
  by (induction orig t rule: plain.induct) auto

lemma plain_node:
  assumes \<open>\<And>m j us. ts = [PNode m j us] \<Longrightarrow> orig m \<noteq> orig n\<close>
  shows \<open>plain orig (PNode n i ts) = PNode (orig n) i (map (plain orig) ts)\<close>
  using assms by (cases \<open>(orig, PNode n i ts)\<close> rule: plain.cases) auto

definition no_self_unit :: \<open>('n, 't) is_cfg \<Rightarrow> bool\<close> where
  \<open>no_self_unit G \<longleftrightarrow> (\<forall>n r. (n, [(Nt n, r)]) \<notin> set (iprods G))\<close>

lemma prec_run_wf: \<open>prec_run G A q t \<Longrightarrow> wf_ptree G t\<close>
proof (induction rule: prec_run.induct)
  case (prec_leaf t)
  show ?case by (rule wf_leaf)
next
  case (prec_node n r q ts i)
  show ?case
    by (rule wf_node[OF prec_node.hyps(1)]) (use prec_node.hyps(3) prec_node.IH in \<open>auto simp: list_all2_conv_all_nth\<close>)
qed

locale restrict_ok =
  fixes G :: \<open>('n, 't) is_cfg\<close> and A :: \<open>('n, 't, 'q) prec_aut\<close> and q0 :: 'q
    and Q :: \<open>'q set\<close> and cls :: \<open>'q \<Rightarrow> 'n'\<close>
    and G' :: \<open>('n', 't) is_cfg\<close> and orig :: \<open>'n' \<Rightarrow> 'n\<close>
  assumes start: \<open>q0 \<in> Q\<close> \<open>cls q0 = istart G'\<close> \<open>orig (istart G') = istart G\<close>
      \<open>istart_ind G' = istart_ind G\<close>
    and no_self: \<open>no_self_unit G\<close>
    and closed: \<open>q \<in> Q \<Longrightarrow> (n, r) \<in> set (iprods G) \<Longrightarrow> n = orig (cls q) \<Longrightarrow> ok A q (n, r) \<Longrightarrow>
        k < length r \<Longrightarrow> fst (r ! k) = Nt x \<Longrightarrow>
        step A q (n, r) k \<in> Q \<and> orig (cls (step A q (n, r) k)) = x\<close>
    and sound: \<open>q \<in> Q \<Longrightarrow> units_star G' orig (cls q) m \<Longrightarrow> (m, r') \<in> set (iprods G') \<Longrightarrow>
        \<not> (\<exists>c. unit_alt orig (m, r') c) \<Longrightarrow>
        (orig m, urhs orig r') \<in> set (iprods G) \<and> ok A q (orig m, urhs orig r') \<and>
        (\<forall>k c. k < length r' \<longrightarrow> fst (r' ! k) = Nt c \<longrightarrow>
           c = cls (step A q (orig m, urhs orig r') k))\<close>
    and complete: \<open>q \<in> Q \<Longrightarrow> (orig (cls q), r) \<in> set (iprods G) \<Longrightarrow> ok A q (orig (cls q), r) \<Longrightarrow>
        \<exists>m r'. units_star G' orig (cls q) m \<and> (m, r') \<in> set (iprods G') \<and> orig m = orig (cls q) \<and>
          urhs orig r' = r \<and> (\<forall>k c. k < length r' \<longrightarrow> fst (r' ! k) = Nt c \<longrightarrow>
             c = cls (step A q (orig (cls q), r) k))\<close>
begin

lemma units_star_orig: \<open>(units G' orig)\<^sup>*\<^sup>* n m \<Longrightarrow> orig m = orig n\<close>
  by (induction rule: rtranclp_induct) (auto simp: units_def unit_alt_def)

lemma units_wrap:
  assumes \<open>(units G' orig)\<^sup>*\<^sup>* n m\<close>
  shows \<open>wf_ptree G' s \<Longrightarrow> proot s = (Nt m, i) \<Longrightarrow>
    \<exists>t'. wf_ptree G' t' \<and> proot t' = (Nt n, i) \<and> plain orig t' = plain orig s\<close>
  using assms
proof (induction rule: converse_rtranclp_induct)
  case base
  then show ?case by blast
next
  case (step n n\<^sub>2)
  then obtain t' where t': \<open>wf_ptree G' t'\<close> \<open>proot t' = (Nt n\<^sub>2, i)\<close> \<open>plain orig t' = plain orig s\<close>
    by blast
  from step.hyps(1) obtain r where r: \<open>(n, r) \<in> set (iprods G')\<close> \<open>r = [(Nt n\<^sub>2, Eq)]\<close>
    \<open>orig n\<^sub>2 = orig n\<close> by (auto simp: units_def unit_alt_def)
  from t'(2) obtain us where us: \<open>t' = PNode n\<^sub>2 i us\<close> by (cases t') auto
  have \<open>wf_ptree G' (PNode n i [t'])\<close>
    using wf_node[OF r(1), of i \<open>[t']\<close>] r(2) t' by simp
  with us r(3) t'(3) show ?case
    by (intro exI[of _ \<open>PNode n i [t']\<close>]) simp
qed

lemma urhs_nth:
  \<open>k < length r' \<Longrightarrow> urhs orig r' ! k = (usym orig (fst (r' ! k)), snd (r' ! k))\<close>
  by (auto simp: urhs_def case_prod_beta)

lemma length_urhs[simp]: \<open>length (urhs orig r') = length r'\<close>
  by (simp add: urhs_def)

lemma usym_Nt: \<open>usym orig X = Nt x \<Longrightarrow> \<exists>c. X = Nt c \<and> orig c = x\<close>
  by (cases X) auto

lemma usym_Tm: \<open>usym orig X = Tm t \<Longrightarrow> X = Tm t\<close>
  by (cases X) auto

theorem restrict_sound:
  fixes t' :: \<open>('m, 'ch, 'n', 't) ptree\<close>
  assumes \<open>wf_ptree G' t'\<close>
  shows \<open>\<And>n' q. fst (proot t') = Nt n' \<Longrightarrow> q \<in> Q \<Longrightarrow> units_star G' orig (cls q) n' \<Longrightarrow>
    prec_run G A q (plain orig t') \<and>
    proot (plain orig t') = (Nt (orig n'), snd (proot t'))\<close>
  using assms
proof (induction rule: wf_ptree.induct)
  case (wf_leaf t)
  then show ?case by simp
next
  case (wf_node a rhs i pts)
  from wf_node.prems(1) have n: \<open>n' = a\<close> by simp
  note q = \<open>q \<in> Q\<close>
  have ustar: \<open>units_star G' orig (cls q) a\<close> using wf_node.prems(3) n by simp
  have len: \<open>length pts = length rhs\<close> using wf_node.IH by (simp add: list_all2_lengthD)
  have ih: \<open>fst (proot (pts ! k)) = fst (rhs ! k) \<and>
      irel_sat (snd (rhs ! k)) (snd (proot (pts ! k))) i \<and> wf_ptree G' (pts ! k) \<and>
      (\<forall>x xa. fst (proot (pts ! k)) = Nt x \<longrightarrow> xa \<in> Q \<longrightarrow> units_star G' orig (cls xa) x \<longrightarrow>
        prec_run G A xa (plain orig (pts ! k)) \<and>
        proot (plain orig (pts ! k)) = (Nt (orig x), snd (proot (pts ! k))))\<close>
    if \<open>k < length rhs\<close> for k
    using list_all2_nthD[OF wf_node.IH that] by simp
  show ?case
  proof (cases \<open>\<exists>c. unit_alt orig (a, rhs) c\<close>)
    case True
    then obtain c where c: \<open>rhs = [(Nt c, Eq)]\<close> \<open>orig c = orig a\<close>
      by (auto simp: unit_alt_def)
    with len obtain p where p: \<open>pts = [p]\<close> by (cases pts) auto
    from ih[of 0] c p have 1: \<open>fst (proot p) = Nt c\<close> \<open>snd (proot p) = i\<close> by auto
    then obtain us where u: \<open>p = PNode c i us\<close> by (cases p) auto
    have ustar': \<open>units_star G' orig (cls q) c\<close>
      using ustar wf_node.hyps c by (auto simp: units_def unit_alt_def intro: rtranclp.rtrancl_into_rtrancl)
    from ih[of 0] c p have \<open>prec_run G A q (plain orig p)\<close>
      \<open>proot (plain orig p) = (Nt (orig c), i)\<close> using q ustar' 1 by auto
    with c p u n show ?thesis by simp
  next
    case False
    from sound[OF q ustar wf_node.hyps False]
    have s: \<open>(orig a, urhs orig rhs) \<in> set (iprods G)\<close> \<open>ok A q (orig a, urhs orig rhs)\<close>
      \<open>\<And>k c. k < length rhs \<Longrightarrow> fst (rhs ! k) = Nt c \<Longrightarrow>
         c = cls (step A q (orig a, urhs orig rhs) k)\<close> by auto
    have pn: \<open>plain orig (PNode a i pts) = PNode (orig a) i (map (plain orig) pts)\<close>
    proof (rule plain_node, rule notI)
      fix m j us assume \<open>pts = [PNode m j us]\<close> \<open>orig m = orig a\<close>
      moreover from this(1) len obtain r\<^sub>1 where \<open>rhs = [r\<^sub>1]\<close>
        by (cases rhs) auto
      moreover from calculation ih[of 0] have \<open>fst r\<^sub>1 = Nt m\<close> by simp
      ultimately have \<open>(orig a, [(Nt (orig a), snd r\<^sub>1)]) \<in> set (iprods G)\<close>
        using s(1) by (cases r\<^sub>1) (simp add: urhs_def)
      with no_self show False by (auto simp: no_self_unit_def)
    qed
    have \<open>prec_run G A q (PNode (orig a) i (map (plain orig) pts))\<close>
    proof (rule prec_node[OF s(1,2)])
      show \<open>length (map (plain orig) pts) = length (urhs orig rhs)\<close> using len by simp
    next
      fix k assume k: \<open>k < length (urhs orig rhs)\<close>
      then have k': \<open>k < length rhs\<close> by simp
      note ihk = ih[OF k']
      have un: \<open>urhs orig rhs ! k = (usym orig (fst (rhs ! k)), snd (rhs ! k))\<close>
        using urhs_nth[OF k'] .
      show \<open>fst (proot (map (plain orig) pts ! k)) = fst (urhs orig rhs ! k) \<and>
        irel_sat (snd (urhs orig rhs ! k)) (snd (proot (map (plain orig) pts ! k))) i \<and>
        prec_run G A (step A q (orig a, urhs orig rhs) k) (map (plain orig) pts ! k)\<close>
      proof (cases \<open>fst (rhs ! k)\<close>)
        case (Nt c)
        have rx: \<open>fst (urhs orig rhs ! k) = Nt (orig c)\<close> using un Nt by simp
        have orig_a: \<open>orig a = orig (cls q)\<close> using units_star_orig[OF ustar] .
        have st: \<open>step A q (orig a, urhs orig rhs) k \<in> Q\<close>
          using closed[OF q s(1) orig_a s(2), of k \<open>orig c\<close>] k rx by simp
        have \<open>c = cls (step A q (orig a, urhs orig rhs) k)\<close> using s(3)[OF k' Nt] .
        with ihk Nt st have
          \<open>prec_run G A (step A q (orig a, urhs orig rhs) k) (plain orig (pts ! k))\<close>
          \<open>proot (plain orig (pts ! k)) = (Nt (orig c), snd (proot (pts ! k)))\<close>
          by (metis rtranclp.rtrancl_refl)+
        with ihk un Nt k' len show ?thesis by simp
      next
        case (Tm x)
        with ihk obtain tk where \<open>pts ! k = PLeaf tk\<close> \<open>tok tk = x\<close>
          by (auto simp: fst_proot_Tm_iff)
        with ihk un Tm k' len show ?thesis by (auto intro: prec_leaf)
      qed
    qed
    with pn n show ?thesis by simp
  qed
qed

theorem restrict_complete:
  fixes t :: \<open>('m, 'ch, 'n, 't) ptree\<close>
  assumes \<open>prec_run G A q t\<close> \<open>q \<in> Q\<close> \<open>fst (proot t) = Nt (orig (cls q))\<close>
  shows \<open>\<exists>t'. wf_ptree G' t' \<and> proot t' = (Nt (cls q), snd (proot t)) \<and> plain orig t' = t\<close>
  using assms
proof (induction rule: prec_run.induct)
  case (prec_leaf t)
  then show ?case by simp
next
  case (prec_node n r q ts i)
  have nq: \<open>n = orig (cls q)\<close> using prec_node.prems(2) by simp
  note q = prec_node.prems(1)
  have g: \<open>(orig (cls q), r) \<in> set (iprods G)\<close> and o: \<open>ok A q (orig (cls q), r)\<close>
    using prec_node.hyps(1,2) nq by simp_all
  from complete[OF q g o] obtain m r' where m:
    \<open>units_star G' orig (cls q) m\<close> \<open>(m, r') \<in> set (iprods G')\<close> \<open>orig m = orig (cls q)\<close>
    \<open>urhs orig r' = r\<close>
    \<open>\<And>k c. k < length r' \<Longrightarrow> fst (r' ! k) = Nt c \<Longrightarrow> c = cls (step A q (orig (cls q), r) k)\<close>
    by blast
  have lr: \<open>length r' = length r\<close> using m(4) by auto
  define P where \<open>P k s \<longleftrightarrow> wf_ptree G' s \<and> fst (proot s) = fst (r' ! k) \<and>
    snd (proot s) = snd (proot (ts ! k)) \<and> plain orig s = ts ! k\<close>
    for k and s :: \<open>('m, 'ch, 'n', 't) ptree\<close>
  have ex: \<open>\<exists>s. P k s\<close> if k: \<open>k < length r\<close> for k
  proof (cases \<open>fst (r' ! k)\<close>)
    case (Nt c)
    have k': \<open>k < length r'\<close> using k lr by simp
    have rk: \<open>fst (r ! k) = Nt (orig c)\<close>
      using urhs_nth[OF k'] m(4) Nt by simp
    have c: \<open>c = cls (step A q (orig (cls q), r) k)\<close> using m(5)[OF k' Nt] .
    from closed[OF q g refl o k rk]
    have st: \<open>step A q (orig (cls q), r) k \<in> Q\<close> by blast
    from prec_node.IH[OF k] have \<open>fst (proot (ts ! k)) = fst (r ! k)\<close> by blast
    with prec_node.IH[OF k] st rk c nq obtain s where
      \<open>wf_ptree G' s\<close> \<open>proot s = (Nt c, snd (proot (ts ! k)))\<close> \<open>plain orig s = ts ! k\<close>
      by (metis (no_types, lifting))
    with Nt show ?thesis by (auto simp: P_def)
  next
    case (Tm x)
    have k': \<open>k < length r'\<close> using k lr by simp
    have rk: \<open>fst (r ! k) = Tm x\<close> using urhs_nth[OF k'] m(4) Tm by simp
    from prec_node.IH[OF k] rk obtain tk where lf: \<open>ts ! k = PLeaf tk\<close> \<open>tok tk = x\<close>
      by (auto simp: fst_proot_Tm_iff)
    show ?thesis unfolding P_def using lf Tm
      by (intro exI[of _ \<open>PLeaf tk\<close>]) (auto intro: wf_leaf)
  qed
  then obtain f where f: \<open>\<And>k. k < length r \<Longrightarrow> P k (f k)\<close> by metis
  define ts' where \<open>ts' = map f [0..<length r]\<close>
  have lts': \<open>length ts' = length r'\<close> using lr by (simp add: ts'_def)
  have nth: \<open>ts' ! k = f k\<close> if \<open>k < length r\<close> for k using that by (simp add: ts'_def)
  have sat: \<open>irel_sat (snd (r' ! k)) (snd (proot (ts' ! k))) i\<close> if k: \<open>k < length r'\<close> for k
  proof -
    have \<open>k < length r\<close> using k lr by simp
    with prec_node.IH[OF this] f[OF this] nth[OF this] urhs_nth[OF k] m(4)
    show ?thesis by (simp add: P_def)
  qed
  have wf: \<open>wf_ptree G' (PNode m i ts')\<close>
  proof (rule wf_node[OF m(2)])
    show \<open>list_all2 (\<lambda>Xr pt. fst (proot pt) = fst Xr \<and> irel_sat (snd Xr) (snd (proot pt)) i \<and>
        wf_ptree G' pt) r' ts'\<close>
      using lts' f nth sat lr by (auto simp: list_all2_conv_all_nth P_def)
  qed
  have pl: \<open>plain orig (PNode m i ts') = PNode (orig m) i (map (plain orig) ts')\<close>
  proof (rule plain_node, rule notI)
    fix m\<^sub>2 j us assume a: \<open>ts' = [PNode m\<^sub>2 j us]\<close> \<open>orig m\<^sub>2 = orig m\<close>
    with lts' obtain r\<^sub>1 where r1: \<open>r' = [r\<^sub>1]\<close> by (cases r') auto
    with lr have l1: \<open>length r = 1\<close> by simp
    have \<open>P 0 (PNode m\<^sub>2 j us)\<close> using f[of 0] nth[of 0] a l1 by simp
    then have \<open>fst r\<^sub>1 = Nt m\<^sub>2\<close> using r1 by (simp add: P_def)
    then have \<open>r = [(Nt (orig m), snd r\<^sub>1)]\<close> using m(4) r1 a(2)
      by (cases r\<^sub>1) (auto simp: urhs_def)
    with g m(3) no_self show False by (auto simp: no_self_unit_def)
  qed
  have ts: \<open>map (plain orig) ts' = ts\<close>
    by (rule nth_equalityI) (use prec_node.hyps(3) lr f nth lts' in \<open>auto simp: P_def\<close>)
  from units_wrap[OF m(1) wf, of i]
  obtain t' where \<open>wf_ptree G' t'\<close> \<open>proot t' = (Nt (cls q), i)\<close>
    \<open>plain orig t' = plain orig (PNode m i ts')\<close> by auto
  with pl ts m(3) nq show ?case by (intro exI[of _ t']) simp
qed

lemma ilang_iff_ptree:
  \<open>w \<in> ilang H \<longleftrightarrow> (\<exists>pt. wf_ptree H pt \<and> proot pt = (Nt (istart H), istart_ind H) \<and> pyield pt = w)\<close>
  by (simp add: ilang_derives derives_iff_ptree)

theorem restrict_ilang:
  \<open>w \<in> ilang G' \<longleftrightarrow>
   (\<exists>t. prec_run G A q0 t \<and> proot t = (Nt (istart G), istart_ind G) \<and> pyield t = w)\<close>
  unfolding ilang_iff_ptree
proof
  assume \<open>\<exists>pt. wf_ptree G' pt \<and> proot pt = (Nt (istart G'), istart_ind G') \<and> pyield pt = w\<close>
  then obtain pt where pt: \<open>wf_ptree G' pt\<close> \<open>proot pt = (Nt (istart G'), istart_ind G')\<close>
    \<open>pyield pt = w\<close> by blast
  have \<open>prec_run G A q0 (plain orig pt) \<and>
      proot (plain orig pt) = (Nt (orig (istart G')), snd (proot pt))\<close>
    by (rule restrict_sound[OF pt(1)]) (use pt(2) start in auto)
  with pt start show \<open>\<exists>t. prec_run G A q0 t \<and> proot t = (Nt (istart G), istart_ind G) \<and> pyield t = w\<close>
    by (intro exI[of _ \<open>plain orig pt\<close>]) simp
next
  assume \<open>\<exists>t. prec_run G A q0 t \<and> proot t = (Nt (istart G), istart_ind G) \<and> pyield t = w\<close>
  then obtain t where t: \<open>prec_run G A q0 t\<close> \<open>proot t = (Nt (istart G), istart_ind G)\<close>
    \<open>pyield t = w\<close> by blast
  from restrict_complete[OF t(1)] t(2) start obtain t' where
    \<open>wf_ptree G' t'\<close> \<open>proot t' = (Nt (istart G'), istart_ind G')\<close> \<open>plain orig t' = t\<close> by auto
  with t(3) pyield_plain[of orig t']
  show \<open>\<exists>pt. wf_ptree G' pt \<and> proot pt = (Nt (istart G'), istart_ind G') \<and> pyield pt = w\<close>
    by metis
qed

end

section \<open>Reachability by a worklist\<close>

fun reach_step :: \<open>('a \<Rightarrow> 'a list) \<Rightarrow> 'a list \<times> 'a list \<Rightarrow> 'a list \<times> 'a list\<close> where
  \<open>reach_step f (x # ws, vs) = (if x \<in> set vs then (ws, vs) else (f x @ ws, x # vs))\<close>
| \<open>reach_step f ([], vs) = ([], vs)\<close>

definition reach :: \<open>('a \<Rightarrow> 'a list) \<Rightarrow> 'a \<Rightarrow> 'a list\<close> where
  \<open>reach f x = rev (snd (the (while_option (\<lambda>s. fst s \<noteq> []) (reach_step f) ([x], []))))\<close>

definition steps :: \<open>('a \<Rightarrow> 'a list) \<Rightarrow> ('a \<times> 'a) set\<close> where
  \<open>steps f = {(x, y). y \<in> set (f x)}\<close>

lemma steps_closed:
  assumes \<open>z \<in> (steps f)\<^sup>* `` {x}\<close> \<open>y \<in> set (f z)\<close>
  shows \<open>y \<in> (steps f)\<^sup>* `` {x}\<close>
proof -
  have \<open>(z, y) \<in> steps f\<close> using assms(2) by (simp add: steps_def)
  with assms(1) show ?thesis by (auto intro: rtrancl_into_rtrancl)
qed

lemma reach_terminates:
  assumes fin: \<open>finite ((steps f)\<^sup>* `` {x})\<close>
  shows \<open>\<exists>t. while_option (\<lambda>s. fst s \<noteq> []) (reach_step f) ([x], []) = Some t\<close>
proof -
  let ?C = \<open>(steps f)\<^sup>* `` {x}\<close>
  let ?P = \<open>\<lambda>s. set (fst s) \<subseteq> ?C \<and> set (snd s) \<subseteq> ?C\<close>
  let ?R = \<open>inv_image (less_than <*lex*> less_than)
     (\<lambda>s. (card (?C - set (snd s)), length (fst s)))\<close>
  show ?thesis
  proof (rule wf_rel_while_option_Some[where R = ?R and P = ?P])
    show \<open>wf ?R\<close> by auto
  next
    fix s assume s: \<open>?P s \<and> fst s \<noteq> []\<close>
    obtain y ws vs where e: \<open>s = (y # ws, vs)\<close> using s by (cases s; cases \<open>fst s\<close>) auto
    show \<open>(reach_step f s, s) \<in> ?R\<close>
    proof (cases \<open>y \<in> set vs\<close>)
      case True then show ?thesis by (simp add: e)
    next
      case False
      with s e have \<open>y \<in> ?C - set vs\<close> by auto
      then have \<open>card (?C - insert y (set vs)) < card (?C - set vs)\<close>
        using fin by (metis Diff_insert card_Diff1_less finite_Diff)
      with False show ?thesis by (simp add: e)
    qed
  next
    fix s assume s: \<open>?P s \<and> fst s \<noteq> []\<close>
    obtain y ws vs where e: \<open>s = (y # ws, vs)\<close> using s by (cases s; cases \<open>fst s\<close>) auto
    with s steps_closed[of y f x] show \<open>?P (reach_step f s)\<close> by auto
  next
    show \<open>?P ([x], [])\<close> by simp
  qed
qed

lemma reach_spec:
  assumes fin: \<open>finite ((steps f)\<^sup>* `` {x})\<close>
  shows \<open>x \<in> set (reach f x)\<close> \<open>\<And>y z. y \<in> set (reach f x) \<Longrightarrow> z \<in> set (f y) \<Longrightarrow> z \<in> set (reach f x)\<close>
    \<open>set (reach f x) \<subseteq> (steps f)\<^sup>* `` {x}\<close>
proof -
  from reach_terminates[OF fin] obtain t where t:
    \<open>while_option (\<lambda>s. fst s \<noteq> []) (reach_step f) ([x], []) = Some t\<close> by blast
  let ?C = \<open>(steps f)\<^sup>* `` {x}\<close>
  let ?P = \<open>\<lambda>s. (x \<in> set (fst s) \<union> set (snd s)) \<and>
     (\<forall>y \<in> set (snd s). set (f y) \<subseteq> set (fst s) \<union> set (snd s)) \<and> set (snd s) \<subseteq> ?C \<and> set (fst s) \<subseteq> ?C\<close>
  have \<open>?P t\<close>
  proof (rule while_option_rule[OF _ t])
    fix s assume s: \<open>?P s\<close> \<open>fst s \<noteq> []\<close>
    obtain y ws vs where e: \<open>s = (y # ws, vs)\<close> using s(2) by (cases s; cases \<open>fst s\<close>) auto
    have \<open>set (f y) \<subseteq> ?C\<close> using s e steps_closed[of y f x] by auto
    with s(1) e show \<open>?P (reach_step f s)\<close> by auto
  next
    show \<open>?P ([x], [])\<close> by simp
  qed
  moreover have \<open>fst t = []\<close> using while_option_stop[OF t] by simp
  ultimately show \<open>x \<in> set (reach f x)\<close> \<open>set (reach f x) \<subseteq> ?C\<close>
    \<open>\<And>y z. y \<in> set (reach f x) \<Longrightarrow> z \<in> set (f y) \<Longrightarrow> z \<in> set (reach f x)\<close>
    by (auto simp: reach_def t)
qed

section \<open>Moore's partition refinement\<close>

fun first_ix :: \<open>'a \<Rightarrow> 'a list \<Rightarrow> nat\<close> where
  \<open>first_ix x [] = 0\<close>
| \<open>first_ix x (y # ys) = (if x = y then 0 else Suc (first_ix x ys))\<close>

lemma first_ix_nth: \<open>x \<in> set xs \<Longrightarrow> first_ix x xs < length xs \<and> xs ! first_ix x xs = x\<close>
  by (induction xs) auto

definition number :: \<open>'a list \<Rightarrow> nat list\<close> where
  \<open>number xs = map (\<lambda>x. first_ix x xs) xs\<close>

lemma number_eq:
  assumes \<open>i < length xs\<close> \<open>j < length xs\<close> \<open>number xs ! i = number xs ! j\<close>
  shows \<open>xs ! i = xs ! j\<close>
proof -
  have a: \<open>xs ! first_ix (xs ! i) xs = xs ! i\<close>
    using first_ix_nth[OF nth_mem[OF assms(1)]] by blast
  have b: \<open>xs ! first_ix (xs ! j) xs = xs ! j\<close>
    using first_ix_nth[OF nth_mem[OF assms(2)]] by blast
  have \<open>first_ix (xs ! i) xs = first_ix (xs ! j) xs\<close>
    using assms by (simp add: number_def)
  with a b show ?thesis by metis
qed

type_synonym 'l mtab = \<open>('l \<times> nat option list) list list\<close>

definition sg :: \<open>'k list \<Rightarrow> 'l mtab \<Rightarrow> nat list \<Rightarrow> nat \<Rightarrow> 'k \<times> ('l \<times> nat option list) list\<close> where
  \<open>sg K T \<pi> i = (K ! i, map (\<lambda>(l, ks). (l, map (map_option ((!) \<pi>)) ks)) (T ! i))\<close>

definition refine :: \<open>'k list \<Rightarrow> 'l mtab \<Rightarrow> nat list \<Rightarrow> nat list\<close> where
  \<open>refine K T \<pi> = number (map (sg K T \<pi>) [0..<length T])\<close>

fun moore :: \<open>'k list \<Rightarrow> 'l mtab \<Rightarrow> nat \<Rightarrow> nat list \<Rightarrow> nat list\<close> where
  \<open>moore K T 0 \<pi> = [0..<length T]\<close>
| \<open>moore K T (Suc f) \<pi> =
     (let \<pi>' = refine K T \<pi> in if \<pi>' = \<pi> then \<pi> else moore K T f \<pi>')\<close>

definition mstable :: \<open>'k list \<Rightarrow> 'l mtab \<Rightarrow> nat list \<Rightarrow> bool\<close> where
  \<open>mstable K T \<pi> \<longleftrightarrow> length \<pi> = length T \<and>
     (\<forall>i j. i < length T \<longrightarrow> j < length T \<longrightarrow> \<pi> ! i = \<pi> ! j \<longrightarrow> sg K T \<pi> i = sg K T \<pi> j)\<close>

lemma mstable_moore: \<open>mstable K T (moore K T f \<pi>)\<close>
proof (induction f arbitrary: \<pi>)
  case 0
  have \<open>sg K T [0..<length T] i = sg K T [0..<length T] j\<close>
    if \<open>i < length T\<close> \<open>j < length T\<close> \<open>[0..<length T] ! i = [0..<length T] ! j\<close> for i j
  proof -
    from that have \<open>i = j\<close> by simp
    then show ?thesis by (rule arg_cong)
  qed
  then show ?case unfolding mstable_def moore.simps by simp
next
  case (Suc f)
  show ?case
  proof (cases \<open>refine K T \<pi> = \<pi>\<close>)
    case False
    with Suc show ?thesis by (simp add: Let_def)
  next
    case True
    have \<open>sg K T \<pi> i = sg K T \<pi> j\<close>
      if \<open>i < length T\<close> \<open>j < length T\<close> \<open>\<pi> ! i = \<pi> ! j\<close> for i j
      using number_eq[of i \<open>map (sg K T \<pi>) [0..<length T]\<close> j] that True
      by (simp add: refine_def)
    moreover have \<open>length \<pi> = length T\<close>
      using arg_cong[OF True, of length] by (simp add: refine_def number_def)
    ultimately have \<open>mstable K T \<pi>\<close> unfolding mstable_def by blast
    moreover have \<open>moore K T (Suc f) \<pi> = \<pi>\<close> using True by (simp add: Let_def)
    ultimately show ?thesis by (simp only:)
  qed
qed

definition mclass :: \<open>'k list \<Rightarrow> 'l mtab \<Rightarrow> nat list\<close> where
  \<open>mclass K T = moore K T (Suc (length T)) (replicate (length T) 0)\<close>

lemma mstable_mclass: \<open>mstable K T (mclass K T)\<close>
  unfolding mclass_def by (rule mstable_moore)

section \<open>From a partition to a grammar\<close>

type_synonym cell = \<open>nat \<times> nat option list\<close>

definition ralts :: \<open>('n, 't) is_cfg \<Rightarrow> ('n, 't, 'q) prec_aut \<Rightarrow> ('q \<Rightarrow> 'n) \<Rightarrow> 'q \<Rightarrow> nat list\<close> where
  \<open>ralts G A nt q = filter (\<lambda>l. fst (iprods G ! l) = nt q \<and> ok A q (iprods G ! l))
     [0..<length (iprods G)]\<close>

lemma set_ralts: \<open>l \<in> set (ralts G A nt q) \<longleftrightarrow>
    l < length (iprods G) \<and> fst (iprods G ! l) = nt q \<and> ok A q (iprods G ! l)\<close>
  by (auto simp: ralts_def)

definition ckid :: \<open>('n, 't, 'q) prec_aut \<Rightarrow> ('q \<Rightarrow> nat) \<Rightarrow> 'q \<Rightarrow> ('n, 't) alt \<Rightarrow> nat \<Rightarrow> nat option\<close> where
  \<open>ckid A cl q p k = (case fst (snd p ! k) of Nt _ \<Rightarrow> Some (cl (step A q p k)) | Tm _ \<Rightarrow> None)\<close>

definition ccands :: \<open>(nat \<Rightarrow> cell list) \<Rightarrow> (nat \<Rightarrow> 'k) \<Rightarrow> nat list \<Rightarrow> nat \<Rightarrow> nat list\<close> where
  \<open>ccands as key C c = rev (sort_key (\<lambda>b. length (as b))
     (filter (\<lambda>b. b \<noteq> c \<and> key b = key c \<and> 2 \<le> length (as b) \<and> set (as b) \<subset> set (as c)) C))\<close>

fun cstep :: \<open>(nat \<Rightarrow> cell list) \<Rightarrow> cell list \<times> nat list \<Rightarrow> nat \<Rightarrow> cell list \<times> nat list\<close> where
  \<open>cstep as (left, us) b = (if set (as b) \<subseteq> set left
     then (filter (\<lambda>a. a \<notin> set (as b)) left, b # us) else (left, us))\<close>

definition ccover :: \<open>(nat \<Rightarrow> cell list) \<Rightarrow> (nat \<Rightarrow> 'k) \<Rightarrow> nat list \<Rightarrow> nat \<Rightarrow> cell list \<times> nat list\<close> where
  \<open>ccover as key C c = foldl (cstep as) (as c, []) (ccands as key C c)\<close>

lemma cstep_foldl:
  \<open>foldl (cstep as) (l0, u0) bs = (l, u) \<Longrightarrow>
   set l \<union> (\<Union>x \<in> set u. set (as x)) = set l0 \<union> (\<Union>x \<in> set u0. set (as x)) \<and>
   set l \<subseteq> set l0 \<and> set u \<subseteq> set u0 \<union> set bs\<close>
proof (induction bs arbitrary: l0 u0)
  case (Cons b bs)
  show ?case
  proof (cases \<open>set (as b) \<subseteq> set l0\<close>)
    case True
    with Cons.prems have \<open>foldl (cstep as) (filter (\<lambda>a. a \<notin> set (as b)) l0, b # u0) bs = (l, u)\<close>
      by simp
    from Cons.IH[OF this] True show ?thesis by auto
  next
    case False
    with Cons.prems have \<open>foldl (cstep as) (l0, u0) bs = (l, u)\<close> by simp
    from Cons.IH[OF this] show ?thesis by auto
  qed
qed simp

definition sub :: \<open>(nat \<Rightarrow> 'n') \<Rightarrow> ('n, 't) rhs \<Rightarrow> nat option list \<Rightarrow> ('n', 't) rhs\<close> where
  \<open>sub nm r ks = map2 (\<lambda>(X, i) k. (case X of Nt _ \<Rightarrow> Nt (nm (the k)) | Tm t \<Rightarrow> Tm t, i)) r ks\<close>

lemma length_sub: \<open>length ks = length r \<Longrightarrow> length (sub nm r ks) = length r\<close>
  by (simp add: sub_def)

lemma sub_nth: \<open>length ks = length r \<Longrightarrow> k < length r \<Longrightarrow> sub nm r ks ! k =
    (case fst (r ! k) of Nt _ \<Rightarrow> Nt (nm (the (ks ! k))) | Tm t \<Rightarrow> Tm t, snd (r ! k))\<close>
  by (simp add: sub_def split: prod.split)

lemma set_map_filter_id: \<open>x \<in> set (List.map_filter id ks) \<longleftrightarrow> Some x \<in> set ks\<close>
  by (induction ks) (auto split: option.split)

definition cnext :: \<open>(nat \<Rightarrow> cell list) \<Rightarrow> (nat \<Rightarrow> 'k) \<Rightarrow> nat list \<Rightarrow> nat \<Rightarrow> nat list\<close> where
  \<open>cnext as key C c = (let cv = ccover as key C c in
     snd cv @ concat (map (\<lambda>a. List.map_filter id (snd a)) (fst cv)))\<close>

definition cprods :: \<open>('n \<times> ('n, 't) rhs) list \<Rightarrow> (nat \<Rightarrow> cell list) \<Rightarrow> (nat \<Rightarrow> 'k) \<Rightarrow> nat list \<Rightarrow>
    (nat \<Rightarrow> 'n') \<Rightarrow> nat list \<Rightarrow> ('n' \<times> ('n', 't) rhs) list\<close> where
  \<open>cprods P as key C nm L = concat (map (\<lambda>c. let cv = ccover as key C c in
     map (\<lambda>a. (nm c, sub nm (snd (P ! fst a)) (snd a))) (fst cv) @
     map (\<lambda>u. (nm c, [(Nt (nm u), Eq)])) (snd cv)) L)\<close>

locale class_gram0 =
  fixes G :: \<open>('n, 't) is_cfg\<close> and A :: \<open>('n, 't, 'q) prec_aut\<close> and nt :: \<open>'q \<Rightarrow> 'n\<close>
    and q0 :: 'q and ss :: \<open>'q set\<close> and cl :: \<open>'q \<Rightarrow> nat\<close>
    and as :: \<open>nat \<Rightarrow> cell list\<close> and key :: \<open>nat \<Rightarrow> 'k\<close> and C :: \<open>nat list\<close>
    and nm :: \<open>nat \<Rightarrow> 'n'\<close> and orig :: \<open>'n' \<Rightarrow> 'n\<close>
  assumes q0: \<open>q0 \<in> ss\<close> \<open>nt q0 = istart G\<close>
    and no_self: \<open>no_self_unit G\<close>
    and kids: \<open>q \<in> ss \<Longrightarrow> p \<in> set (iprods G) \<Longrightarrow> fst p = nt q \<Longrightarrow> ok A q p \<Longrightarrow>
        k < length (snd p) \<Longrightarrow> fst (snd p ! k) = Nt x \<Longrightarrow>
        step A q p k \<in> ss \<and> nt (step A q p k) = x\<close>
    and as_spec: \<open>q \<in> ss \<Longrightarrow> as (cl q) = map (\<lambda>l. (l, map (ckid A cl q (iprods G ! l))
        [0..<length (snd (iprods G ! l))])) (ralts G A nt q)\<close>
    and C_spec: \<open>set C = cl ` ss\<close>
    and orig_nm: \<open>orig (nm (cl q)) = nt q \<or> q \<notin> ss\<close>
    and key_nm: \<open>c \<in> set C \<Longrightarrow> d \<in> set C \<Longrightarrow> key c = key d \<Longrightarrow> orig (nm c) = orig (nm d)\<close>
    and key_nm': \<open>c \<in> set C \<Longrightarrow> d \<in> set C \<Longrightarrow> orig (nm c) = orig (nm d) \<Longrightarrow> key c = key d\<close>
    and nm_inj: \<open>inj_on nm (set C)\<close>
begin

abbreviation \<open>lft c \<equiv> fst (ccover as key C c)\<close>
abbreviation \<open>uss c \<equiv> snd (ccover as key C c)\<close>

lemma cover:
  \<open>set (as c) = set (lft c) \<union> (\<Union>u \<in> set (uss c). set (as u))\<close>
  \<open>set (lft c) \<subseteq> set (as c)\<close>
  \<open>u \<in> set (uss c) \<Longrightarrow> u \<in> set C \<and> key u = key c \<and> set (as u) \<subset> set (as c)\<close>
proof -
  obtain l v where e: \<open>ccover as key C c = (l, v)\<close> by fastforce
  from cstep_foldl[OF e[unfolded ccover_def]]
  show \<open>set (as c) = set (lft c) \<union> (\<Union>u \<in> set (uss c). set (as u))\<close>
    \<open>set (lft c) \<subseteq> set (as c)\<close>
    \<open>u \<in> set (uss c) \<Longrightarrow> u \<in> set C \<and> key u = key c \<and> set (as u) \<subset> set (as c)\<close>
    by (auto simp: e ccands_def)
qed

lemma as_mem:
  assumes \<open>q \<in> ss\<close> \<open>(l, ks) \<in> set (as (cl q))\<close>
  shows \<open>l < length (iprods G)\<close> \<open>fst (iprods G ! l) = nt q\<close> \<open>ok A q (iprods G ! l)\<close>
    \<open>ks = map (ckid A cl q (iprods G ! l)) [0..<length (snd (iprods G ! l))]\<close>
  using assms by (auto simp: as_spec set_ralts)

lemma alt_kid:
  assumes q: \<open>q \<in> ss\<close> and a: \<open>(l, ks) \<in> set (as (cl q))\<close>
    and k: \<open>k < length (snd (iprods G ! l))\<close> and x: \<open>fst (snd (iprods G ! l) ! k) = Nt x\<close>
  shows \<open>ks ! k = Some (cl (step A q (iprods G ! l) k))\<close>
    \<open>step A q (iprods G ! l) k \<in> ss\<close> \<open>nt (step A q (iprods G ! l) k) = x\<close>
proof -
  note m = as_mem[OF q a]
  show \<open>ks ! k = Some (cl (step A q (iprods G ! l) k))\<close>
    using k x by (simp add: m(4) ckid_def)
  from kids[OF q nth_mem[OF m(1)] m(2) m(3) k x]
  show \<open>step A q (iprods G ! l) k \<in> ss\<close> \<open>nt (step A q (iprods G ! l) k) = x\<close> by auto
qed

lemma length_kids:
  assumes \<open>q \<in> ss\<close> \<open>(l, ks) \<in> set (as (cl q))\<close>
  shows \<open>length ks = length (snd (iprods G ! l))\<close>
  by (subst as_mem(4)[OF assms]) simp

lemma urhs_sub:
  assumes q: \<open>q \<in> ss\<close> and a: \<open>(l, ks) \<in> set (as (cl q))\<close>
  shows \<open>urhs orig (sub nm (snd (iprods G ! l)) ks) = snd (iprods G ! l)\<close>
proof (rule nth_equalityI)
  note len = length_kids[OF q a]
  show \<open>length (urhs orig (sub nm (snd (iprods G ! l)) ks)) = length (snd (iprods G ! l))\<close>
    by (simp add: urhs_def length_sub[OF len])
  fix k assume \<open>k < length (urhs orig (sub nm (snd (iprods G ! l)) ks))\<close>
  then have k: \<open>k < length (snd (iprods G ! l))\<close> by (simp add: urhs_def length_sub[OF len])
  show \<open>urhs orig (sub nm (snd (iprods G ! l)) ks) ! k = snd (iprods G ! l) ! k\<close>
  proof (cases \<open>fst (snd (iprods G ! l) ! k)\<close>)
    case (Nt x)
    note kid = alt_kid[OF q a k Nt]
    have \<open>orig (nm (cl (step A q (iprods G ! l) k))) = x\<close> using orig_nm kid(2,3) by metis
    with k Nt kid(1) show ?thesis
      by (cases \<open>snd (iprods G ! l) ! k\<close>)
        (simp add: urhs_def length_sub[OF len] sub_nth[OF len])
  next
    case (Tm t)
    with k show ?thesis
      by (cases \<open>snd (iprods G ! l) ! k\<close>)
        (simp add: urhs_def length_sub[OF len] sub_nth[OF len])
  qed
qed

lemma cnext_in_C:
  assumes \<open>c \<in> set C\<close> \<open>x \<in> set (cnext as key C c)\<close>
  shows \<open>x \<in> set C\<close>
proof -
  from assms(1) C_spec obtain q where q: \<open>q \<in> ss\<close> \<open>c = cl q\<close> by auto
  from assms(2) consider \<open>x \<in> set (uss c)\<close> | l ks where \<open>(l, ks) \<in> set (lft c)\<close> \<open>Some x \<in> set ks\<close>
    by (fastforce simp: cnext_def Let_def set_map_filter_id)
  then show ?thesis
  proof cases
    case 1
    then show ?thesis using cover(3) by blast
  next
    case 2
    then have a: \<open>(l, ks) \<in> set (as (cl q))\<close> using cover(2) q(2) by blast
    from 2(2) obtain k where k: \<open>k < length ks\<close> \<open>ks ! k = Some x\<close> by (auto simp: in_set_conv_nth)
    have k': \<open>k < length (snd (iprods G ! l))\<close> using k length_kids[OF q(1) a] by simp
    show ?thesis
    proof (cases \<open>fst (snd (iprods G ! l) ! k)\<close>)
      case (Nt y)
      note kid = alt_kid[OF q(1) a k' Nt]
      with k C_spec show ?thesis by auto
    next
      case (Tm t)
      with k k' show ?thesis by (simp add: as_mem(4)[OF q(1) a] ckid_def)
    qed
  qed
qed

end

locale class_gram = class_gram0 +
  fixes L :: \<open>nat list\<close>
  assumes L_sub: \<open>set L \<subseteq> set C\<close> and L_start: \<open>cl q0 \<in> set L\<close>
    and L_closed: \<open>c \<in> set L \<Longrightarrow> x \<in> set (cnext as key C c) \<Longrightarrow> x \<in> set L\<close>
begin

definition G' where
  \<open>G' = \<lparr>iprods = cprods (iprods G) as key C nm L, istart = nm (cl q0), istart_ind = istart_ind G\<rparr>\<close>

lemma mem_G':
  \<open>(m, r) \<in> set (iprods G') \<longleftrightarrow> (\<exists>c \<in> set L. m = nm c \<and>
     ((\<exists>l ks. (l, ks) \<in> set (lft c) \<and> r = sub nm (snd (iprods G ! l)) ks) \<or>
      (\<exists>u \<in> set (uss c). r = [(Nt (nm u), Eq)])))\<close>
proof -
  have a: \<open>(m, r) \<in> (\<lambda>a. (nm c, sub nm (snd (iprods G ! fst a)) (snd a))) ` set (lft c) \<longleftrightarrow>
      m = nm c \<and> (\<exists>l ks. (l, ks) \<in> set (lft c) \<and> r = sub nm (snd (iprods G ! l)) ks)\<close> for c
    by force
  have b: \<open>(m, r) \<in> (\<lambda>u. (nm c, [(Nt (nm u), Eq)])) ` set (uss c) \<longleftrightarrow>
      m = nm c \<and> (\<exists>u \<in> set (uss c). r = [(Nt (nm u), Eq)])\<close> for c
    by force
  show ?thesis by (simp add: G'_def cprods_def Let_def a b) blast
qed

lemma L_C: \<open>c \<in> set L \<Longrightarrow> c \<in> set C\<close>
  using L_sub by blast

lemma left_not_unit:
  assumes c: \<open>c \<in> set L\<close> and a: \<open>(l, ks) \<in> set (lft c)\<close>
    and u: \<open>unit_alt orig (nm c, sub nm (snd (iprods G ! l)) ks) m\<close>
  shows False
proof -
  from L_C[OF c] C_spec obtain q where q: \<open>q \<in> ss\<close> \<open>c = cl q\<close> by auto
  have a': \<open>(l, ks) \<in> set (as (cl q))\<close> using a cover(2) q(2) by blast
  have r: \<open>sub nm (snd (iprods G ! l)) ks = [(Nt m, Eq)]\<close> and om: \<open>orig m = orig (nm c)\<close>
    using u by (auto simp: unit_alt_def)
  have \<open>snd (iprods G ! l) = [(Nt (orig m), Eq)]\<close>
    using urhs_sub[OF q(1) a'] by (simp add: r urhs_def)
  moreover have \<open>fst (iprods G ! l) = orig m\<close>
    using as_mem(2)[OF q(1) a'] om orig_nm q by metis
  ultimately have \<open>(orig m, [(Nt (orig m), Eq)]) \<in> set (iprods G)\<close>
    using nth_mem[OF as_mem(1)[OF q(1) a']] by (metis prod.collapse)
  with no_self show False by (simp add: no_self_unit_def)
qed

lemma unit_uss:
  assumes c: \<open>c \<in> set L\<close> and u: \<open>units G' orig (nm c) m\<close>
  shows \<open>\<exists>x \<in> set (uss c). m = nm x\<close>
proof -
  from u obtain r where r: \<open>(nm c, r) \<in> set (iprods G')\<close> \<open>unit_alt orig (nm c, r) m\<close>
    by (auto simp: units_def)
  from r(1) obtain d where d: \<open>d \<in> set L\<close> \<open>nm c = nm d\<close>
    \<open>(\<exists>l ks. (l, ks) \<in> set (lft d) \<and> r = sub nm (snd (iprods G ! l)) ks) \<or>
      (\<exists>x \<in> set (uss d). r = [(Nt (nm x), Eq)])\<close>
    by (auto simp: mem_G')
  have \<open>c = d\<close> using inj_onD[OF nm_inj d(2) L_C[OF c] L_C[OF d(1)]] .
  from d(3) show ?thesis
  proof (elim disjE exE conjE bexE)
    fix l ks assume \<open>(l, ks) \<in> set (lft d)\<close> \<open>r = sub nm (snd (iprods G ! l)) ks\<close>
    with c r(2) left_not_unit[of c l ks m] \<open>c = d\<close> show ?thesis by simp
  next
    fix x assume \<open>x \<in> set (uss d)\<close> \<open>r = [(Nt (nm x), Eq)]\<close>
    with r(2) \<open>c = d\<close> show ?thesis by (auto simp: unit_alt_def)
  qed
qed

lemma uss_L: \<open>c \<in> set L \<Longrightarrow> u \<in> set (uss c) \<Longrightarrow> u \<in> set L\<close>
  by (rule L_closed) (auto simp: cnext_def Let_def)

lemma uss_units:
  assumes \<open>c \<in> set L\<close> \<open>u \<in> set (uss c)\<close>
  shows \<open>units G' orig (nm c) (nm u)\<close>
proof -
  have \<open>(nm c, [(Nt (nm u), Eq)]) \<in> set (iprods G')\<close>
    using assms by (auto simp: mem_G')
  moreover have \<open>orig (nm u) = orig (nm c)\<close>
  proof -
    note cu = cover(3)[OF assms(2)]
    from cu have \<open>u \<in> set C\<close> \<open>key u = key c\<close> by auto
    from key_nm[OF this(1) L_C[OF assms(1)] this(2)] show ?thesis .
  qed
  ultimately show ?thesis by (auto simp: units_def unit_alt_def)
qed

lemma units_star_sub:
  assumes \<open>units_star G' orig (nm c) m\<close> \<open>c \<in> set L\<close>
  shows \<open>\<exists>d \<in> set L. m = nm d \<and> set (as d) \<subseteq> set (as c) \<and> orig (nm d) = orig (nm c)\<close>
  using assms(1)
proof (induction rule: rtranclp_induct)
  case base
  from assms(2) show ?case by blast
next
  case (step y z)
  then obtain d where d: \<open>d \<in> set L\<close> \<open>y = nm d\<close> \<open>set (as d) \<subseteq> set (as c)\<close>
    \<open>orig (nm d) = orig (nm c)\<close> by blast
  with step(2) obtain x where x: \<open>x \<in> set (uss d)\<close> \<open>z = nm x\<close> using unit_uss by blast
  note cu = cover(3)[OF x(1)]
  have h1: \<open>set (as x) \<subseteq> set (as d)\<close> using cu by auto
  have h2: \<open>orig (nm x) = orig (nm d)\<close> using key_nm[of x d] cu L_C[OF d(1)] by blast
  show ?case using uss_L[OF d(1) x(1)] x(2) h1 h2 d(3,4)
    by (intro bexI[of _ x]) auto
qed

lemma chain:
  assumes \<open>c \<in> set L\<close> \<open>a \<in> set (as c)\<close>
  shows \<open>\<exists>m \<in> set L. units_star G' orig (nm c) (nm m) \<and> a \<in> set (lft m)\<close>
  using assms
proof (induction \<open>card (set (as c))\<close> arbitrary: c rule: less_induct)
  case less
  from less.prems(2) cover(1)[of c] consider \<open>a \<in> set (lft c)\<close> | u where \<open>u \<in> set (uss c)\<close> \<open>a \<in> set (as u)\<close>
    by blast
  then show ?case
  proof cases
    case 1
    with less.prems(1) show ?thesis by blast
  next
    case 2
    have \<open>card (set (as u)) < card (set (as c))\<close>
      using cover(3)[OF 2(1)] by (simp add: psubset_card_mono)
    from less.hyps[OF this uss_L[OF less.prems(1) 2(1)] 2(2)] uss_units[OF less.prems(1) 2(1)]
    show ?thesis by (meson converse_rtranclp_into_rtranclp)
  qed
qed

theorem restrict_ok: \<open>restrict_ok G A q0 {q \<in> ss. cl q \<in> set L} (\<lambda>q. nm (cl q)) G' orig\<close>
proof
  show \<open>q0 \<in> {q \<in> ss. cl q \<in> set L}\<close> using q0 L_start by simp
  show \<open>nm (cl q0) = istart G'\<close> by (simp add: G'_def)
  show \<open>orig (istart G') = istart G\<close> using orig_nm[of q0] q0 by (simp add: G'_def)
  show \<open>istart_ind G' = istart_ind G\<close> by (simp add: G'_def)
  show \<open>no_self_unit G\<close> by (rule no_self)
next
  fix q n r k x
  assume q: \<open>q \<in> {q \<in> ss. cl q \<in> set L}\<close> and p: \<open>(n, r) \<in> set (iprods G)\<close>
    and n: \<open>n = orig (nm (cl q))\<close> and o: \<open>ok A q (n, r)\<close> and k: \<open>k < length r\<close> and x: \<open>fst (r ! k) = Nt x\<close>
  have nq: \<open>n = nt q\<close> using n q orig_nm[of q] by simp
  from kids[of q \<open>(n, r)\<close> k x] q p nq o k x
  have s: \<open>step A q (n, r) k \<in> ss\<close> \<open>nt (step A q (n, r) k) = x\<close> by auto
  from p obtain l where l: \<open>l < length (iprods G)\<close> \<open>iprods G ! l = (n, r)\<close> by (auto simp: in_set_conv_nth)
  have \<open>l \<in> set (ralts G A nt q)\<close> using l nq o by (simp add: set_ralts)
  then obtain ks where a: \<open>(l, ks) \<in> set (as (cl q))\<close> using q by (fastforce simp: as_spec)
  from chain[OF _ a] q obtain m where m: \<open>m \<in> set L\<close> \<open>(l, ks) \<in> set (lft m)\<close> by auto
  have \<open>ks ! k = Some (cl (step A q (n, r) k))\<close> \<open>k < length ks\<close>
    using alt_kid(1)[of q l ks k x] length_kids[of q l ks] q a k x l by auto
  then have \<open>Some (cl (step A q (n, r) k)) \<in> set ks\<close> by (metis nth_mem)
  with m have \<open>cl (step A q (n, r) k) \<in> set L\<close>
    by (intro L_closed[OF m(1)]) (force simp: cnext_def Let_def set_map_filter_id)
  with s orig_nm[of \<open>step A q (n, r) k\<close>]
  show \<open>step A q (n, r) k \<in> {q \<in> ss. cl q \<in> set L} \<and> orig (nm (cl (step A q (n, r) k))) = x\<close> by auto
next
  fix q m r'
  assume q: \<open>q \<in> {q \<in> ss. cl q \<in> set L}\<close> and us: \<open>units_star G' orig (nm (cl q)) m\<close>
    and p: \<open>(m, r') \<in> set (iprods G')\<close> and nu: \<open>\<not> (\<exists>c. unit_alt orig (m, r') c)\<close>
  from units_star_sub[OF us] q obtain d where d: \<open>d \<in> set L\<close> \<open>m = nm d\<close>
    \<open>set (as d) \<subseteq> set (as (cl q))\<close> \<open>orig (nm d) = orig (nm (cl q))\<close> by auto
  from p d(2) obtain e where e: \<open>e \<in> set L\<close> \<open>nm d = nm e\<close>
    \<open>(\<exists>l ks. (l, ks) \<in> set (lft e) \<and> r' = sub nm (snd (iprods G ! l)) ks) \<or>
      (\<exists>x \<in> set (uss e). r' = [(Nt (nm x), Eq)])\<close> by (auto simp: mem_G')
  have de: \<open>d = e\<close> using inj_onD[OF nm_inj e(2) L_C[OF d(1)] L_C[OF e(1)]] .
  have \<open>\<exists>l ks. (l, ks) \<in> set (lft d) \<and> r' = sub nm (snd (iprods G ! l)) ks\<close>
  proof (rule ccontr)
    assume \<open>\<nexists>l ks. (l, ks) \<in> set (lft d) \<and> r' = sub nm (snd (iprods G ! l)) ks\<close>
    with e(3) de obtain x where x: \<open>x \<in> set (uss d)\<close> \<open>r' = [(Nt (nm x), Eq)]\<close> by auto
    have \<open>orig (nm x) = orig (nm d)\<close>
      using key_nm[of x d] L_C[OF d(1)] cover(3)[OF x(1)] by blast
    with nu x(2) d(2) show False by (auto simp: unit_alt_def)
  qed
  then obtain l ks where a: \<open>(l, ks) \<in> set (lft d)\<close> and r': \<open>r' = sub nm (snd (iprods G ! l)) ks\<close> by blast
  have q': \<open>q \<in> ss\<close> using q by simp
  have a': \<open>(l, ks) \<in> set (as (cl q))\<close> using a cover(2) d(3) by blast
  note mm = as_mem[OF q' a']
  have om: \<open>orig m = nt q\<close> using d(2,4) orig_nm[of q] q' by simp
  have pl: \<open>(orig m, urhs orig r') = iprods G ! l\<close>
    using mm(2) om urhs_sub[OF q' a'] by (simp add: r' prod_eq_iff)
  have \<open>c = nm (cl (step A q (iprods G ! l) k))\<close>
    if k: \<open>k < length r'\<close> and c: \<open>fst (r' ! k) = Nt c\<close> for k c
  proof -
    note len = length_kids[OF q' a']
    have k': \<open>k < length (snd (iprods G ! l))\<close> using k by (simp add: r' length_sub[OF len])
    show ?thesis
    proof (cases \<open>fst (snd (iprods G ! l) ! k)\<close>)
      case (Nt y)
      with c k' show ?thesis by (simp add: r' sub_nth[OF len k'] alt_kid(1)[OF q' a' k' Nt])
    next
      case (Tm t)
      with c k' show ?thesis by (simp add: r' sub_nth[OF len k'])
    qed
  qed
  then show \<open>(orig m, urhs orig r') \<in> set (iprods G) \<and> ok A q (orig m, urhs orig r') \<and>
      (\<forall>k c. k < length r' \<longrightarrow> fst (r' ! k) = Nt c \<longrightarrow>
         c = nm (cl (step A q (orig m, urhs orig r') k)))\<close>
    using pl mm(1,3) by (simp add: nth_mem[OF mm(1), folded pl])
next
  fix q r
  assume q: \<open>q \<in> {q \<in> ss. cl q \<in> set L}\<close> and p: \<open>(orig (nm (cl q)), r) \<in> set (iprods G)\<close>
    and o: \<open>ok A q (orig (nm (cl q)), r)\<close>
  have q': \<open>q \<in> ss\<close> using q by simp
  have nq: \<open>orig (nm (cl q)) = nt q\<close> using q' orig_nm[of q] by simp
  from p obtain l where l: \<open>l < length (iprods G)\<close> \<open>iprods G ! l = (nt q, r)\<close>
    by (auto simp: nq in_set_conv_nth)
  have \<open>l \<in> set (ralts G A nt q)\<close> using l o nq by (simp add: set_ralts)
  then obtain ks where a: \<open>(l, ks) \<in> set (as (cl q))\<close> using q' by (fastforce simp: as_spec)
  from chain[OF _ a] q obtain m where m: \<open>m \<in> set L\<close> \<open>units_star G' orig (nm (cl q)) (nm m)\<close>
    \<open>(l, ks) \<in> set (lft m)\<close> by auto
  note len = length_kids[OF q' a]
  let ?r' = \<open>sub nm r ks\<close>
  have rr: \<open>r = snd (iprods G ! l)\<close> using l(2) by simp
  have \<open>(nm m, ?r') \<in> set (iprods G')\<close> unfolding mem_G' using m(1,3) rr by blast
  moreover have \<open>orig (nm m) = orig (nm (cl q))\<close> using units_star_sub[OF m(2)] q m(1)
    by (auto dest: inj_onD[OF nm_inj] L_C)
  moreover have \<open>urhs orig ?r' = r\<close> using urhs_sub[OF q' a] l(2) by simp
  moreover have \<open>c = nm (cl (step A q (orig (nm (cl q)), r) k))\<close>
    if k: \<open>k < length ?r'\<close> and c: \<open>fst (?r' ! k) = Nt c\<close> for k c
  proof -
    have len': \<open>length ks = length r\<close> using len l(2) by simp
    have k': \<open>k < length r\<close> using k by (simp add: length_sub[OF len'])
    have k'': \<open>k < length (snd (iprods G ! l))\<close> using k' l(2) by simp
    show ?thesis
    proof (cases \<open>fst (r ! k)\<close>)
      case (Nt y)
      have \<open>ks ! k = Some (cl (step A q (iprods G ! l) k))\<close>
        using alt_kid(1)[OF q' a k''] Nt l(2) by simp
      with c k' Nt show ?thesis by (simp add: sub_nth[OF len' k'] l(2) nq)
    next
      case (Tm t)
      with c k' show ?thesis by (simp add: sub_nth[OF len' k'])
    qed
  qed
  ultimately show \<open>\<exists>m r'. units_star G' orig (nm (cl q)) m \<and> (m, r') \<in> set (iprods G') \<and>
      orig m = orig (nm (cl q)) \<and> urhs orig r' = r \<and>
      (\<forall>k c. k < length r' \<longrightarrow> fst (r' ! k) = Nt c \<longrightarrow>
         c = nm (cl (step A q (orig (nm (cl q)), r) k)))\<close>
    using m(2) by blast
qed

end

section \<open>The whole construction\<close>

lemma reach_within:
  assumes S: \<open>finite S\<close> \<open>x \<in> S\<close> \<open>\<And>y. y \<in> S \<Longrightarrow> set (f y) \<subseteq> S\<close>
  shows \<open>(steps f)\<^sup>* `` {x} \<subseteq> S\<close> \<open>finite ((steps f)\<^sup>* `` {x})\<close>
proof -
  have \<open>(x, y) \<in> (steps f)\<^sup>* \<Longrightarrow> y \<in> S\<close> for y
    by (induction rule: rtrancl_induct) (use S in \<open>auto simp: steps_def\<close>)
  then show *: \<open>(steps f)\<^sup>* `` {x} \<subseteq> S\<close> by blast
  from finite_subset[OF * S(1)] show \<open>finite ((steps f)\<^sup>* `` {x})\<close> .
qed

fun enc :: \<open>nat \<Rightarrow> string\<close> where
  \<open>enc n = (if n = 0 then [] else (if even n then CHR ''a'' else CHR ''b'') # enc (n div 2))\<close>

declare enc.simps[simp del]

lemma enc_inj: \<open>enc n = enc m \<Longrightarrow> n = m\<close>
proof (induction n arbitrary: m rule: enc.induct)
  case (1 n)
  show ?case
  proof (cases \<open>n = 0\<close>)
    case True
    with "1.prems" show ?thesis by (subst (asm) (1 2) enc.simps) (auto split: if_splits)
  next
    case False
    with "1.prems" have m: \<open>m \<noteq> 0\<close> by (subst (asm) (1 2) enc.simps) (auto split: if_splits)
    from "1.prems" False m have e: \<open>even n \<longleftrightarrow> even m\<close> and t: \<open>enc (n div 2) = enc (m div 2)\<close>
      by (subst (asm) (1 2) enc.simps; auto split: if_splits)+
    have \<open>n div 2 = m div 2\<close> using "1.IH"[OF False t] .
    with e show ?thesis by presburger
  qed
qed

lemma enc_hash: \<open>CHR ''#'' \<notin> set (enc n)\<close>
proof (induction n rule: enc.induct)
  case (1 n)
  then show ?case by (subst enc.simps) auto
qed

definition orig_name :: \<open>string \<Rightarrow> string\<close> where
  \<open>orig_name s = (case dropWhile (\<lambda>c. c \<noteq> CHR ''#'') (rev s) of
     [] \<Rightarrow> s | _ # t \<Rightarrow> rev t)\<close>

lemma orig_name_cut: \<open>orig_name (k @ CHR ''#'' # enc c) = k\<close>
proof -
  have \<open>dropWhile (\<lambda>c. c \<noteq> CHR ''#'') (rev (enc c) @ CHR ''#'' # rev k) = CHR ''#'' # rev k\<close>
  proof -
    have \<open>\<forall>x \<in> set (enc c). x \<noteq> CHR ''#''\<close> using enc_hash[of c] by blast
    then show ?thesis by (simp add: dropWhile_append3)
  qed
  then show ?thesis by (simp add: orig_name_def)
qed

definition rsucc :: \<open>('n, 't) is_cfg \<Rightarrow> ('n, 't, 'q) prec_aut \<Rightarrow> ('q \<Rightarrow> 'n) \<Rightarrow> 'q \<Rightarrow> 'q list\<close> where
  \<open>rsucc G A nt q = concat (map (\<lambda>l. concat (map (\<lambda>k.
       case fst (snd (iprods G ! l) ! k) of Nt _ \<Rightarrow> [step A q (iprods G ! l) k] | Tm _ \<Rightarrow> [])
     [0..<length (snd (iprods G ! l))])) (ralts G A nt q))\<close>

definition rtab :: \<open>('n, 't) is_cfg \<Rightarrow> ('n, 't, 'q) prec_aut \<Rightarrow> ('q \<Rightarrow> 'n) \<Rightarrow> ('q \<Rightarrow> nat) \<Rightarrow> 'q list \<Rightarrow> nat mtab\<close> where
  \<open>rtab G A nt ix ss = map (\<lambda>q. map (\<lambda>l. (l, map (ckid A ix q (iprods G ! l))
     [0..<length (snd (iprods G ! l))])) (ralts G A nt q)) ss\<close>

definition restrict_gen ::
  \<open>(string, 't) is_cfg \<Rightarrow> (string, 't, 'q) prec_aut \<Rightarrow> ('q \<Rightarrow> string) \<Rightarrow> 'q \<Rightarrow> (string, 't) is_cfg\<close> where
  \<open>restrict_gen G A nt q0 =
    (let ss = reach (rsucc G A nt) q0;
         ix = (\<lambda>q. first_ix q ss);
         T = rtab G A nt ix ss;
         K = map nt ss;
         \<pi> = mclass K T;
         cl = (\<lambda>q. \<pi> ! ix q);
         AT = map (\<lambda>i. snd (sg K T \<pi> i)) [0..<length T];
         as = (\<lambda>c. AT ! first_ix c \<pi>);
         key = (\<lambda>c. K ! first_ix c \<pi>);
         C = remdups (map cl ss);
         nm = (\<lambda>c. key c @ CHR ''#'' # enc c);
         L = reach (cnext as key C) (cl q0)
     in \<lparr>iprods = cprods (iprods G) as key C nm L, istart = nm (cl q0), istart_ind = istart_ind G\<rparr>)\<close>

theorem restrict_gen_correct:
  fixes G :: \<open>(string, 't) is_cfg\<close> and A :: \<open>(string, 't, 'q) prec_aut\<close>
  assumes fin: \<open>finite ((steps (rsucc G A nt))\<^sup>* `` {q0})\<close>
    and start: \<open>nt q0 = istart G\<close>
    and no_self: \<open>no_self_unit G\<close>
    and nt_step: \<open>\<And>q p k x. p \<in> set (iprods G) \<Longrightarrow> fst p = nt q \<Longrightarrow> ok A q p \<Longrightarrow>
        k < length (snd p) \<Longrightarrow> fst (snd p ! k) = Nt x \<Longrightarrow> nt (step A q p k) = x\<close>
  shows \<open>\<exists>Q (cls :: 'q \<Rightarrow> string). restrict_ok G A q0 Q cls (restrict_gen G A nt q0) orig_name\<close>
proof -
  define ss where \<open>ss = reach (rsucc G A nt) q0\<close>
  define ix where \<open>ix = (\<lambda>q. first_ix q ss)\<close>
  define T where \<open>T = rtab G A nt ix ss\<close>
  define K where \<open>K = map nt ss\<close>
  define \<pi> where \<open>\<pi> = mclass K T\<close>
  define cl where \<open>cl = (\<lambda>q. \<pi> ! ix q)\<close>
  define AT where \<open>AT = map (\<lambda>i. snd (sg K T \<pi> i)) [0..<length T]\<close>
  define as where \<open>as = (\<lambda>c. AT ! first_ix c \<pi>)\<close>
  define key where \<open>key = (\<lambda>c. K ! first_ix c \<pi>)\<close>
  define C where \<open>C = remdups (map cl ss)\<close>
  define nm where \<open>nm = (\<lambda>c. key c @ CHR ''#'' # enc c)\<close>
  note st = reach_spec[OF fin, folded ss_def]
  have st_def: \<open>length \<pi> = length T\<close>
    \<open>\<And>i j. i < length T \<Longrightarrow> j < length T \<Longrightarrow> \<pi> ! i = \<pi> ! j \<Longrightarrow> sg K T \<pi> i = sg K T \<pi> j\<close>
    using mstable_mclass[of K T] unfolding mstable_def \<pi>_def by blast+
  have lenT: \<open>length T = length ss\<close> by (simp add: T_def rtab_def)
  have ixs: \<open>ix q < length ss\<close> \<open>ss ! ix q = q\<close> if \<open>q \<in> set ss\<close> for q
    using first_ix_nth[OF that] by (auto simp: ix_def)
  have rep: \<open>first_ix (cl q) \<pi> < length T \<and> \<pi> ! first_ix (cl q) \<pi> = cl q\<close> if \<open>q \<in> set ss\<close> for q
  proof -
    have \<open>cl q \<in> set \<pi>\<close> unfolding cl_def using ixs[OF that] st_def(1) lenT by simp
    from first_ix_nth[OF this] show ?thesis using st_def(1) by simp
  qed
  have sg_eq: \<open>sg K T \<pi> (first_ix (cl q) \<pi>) = sg K T \<pi> (ix q)\<close> if q: \<open>q \<in> set ss\<close> for q
    using st_def(2)[of \<open>first_ix (cl q) \<pi>\<close> \<open>ix q\<close>] rep[OF q] ixs[OF q] lenT by (simp add: cl_def)
  have key_cl: \<open>key (cl q) = nt q\<close> if q: \<open>q \<in> set ss\<close> for q
  proof -
    have \<open>K ! first_ix (cl q) \<pi> = K ! ix q\<close> using sg_eq[OF q] by (simp add: sg_def)
    also have \<open>\<dots> = nt q\<close> using ixs[OF q] by (simp add: K_def)
    finally show ?thesis by (simp add: key_def)
  qed
  have kid_eq: \<open>map_option ((!) \<pi>) (ckid A ix q p k) = ckid A cl q p k\<close> for q p k
    by (simp add: ckid_def cl_def split: sym.split)
  have as_cl: \<open>as (cl q) = map (\<lambda>l. (l, map (ckid A cl q (iprods G ! l))
      [0..<length (snd (iprods G ! l))])) (ralts G A nt q)\<close> if q: \<open>q \<in> set ss\<close> for q
  proof -
    have \<open>as (cl q) = snd (sg K T \<pi> (first_ix (cl q) \<pi>))\<close>
      using rep[OF q] by (simp add: as_def AT_def)
    also have \<open>\<dots> = snd (sg K T \<pi> (ix q))\<close> by (simp only: sg_eq[OF q])
    also have \<open>\<dots> = map (\<lambda>(l, ks). (l, map (map_option ((!) \<pi>)) ks))
        (map (\<lambda>l. (l, map (ckid A ix q (iprods G ! l)) [0..<length (snd (iprods G ! l))])) (ralts G A nt q))\<close>
      using ixs[OF q] by (simp add: sg_def T_def rtab_def)
    also have \<open>\<dots> = map (\<lambda>l. (l, map (ckid A cl q (iprods G ! l))
        [0..<length (snd (iprods G ! l))])) (ralts G A nt q)\<close>
      by (simp add: comp_def kid_eq)
    finally show ?thesis .
  qed
  have kids: \<open>step A q p k \<in> set ss \<and> nt (step A q p k) = x\<close>
    if q: \<open>q \<in> set ss\<close> and p: \<open>p \<in> set (iprods G)\<close> \<open>fst p = nt q\<close> \<open>ok A q p\<close>
      and k: \<open>k < length (snd p)\<close> \<open>fst (snd p ! k) = Nt x\<close> for q p k x
  proof -
    from p(1) obtain l where l: \<open>l < length (iprods G)\<close> \<open>iprods G ! l = p\<close> by (auto simp: in_set_conv_nth)
    have \<open>l \<in> set (ralts G A nt q)\<close> using l p by (simp add: set_ralts)
    with l k have \<open>step A q p k \<in> set (rsucc G A nt q)\<close>
      by (force simp: rsucc_def)
    from st(2)[OF q this] nt_step[OF p k] show ?thesis by blast
  qed
  have orig_nm: \<open>orig_name (nm c) = key c\<close> for c
    by (simp add: nm_def orig_name_cut)
  have nm_inj: \<open>inj_on nm (set C)\<close>
  proof (rule inj_onI)
    fix c d assume e: \<open>nm c = nm d\<close>
    with orig_nm have \<open>key c = key d\<close> by metis
    with e have \<open>enc c = enc d\<close> by (simp add: nm_def)
    then show \<open>c = d\<close> by (rule enc_inj)
  qed
  have set_C: \<open>set C = cl ` set ss\<close> by (simp add: C_def)
  interpret g0: class_gram0 G A nt q0 \<open>set ss\<close> cl as key C nm orig_name
  proof
    show \<open>q0 \<in> set ss\<close> by (rule st(1))
    show \<open>nt q0 = istart G\<close> by (rule start)
    show \<open>no_self_unit G\<close> by (rule no_self)
    show \<open>orig_name (nm (cl q)) = nt q \<or> q \<notin> set ss\<close> for q
      using orig_nm key_cl by metis
    show \<open>inj_on nm (set C)\<close> by (rule nm_inj)
    show \<open>set C = cl ` set ss\<close> by (rule set_C)
    show \<open>orig_name (nm c) = orig_name (nm d)\<close> if \<open>key c = key d\<close> for c d
      using that by (simp add: orig_nm)
    show \<open>key c = key d\<close> if \<open>orig_name (nm c) = orig_name (nm d)\<close> for c d
      using that by (simp add: orig_nm)
  qed (use kids as_cl in auto)
  define L where \<open>L = reach (cnext as key C) (cl q0)\<close>
  have C_in: \<open>cl q0 \<in> set C\<close> using st(1) set_C by auto
  have rw: \<open>(steps (cnext as key C))\<^sup>* `` {cl q0} \<subseteq> set C\<close>
    \<open>finite ((steps (cnext as key C))\<^sup>* `` {cl q0})\<close>
    using reach_within[of \<open>set C\<close> \<open>cl q0\<close> \<open>cnext as key C\<close>] C_in g0.cnext_in_C by auto
  note lr = reach_spec[OF rw(2), folded L_def]
  interpret g: class_gram G A nt q0 \<open>set ss\<close> cl as key C nm orig_name L
    by unfold_locales (use lr rw(1) in auto)
  have \<open>restrict_gen G A nt q0 = g.G'\<close>
    unfolding restrict_gen_def g.G'_def Let_def
    by (simp only: L_def nm_def C_def key_def as_def AT_def cl_def \<pi>_def K_def T_def ix_def ss_def)
  with g.restrict_ok show ?thesis by metis
qed

end
