theory LR_Det
  imports LR_Driver
begin

section \<open>The static sufficient condition for \<^const>\<open>mdet\<close>\<close>

text \<open>This theory proves \<open>rlalr_conflicts G Shn = [] \<Longrightarrow> mdet G Shn\<close>
  (\<^text>\<open>rlalr_sufficient\<close>, at the end): an executable check on the
  driver's tables implies the determinism premise of its completeness.
  After Barthwal (2010, Def. 5.3.7 \<open>okSlr\<close> and Thm 5.4.4: conflict
  freedom is demanded on viable-prefix-reachable states only), DeRemer and
  Pennello (1982, Sect. 3: per-item lookahead) and Jourdan, Pottier and
  Leroy (2012, Sect. 3.3 and Thm 4).

  In order: saturation of the anchored reachable closure; the precise
  (viable-prefix) automaton \<^text>\<open>pr0_states\<close> and its worklist; the
  rigid-point conflict analysis \<^text>\<open>rlalr_conflicts\<close>; tracking every
  reachable configuration by the driver's index stack; the pooled width
  invariant; the canonical tracked stack \<^text>\<open>strack\<close> and its descent;
  the soundness of the rigid-point walk, from which
  \<^text>\<open>rlalr_sufficient\<close> follows.\<close>


section \<open>Saturation of the anchored reachable closure\<close>

text \<open>The report and the check read the fuelled \<^const>\<open>wreach\<close>, which is
  total; this section shows it is saturated.  The general argument:
  \<^const>\<open>wreach_step\<close> only emits dot-0 items, so regardless of the kernel the
  chain grows by at most one item per production per \<^typ>\<open>wrel\<close>, which is
  \<^const>\<open>wreach\<close>'s fuel.  \<^text>\<open>funpow_saturates\<close> bounds the chain by
  \<^term>\<open>card U\<close> for a universe \<^term>\<open>U\<close> containing the start, too coarse
  here; the variant below bounds it by the increment.\<close>


subsection \<open>\<^const>\<open>wreach_step\<close> is extensional, monotone, and dot-0 bounded\<close>

text \<open>\<^const>\<open>wreach_step\<close> inlines its contribution function; name it for the
  set-level reasoning below.\<close>

definition wcontrib :: \<open>('n, 't) is_cfg \<Rightarrow> ('n, 't) witem \<Rightarrow> ('n, 't) witem list\<close> where
  \<open>wcontrib G = (\<lambda>(pr, m, \<rho>).
      if m < length (snd pr)
      then (case fst (snd pr ! m) of
             Nt B \<Rightarrow> map (\<lambda>br. (br, 0, wcomp (winv (w_of (snd (snd pr ! m)))) \<rho>))
                     (filter (\<lambda>br. fst br = B) (iprods G))
           | Tm _ \<Rightarrow> [])
      else [])\<close>

lemma wreach_step_alt:
  \<open>wreach_step G ws = remdups (ws @ concat (map (wcontrib G) ws))\<close>
  unfolding wreach_step_def wcontrib_def by simp

lemma wreach_step_set:
  \<open>set (wreach_step G xs) = set xs \<union> (\<Union>x \<in> set xs. set (wcontrib G x))\<close>
  unfolding wreach_step_alt by auto

lemma wreach_step_ext:
  \<open>set xs = set ys \<Longrightarrow> set (wreach_step G xs) = set (wreach_step G ys)\<close>
  by (simp add: wreach_step_set)

lemma wreach_step_mono: \<open>set xs \<subseteq> set (wreach_step G xs)\<close>
  by (simp add: wreach_step_set)

text \<open>Every item \<^const>\<open>wreach_step\<close> emits sits at dot 0 on a production of
  the grammar; this bounds the growth independently of the kernel.\<close>

definition wdot0 :: \<open>('n, 't) is_cfg \<Rightarrow> ('n, 't) witem list\<close> where
  \<open>wdot0 G = concat (map (\<lambda>pr. map (\<lambda>\<rho>. (pr, 0, \<rho>))
      [WEq, WGe, WGt, WLe, WLt, WAny]) (iprods G))\<close>

lemma wdot0_mem: \<open>pr \<in> set (iprods G) \<Longrightarrow> (pr, 0, \<rho>) \<in> set (wdot0 G)\<close>
  unfolding wdot0_def by (cases \<rho>) force+

lemma length_wdot0: \<open>length (wdot0 G) = length (iprods G) * 6\<close>
proof -
  have \<open>length (concat (map (\<lambda>pr. [(pr, 0, WEq), (pr, 0, WGe), (pr, 0, WGt),
        (pr, 0, WLe), (pr, 0, WLt), (pr, 0, WAny)]) ps)) = length ps * 6\<close>
    for ps :: \<open>('n \<times> ('n, 't) rhs) list\<close>
    by (induction ps) auto
  then show ?thesis unfolding wdot0_def by simp
qed

lemma wcontrib_simp:
  \<open>wcontrib G (pr, m, \<rho>) =
      (if m < length (snd pr)
       then (case fst (snd pr ! m) of
              Nt B \<Rightarrow> map (\<lambda>br. (br, 0, wcomp (winv (w_of (snd (snd pr ! m)))) \<rho>))
                      (filter (\<lambda>br. fst br = B) (iprods G))
            | Tm _ \<Rightarrow> [])
       else [])\<close>
  unfolding wcontrib_def by simp

lemma wcontrib_dot0:
  assumes \<open>y \<in> set (wcontrib G x)\<close>
  shows \<open>y \<in> set (wdot0 G)\<close>
proof -
  obtain pr m \<rho> where x: \<open>x = (pr, m, \<rho>)\<close> by (cases x) auto
  show ?thesis
  proof (cases \<open>m < length (snd pr)\<close>)
    case False
    then show ?thesis using assms unfolding x wcontrib_simp by simp
  next
    case True
    show ?thesis
    proof (cases \<open>fst (snd pr ! m)\<close>)
      case (Tm a)
      then show ?thesis using assms True unfolding x wcontrib_simp by simp
    next
      case (Nt B)
      have \<open>y \<in> set (map (\<lambda>br. (br, 0, wcomp (winv (w_of (snd (snd pr ! m)))) \<rho>))
                     (filter (\<lambda>br. fst br = B) (iprods G)))\<close>
        using assms True Nt unfolding x wcontrib_simp by simp
      then obtain br where br: \<open>br \<in> set (iprods G)\<close>
        and yeq: \<open>y = (br, 0, wcomp (winv (w_of (snd (snd pr ! m)))) \<rho>)\<close> by auto
      show ?thesis unfolding yeq by (rule wdot0_mem[OF br])
    qed
  qed
qed
lemma wreach_step_delta: \<open>set (wreach_step G xs) \<subseteq> set xs \<union> set (wdot0 G)\<close>
  by (auto simp: wreach_step_set dest: wcontrib_dot0)

subsection \<open>Hence the fuelled \<^const>\<open>wreach\<close> is saturated\<close>

theorem wreach_stable: \<open>set (wreach_step G (wreach G s)) = set (wreach G s)\<close>
  unfolding wreach_def
proof (rule funpow_saturates_delta[where D = \<open>set (wdot0 G)\<close>])
  show \<open>\<And>xs ys. set xs = set ys \<Longrightarrow> set (wreach_step G xs) = set (wreach_step G ys)\<close>
    by (rule wreach_step_ext)
  show \<open>\<And>xs. set xs \<subseteq> set (wreach_step G xs)\<close> by (rule wreach_step_mono)
  show \<open>\<And>xs. set (wreach_step G xs) \<subseteq> set xs \<union> set (wdot0 G)\<close>
    by (rule wreach_step_delta)
  show \<open>finite (set (wdot0 G))\<close> by simp
  show \<open>card (set (wdot0 G)) \<le> Suc (length (iprods G) * 6)\<close>
    using card_length[of \<open>wdot0 G\<close>] length_wdot0[of G] by simp
qed

lemma funpow_wreach_mono: \<open>set xs \<subseteq> set ((wreach_step G ^^ k) xs)\<close>
proof (induction k)
  case (Suc k)
  have \<open>set ((wreach_step G ^^ k) xs) \<subseteq> set ((wreach_step G ^^ Suc k) xs)\<close>
    using wreach_step_mono by simp
  with Suc show ?case by simp
qed simp

lemma wreach_kernel: \<open>set (wkernel s) \<subseteq> set (wreach G s)\<close>
  unfolding wreach_def by (rule funpow_wreach_mono)

text \<open>\<^const>\<open>wreach\<close> is saturated, so it contains everything one
  \<^const>\<open>wreach_step\<close> would add.\<close>

lemma wreach_emit:
  assumes mem: \<open>(pr', m', \<rho>') \<in> set (wreach G s)\<close>
    and m_lt: \<open>m' < length (snd pr')\<close>
    and nxt: \<open>fst (snd pr' ! m') = Nt (fst br)\<close>
    and br: \<open>br \<in> set (iprods G)\<close>
  shows \<open>(br, 0, wcomp (winv (w_of (snd (snd pr' ! m')))) \<rho>') \<in> set (wreach G s)\<close>
proof -
  have \<open>(br, 0, wcomp (winv (w_of (snd (snd pr' ! m')))) \<rho>')
        \<in> set (wcontrib G (pr', m', \<rho>'))\<close>
    unfolding wcontrib_simp using m_lt nxt br by simp
  then have \<open>(br, 0, wcomp (winv (w_of (snd (snd pr' ! m')))) \<rho>')
        \<in> set (wreach_step G (wreach G s))\<close>
    using mem by (auto simp: wreach_step_set)
  then show ?thesis unfolding wreach_stable .
qed

section \<open>The item-relative conflict analysis: diagnosis\<close>

text \<open>Why the entry-relative walk below cannot separate the remaining
  states, on chunk T's state after \<open>"type" LId TVars\<close> (state 7 of
  \<^const>\<open>pr0_states\<close>; \<open>parser/conflicts.md\<close> \<section>9).  Its kernel holds
  \<open>Spec = "type"\<^sup>= LId\<^sup>> TVars\<^sup>> \<cdot>\<close>, the same production continued by
  \<open>"=" Ty\<close>, and \<open>TVars = TVars\<^sup>\<ge> \<cdot> LId\<^sup>\<ge>\<close>.  The entry anchor is the anchor
  of the \<open>TVars\<close> subtree just read, and \<^const>\<open>wreach\<close> relates it to each
  item's own indentation: \<open>WGt\<close> for the two \<open>Spec\<close> items (\<open>TVars\<^sup>>\<close>), \<open>WGe\<close>
  for the \<open>TVars\<close> item (\<open>TVars\<^sup>\<ge>\<close>).  The shift cell on \<open>LId\<close> composes the
  inverse of that \<open>WGe\<close> with the element relation \<open>LId\<^sup>\<ge>\<close>:
  \<open>wcomp WLe WGe = WAny\<close>.  The token is at or right of the inner \<open>TVars\<close>'
  indentation, which is at or left of the anchor; nothing relates the token
  to the anchor.  The reduce seeds on \<open>LId\<close> are the cells \<open>WEq\<close> (the next
  spec of the same block) and \<open>WLt\<close> (the next spec of an enclosing block,
  through \<open>"module" UId ":" Sig\<^sup>>\<close>), each composed with \<open>winv WGt\<close>: \<open>WLt\<close>.
  So the pair at the state is \<open>(WLt, WAny)\<close>, and no entry further back
  recovers a class from \<open>WAny\<close>.  The \<open>WAny\<close> is the item's: the shift side
  is a relation to the \<open>TVars\<close> item's indentation, the reduce side a
  relation to the \<open>Spec\<close> item's, and the entry anchor is \<open>\<ge>\<close>-related to
  the one and \<open>>\<close>-related to the other, so the anchor is the wrong
  quantity to express either against.

  Expressed against the \<open>Spec\<close> item's own indentation both sides are
  exact.  The reduce side already is: a cell relates the lookahead's column
  to the completed item's left-hand-side indentation (\<open>WEq\<close>, \<open>WLt\<close>).  The
  shift side is translated through the items that predicted it.  The
  \<open>TVars\<close> item at dot 1 was predicted one entry back, in the state after
  \<open>"type" LId\<close> (state 8), whose kernel is the two \<open>Spec\<close> items at dot 2; the
  predictors of \<open>TVars\<close> in that state's closure are those two items (through
  \<open>TVars\<^sup>>\<close>: the \<open>TVars\<close> indentation is strictly right of the \<open>Spec\<close>'s) and
  the \<open>TVars\<close> item itself (left recursion through \<open>TVars\<^sup>\<ge>\<close>, which only
  repeats).  The shift side becomes \<open>wcomp WGt WGe = WGt\<close> against the
  \<open>Spec\<close> item's indentation, the reduce side is \<open>WEq\<close> or \<open>WLt\<close> against the
  same item's indentation, popped along the same entry, and the two are
  \<^const>\<open>wdisjoint\<close>.

  The comparison is sound because the reference is one column.  \<open>Spec\<close> is
  anchored (\<open>anchored_nts\<close> below: \<open>"type"\<^sup>=\<close>), so in the real frame every  \<open>Spec\<close> item at a dot \<open>\<ge> 1\<close> has the singleton pool \<open>{column of "type"}\<close>,
  and two such items at the same dot in the same frame read that \<open>"type"\<close>
  at the same entry; both sides' relations hold at that column, a disjoint
  pair is impossible.  At a nonterminal whose pool is not a singleton the
  two sides may be satisfied at different pool elements and disjointness
  proves nothing: that is the two-action layout of the unpinned \<open>Ctor\<close> and
  \<open>ArrTail\<close> of \<open>conflicts.md\<close> \<section>8, which the grammar now pins
  (\<open>rationale.md\<close> 57).  The other sound reference is the start item at the
  start state, whose pool is \<open>{istart_ind}\<close>.

  The walk that follows from this (the next section): a triple is a state
  with two cursors, each an item of the state's closure and a class relating
  the lookahead's column to the item's left-hand-side indentation.  A cursor
  at dot 0 is replaced by its predictors in the same state, the class
  The walk that follows from this (the next section): a triple is a state
  with two cursors, each an item of the state's closure and a class relating
  the lookahead's column to the item's left-hand-side indentation.  A cursor
  at dot 0 is replaced by its predictors in the same state, the class
  composed with the predicted position's relation; two cursors at kernel
  items pop one entry along the same edge of the precise automaton (the
  entry symbol is the symbol before both dots), the classes unchanged, and
  where that entry is rigid both are first read against its column and a
  disjoint pair is refuted.  The \<open>Spec\<close> pair above is refuted one pop later,
  at the state entered over \<open>"type"\<close>.  At the start state both cursors predict
  up to the start item and are compared there.  No entry anchor, no
  \<open>rho_classes\<close>, no \<open>tm_classes\<close>.\<close>

section \<open>The item-relative conflict analysis\<close>

text \<open>Comparing the two sides of a candidate pair against a single shared
  state anchor is unsound for \<^const>\<open>mdet\<close>: a reduce-built frame pools
  entry anchors, and the two sides can be live via different ones.  The
  comparison is sound only where both sides are read against one column: the
  column of a shifted token, the anchor of an anchored nonterminal, or
  \<open>istart_ind\<close> at the start state.  So the analysis keeps each side on its
  item.  A cursor is a \<^typ>\<open>('n, 't) witem\<close> read item-relatively: in
  \<open>(pr, m, \<sigma>)\<close> the class \<open>\<sigma>\<close> relates the lookahead's column to the
  indentation of the instance of \<open>pr\<close>'s left-hand side the item stands for.
  A reduce seed is the completed item with its cell's relation, a shift seed
  the item whose dotted terminal is the lookahead, with that terminal's
  relation.  The walk goes back through the entries of the precise automaton
  as far as the start state: a cursor at dot 0 moves to the items that
  predicted it (the predicting position's relation composes, the state stays);
  two cursors at kernel items move together to every predecessor along the
  state's entry, unchanged.  \<^const>\<open>wdisjoint\<close> runs where the entry is
  rigid, both cursors read against the entry's column through the relation
  of the symbol before their dots: a disjoint pair refutes the path, a pair
  that is not disjoint walks on, since the entry that separates the two
  sides may lie further back.  A pair that reaches the start item undisjoint
  is a conflict.  The walk is a worklist over triples (state, cursor,
  cursor) in a finite space; exhausted fuel reports a conflict, and so does a
  triple with both classes \<open>WAny\<close>: nothing composes out of \<open>WAny\<close>, so
  every descendant of such a triple is one, none is disjoint, and the walk
  would only reach the start item undisjoint; returning at once saves the
  walk.\<close>

text \<open>The analysis runs over the precise automaton (\<^const>\<open>pr0_states\<close>
  with the \<^const>\<open>pgtab\<close> gotos and the \<^const>\<open>la_fix\<close> cells): these
  are the driver's own tables, so a cell that licenses a runtime reduce is one
  of the cells inspected here.\<close>

definition pin_edges :: \<open>(('n, 't) sym \<times> nat) list list \<Rightarrow> nat \<Rightarrow>
    (nat \<times> ('n, 't) sym) list\<close> where
  \<open>pin_edges gt s = concat (map (\<lambda>p.
       map (\<lambda>(X, s'). (p, X)) (filter (\<lambda>(X, s'). s' = s) (gt ! p)))
     [0..<length gt])\<close>

text \<open>All static reads below use \<^const>\<open>wreach\<close>, the form the saturation
  lemmas of this theory speak about; the classes it carries are not used.\<close>

text \<open>A nonterminal \<open>A\<close> is \<open>anchored\<close> when every \<open>A\<close>-production starts with
  an \<open>Eq\<close>-related element that is a terminal or itself an anchored
  nonterminal: any tree of \<open>A\<close> then admits exactly one anchor, the column of
  its leftmost token (cf. the \<open>anchored\<close>/\<open>lead_refl\<close> analysis of
  \<open>Indentation_Sensitive\<close> section 4).  A reduce-goto over an anchored
  nonterminal therefore carries a \<open>rigid\<close> entry anchor, a token column
  shared by both sides of a pair, and the \<^const>\<open>wdisjoint\<close> comparison
  is sound there, as at a shift entry.  Computed as a decreasing fixpoint
  from the full nonterminal list.\<close>

definition anchored_nts :: \<open>('n, 't) is_cfg \<Rightarrow> 'n list\<close> where
  \<open>anchored_nts G = (let nts = remdups (map fst (iprods G));
       ok = (\<lambda>S (B, rhs). rhs \<noteq> [] \<and> snd (hd rhs) = Eq \<and>
               (case fst (hd rhs) of Tm _ \<Rightarrow> True | Nt B' \<Rightarrow> B' \<in> set S));
       step = (\<lambda>S. filter (\<lambda>A. list_all (\<lambda>p. fst p \<noteq> A \<or> ok S p) (iprods G)) S)
   in (step ^^ length nts) nts)\<close>

definition irigid :: \<open>'n list \<Rightarrow> ('n, 't) sym \<Rightarrow> bool\<close> where
  \<open>irigid anc X \<longleftrightarrow> (case X of Tm _ \<Rightarrow> True | Nt B \<Rightarrow> B \<in> set anc)\<close>

text \<open>The walk reads the states' closures from \<open>wrs\<close>, the list of their
  \<^const>\<open>wreach\<close> lists, computed once for all states.  The cursors that
  predicted an \<open>A\<close>-item at dot 0 in state \<open>s\<close>: the items of \<open>s\<close> with
  \<open>Nt A\<close> at the dot, the class composed with that position's relation (the
  predicted indentation relates by it to the predictor's).\<close>

definition ipreds :: \<open>('n, 't) witem list list \<Rightarrow> nat \<Rightarrow> 'n \<Rightarrow> wrel \<Rightarrow>
    ('n, 't) witem list\<close> where
  \<open>ipreds wrs s A \<sigma> = remdups (List.map_filter (\<lambda>(pr, m, _).
      if m < length (snd pr) \<and> fst (snd pr ! m) = Nt A
      then Some (pr, m, wcomp (w_of (snd (snd pr ! m))) \<sigma>) else None)
      (wrs ! s))\<close>

text \<open>Whether a closure holds an item, in any class.\<close>

definition ihas :: \<open>('n, 't) witem list \<Rightarrow> 'n \<times> ('n, 't) rhs \<Rightarrow> nat \<Rightarrow> bool\<close> where
  \<open>ihas ws pr m \<longleftrightarrow> list_ex (\<lambda>(pr', m', _). pr' = pr \<and> m' = m) ws\<close>

text \<open>A kernel cursor read against the column of the state's entry, through
  the relation of the symbol before its dot (the kernel item's pool was
  filtered by that relation against the entry pool).\<close>

definition itrans :: \<open>('n, 't) witem \<Rightarrow> wrel\<close> where
  \<open>itrans = (\<lambda>(pr, m, \<sigma>). wcomp (winv (w_of (snd (snd pr ! (m - 1))))) \<sigma>)\<close>

text \<open>The walk's terminal triples: both classes \<open>WAny\<close>; two cursors on the
  start item that are not disjoint against \<open>istart_ind\<close>; a triple no frame
  can hold (one cursor on the start item, the other at a kernel item; two
  kernel items with different symbols before the dot), reported rather than
  carrying a proof that it is dead, which the precise automaton never
  produces.  Two cursors on the start item that are disjoint have no
  successor.\<close>

fun ifires :: \<open>'n \<Rightarrow> 'n list \<Rightarrow> nat \<times> ('n, 't) witem \<times> ('n, 't) witem \<Rightarrow> bool\<close> where
  \<open>ifires Shn anc (s, (pr\<^sub>1, m\<^sub>1, \<sigma>\<^sub>1), (pr\<^sub>2, m\<^sub>2, \<sigma>\<^sub>2)) \<longleftrightarrow>
     \<sigma>\<^sub>1 = WAny \<and> \<sigma>\<^sub>2 = WAny \<or>
     (if m\<^sub>1 = 0 \<and> fst pr\<^sub>1 = Shn \<and> m\<^sub>2 = 0 \<and> fst pr\<^sub>2 = Shn then \<not> wdisjoint \<sigma>\<^sub>1 \<sigma>\<^sub>2
      else if m\<^sub>1 = 0 \<and> fst pr\<^sub>1 \<noteq> Shn \<or> m\<^sub>2 = 0 \<and> fst pr\<^sub>2 \<noteq> Shn then False
      else m\<^sub>1 = 0 \<or> m\<^sub>2 = 0 \<or> fst (snd pr\<^sub>1 ! (m\<^sub>1 - 1)) \<noteq> fst (snd pr\<^sub>2 ! (m\<^sub>2 - 1)))\<close>

text \<open>The successors of a triple: the left cursor at dot 0 predicted first,
  then the right; two kernel cursors with the same symbol before the dot pop
  together along every entry of the state whose source state holds both
  popped items, unless the entry is rigid and they are disjoint against its
  column.\<close>

fun isuccs :: \<open>'n \<Rightarrow> ('n, 't) witem list list \<Rightarrow> (('n, 't) sym \<times> nat) list list \<Rightarrow>
    'n list \<Rightarrow> nat \<times> ('n, 't) witem \<times> ('n, 't) witem \<Rightarrow>
    (nat \<times> ('n, 't) witem \<times> ('n, 't) witem) list\<close>
  where
  \<open>isuccs Shn wrs gt anc (s, (pr\<^sub>1, m\<^sub>1, \<sigma>\<^sub>1), (pr\<^sub>2, m\<^sub>2, \<sigma>\<^sub>2)) =
     (if m\<^sub>1 = 0 \<and> fst pr\<^sub>1 = Shn \<and> m\<^sub>2 = 0 \<and> fst pr\<^sub>2 = Shn then []
      else if m\<^sub>1 = 0 \<and> fst pr\<^sub>1 \<noteq> Shn
      then map (\<lambda>c. (s, c, (pr\<^sub>2, m\<^sub>2, \<sigma>\<^sub>2))) (ipreds wrs s (fst pr\<^sub>1) \<sigma>\<^sub>1)
      else if m\<^sub>2 = 0 \<and> fst pr\<^sub>2 \<noteq> Shn
      then map (\<lambda>c. (s, (pr\<^sub>1, m\<^sub>1, \<sigma>\<^sub>1), c)) (ipreds wrs s (fst pr\<^sub>2) \<sigma>\<^sub>2)
      else if m\<^sub>1 = 0 \<or> m\<^sub>2 = 0 then []
      else (let X = fst (snd pr\<^sub>1 ! (m\<^sub>1 - 1)) in
        if X \<noteq> fst (snd pr\<^sub>2 ! (m\<^sub>2 - 1)) \<or>
           irigid anc X \<and> wdisjoint (itrans (pr\<^sub>1, m\<^sub>1, \<sigma>\<^sub>1)) (itrans (pr\<^sub>2, m\<^sub>2, \<sigma>\<^sub>2))
        then []
        else List.map_filter (\<lambda>(p, X'). if X' = X \<and>
               ihas (wrs ! p) pr\<^sub>1 (m\<^sub>1 - 1) \<and> ihas (wrs ! p) pr\<^sub>2 (m\<^sub>2 - 1)
               then Some (p, (pr\<^sub>1, m\<^sub>1 - 1, \<sigma>\<^sub>1), (pr\<^sub>2, m\<^sub>2 - 1, \<sigma>\<^sub>2)) else None)
             (pin_edges gt s)))\<close>

text \<open>The walk: a worklist with a seen set, each triple popped at most once.\<close>

primrec ifire :: \<open>'n \<Rightarrow> ('n, 't) witem list list \<Rightarrow> (('n, 't) sym \<times> nat) list list \<Rightarrow>
    'n list \<Rightarrow> nat \<Rightarrow> (nat \<times> ('n, 't) witem \<times> ('n, 't) witem) list \<Rightarrow>
    (nat \<times> ('n, 't) witem \<times> ('n, 't) witem) list \<Rightarrow> bool\<close> where
  \<open>ifire Shn wrs gt anc 0 seen work = True\<close>
| \<open>ifire Shn wrs gt anc (Suc n) seen work =
     (case work of
        [] \<Rightarrow> False
      | t # wk \<Rightarrow>
          if ifires Shn anc t then True
          else ifire Shn wrs gt anc n (t # seen)
            (filter (\<lambda>t'. t' \<notin> set (t # seen) \<and> t' \<notin> set wk)
               (remdups (isuccs Shn wrs gt anc t)) @ wk))\<close>

lemma ifire_Nil [simp]: \<open>ifire Shn wrs gt anc (Suc n) seen [] = False\<close>
  by simp

lemma ifire_Cons [simp]:
  \<open>ifire Shn wrs gt anc (Suc n) seen (t # wk) =
     (if ifires Shn anc t then True
      else ifire Shn wrs gt anc n (t # seen)
        (filter (\<lambda>t'. t' \<notin> set (t # seen) \<and> t' \<notin> set wk)
           (remdups (isuccs Shn wrs gt anc t)) @ wk))\<close>
  by simp

text \<open>Fuel for the triples the walk can visit: both cursors of a triple at
  state \<open>s\<close> are items of \<open>s\<close>'s closure (the seeds and the predictions are
  drawn from it, a pop is kept only if its target holds both items), each in
  one of six classes, and the worklist pops a triple at most once.  Naturals
  are unary in the generated code, so the bound is the sum over the states of
  the squared item counts, not a square of the grammar's size.\<close>

definition ifuel :: \<open>('n, 't) witem list list \<Rightarrow> nat\<close> where
  \<open>ifuel wrs = Suc (36 * sum_list (map (\<lambda>ws.
     let n = length (remdups (map (\<lambda>(pr, m, _). (pr, m)) ws)) in n * n) wrs))\<close>

text \<open>Reduce seeds at a state: one per cell of a production completed in the
  precise closure, the cursor's class the cell's own relation; the lookahead
  stays with it.  A completed production the precise context excludes seeds
  nothing; the runtime's anchor filtering excludes it dynamically.\<close>

definition ireds_at :: \<open>('n, 't) is_cfg \<Rightarrow> 'n \<Rightarrow> ('n, 't) citem list list \<Rightarrow>
    ('n, 't) lacell list \<Rightarrow> nat \<Rightarrow> ('t option \<times> ('n, 't) witem) list\<close> where
  \<open>ireds_at G Shn sp L i =
     (let ws = wreach G (sp ! i)
      in List.map_filter (\<lambda>(i', (pr, m), t, \<tau>).
           if i' = i \<and> m = length (snd pr) \<and> fst pr \<noteq> Shn \<and>
              list_ex (\<lambda>(pr', m', \<rho>). pr' = pr \<and> m' = m) ws
           then Some (t, (pr, m, \<tau>)) else None) L)\<close>

text \<open>Shift seeds: the items with a terminal at the dot, the class that
  terminal's relation.\<close>

definition ishifts :: \<open>('n, 't) witem list \<Rightarrow> ('t \<times> ('n, 't) witem) list\<close> where
  \<open>ishifts ws = remdups (List.map_filter (\<lambda>(pr, m, \<rho>).
      if m < length (snd pr)
      then (case fst (snd pr ! m) of
             Tm a \<Rightarrow> Some (a, (pr, m, w_of (snd (snd pr ! m)))) | Nt _ \<Rightarrow> None)
      else None) ws)\<close>

definition rr_none_at :: \<open>('n, 't) is_cfg \<Rightarrow> 'n \<Rightarrow> ('n, 't) citem list list \<Rightarrow>
    ('n, 't) lacell list \<Rightarrow> nat \<Rightarrow> bool\<close> where
  \<open>rr_none_at G Shn sp L i =
     (let reds = ireds_at G Shn sp L i
      in list_ex (\<lambda>(t, c). t = None \<and>
           list_ex (\<lambda>(t', c'). fst c' \<noteq> fst c \<and> t' = None) reds) reds)\<close>

definition ipairs_at :: \<open>('n, 't) is_cfg \<Rightarrow> 'n \<Rightarrow> ('n, 't) citem list list \<Rightarrow>
    ('n, 't) lacell list \<Rightarrow> nat \<Rightarrow> (('n, 't) witem \<times> ('n, 't) witem) list\<close> where
  \<open>ipairs_at G Shn sp L i =
     (let reds = ireds_at G Shn sp L i;
          shifts = ishifts (wreach G (sp ! i));
          srs = concat (map (\<lambda>(t, c). case t of
              Some a \<Rightarrow> map (\<lambda>(a', c'). (c, c')) (filter (\<lambda>(a', c'). a' = a) shifts)
            | None \<Rightarrow> []) reds);
          rrs = concat (map (\<lambda>(t, c). List.map_filter (\<lambda>(t', c').
                 if fst c' \<noteq> fst c \<and> t' = t \<and> t \<noteq> None then Some (c, c') else None) reds)
                 reds)
      in remdups (srs @ rrs))\<close>

definition rlalr_conflict_at :: \<open>('n, 't) is_cfg \<Rightarrow> 'n \<Rightarrow> ('n, 't) citem list list \<Rightarrow>
    ('n, 't) lacell list \<Rightarrow> nat \<Rightarrow> bool\<close> where
  \<open>rlalr_conflict_at G Shn sp L i \<longleftrightarrow>
     rr_none_at G Shn sp L i \<or>
     list_ex (\<lambda>(c\<^sub>1, c\<^sub>2). ifire Shn (map (wreach G) sp) (pgtab G sp) (anchored_nts G)
         (ifuel (map (wreach G) sp)) [] [(i, c\<^sub>1, c\<^sub>2)])
       (ipairs_at G Shn sp L i)\<close>

definition rlalr_conflicts :: \<open>('n, 't) is_cfg \<Rightarrow> 'n \<Rightarrow> nat list\<close> where
  \<open>rlalr_conflicts G Shn = (let sp = pr0_states G Shn; L = la_fix G Shn in
     filter (rlalr_conflict_at G Shn sp L) [0..<length sp])\<close>

section \<open>From a determinism violation to concrete witnesses\<close>

text \<open>Eliminations for the sufficiency proof: the negation of
  \<^const>\<open>mdet\<close> yields concrete witnesses, the cell that licensed each
  reduce candidate and the closure item and anchor that keep each successor
  alive.\<close>

lemma liveE:
  assumes \<open>live xs\<close>
  obtains pr m R j where \<open>(pr, m, R) \<in> set xs\<close> and \<open>j \<in> irep_set R\<close>
  using assms that unfolding live_def
  by (fastforce simp: list_ex_iff)

lemma dliveE:
  assumes \<open>dlive (Xs, w)\<close>
  obtains pr m R j where \<open>Xs \<noteq> []\<close> and \<open>(pr, m, R) \<in> set (hd Xs)\<close>
    and \<open>j \<in> irep_set R\<close>
  using assms that unfolding dlive_def by (auto elim: liveE)

lemma dlicE:
  assumes \<open>dlic i cells ((a, c) # w') pr RS\<close>
  obtains \<tau> where \<open>(i, (pr, length (snd pr)), Some a, \<tau>) \<in> set cells\<close>
    and \<open>irep_ex_wsat \<tau> c RS\<close>
  using assms that unfolding dlic_def by (fastforce simp: list_ex_iff)

lemma dlic_NilE:
  assumes \<open>dlic i cells [] pr RS\<close>
  obtains \<tau> where \<open>(i, (pr, length (snd pr)), None, \<tau>) \<in> set cells\<close>
  using assms that unfolding dlic_def by (fastforce simp: list_ex_iff)

text \<open>A live shift successor yields a closure item with the shifted terminal
  at its dot and an anchor compatible with the token's column.\<close>

lemma shift_live_srcE:
  assumes step: \<open>mstep_cached G cstk (Xs, w) DShift = Some gc'\<close>
    and live: \<open>dlive gc'\<close>
  obtains a c w' pr m R j where
    \<open>w = (a, c) # w'\<close>
    and \<open>(pr, m, R) \<in> set (hd cstk)\<close>
    and \<open>m < length (snd pr)\<close>
    and \<open>fst (snd pr ! m) = Tm a\<close>
    and \<open>j \<in> irep_set R\<close>
    and \<open>irel_sat (snd (snd pr ! m)) c j\<close>
proof -
  from step obtain a c w' where
    w: \<open>w = (a, c) # w'\<close> and Xs_ne: \<open>Xs \<noteq> []\<close>
    and gc': \<open>gc' = (lgoto (hd cstk) (Tm a) (FinRep [c]) # Xs, w')\<close>
    by (rule mstep_shift_shape)
  from live obtain pr m' R' j where
    itm: \<open>(pr, m', R') \<in> set (lgoto (hd cstk) (Tm a) (FinRep [c]))\<close>
    and jR': \<open>j \<in> irep_set R'\<close>
    unfolding gc' by (auto elim: dliveE)
  obtain m where m': \<open>m' = Suc m\<close> using lgoto_dot_pos[OF itm] by (cases m') auto
  from lgoto_kernel_step[OF itm[unfolded m']] obtain R where
    src: \<open>(pr, m, R) \<in> set (hd cstk)\<close> and m_lt: \<open>m < length (snd pr)\<close>
    and sym: \<open>fst (snd pr ! m) = Tm a\<close>
    and R': \<open>R' = irep_inter R (irep_pre (snd (snd pr ! m)) (FinRep [c]))\<close> .
  have jR: \<open>j \<in> irep_set R\<close> and jrel: \<open>irel_sat (snd (snd pr ! m)) c j\<close>
    using jR' unfolding R' by auto
  from that[OF w src m_lt sym jR jrel] show thesis .
qed

section \<open>Tracking a reachable configuration\<close>

text \<open>The dynamic half of the sufficiency argument: every configuration the
  indexed machine reaches is tracked, frame by frame, by the driver's own
  index stack under \<^const>\<open>didx_ok\<close>.  A frame owes its obligations only
  where it has a \<open>live\<close> (anchored) item: a dead frame never contributes a
  candidate, and by \<open>xclosure_auto_live_creach\<close> over the empty kernel a
  dead kernel has a dead closure.  Where the pushed frame is live the table's
  goto is the canonical successor index, so the index stack also records the
  goto history the descent below walks.\<close>

lemma dnext_st_find:
  assumes tab: \<open>tables_ok G Shn sts gt L\<close>
    and ok: \<open>didx_ok G sts Xs istk\<close>
    and d_lt: \<open>d < length Xs\<close>
    and live: \<open>lcore (lgoto (xclosure_auto G (Xs ! d)) X RA) \<noteq> {}\<close>
  shows \<open>dnext gt sts (istk ! d) X = st_find sts (cgoto (creach G (sts ! (istk ! d))) X)\<close>
proof -
  from live obtain pr\<^sub>0 n\<^sub>0 R\<^sub>0' j\<^sub>0 where
    g0: \<open>(pr\<^sub>0, n\<^sub>0, R\<^sub>0') \<in> set (lgoto (xclosure_auto G (Xs ! d)) X RA)\<close>
    and j0: \<open>j\<^sub>0 \<in> irep_set R\<^sub>0'\<close>
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
  have lookup0: \<open>map_of (gt ! (istk ! d)) (fst (snd pr\<^sub>0 ! m\<^sub>0)) =
      Some (st_find sts (cgoto (creach G (sts ! (istk ! d))) (fst (snd pr\<^sub>0 ! m\<^sub>0))))\<close>
    using tab p_lt src0_cr m0_lt unfolding tables_ok_def by blast
  have lookup: \<open>map_of (gt ! (istk ! d)) X =
      Some (st_find sts (cgoto (creach G (sts ! (istk ! d))) X))\<close>
    using lookup0 unfolding X0 .
  have gt_len: \<open>length gt = length sts\<close> using tab unfolding tables_ok_def by blast
  show ?thesis
    unfolding dnext_def la_next_def lookup option.case
    using p_lt gt_len by (simp add: min_def st_find_le)
qed

text \<open>A cell of the driver's reduce bucket \<open>i\<close> is a completed cell of
  \<^const>\<open>la_fix\<close> at index \<open>i\<close>.\<close>

lemma red_buckets_memD:
  assumes \<open>i < n\<close> and \<open>c \<in> set (red_buckets G Shn n ! i)\<close>
  shows \<open>c \<in> set (la_fix G Shn) \<and> fst c = i \<and>
         (case c of (i', itm, t, \<tau>) \<Rightarrow> snd itm = length (snd (fst itm)))\<close>
  using assms unfolding red_buckets_def cell_buckets_def by (auto simp: Let_def)

section \<open>Accept/reduce conflicts\<close>

text \<open>The case \<^const>\<open>rlalr_conflicts\<close> ignores: the start production
  completed next to an end-of-input reduce cell of another production, the
  driver accepting where the relation of the grammar has a second value.\<close>

definition acc_conflicts :: \<open>('n, 't) is_cfg \<Rightarrow> 'n \<Rightarrow> nat list\<close> where
  \<open>acc_conflicts G Shn = (let sts = pr0_states G Shn in
     filter (\<lambda>i. (start_prod G Shn, Suc 0) \<in> set (sts ! i) \<and>
        list_ex (\<lambda>(i', (pr, m), t, \<tau>). i' = i \<and> m = length (snd pr) \<and>
                  t = None \<and> pr \<noteq> start_prod G Shn) (la_fix G Shn))
       [0..<length sts])\<close>

text \<open>Reducing by the start production is dead: nothing in the initial
  closure expects \<^term>\<open>Nt Shn\<close>.\<close>

lemma lgoto_xinit_Shn:
  assumes fn: \<open>fresh_name G Shn\<close>
  shows \<open>lgoto (xclosure_auto G (xinit G Shn)) (Nt Shn) RA = []\<close>
proof -
  have \<open>\<not> (m < length (snd pr) \<and> fst (snd pr ! m) = Nt Shn)\<close>
    if item: \<open>(pr, m, R) \<in> set (xclosure_auto G (xinit G Shn))\<close> for pr m R
  proof
    assume \<open>m < length (snd pr) \<and> fst (snd pr ! m) = Nt Shn\<close>
    then have m: \<open>m < length (snd pr)\<close> and X: \<open>fst (snd pr ! m) = Nt Shn\<close> by auto
    from dshape_prods[OF dshape_init, of 0 pr m R] item
    have \<open>pr \<in> set (iprods G) \<or> pr = start_prod G Shn\<close> by simp
    then show False
    proof
      assume prG: \<open>pr \<in> set (iprods G)\<close>
      have \<open>snd pr ! m \<in> set (snd pr)\<close> using m by simp
      with fn prG X show False
        unfolding fresh_name_def by (cases pr; cases \<open>snd pr ! m\<close>) fastforce
    next
      assume \<open>pr = start_prod G Shn\<close>
      with m X fn show False unfolding start_prod_def fresh_name_def by simp
    qed
  qed
  then show ?thesis unfolding lgoto_def by (auto simp: filter_empty_conv)
qed

lemma final_shape:
  assumes fn: \<open>fresh_name G Shn\<close>
    and inv: \<open>dinv G Shn w ((Xs, u), cstk, istk, v, tstk)\<close>
    and fin: \<open>gfinal G Shn (Xs, u)\<close>
  shows \<open>\<exists>X. Xs = [X, xinit G Shn]\<close>
proof -
  have fin': \<open>gfinal G Shn (fst ((Xs, u), cstk, istk, v, tstk))\<close> using fin by simp
  from dinv_final[OF fn inv fin'] obtain t where tstk: \<open>tstk = [t]\<close> by auto
  from inv obtain RAs where lenR: \<open>length RAs = length tstk\<close>
    and sh: \<open>dshape G Shn Xs (zip (map asym tstk) RAs)\<close>
    unfolding dinv_def by auto
  have \<open>length Xs = 2\<close> \<open>Xs ! 1 = xinit G Shn\<close>
    using sh lenR tstk unfolding dshape_def by auto
  then show ?thesis
    by (cases Xs) (auto simp: length_Suc_conv)
qed

text \<open>With an empty accept/reduce report, no live reduce is offered at an
  accepting configuration.\<close>

lemma no_reduce_at_final:
  assumes fn: \<open>fresh_name G Shn\<close> and chk: \<open>acc_conflicts G Shn = []\<close>
    and inv: \<open>dinv G Shn w ((Xs, u), cstk, istk, v, tstk)\<close>
    and ok: \<open>didx_ok G (pr0_states G Shn) Xs istk\<close>
    and fin: \<open>gfinal G Shn (Xs, u)\<close>
    and cand: \<open>DReduce pr \<in> set (dcands G (hd istk)
                 (red_buckets G Shn (length (pr0_states G Shn)) ! hd istk)
                 (xclosure_auto G (hd Xs)) (Xs, u))\<close>
    and step: \<open>mstep G (Xs, u) (DReduce pr) = Some gc'\<close> and live: \<open>dlive gc'\<close>
  shows False
proof -
  let ?sts = \<open>pr0_states G Shn\<close> and ?i = \<open>hd istk\<close>
  from final_shape[OF fn inv fin] obtain X where Xs: \<open>Xs = [X, xinit G Shn]\<close> by blast
  have u: \<open>u = []\<close> using fin unfolding gfinal_def by simp
  have istk_ne: \<open>istk \<noteq> []\<close> using didx_ok_len[OF ok] Xs by auto
  from fin obtain pr\<^sub>0 R where item: \<open>(pr\<^sub>0, Suc 0, R) \<in> set X\<close> and Shn: \<open>fst pr\<^sub>0 = Shn\<close>
    and mem: \<open>irep_mem (istart_ind G) R\<close>
    unfolding gfinal_def Xs by (auto simp: list_ex_iff)
  have lv: \<open>(pr\<^sub>0, Suc 0) \<in> lcore X\<close> using lcoreI[OF item, of \<open>istart_ind G\<close>] mem by simp
  have i_lt: \<open>?i < length ?sts\<close> and cover: \<open>lcore X \<subseteq> set (?sts ! ?i)\<close>
    using didx_okD[OF ok, of 0] lv Xs istk_ne by (auto simp: hd_conv_nth)
  from inv obtain RAs where sh: \<open>dshape G Shn Xs (zip (map asym tstk) RAs)\<close>
    unfolding dinv_def by auto
  have item': \<open>(pr\<^sub>0, Suc 0, R) \<in> set (xclosure_auto G (Xs ! 0))\<close>
    using item xclosure_auto_kernel_sub Xs by fastforce
  have pr0: \<open>pr\<^sub>0 = start_prod G Shn\<close>
    using dshape_prods[OF sh _ item'] Shn fn unfolding fresh_name_def by force
  have acc: \<open>(start_prod G Shn, Suc 0) \<in> set (?sts ! ?i)\<close>
    using lv pr0 cover by blast
  from dcands_reduceD[OF cand]
  have \<open>dlic ?i (red_buckets G Shn (length ?sts) ! ?i) u pr (red_set (xclosure_auto G (hd Xs)) pr)\<close>
    by simp
  then obtain \<tau> where
      cell: \<open>(?i, (pr, length (snd pr)), None, \<tau>) \<in> set (red_buckets G Shn (length ?sts) ! ?i)\<close>
    unfolding dlic_def u by (auto simp: list_ex_iff)
  then have cellL: \<open>(?i, (pr, length (snd pr)), None, \<tau>) \<in> set (la_fix G Shn)\<close>
    by (rule red_buckets_memD[OF i_lt, THEN conjunct1])
  have ne: \<open>pr \<noteq> start_prod G Shn\<close>
  proof
    assume pr: \<open>pr = start_prod G Shn\<close>
    have \<open>gc' = (lgoto (xclosure_auto G (xinit G Shn)) (Nt Shn)
                   (red_set (xclosure_auto G X) pr) # [xinit G Shn], u)\<close>
      using step unfolding mstep_def mstep_cached_def Xs pr start_prod_def
      by (auto simp: Let_def split: if_splits)
    then have \<open>gc' = ([] # [xinit G Shn], u)\<close> by (simp add: lgoto_xinit_Shn[OF fn])
    with live show False unfolding dlive_def live_def by simp
  qed
  have \<open>?i \<in> set (acc_conflicts G Shn)\<close>
    unfolding acc_conflicts_def Let_def using i_lt acc cellL ne
    by (auto simp: list_ex_iff intro!: bexI[where x = \<open>(?i, (pr, length (snd pr)), None, \<tau>)\<close>])
  with chk show False by simp
qed

section \<open>Soundness of the item-relative walk: the worklist\<close>

text \<open>A \<open>False\<close> result of \<^const>\<open>ifire\<close> can only arise from an exhausted
  worklist (fuel exhaustion returns \<open>True\<close>), so it certifies that no triple
  the successor relation \<^const>\<open>isuccs\<close> reaches from the seed fires.  The
  worklist invariant: no seen triple fires, and every successor of a seen
  triple is seen or still to do.\<close>

lemma map_filterI:
  \<open>x \<in> set xs \<Longrightarrow> f x = Some y \<Longrightarrow> y \<in> set (List.map_filter f xs)\<close>
  unfolding List.map_filter_def by force

lemma concat_map_memI:
  \<open>x \<in> set xs \<Longrightarrow> y \<in> set (g x) \<Longrightarrow> y \<in> set (concat (map g xs))\<close>
  by auto

text \<open>The worklist's closure: when the walk returns \<open>False\<close>, the triples
  it saw form a set closed under \<^const>\<open>isuccs\<close> none of which fires.\<close>

lemma ifire_False_closed:
  assumes res: \<open>ifire Shn wrs gt anc n seen work = False\<close>
    and inv: \<open>\<forall>t \<in> set seen. \<not> ifires Shn anc t \<and>
        set (isuccs Shn wrs gt anc t) \<subseteq> set seen \<union> set work\<close>
  shows \<open>\<exists>S. set seen \<union> set work \<subseteq> S \<and>
    (\<forall>t \<in> S. \<not> ifires Shn anc t \<and> set (isuccs Shn wrs gt anc t) \<subseteq> S)\<close>
  using res inv
proof (induction n arbitrary: seen work)
  case 0
  then show ?case by simp
next
  case (Suc n)
  show ?case
  proof (cases work)
    case Nil
    with Suc.prems show ?thesis by (intro exI[of _ \<open>set seen\<close>]) auto
  next
    case (Cons t wk)
    have nf: \<open>\<not> ifires Shn anc t\<close> using Suc.prems Cons by (auto split: if_splits)
    have rec: \<open>ifire Shn wrs gt anc n (t # seen)
      (filter (\<lambda>t'. t' \<notin> set (t # seen) \<and> t' \<notin> set wk)
         (remdups (isuccs Shn wrs gt anc t)) @ wk) = False\<close>
      using Suc.prems Cons nf by simp
    have inv': \<open>\<forall>u \<in> set (t # seen). \<not> ifires Shn anc u \<and>
        set (isuccs Shn wrs gt anc u) \<subseteq> set (t # seen) \<union>
          set (filter (\<lambda>t'. t' \<notin> set (t # seen) \<and> t' \<notin> set wk)
            (remdups (isuccs Shn wrs gt anc t)) @ wk)\<close>
      using Suc.prems Cons nf by auto
    from Suc.IH[OF rec inv'] Cons show ?thesis by auto
  qed
qed

lemma ifire_False_sound:
  assumes res: \<open>ifire Shn wrs gt anc n seen work = False\<close>
    and inv: \<open>\<forall>t \<in> set seen. \<not> ifires Shn anc t \<and>
        set (isuccs Shn wrs gt anc t) \<subseteq> set seen \<union> set work\<close>
    and t0: \<open>t\<^sub>0 \<in> set seen \<union> set work\<close>
    and desc: \<open>(\<lambda>t t'. t' \<in> set (isuccs Shn wrs gt anc t))\<^sup>*\<^sup>* t\<^sub>0 t'\<close>
  shows \<open>\<not> ifires Shn anc t'\<close>
proof -
  obtain S where sub: \<open>set seen \<union> set work \<subseteq> S\<close>
    and cl: \<open>\<forall>t \<in> S. \<not> ifires Shn anc t \<and> set (isuccs Shn wrs gt anc t) \<subseteq> S\<close>
    using ifire_False_closed[OF res inv] by blast
  have \<open>t' \<in> S\<close>
    using desc t0 sub cl by (induction rule: rtranclp_induct) auto
  with cl show ?thesis by blast
qed

theorem ifire_sound:
  assumes res: \<open>ifire Shn wrs gt anc n [] [t\<^sub>0] = False\<close>
    and desc: \<open>(\<lambda>t t'. t' \<in> set (isuccs Shn wrs gt anc t))\<^sup>*\<^sup>* t\<^sub>0 t'\<close>
  shows \<open>\<not> ifires Shn anc t'\<close>
  using ifire_False_sound[OF res _ _ desc] by auto


section \<open>Stack shape along reachability, and anchor persistence\<close>

lemma dshapeD:
  assumes \<open>dshape G Shn Xs \<alpha>\<close>
  shows \<open>length Xs = length \<alpha> + 1\<close> and \<open>Xs ! length \<alpha> = xinit G Shn\<close>
    and \<open>\<And>k. k < length \<alpha> \<Longrightarrow>
      Xs ! k = lgoto (xclosure_auto G (Xs ! Suc k)) (fst (\<alpha> ! k)) (snd (\<alpha> ! k))\<close>
  using assms unfolding dshape_def by auto

text \<open>Every reachable stack is \<^const>\<open>dshape\<close>-shaped (part of the
  tracking invariant of \<^text>\<open>imreach_strack\<close> below): each frame is the
  \<^const>\<open>lgoto\<close> of the closure of the frame below, along a recorded goto
  history.  Anchors of a kernel item persist from its prediction: descending
  the dots, the item's anchor set only shrinks from the dot-0 slot in the
  closure of the frame where it was predicted.\<close>

lemma wkernel_memI:
  \<open>(pr, m) \<in> set s \<Longrightarrow>
   (pr, m, if m = 0 then WAny else w_of (snd (snd pr ! (m - 1)))) \<in> set (wkernel s)\<close>
  unfolding wkernel_def by force

lemma xclosure_auto_kernelD:
  assumes \<open>(pr, m, R) \<in> set (xclosure_auto G s)\<close> and \<open>1 \<le> m\<close>
  shows \<open>(pr, m, R) \<in> set s\<close>
proof -
  have \<open>(pr, m, R) \<in> set (xslots G s (xiter G s (xfuel G s)))\<close>
    using assms(1) unfolding xclosure_auto_def xclosure_def .
  then show ?thesis
  proof (rule xslots_memE)
    assume \<open>(pr, m, R) \<in> set s\<close> then show ?thesis .
  next
    fix q assume \<open>q < length (iprods G)\<close>
      and \<open>q < length (xiter G s (xfuel G s))\<close>
      and \<open>(pr, m, R) = (iprods G ! q, 0, xiter G s (xfuel G s) ! q)\<close>
    then show ?thesis using assms(2) by auto
  qed
qed

text \<open>A kernel item at dot \<open>m \<ge> 1\<close> in frame \<open>k\<close> descends to the dot-0 slot of
  the closure of frame \<open>k + m\<close>, its anchor set only shrinking.\<close>

lemma dshape_persist:
  assumes sh: \<open>dshape G Shn Xs \<alpha>\<close>
  shows \<open>(pr, m, R) \<in> set (Xs ! k) \<Longrightarrow> k < length Xs \<Longrightarrow> 1 \<le> m \<Longrightarrow>
     \<exists>R\<^sub>0. k + m < length Xs \<and> (pr, 0, R\<^sub>0) \<in> set (xclosure_auto G (Xs ! (k + m))) \<and>
           irep_set R \<subseteq> irep_set R\<^sub>0\<close>
proof (induction m arbitrary: k R)
  case 0
  then show ?case by simp
next
  case (Suc m)
  note lenX = dshapeD(1)[OF sh] and bot = dshapeD(2)[OF sh] and shp = dshapeD(3)[OF sh]
  have k_lt_a: \<open>k < length \<alpha>\<close>
  proof (rule ccontr)
    assume \<open>\<not> k < length \<alpha>\<close>
    then have \<open>k = length \<alpha>\<close> using Suc.prems(2) lenX by simp
    then have \<open>(pr, Suc m, R) \<in> set (xinit G Shn)\<close> using Suc.prems(1) bot by simp
    then show False unfolding xinit_def by auto
  qed
  have frame: \<open>Xs ! k = lgoto (xclosure_auto G (Xs ! Suc k)) (fst (\<alpha> ! k)) (snd (\<alpha> ! k))\<close>
    by (rule shp[OF k_lt_a])
  from lgoto_kernel_step[OF Suc.prems(1)[unfolded frame]] obtain R' where
    src: \<open>(pr, m, R') \<in> set (xclosure_auto G (Xs ! Suc k))\<close>
    and Req: \<open>R = irep_inter R' (irep_pre (snd (snd pr ! m)) (snd (\<alpha> ! k)))\<close> .
  have sub: \<open>irep_set R \<subseteq> irep_set R'\<close> unfolding Req by auto
  show ?case
  proof (cases m)
    case 0
    have \<open>Suc k < length Xs\<close> using k_lt_a lenX by simp
    then show ?thesis using src sub 0 by auto
  next
    case (Suc m')
    have m_pos: \<open>1 \<le> m\<close> using Suc by simp
    have src': \<open>(pr, m, R') \<in> set (xslots G (Xs ! Suc k)
        (xiter G (Xs ! Suc k) (xfuel G (Xs ! Suc k))))\<close>
      using src unfolding xclosure_auto_def xclosure_def .
    have kern: \<open>(pr, m, R') \<in> set (Xs ! Suc k)\<close>
      using src'
    proof (rule xslots_memE)
      assume \<open>(pr, m, R') \<in> set (Xs ! Suc k)\<close>
      then show ?thesis .
    next
      fix q assume \<open>q < length (iprods G)\<close>
        and \<open>q < length (xiter G (Xs ! Suc k) (xfuel G (Xs ! Suc k)))\<close>
        and \<open>(pr, m, R') = (iprods G ! q, 0, xiter G (Xs ! Suc k) (xfuel G (Xs ! Suc k)) ! q)\<close>
      then show ?thesis using Suc by auto
    qed
    have Sk_lt: \<open>Suc k < length Xs\<close> using k_lt_a lenX by simp
    from Suc.IH[OF kern Sk_lt m_pos] obtain R\<^sub>0 where
      \<open>Suc k + m < length Xs\<close>
      and s0: \<open>(pr, 0, R\<^sub>0) \<in> set (xclosure_auto G (Xs ! (Suc k + m)))\<close>
      and sub2: \<open>irep_set R' \<subseteq> irep_set R\<^sub>0\<close> by blast
    then show ?thesis using sub by fastforce
  qed
qed

section \<open>The pooled width invariant\<close>

text \<open>The per-item form of the width invariant: each anchored closure item
  relates to \<open>some\<close> element of the frame's entry pool \<open>P\<close> by a \<open>wreach\<close>
  class; different items may pick different pool elements, as the pooled
  machine's frames demand.  First the closure preservation, by
  induction on the round number of \<open>xiter\<close>: every step reuses its source's
  pool element.\<close>

lemma xiter_pool:
  assumes kern: \<open>\<And>pr m R j. (pr, m, R) \<in> set xs \<Longrightarrow> j \<in> irep_set R \<Longrightarrow>
      \<exists>\<rho> l. (pr, m, \<rho>) \<in> set (wreach G s) \<and> l \<in> P \<and> wsat \<rho> l j\<close>
  shows \<open>p < length (iprods G) \<Longrightarrow> j \<in> irep_set (xiter G xs t ! p) \<Longrightarrow>
     \<exists>\<rho> l. (iprods G ! p, 0, \<rho>) \<in> set (wreach G s) \<and> l \<in> P \<and> wsat \<rho> l j\<close>
proof (induction t arbitrary: p j)
  case 0
  then show ?case by simp
next
  case (Suc t)
  have len: \<open>length (xiter G xs t) = length (iprods G)\<close> by simp
  have \<open>xiter G xs (Suc t) ! p =
      fold (xcontrib (iprods G ! p)) (xslots G xs (xiter G xs t)) (xiter G xs t ! p)\<close>
    by (simp add: xround_nth[OF len Suc.prems(1)])
  with Suc.prems(2) have
    \<open>j \<in> irep_set (xiter G xs t ! p) \<or>
     (\<exists>xit \<in> set (xslots G xs (xiter G xs t)). j \<in> ximg (iprods G ! p) xit)\<close>
    by (simp add: fold_xcontrib_set)
  then show ?case
  proof
    assume \<open>j \<in> irep_set (xiter G xs t ! p)\<close>
    from Suc.IH[OF Suc.prems(1) this] show ?thesis .
  next
    assume \<open>\<exists>xit \<in> set (xslots G xs (xiter G xs t)). j \<in> ximg (iprods G ! p) xit\<close>
    then obtain xit where xit: \<open>xit \<in> set (xslots G xs (xiter G xs t))\<close>
      and jimg: \<open>j \<in> ximg (iprods G ! p) xit\<close> by blast
    obtain pr' m' R' where xeq: \<open>xit = (pr', m', R')\<close> by (cases xit) auto
    obtain A rhs where pr': \<open>pr' = (A, rhs)\<close> by (cases pr')
    from jimg have m_lt: \<open>m' < length rhs\<close>
      and nxt: \<open>fst (rhs ! m') = Nt (fst (iprods G ! p))\<close>
      and jsat: \<open>\<exists>i \<in> irep_set R'. irel_sat (snd (rhs ! m')) j i\<close>
      unfolding xeq pr' by (auto split: if_splits)
    from jsat obtain i where iR: \<open>i \<in> irep_set R'\<close>
      and rel: \<open>irel_sat (snd (rhs ! m')) j i\<close> by blast
    have src: \<open>\<exists>\<rho>' l. (pr', m', \<rho>') \<in> set (wreach G s) \<and> l \<in> P \<and> wsat \<rho>' l i\<close>
      using xit
    proof (rule xslots_memE)
      assume \<open>xit \<in> set xs\<close>
      then have memxs: \<open>(pr', m', R') \<in> set xs\<close> using xeq by simp
      from kern[OF memxs iR] show ?thesis .
    next
      fix q assume q: \<open>q < length (iprods G)\<close> and \<open>q < length (xiter G xs t)\<close>
        and xq: \<open>xit = (iprods G ! q, 0, xiter G xs t ! q)\<close>
      have pq: \<open>pr' = iprods G ! q\<close> and mq: \<open>m' = 0\<close>
        and Rq: \<open>R' = xiter G xs t ! q\<close> using xq xeq by auto
      have \<open>i \<in> irep_set (xiter G xs t ! q)\<close> using iR Rq by simp
      from Suc.IH[OF q this] show ?thesis unfolding pq mq by simp
    qed
    from src obtain \<rho>' l where mem: \<open>(pr', m', \<rho>') \<in> set (wreach G s)\<close>
      and lP: \<open>l \<in> P\<close> and wl: \<open>wsat \<rho>' l i\<close> by blast
    have m_lt': \<open>m' < length (snd pr')\<close> using m_lt pr' by simp
    have nxt': \<open>fst (snd pr' ! m') = Nt (fst (iprods G ! p))\<close> using nxt pr' by simp
    have prp: \<open>iprods G ! p \<in> set (iprods G)\<close> using Suc.prems(1) by simp
    from wreach_emit[OF mem m_lt' nxt' prp]
    have \<open>(iprods G ! p, 0, wcomp (winv (w_of (snd (snd pr' ! m')))) \<rho>')
          \<in> set (wreach G s)\<close> .
    moreover have \<open>wsat (wcomp (winv (w_of (snd (snd pr' ! m')))) \<rho>') l j\<close>
      by (rule wsat_reanchor[OF _ wl]) (use rel pr' in simp)
    ultimately show ?thesis using lP by blast
  qed
qed

theorem xclosure_auto_pool:
  assumes kern: \<open>\<And>pr m R j. (pr, m, R) \<in> set xs \<Longrightarrow> j \<in> irep_set R \<Longrightarrow>
      \<exists>\<rho> l. (pr, m, \<rho>) \<in> set (wreach G s) \<and> l \<in> P \<and> wsat \<rho> l j\<close>
    and mem: \<open>(pr, m, R) \<in> set (xclosure_auto G xs)\<close>
    and jR: \<open>j \<in> irep_set R\<close>
  shows \<open>\<exists>\<rho> l. (pr, m, \<rho>) \<in> set (wreach G s) \<and> l \<in> P \<and> wsat \<rho> l j\<close>
proof -
  have mem': \<open>(pr, m, R) \<in> set (xslots G xs (xiter G xs (xfuel G xs)))\<close>
    using mem unfolding xclosure_auto_def xclosure_def .
  show ?thesis
    using mem'
  proof (rule xslots_memE)
    assume mem2: \<open>(pr, m, R) \<in> set xs\<close>
    from kern[OF mem2 jR] show ?thesis .
  next
    fix q assume q: \<open>q < length (iprods G)\<close>
      and \<open>q < length (xiter G xs (xfuel G xs))\<close>
      and eq: \<open>(pr, m, R) = (iprods G ! q, 0, xiter G xs (xfuel G xs) ! q)\<close>
    have \<open>j \<in> irep_set (xiter G xs (xfuel G xs) ! q)\<close> using jR eq by simp
    from xiter_pool[OF kern q this] show ?thesis using eq by simp
  qed
qed

text \<open>The kernel hypothesis, per frame kind: an \<open>lgoto\<close>-built frame pools the
  goto label's anchors, the bottom frame is pinned at \<open>istart_ind\<close>.\<close>

lemma wanch_pool_lgoto:
  assumes cover: \<open>\<And>pr m R j. (pr, m, R) \<in> set (lgoto CL X RA) \<Longrightarrow> j \<in> irep_set R \<Longrightarrow>
      (pr, m) \<in> set s\<close>
    and mem: \<open>(pr, m, R) \<in> set (lgoto CL X RA)\<close> and jR: \<open>j \<in> irep_set R\<close>
  shows \<open>\<exists>\<rho> l. (pr, m, \<rho>) \<in> set (wreach G s) \<and> l \<in> irep_set RA \<and> wsat \<rho> l j\<close>
proof -
  obtain m\<^sub>0 where m: \<open>m = Suc m\<^sub>0\<close> using lgoto_dot_pos[OF mem] by (cases m) auto
  from lgoto_kernel_step[OF mem[unfolded m]] obtain R\<^sub>s where
    m0_lt: \<open>m\<^sub>0 < length (snd pr)\<close>
    and Req: \<open>R = irep_inter R\<^sub>s (irep_pre (snd (snd pr ! m\<^sub>0)) RA)\<close> .
  from jR obtain l where lRA: \<open>l \<in> irep_set RA\<close>
    and rel: \<open>irel_sat (snd (snd pr ! m\<^sub>0)) l j\<close>
    unfolding Req by auto
  have kmem: \<open>(pr, m) \<in> set s\<close> by (rule cover[OF mem jR])
  have \<open>(pr, m, w_of (snd (snd pr ! (m - 1)))) \<in> set (wkernel s)\<close>
    using wkernel_memI[OF kmem] unfolding m by simp
  then have wmem: \<open>(pr, m, w_of (snd (snd pr ! m\<^sub>0))) \<in> set (wreach G s)\<close>
    using wreach_kernel unfolding m by auto
  have \<open>wsat (w_of (snd (snd pr ! m\<^sub>0))) l j\<close> by (rule w_of_sound[OF rel])
  then show ?thesis using wmem lRA by blast
qed

lemma wanch_pool_xinit:
  assumes mem: \<open>(pr, m, R) \<in> set (xinit G Shn)\<close> and jR: \<open>j \<in> irep_set R\<close>
    and cover: \<open>(pr, m) \<in> set s\<close>
  shows \<open>\<exists>\<rho>. (pr, m, \<rho>) \<in> set (wreach G s) \<and> wsat \<rho> (istart_ind G) j\<close>
proof -
  have m0: \<open>m = 0\<close> using mem unfolding xinit_def by auto
  have \<open>(pr, m, WAny) \<in> set (wkernel s)\<close>
    using wkernel_memI[OF cover] unfolding m0 by simp
  then have \<open>(pr, m, WAny) \<in> set (wreach G s)\<close> using wreach_kernel by auto
  then show ?thesis by auto
qed

section \<open>The anchored-nonterminal fixpoint\<close>

text \<open>\<^const>\<open>anchored_nts\<close> iterates a filter; each round either fixes the
  list or strictly shortens it, so \<open>length nts\<close> rounds reach the greatest
  fixpoint.  The destructor: an anchored nonterminal's productions all start
  with an \<open>Eq\<close>-related terminal or anchored nonterminal.\<close>

lemma funpow_filter_fix:
  fixes stp :: \<open>'a list \<Rightarrow> 'a list\<close>
  assumes step: \<open>\<And>S. stp S = S \<or> length (stp S) < length S\<close>
  shows \<open>stp ((stp ^^ n) S\<^sub>0) = (stp ^^ n) S\<^sub>0 \<or> length ((stp ^^ n) S\<^sub>0) \<le> length S\<^sub>0 - n\<close>
proof (induction n)
  case 0
  then show ?case using step by auto
next
  case (Suc n)
  show ?case
  proof (cases \<open>stp ((stp ^^ n) S\<^sub>0) = (stp ^^ n) S\<^sub>0\<close>)
    case True
    then have \<open>(stp ^^ Suc n) S\<^sub>0 = (stp ^^ n) S\<^sub>0\<close> by simp
    then show ?thesis using True by simp
  next
    case False
    with Suc.IH have len_n: \<open>length ((stp ^^ n) S\<^sub>0) \<le> length S\<^sub>0 - n\<close> by blast
    from step[of \<open>(stp ^^ n) S\<^sub>0\<close>] False
    have \<open>length (stp ((stp ^^ n) S\<^sub>0)) < length ((stp ^^ n) S\<^sub>0)\<close> by blast
    then have \<open>length ((stp ^^ Suc n) S\<^sub>0) \<le> length S\<^sub>0 - Suc n\<close>
      using len_n by simp
    then show ?thesis by blast
  qed
qed

lemma funpow_filter_stable:
  fixes stp :: \<open>'a list \<Rightarrow> 'a list\<close>
  assumes step: \<open>\<And>S. stp S = S \<or> length (stp S) < length S\<close>
    and nil: \<open>stp [] = []\<close>
  shows \<open>stp ((stp ^^ length S\<^sub>0) S\<^sub>0) = (stp ^^ length S\<^sub>0) S\<^sub>0\<close>
proof -
  from funpow_filter_fix[OF step, of \<open>length S\<^sub>0\<close> S\<^sub>0]
  consider \<open>stp ((stp ^^ length S\<^sub>0) S\<^sub>0) = (stp ^^ length S\<^sub>0) S\<^sub>0\<close>
    | \<open>length ((stp ^^ length S\<^sub>0) S\<^sub>0) = 0\<close> by fastforce
  then show ?thesis
  proof cases
    case 1
    then show ?thesis .
  next
    case 2
    then have \<open>(stp ^^ length S\<^sub>0) S\<^sub>0 = []\<close> by simp
    then show ?thesis using nil by simp
  qed
qed

lemma anchored_ntsD:
  fixes G :: \<open>('n, 't) is_cfg\<close>
  assumes A: \<open>A \<in> set (anchored_nts G)\<close> and pr: \<open>(A, rhs) \<in> set (iprods G)\<close>
  shows \<open>rhs \<noteq> [] \<and> snd (hd rhs) = Eq \<and>
         (case fst (hd rhs) of Tm _ \<Rightarrow> True | Nt B \<Rightarrow> B \<in> set (anchored_nts G))\<close>
proof -
  define ok where \<open>ok = (\<lambda>S (B :: 'n, rhs :: ('n, 't) rhs). rhs \<noteq> [] \<and> snd (hd rhs) = Eq \<and>
      (case fst (hd rhs) of Tm _ \<Rightarrow> True | Nt B' \<Rightarrow> B' \<in> set S))\<close>
  define stp where \<open>stp = (\<lambda>S. filter (\<lambda>A. list_all (\<lambda>p. fst p \<noteq> A \<or> ok S p) (iprods G)) S)\<close>
  have step: \<open>stp S = S \<or> length (stp S) < length S\<close> for S
  proof (cases \<open>\<forall>A \<in> set S. list_all (\<lambda>p. fst p \<noteq> A \<or> ok S p) (iprods G)\<close>)
    case True
    then have \<open>stp S = S\<close> unfolding stp_def by (simp add: filter_id_conv)
    then show ?thesis ..
  next
    case False
    then obtain A' where \<open>A' \<in> set S\<close>
      and \<open>\<not> list_all (\<lambda>p. fst p \<noteq> A' \<or> ok S p) (iprods G)\<close> by blast
    then have \<open>length (stp S) < length S\<close>
      unfolding stp_def by (intro length_filter_less) auto
    then show ?thesis ..
  qed
  have nil: \<open>stp [] = []\<close> unfolding stp_def by simp
  have unf: \<open>anchored_nts G = (stp ^^ length (remdups (map fst (iprods G))))
      (remdups (map fst (iprods G)))\<close>
    unfolding anchored_nts_def stp_def ok_def Let_def by simp
  have stable: \<open>stp (anchored_nts G) = anchored_nts G\<close>
    unfolding unf by (rule funpow_filter_stable[OF step nil])
  have \<open>A \<in> set (stp (anchored_nts G))\<close> using A stable by simp
  then have \<open>list_all (\<lambda>p. fst p \<noteq> A \<or> ok (anchored_nts G) p) (iprods G)\<close>
    unfolding stp_def by simp
  then have \<open>ok (anchored_nts G) (A, rhs)\<close>
    using pr by (fastforce simp: list_all_iff)
  then show ?thesis unfolding ok_def by simp
qed

section \<open>Anchored pools are singletons\<close>

lemma anchored_nts_sub: \<open>set (anchored_nts G) \<subseteq> fst ` set (iprods G)\<close>
proof -
  have gen: \<open>set ((stp ^^ k) S\<^sub>0) \<subseteq> set S\<^sub>0\<close>
    if sub: \<open>\<And>S. set (stp S) \<subseteq> set S\<close> for stp :: \<open>'x list \<Rightarrow> 'x list\<close> and k S\<^sub>0
  proof (induction k)
    case 0 then show ?case by simp
  next
    case (Suc k)
    have \<open>set ((stp ^^ Suc k) S\<^sub>0) \<subseteq> set ((stp ^^ k) S\<^sub>0)\<close> using sub by simp
    then show ?case using Suc.IH by blast
  qed
  show ?thesis
    unfolding anchored_nts_def Let_def
    by (rule subset_trans[OF gen]) auto
qed

lemma dshape_persist1:
  assumes sh: \<open>dshape G Shn Xs \<alpha>\<close>
  shows \<open>(pr, m, R) \<in> set (Xs ! k) \<Longrightarrow> k < length Xs \<Longrightarrow> 1 \<le> m \<Longrightarrow>
     \<exists>R\<^sub>1. k + m - 1 < length \<alpha> \<and> (pr, 1, R\<^sub>1) \<in> set (Xs ! (k + m - 1)) \<and>
           irep_set R \<subseteq> irep_set R\<^sub>1\<close>
proof (induction m arbitrary: k R)
  case 0
  then show ?case by simp
next
  case (Suc m)
  note lenX = dshapeD(1)[OF sh] and bot = dshapeD(2)[OF sh] and shp = dshapeD(3)[OF sh]
  have k_lt_a: \<open>k < length \<alpha>\<close>
  proof (rule ccontr)
    assume \<open>\<not> k < length \<alpha>\<close>
    then have \<open>k = length \<alpha>\<close> using Suc.prems(2) lenX by simp
    then have \<open>(pr, Suc m, R) \<in> set (xinit G Shn)\<close> using Suc.prems(1) bot by simp
    then show False unfolding xinit_def by auto
  qed
  show ?case
  proof (cases m)
    case 0
    then show ?thesis using Suc.prems(1) k_lt_a by auto
  next
    case (Suc m')
    have frame: \<open>Xs ! k = lgoto (xclosure_auto G (Xs ! Suc k)) (fst (\<alpha> ! k)) (snd (\<alpha> ! k))\<close>
      by (rule shp[OF k_lt_a])
    from lgoto_kernel_step[OF Suc.prems(1)[unfolded frame]] obtain R' where
      src: \<open>(pr, m, R') \<in> set (xclosure_auto G (Xs ! Suc k))\<close>
      and Req: \<open>R = irep_inter R' (irep_pre (snd (snd pr ! m)) (snd (\<alpha> ! k)))\<close> .
    have sub: \<open>irep_set R \<subseteq> irep_set R'\<close> unfolding Req by auto
    have src'': \<open>(pr, m, R') \<in> set (xslots G (Xs ! Suc k)
        (xiter G (Xs ! Suc k) (xfuel G (Xs ! Suc k))))\<close>
      using src unfolding xclosure_auto_def xclosure_def .
    have kern: \<open>(pr, m, R') \<in> set (Xs ! Suc k)\<close>
      using src''
    proof (rule xslots_memE)
      assume \<open>(pr, m, R') \<in> set (Xs ! Suc k)\<close>
      then show ?thesis .
    next
      fix q assume \<open>q < length (iprods G)\<close>
        and \<open>q < length (xiter G (Xs ! Suc k) (xfuel G (Xs ! Suc k)))\<close>
        and \<open>(pr, m, R') = (iprods G ! q, 0, xiter G (Xs ! Suc k) (xfuel G (Xs ! Suc k)) ! q)\<close>
      then show ?thesis using Suc by auto
    qed
    have Sk_lt: \<open>Suc k < length Xs\<close> using k_lt_a lenX by simp
    have m_pos: \<open>1 \<le> m\<close> using Suc by simp
    from Suc.IH[OF kern Sk_lt m_pos] obtain R\<^sub>1 where
      lt1: \<open>Suc k + m - 1 < length \<alpha>\<close>
      and s1: \<open>(pr, 1, R\<^sub>1) \<in> set (Xs ! (Suc k + m - 1))\<close>
      and sub1: \<open>irep_set R' \<subseteq> irep_set R\<^sub>1\<close> by blast
    have idx: \<open>Suc k + m - 1 = k + Suc m - 1\<close> using m_pos by simp
    show ?thesis using lt1 s1 sub sub1 unfolding idx by blast
  qed
qed

lemma irep_pre_Eq: \<open>irep_set (irep_pre Eq L) = irep_set L\<close>
  by auto

text \<open>The label of a reduce over an anchored nonterminal is bounded by a
  single column: every completed instance descends to its dot-1 form, whose
  \<open>Eq\<close> first-symbol filter bounds it by the pool of the frame where the
  first symbol was crossed: a shift column, or an anchored pool one level
  down.\<close>

lemma red_set_anchored_singleton:
  assumes sh: \<open>dshape G Shn Xs \<alpha>\<close> and ne: \<open>Xs \<noteq> []\<close>
    and tmS: \<open>\<forall>k < length \<alpha>. \<forall>a. fst (\<alpha> ! k) = Tm a \<longrightarrow> (\<exists>c. snd (\<alpha> ! k) = FinRep [c])\<close>
    and sng: \<open>\<forall>k < length \<alpha>. \<forall>B. fst (\<alpha> ! k) = Nt B \<longrightarrow> B \<in> set (anchored_nts G) \<longrightarrow>
                (\<exists>c. irep_set (snd (\<alpha> ! k)) \<subseteq> {c})\<close>
    and fresh: \<open>fresh_name G Shn\<close>
    and anch: \<open>fst pr \<in> set (anchored_nts G)\<close>
  shows \<open>\<exists>c. irep_set (red_set (xclosure_auto G (hd Xs)) pr) \<subseteq> {c}\<close>
proof (cases \<open>\<exists>R. (pr, length (snd pr), R) \<in> set (xclosure_auto G (hd Xs)) \<and>
    irep_set R \<noteq> {}\<close>)
  case False
  have \<open>irep_set (red_set (xclosure_auto G (hd Xs)) pr) \<subseteq> {0}\<close>
    using False by (fastforce simp: red_set_correct)
  then show ?thesis by blast
next
  case True
  then obtain R\<^sub>w where inst_w: \<open>(pr, length (snd pr), R\<^sub>w) \<in> set (xclosure_auto G (hd Xs))\<close>
    by blast
  note lenX = dshapeD(1)[OF sh]
  have hd0: \<open>hd Xs = Xs ! 0\<close> using ne by (simp add: hd_conv_nth)
  have prG: \<open>pr \<in> set (iprods G)\<close>
  proof -
    have \<open>pr \<in> set (iprods G) \<or> pr = start_prod G Shn\<close>
      using dshape_prods[OF sh _ inst_w[unfolded hd0]] by simp
    moreover have \<open>pr \<noteq> start_prod G Shn\<close>
    proof
      assume \<open>pr = start_prod G Shn\<close>
      then have \<open>fst pr = Shn\<close> unfolding start_prod_def by simp
      then have \<open>Shn \<in> set (anchored_nts G)\<close> using anch by simp
      then have \<open>Shn \<in> fst ` set (iprods G)\<close>
        by (rule subsetD[OF anchored_nts_sub])
      then show False using fresh unfolding fresh_name_def by auto
    qed
    ultimately show ?thesis by blast
  qed
  obtain A rhs where preq: \<open>pr = (A, rhs)\<close> by (cases pr)
  from anchored_ntsD[OF anch[unfolded preq fst_conv] prG[unfolded preq]]
  have rhs_ne: \<open>rhs \<noteq> []\<close> and hdEq: \<open>snd (hd rhs) = Eq\<close>
    and hdok: \<open>case fst (hd rhs) of Tm _ \<Rightarrow> True | Nt B \<Rightarrow> B \<in> set (anchored_nts G)\<close>
    by auto
  define d where \<open>d = length (snd pr)\<close>
  have d_pos: \<open>1 \<le> d\<close> unfolding d_def preq using rhs_ne by (cases rhs) auto
  have one: \<open>d - 1 < length \<alpha> \<and> fst (\<alpha> ! (d - 1)) = fst (snd pr ! 0) \<and>
      irep_set R \<subseteq> irep_set (irep_pre (snd (snd pr ! 0)) (snd (\<alpha> ! (d - 1))))\<close>
    if inst: \<open>(pr, length (snd pr), R) \<in> set (xclosure_auto G (hd Xs))\<close> for R
  proof -
    have inst': \<open>(pr, length (snd pr), R) \<in> set (xslots G (hd Xs)
        (xiter G (hd Xs) (xfuel G (hd Xs))))\<close>
      using inst unfolding xclosure_auto_def xclosure_def .
    have kern: \<open>(pr, length (snd pr), R) \<in> set (hd Xs)\<close>
      using inst'
    proof (rule xslots_memE)
      assume \<open>(pr, length (snd pr), R) \<in> set (hd Xs)\<close>
      then show ?thesis .
    next
      fix q assume \<open>q < length (iprods G)\<close>
        and \<open>q < length (xiter G (hd Xs) (xfuel G (hd Xs)))\<close>
        and eq: \<open>(pr, length (snd pr), R) =
           (iprods G ! q, 0, xiter G (hd Xs) (xfuel G (hd Xs)) ! q)\<close>
      have \<open>length (snd pr) = 0\<close> using eq by auto
      then show ?thesis using d_pos unfolding d_def by simp
    qed
    have k0_lt: \<open>(0 :: nat) < length Xs\<close> using ne by (cases Xs) auto
    have dm: \<open>1 \<le> length (snd pr)\<close> using d_pos unfolding d_def by simp
    from dshape_persist1[OF sh kern[unfolded hd0] k0_lt dm]
    obtain R\<^sub>1 where lt1: \<open>0 + length (snd pr) - 1 < length \<alpha>\<close>
      and s1: \<open>(pr, 1, R\<^sub>1) \<in> set (Xs ! (0 + length (snd pr) - 1))\<close>
      and sub1: \<open>irep_set R \<subseteq> irep_set R\<^sub>1\<close> by blast
    have idx: \<open>0 + length (snd pr) - 1 = d - 1\<close> unfolding d_def by simp
    have lt': \<open>d - 1 < length \<alpha>\<close> using lt1 unfolding idx .
    have frame: \<open>Xs ! (d - 1) =
        lgoto (xclosure_auto G (Xs ! Suc (d - 1))) (fst (\<alpha> ! (d - 1))) (snd (\<alpha> ! (d - 1)))\<close>
      using sh lt' unfolding dshape_def by auto
    have s1': \<open>(pr, Suc 0, R\<^sub>1) \<in> set (lgoto (xclosure_auto G (Xs ! Suc (d - 1)))
        (fst (\<alpha> ! (d - 1))) (snd (\<alpha> ! (d - 1))))\<close>
      using s1 unfolding idx frame by simp
    from lgoto_kernel_step[OF s1'] obtain R\<^sub>0 where
      src0: \<open>(pr, 0, R\<^sub>0) \<in> set (xclosure_auto G (Xs ! Suc (d - 1)))\<close>
      and m0: \<open>0 < length (snd pr)\<close>
      and X0: \<open>fst (snd pr ! 0) = fst (\<alpha> ! (d - 1))\<close>
      and R1eq: \<open>R\<^sub>1 = irep_inter R\<^sub>0 (irep_pre (snd (snd pr ! 0)) (snd (\<alpha> ! (d - 1))))\<close> .
    have sub2: \<open>irep_set R\<^sub>1 \<subseteq> irep_set (irep_pre (snd (snd pr ! 0)) (snd (\<alpha> ! (d - 1))))\<close>
      unfolding R1eq by auto
    have \<open>irep_set R \<subseteq> irep_set (irep_pre (snd (snd pr ! 0)) (snd (\<alpha> ! (d - 1))))\<close>
      using sub1 sub2 by (rule subset_trans)
    then show ?thesis using lt' X0 by simp
  qed
  from one[OF inst_w] have k1: \<open>d - 1 < length \<alpha>\<close>
    and Xa: \<open>fst (\<alpha> ! (d - 1)) = fst (snd pr ! 0)\<close> by auto
  have first_rel: \<open>snd (snd pr ! 0) = Eq\<close>
    using hdEq rhs_ne unfolding preq by (simp add: hd_conv_nth)
  have bound: \<open>\<exists>c. irep_set (irep_pre (snd (snd pr ! 0)) (snd (\<alpha> ! (d - 1)))) \<subseteq> {c}\<close>
  proof (cases \<open>fst (snd pr ! 0)\<close>)
    case (Tm b)
    from tmS k1 Xa Tm obtain c where \<open>snd (\<alpha> ! (d - 1)) = FinRep [c]\<close> by auto
    then show ?thesis unfolding first_rel irep_pre_Eq by auto
  next
    case (Nt B)
    have hd0': \<open>fst (hd rhs) = fst (snd pr ! 0)\<close>
      using rhs_ne unfolding preq by (simp add: hd_conv_nth)
    have Banch: \<open>B \<in> set (anchored_nts G)\<close>
      using hdok unfolding hd0' Nt by simp
    have \<open>\<exists>c. irep_set (snd (\<alpha> ! (d - 1))) \<subseteq> {c}\<close>
      using sng[rule_format, of \<open>d - 1\<close> B] k1 Xa Nt Banch by simp
    then obtain c where \<open>irep_set (snd (\<alpha> ! (d - 1))) \<subseteq> {c}\<close> by blast
    then show ?thesis unfolding first_rel irep_pre_Eq by auto
  qed
  have bound': \<open>\<exists>c. \<forall>R. (pr, length (snd pr), R) \<in> set (xclosure_auto G (hd Xs)) \<longrightarrow>
      irep_set R \<subseteq> {c}\<close>
    using bound one by blast
  then obtain c where c: \<open>\<And>R. (pr, length (snd pr), R) \<in> set (xclosure_auto G (hd Xs)) \<Longrightarrow>
      irep_set R \<subseteq> {c}\<close> by blast
  have \<open>irep_set (red_set (xclosure_auto G (hd Xs)) pr) \<subseteq> {c}\<close>
    using c by (fastforce simp: red_set_correct)
  then show ?thesis by blast
qed

section \<open>The canonical tracked stack\<close>

text \<open>The descent needs more than \<^const>\<open>didx_ok\<close>: the goto history
  (\<^const>\<open>dshape\<close>), singleton pools on shift entries, the canonical bottom
  index, and the \<open>adjacency\<close> tying each tracked index to the canonical goto
  target of the index below along the recorded symbol.  The reachability
  induction constructs exactly these witnesses.\<close>

definition strack :: \<open>('n, 't) is_cfg \<Rightarrow> 'n \<Rightarrow> ('n, 't) xitem list list \<Rightarrow>
    (('n, 't) sym \<times> indrep) list \<Rightarrow> nat list \<Rightarrow> bool\<close> where
  \<open>strack G Shn Xs \<alpha> pstk \<longleftrightarrow>
     dshape G Shn Xs \<alpha> \<and>
     didx_ok G (pr0_states G Shn) Xs pstk \<and>
     last pstk = p0start G Shn \<and>
     (\<forall>k < length \<alpha>. \<forall>a. fst (\<alpha> ! k) = Tm a \<longrightarrow> (\<exists>c. snd (\<alpha> ! k) = FinRep [c])) \<and>
     (\<forall>k < length \<alpha>. \<forall>B. fst (\<alpha> ! k) = Nt B \<longrightarrow> B \<in> set (anchored_nts G) \<longrightarrow>
        (\<exists>c. irep_set (snd (\<alpha> ! k)) \<subseteq> {c})) \<and>
     (\<forall>k < length \<alpha>. \<forall>B. fst (\<alpha> ! k) = Nt B \<longrightarrow>
        (\<forall>l \<in> irep_set (snd (\<alpha> ! k)). \<exists>pr R\<^sub>0. fst pr = B \<and>
           (pr, 0, R\<^sub>0) \<in> set (xclosure_auto G (Xs ! Suc k)) \<and> l \<in> irep_set R\<^sub>0)) \<and>
     (\<forall>k < length \<alpha>. pstk ! k =
        st_find (pr0_states G Shn)
          (cgoto (creach G (pr0_states G Shn ! (pstk ! Suc k))) (fst (\<alpha> ! k))))\<close>

lemma strackD:
  assumes \<open>strack G Shn Xs \<alpha> pstk\<close>
  shows \<open>dshape G Shn Xs \<alpha>\<close> and \<open>didx_ok G (pr0_states G Shn) Xs pstk\<close>
    and \<open>last pstk = p0start G Shn\<close>
    and \<open>\<forall>k < length \<alpha>. \<forall>a. fst (\<alpha> ! k) = Tm a \<longrightarrow> (\<exists>c. snd (\<alpha> ! k) = FinRep [c])\<close>
    and \<open>\<forall>k < length \<alpha>. \<forall>B. fst (\<alpha> ! k) = Nt B \<longrightarrow> B \<in> set (anchored_nts G) \<longrightarrow>
        (\<exists>c. irep_set (snd (\<alpha> ! k)) \<subseteq> {c})\<close>
    and \<open>\<forall>k < length \<alpha>. \<forall>B. fst (\<alpha> ! k) = Nt B \<longrightarrow>
        (\<forall>l \<in> irep_set (snd (\<alpha> ! k)). \<exists>pr R\<^sub>0. fst pr = B \<and>
           (pr, 0, R\<^sub>0) \<in> set (xclosure_auto G (Xs ! Suc k)) \<and> l \<in> irep_set R\<^sub>0)\<close>
    and \<open>\<forall>k < length \<alpha>. pstk ! k =
        st_find (pr0_states G Shn)
          (cgoto (creach G (pr0_states G Shn ! (pstk ! Suc k))) (fst (\<alpha> ! k)))\<close>
  using assms unfolding strack_def by blast+

lemma strackI:
  assumes \<open>dshape G Shn Xs \<alpha>\<close> and \<open>didx_ok G (pr0_states G Shn) Xs pstk\<close>
    and \<open>last pstk = p0start G Shn\<close>
    and \<open>\<forall>k < length \<alpha>. \<forall>a. fst (\<alpha> ! k) = Tm a \<longrightarrow> (\<exists>c. snd (\<alpha> ! k) = FinRep [c])\<close>
    and \<open>\<forall>k < length \<alpha>. \<forall>B. fst (\<alpha> ! k) = Nt B \<longrightarrow> B \<in> set (anchored_nts G) \<longrightarrow>
        (\<exists>c. irep_set (snd (\<alpha> ! k)) \<subseteq> {c})\<close>
    and \<open>\<forall>k < length \<alpha>. \<forall>B. fst (\<alpha> ! k) = Nt B \<longrightarrow>
        (\<forall>l \<in> irep_set (snd (\<alpha> ! k)). \<exists>pr R\<^sub>0. fst pr = B \<and>
           (pr, 0, R\<^sub>0) \<in> set (xclosure_auto G (Xs ! Suc k)) \<and> l \<in> irep_set R\<^sub>0)\<close>
    and \<open>\<forall>k < length \<alpha>. pstk ! k =
        st_find (pr0_states G Shn)
          (cgoto (creach G (pr0_states G Shn ! (pstk ! Suc k))) (fst (\<alpha> ! k)))\<close>
  shows \<open>strack G Shn Xs \<alpha> pstk\<close>
  using assms unfolding strack_def by blast

lemma strack_tl:
  assumes tr: \<open>strack G Shn Xs ((X\<^sub>0, RA) # \<alpha>') pstk\<close>
  shows \<open>strack G Shn (tl Xs) \<alpha>' (tl pstk)\<close>
proof -
  note sh = strackD(1)[OF tr] and mt = strackD(2)[OF tr] and lastp = strackD(3)[OF tr]
    and tmS = strackD(4)[OF tr] and sng = strackD(5)[OF tr] and slot = strackD(6)[OF tr]
    and adj = strackD(7)[OF tr]
  note lenX = dshapeD(1)[OF sh] and bot = dshapeD(2)[OF sh] and shp = dshapeD(3)[OF sh]
  have Xs_ne: \<open>Xs \<noteq> []\<close> using lenX by auto
  obtain x\<^sub>0 Xr where Xs_eq: \<open>Xs = x\<^sub>0 # Xr\<close> using Xs_ne by (cases Xs) auto
  have nthX: \<open>\<And>k. tl Xs ! k = Xs ! Suc k\<close> unfolding Xs_eq by simp
  have len_tl: \<open>length (tl Xs) = length \<alpha>' + 1\<close> using lenX by simp
  have lenp: \<open>length pstk = length Xs\<close> by (rule didx_ok_len[OF mt])
  obtain p\<^sub>0 Pr where pstk_eq: \<open>pstk = p\<^sub>0 # Pr\<close>
    using lenp Xs_ne by (cases pstk) auto
  have nthP: \<open>\<And>k. tl pstk ! k = pstk ! Suc k\<close> unfolding pstk_eq by simp
  have Pr_ne: \<open>Pr \<noteq> []\<close> using lenp lenX pstk_eq by auto
  have sh': \<open>dshape G Shn (tl Xs) \<alpha>'\<close>
    unfolding dshape_def
  proof (intro conjI)
    show \<open>length (tl Xs) = length \<alpha>' + 1\<close> by (rule len_tl)
    show \<open>tl Xs ! length \<alpha>' = xinit G Shn\<close> using bot by (simp add: nthX)
    show \<open>\<forall>k < length \<alpha>'. tl Xs ! k =
        lgoto (xclosure_auto G (tl Xs ! Suc k)) (fst (\<alpha>' ! k)) (snd (\<alpha>' ! k))\<close>
    proof (intro allI impI)
      fix k assume k: \<open>k < length \<alpha>'\<close>
      have \<open>Suc k < length ((X\<^sub>0, RA) # \<alpha>')\<close> using k by simp
      from shp[OF this] show \<open>tl Xs ! k =
          lgoto (xclosure_auto G (tl Xs ! Suc k)) (fst (\<alpha>' ! k)) (snd (\<alpha>' ! k))\<close>
        by (simp add: nthX)
    qed
  qed
  have mt': \<open>didx_ok G (pr0_states G Shn) (tl Xs) (tl pstk)\<close>
    unfolding didx_ok_def
  proof (intro conjI)
    show \<open>length (tl pstk) = length (tl Xs)\<close> using lenp by (simp add: Xs_eq pstk_eq)
    show \<open>\<forall>k < length (tl Xs). lcore (tl Xs ! k) \<noteq> {} \<longrightarrow>
        tl pstk ! k < length (pr0_states G Shn) \<and>
        lcore (tl Xs ! k) \<subseteq> set (pr0_states G Shn ! (tl pstk ! k))\<close>
    proof (intro allI impI)
      fix k assume k: \<open>k < length (tl Xs)\<close> and lv: \<open>lcore (tl Xs ! k) \<noteq> {}\<close>
      have sk: \<open>Suc k < length Xs\<close> using k unfolding Xs_eq by simp
      show \<open>tl pstk ! k < length (pr0_states G Shn) \<and>
          lcore (tl Xs ! k) \<subseteq> set (pr0_states G Shn ! (tl pstk ! k))\<close>
        using didx_okD[OF mt sk] lv by (simp add: nthX nthP)
    qed
  qed
  have last': \<open>last (tl pstk) = p0start G Shn\<close>
    using lastp Pr_ne unfolding pstk_eq by simp
  have tmS': \<open>\<forall>k < length \<alpha>'. \<forall>a. fst (\<alpha>' ! k) = Tm a \<longrightarrow>
      (\<exists>c. snd (\<alpha>' ! k) = FinRep [c])\<close>
  proof (intro allI impI)
    fix k a assume k: \<open>k < length \<alpha>'\<close> and t: \<open>fst (\<alpha>' ! k) = Tm a\<close>
    show \<open>\<exists>c. snd (\<alpha>' ! k) = FinRep [c]\<close>
      using tmS[rule_format, of \<open>Suc k\<close> a] k t by simp
  qed
  have sng': \<open>\<forall>k < length \<alpha>'. \<forall>B. fst (\<alpha>' ! k) = Nt B \<longrightarrow>
      B \<in> set (anchored_nts G) \<longrightarrow> (\<exists>c. irep_set (snd (\<alpha>' ! k)) \<subseteq> {c})\<close>
  proof (intro allI impI)
    fix k B assume k: \<open>k < length \<alpha>'\<close> and t: \<open>fst (\<alpha>' ! k) = Nt B\<close>
      and an: \<open>B \<in> set (anchored_nts G)\<close>
    show \<open>\<exists>c. irep_set (snd (\<alpha>' ! k)) \<subseteq> {c}\<close>
      using sng[rule_format, of \<open>Suc k\<close> B] k t an by simp
  qed
  have slot': \<open>\<forall>k < length \<alpha>'. \<forall>B. fst (\<alpha>' ! k) = Nt B \<longrightarrow>
      (\<forall>l \<in> irep_set (snd (\<alpha>' ! k)). \<exists>pr R\<^sub>0. fst pr = B \<and>
         (pr, 0, R\<^sub>0) \<in> set (xclosure_auto G (tl Xs ! Suc k)) \<and> l \<in> irep_set R\<^sub>0)\<close>
  proof (intro allI impI)
    fix k B assume k: \<open>k < length \<alpha>'\<close> and t: \<open>fst (\<alpha>' ! k) = Nt B\<close>
    have \<open>\<forall>l \<in> irep_set (snd (\<alpha>' ! k)). \<exists>pr R\<^sub>0. fst pr = B \<and>
        (pr, 0, R\<^sub>0) \<in> set (xclosure_auto G (Xs ! Suc (Suc k))) \<and> l \<in> irep_set R\<^sub>0\<close>
      using slot[rule_format, of \<open>Suc k\<close> B] k t by simp
    then show \<open>\<forall>l \<in> irep_set (snd (\<alpha>' ! k)). \<exists>pr R\<^sub>0. fst pr = B \<and>
        (pr, 0, R\<^sub>0) \<in> set (xclosure_auto G (tl Xs ! Suc k)) \<and> l \<in> irep_set R\<^sub>0\<close>
      by (simp add: nthX)
  qed
  have adj': \<open>\<forall>k < length \<alpha>'. tl pstk ! k =
      st_find (pr0_states G Shn)
        (cgoto (creach G (pr0_states G Shn ! (tl pstk ! Suc k))) (fst (\<alpha>' ! k)))\<close>
  proof (intro allI impI)
    fix k assume k: \<open>k < length \<alpha>'\<close>
    have \<open>Suc k < length ((X\<^sub>0, RA) # \<alpha>')\<close> using k by simp
    from adj[rule_format, OF this]
    show \<open>tl pstk ! k = st_find (pr0_states G Shn)
        (cgoto (creach G (pr0_states G Shn ! (tl pstk ! Suc k))) (fst (\<alpha>' ! k)))\<close>
      by (simp add: nthP)
  qed
  show ?thesis
    by (rule strackI[OF sh' mt' last' tmS' sng' slot' adj'])
qed

lemma strack_drop:
  \<open>strack G Shn Xs \<alpha> pstk \<Longrightarrow> d \<le> length \<alpha> \<Longrightarrow>
   strack G Shn (drop d Xs) (drop d \<alpha>) (drop d pstk)\<close>
proof (induction d arbitrary: Xs \<alpha> pstk)
  case 0
  then show ?case by simp
next
  case (Suc d)
  obtain X RA \<alpha>' where \<alpha>: \<open>\<alpha> = (X, RA) # \<alpha>'\<close>
    using Suc.prems(2) by (cases \<alpha>) auto
  have tl: \<open>strack G Shn (tl Xs) \<alpha>' (tl pstk)\<close>
    by (rule strack_tl[OF Suc.prems(1)[unfolded \<alpha>]])
  have d_le: \<open>d \<le> length \<alpha>'\<close> using Suc.prems(2) unfolding \<alpha> by simp
  from Suc.IH[OF tl d_le] show ?case unfolding \<alpha> by (simp add: drop_Suc)
qed

text \<open>Pushing a frame on a tracked stack: the new frame's index is the
  canonical goto of the index below along the pushed symbol, the extended
  index stack is checked by \<^const>\<open>didx_ok\<close>, and the three per-label
  conditions are checked for the pushed label only.\<close>

lemma strack_push:
  assumes tr: \<open>strack G Shn Xs \<alpha> pstk\<close>
    and NF: \<open>NF = lgoto (xclosure_auto G (hd Xs)) X RA\<close>
    and p': \<open>p' = st_find (pr0_states G Shn)
        (cgoto (creach G (pr0_states G Shn ! (pstk ! 0))) X)\<close>
    and mt': \<open>didx_ok G (pr0_states G Shn) (NF # Xs) (p' # pstk)\<close>
    and tm: \<open>\<And>a. X = Tm a \<Longrightarrow> \<exists>c. RA = FinRep [c]\<close>
    and sng: \<open>\<And>B. X = Nt B \<Longrightarrow> B \<in> set (anchored_nts G) \<Longrightarrow> \<exists>c. irep_set RA \<subseteq> {c}\<close>
    and slot: \<open>\<And>B l. X = Nt B \<Longrightarrow> l \<in> irep_set RA \<Longrightarrow> \<exists>pr R\<^sub>0. fst pr = B \<and>
        (pr, 0, R\<^sub>0) \<in> set (xclosure_auto G (hd Xs)) \<and> l \<in> irep_set R\<^sub>0\<close>
  shows \<open>strack G Shn (NF # Xs) ((X, RA) # \<alpha>) (p' # pstk)\<close>
proof -
  note sh = strackD(1)[OF tr] and mt = strackD(2)[OF tr] and lastp = strackD(3)[OF tr]
    and tmS = strackD(4)[OF tr] and sngI = strackD(5)[OF tr] and slotI = strackD(6)[OF tr]
    and adj = strackD(7)[OF tr]
  have ne: \<open>Xs \<noteq> []\<close> using dshapeD(1)[OF sh] by auto
  have pstk_ne: \<open>pstk \<noteq> []\<close> using didx_ok_len[OF mt] ne by auto
  have hd0: \<open>hd Xs = Xs ! 0\<close> using ne by (simp add: hd_conv_nth)
  have sh': \<open>dshape G Shn (NF # Xs) ((X, RA) # \<alpha>)\<close>
    unfolding NF by (rule dshape_push[OF sh ne])
  have last': \<open>last (p' # pstk) = p0start G Shn\<close> using lastp pstk_ne by simp
  have tmS': \<open>\<forall>k < length ((X, RA) # \<alpha>). \<forall>b. fst (((X, RA) # \<alpha>) ! k) = Tm b \<longrightarrow>
      (\<exists>c'. snd (((X, RA) # \<alpha>) ! k) = FinRep [c'])\<close>
    using tmS tm by (auto simp: less_Suc_eq_0_disj nth_Cons')
  have sng': \<open>\<forall>k < length ((X, RA) # \<alpha>). \<forall>B. fst (((X, RA) # \<alpha>) ! k) = Nt B \<longrightarrow>
      B \<in> set (anchored_nts G) \<longrightarrow> (\<exists>c'. irep_set (snd (((X, RA) # \<alpha>) ! k)) \<subseteq> {c'})\<close>
    using sngI sng by (auto simp: less_Suc_eq_0_disj nth_Cons')
  have slot': \<open>\<forall>k < length ((X, RA) # \<alpha>). \<forall>B. fst (((X, RA) # \<alpha>) ! k) = Nt B \<longrightarrow>
      (\<forall>l \<in> irep_set (snd (((X, RA) # \<alpha>) ! k)). \<exists>pr R\<^sub>0. fst pr = B \<and>
         (pr, 0, R\<^sub>0) \<in> set (xclosure_auto G ((NF # Xs) ! Suc k)) \<and> l \<in> irep_set R\<^sub>0)\<close>
    using slotI slot hd0 by (auto simp: less_Suc_eq_0_disj nth_Cons')
  have adj': \<open>\<forall>k < length ((X, RA) # \<alpha>). (p' # pstk) ! k =
      st_find (pr0_states G Shn)
        (cgoto (creach G (pr0_states G Shn ! ((p' # pstk) ! Suc k)))
          (fst (((X, RA) # \<alpha>) ! k)))\<close>
  proof (intro allI impI)
    fix k assume \<open>k < length ((X, RA) # \<alpha>)\<close>
    then show \<open>(p' # pstk) ! k =
        st_find (pr0_states G Shn)
          (cgoto (creach G (pr0_states G Shn ! ((p' # pstk) ! Suc k)))
            (fst (((X, RA) # \<alpha>) ! k)))\<close>
      using adj p' by (cases k) auto
  qed
  show ?thesis by (rule strackI[OF sh' mt' last' tmS' sng' slot' adj'])
qed

text \<open>Every configuration the indexed machine reaches carries a tracked
  stack whose indices are the driver's own: a shift pushes the token's
  singleton label, a reduce drops the handle and pushes the nonterminal with
  its pooled anchors.  The pushed index is the table's goto, which resolves
  to the canonical successor because the pushed frame is live
  (\<^text>\<open>dnext_st_find\<close>); the singleton and slot conditions come from
  \<^text>\<open>red_set_anchored_singleton\<close> and \<^text>\<open>dshape_persist\<close>.\<close>

theorem imreach_strack:
  assumes \<open>imreach G Shn (pgtab G (pr0_states G Shn)) (pr0_states G Shn) ic\<close>
    and fresh: \<open>fresh_name G Shn\<close>
  shows \<open>\<exists>\<alpha>. strack G Shn (fst (fst ic)) \<alpha> (snd ic)\<close>
  using assms(1)
proof (induction rule: imreach.induct)
  case (imreach_init w)
  have mt: \<open>didx_ok G (pr0_states G Shn) [xinit G Shn]
      [st_find (pr0_states G Shn) (lr0_start G Shn)]\<close>
    by (rule didx_ok_init[OF tables_ok_concrete])
  have \<open>strack G Shn [xinit G Shn] [] [st_find (pr0_states G Shn) (lr0_start G Shn)]\<close>
    unfolding strack_def using dshape_init mt by (simp add: p0start_def)
  then show ?case by auto
next
  case (imreach_step ic act ic')
  let ?sts = \<open>pr0_states G Shn\<close> and ?gt = \<open>pgtab G (pr0_states G Shn)\<close>
  note tab = tables_ok_concrete[of G Shn]
  obtain gc istk where ic: \<open>ic = (gc, istk)\<close> by (cases ic)
  obtain Xs w where gc: \<open>gc = (Xs, w)\<close> by (cases gc)
  obtain gc' istk' where ic': \<open>ic' = (gc', istk')\<close> by (cases ic')
  obtain \<alpha> where tr: \<open>strack G Shn Xs \<alpha> istk\<close>
    using imreach_step.IH unfolding ic gc by auto
  note sh = strackD(1)[OF tr] and mt = strackD(2)[OF tr]
    and tmS = strackD(4)[OF tr] and sngI = strackD(5)[OF tr]
  note lenXa = dshapeD(1)[OF sh]
  have len: \<open>length istk = length Xs\<close> by (rule didx_ok_len[OF mt])
  have lv': \<open>dlive gc'\<close> using imreach_step.hyps(3) unfolding ic' by simp
  show ?case
  proof (cases act)
    case DShift
    have step0: \<open>imstep G ?gt ?sts ((Xs, w), istk) DShift = Some (gc', istk')\<close>
      using imreach_step.hyps(2) unfolding ic gc ic' DShift .
    then have mstep: \<open>mstep G (Xs, w) DShift = Some gc'\<close>
      and istk': \<open>istk' = dnext ?gt ?sts (hd istk) (Tm (fst (hd w))) # istk\<close>
      unfolding imstep_def by (auto split: option.splits)
    have step: \<open>mstep_cached G (map (xclosure_auto G) Xs) (Xs, w) DShift = Some gc'\<close>
      using mstep unfolding mstep_def by simp
    from mstep_shift_shape[OF step] obtain a c w' where
      w: \<open>w = (a, c) # w'\<close> and ne: \<open>Xs \<noteq> []\<close>
      and gc': \<open>gc' = (lgoto (hd (map (xclosure_auto G) Xs)) (Tm a) (FinRep [c]) # Xs, w')\<close> .
    define NF where \<open>NF = lgoto (xclosure_auto G (hd Xs)) (Tm a) (FinRep [c])\<close>
    define p' where \<open>p' = dnext ?gt ?sts (hd istk) (Tm a)\<close>
    have gc'2: \<open>fst gc' = NF # Xs\<close>
      unfolding gc' NF_def using ne by (simp add: hd_map)
    have istk'2: \<open>istk' = p' # istk\<close> unfolding istk' p'_def w by simp
    have z_lt: \<open>0 < length Xs\<close> using ne by simp
    have hd0: \<open>hd Xs = Xs ! 0\<close> using ne by (simp add: hd_conv_nth)
    have istk_ne: \<open>istk \<noteq> []\<close> using len ne by auto
    have hdi: \<open>hd istk = istk ! 0\<close> using istk_ne by (simp add: hd_conv_nth)
    have liveNF: \<open>lcore NF \<noteq> {}\<close>
      using lv' ne unfolding gc' NF_def dlive_lcore by (simp add: hd_map)
    have p'eq: \<open>p' = st_find ?sts (cgoto (creach G (?sts ! (istk ! 0))) (Tm a))\<close>
      unfolding p'_def hdi
      by (rule dnext_st_find[OF tab mt z_lt liveNF[unfolded NF_def hd0]])
    have mt': \<open>didx_ok G ?sts (NF # Xs) (p' # istk)\<close>
      using didx_ok_push[OF tab mt z_lt, where X = \<open>Tm a\<close> and RA = \<open>FinRep [c]\<close>]
      unfolding NF_def p'_def hd0 hdi by simp
    have \<open>strack G Shn (NF # Xs) ((Tm a, FinRep [c]) # \<alpha>) (p' # istk)\<close>
      by (rule strack_push[OF tr NF_def p'eq mt']) simp_all
    then show ?thesis unfolding ic' fst_conv snd_conv gc'2 istk'2 by blast
  next
    case (DReduce pr)
    define d where \<open>d = length (snd pr)\<close>
    have step0: \<open>imstep G ?gt ?sts ((Xs, w), istk) (DReduce pr) = Some (gc', istk')\<close>
      using imreach_step.hyps(2) unfolding ic gc ic' DReduce .
    then have mstep: \<open>mstep G (Xs, w) (DReduce pr) = Some gc'\<close>
      and istk': \<open>istk' = dnext ?gt ?sts (istk ! d) (Nt (fst pr)) # drop d istk\<close>
      unfolding imstep_def d_def by (auto split: option.splits)
    have step: \<open>mstep_cached G (map (xclosure_auto G) Xs) (Xs, w) (DReduce pr) = Some gc'\<close>
      using mstep unfolding mstep_def by simp
    have d_lt: \<open>d < length Xs\<close>
      unfolding d_def by (rule mstep_reduce_shape[OF step]) blast
    have gc'0: \<open>gc' = (lgoto (map (xclosure_auto G) Xs ! d) (Nt (fst pr))
                  (red_set (hd (map (xclosure_auto G) Xs)) pr) # drop d Xs, w)\<close>
      unfolding d_def by (rule mstep_reduce_shape[OF step]) blast
    have ne: \<open>Xs \<noteq> []\<close> using d_lt by auto
    have hdd: \<open>hd (drop d Xs) = Xs ! d\<close> using d_lt by (simp add: hd_drop_conv_nth)
    define RA where \<open>RA = red_set (xclosure_auto G (hd Xs)) pr\<close>
    define NF where \<open>NF = lgoto (xclosure_auto G (hd (drop d Xs))) (Nt (fst pr)) RA\<close>
    define p' where \<open>p' = dnext ?gt ?sts (istk ! d) (Nt (fst pr))\<close>
    have gc'2: \<open>fst gc' = NF # drop d Xs\<close>
      unfolding gc'0 NF_def RA_def hdd using d_lt ne by (simp add: hd_map)
    have istk'2: \<open>istk' = p' # drop d istk\<close> unfolding istk' p'_def ..
    have d_le_a: \<open>d \<le> length \<alpha>\<close> using d_lt lenXa by simp
    have trd: \<open>strack G Shn (drop d Xs) (drop d \<alpha>) (drop d istk)\<close>
      by (rule strack_drop[OF tr d_le_a])
    have pd: \<open>drop d istk ! 0 = istk ! d\<close> using len d_lt by simp
    have liveNF: \<open>lcore NF \<noteq> {}\<close>
      using lv' d_lt ne unfolding gc'0 NF_def RA_def hdd dlive_lcore by (simp add: hd_map)
    have p'eq: \<open>p' = st_find ?sts (cgoto (creach G (?sts ! (drop d istk ! 0))) (Nt (fst pr)))\<close>
      unfolding p'_def pd
      by (rule dnext_st_find[OF tab mt d_lt liveNF[unfolded NF_def hdd]])
    have mt': \<open>didx_ok G ?sts (NF # drop d Xs) (p' # drop d istk)\<close>
      unfolding NF_def p'_def hdd by (rule didx_ok_push[OF tab mt d_lt])
    have sng0: \<open>fst pr \<in> set (anchored_nts G) \<Longrightarrow> \<exists>c. irep_set RA \<subseteq> {c}\<close>
      unfolding RA_def
      by (rule red_set_anchored_singleton[OF sh ne tmS sngI fresh])
    have slot0: \<open>\<And>l. l \<in> irep_set RA \<Longrightarrow> \<exists>pra R\<^sub>0. fst pra = fst pr \<and>
        (pra, 0, R\<^sub>0) \<in> set (xclosure_auto G (Xs ! d)) \<and> l \<in> irep_set R\<^sub>0\<close>
    proof -
      fix l assume l: \<open>l \<in> irep_set RA\<close>
      then obtain R where R: \<open>(pr, d, R) \<in> set (xclosure_auto G (hd Xs))\<close>
        and lR: \<open>l \<in> irep_set R\<close>
        unfolding RA_def red_set_correct d_def[symmetric] by blast
      have hd0: \<open>hd Xs = Xs ! 0\<close> using ne by (simp add: hd_conv_nth)
      show \<open>\<exists>pra R\<^sub>0. fst pra = fst pr \<and>
          (pra, 0, R\<^sub>0) \<in> set (xclosure_auto G (Xs ! d)) \<and> l \<in> irep_set R\<^sub>0\<close>
      proof (cases d)
        case 0
        have \<open>(pr, 0, R) \<in> set (xclosure_auto G (Xs ! d))\<close>
          using R hd0 unfolding 0 by simp
        then show ?thesis using lR by blast
      next
        case (Suc d')
        have kern: \<open>(pr, d, R) \<in> set (Xs ! 0)\<close>
          by (rule xclosure_auto_kernelD[OF R[unfolded hd0]]) (simp add: Suc)
        have z_lt: \<open>0 < length Xs\<close> using ne by simp
        have one_le: \<open>1 \<le> d\<close> using Suc by simp
        from dshape_persist[OF sh kern z_lt one_le] obtain R\<^sub>0 where
          m0: \<open>(pr, 0, R\<^sub>0) \<in> set (xclosure_auto G (Xs ! (0 + d)))\<close>
          and sb: \<open>irep_set R \<subseteq> irep_set R\<^sub>0\<close> by blast
        have \<open>(pr, 0, R\<^sub>0) \<in> set (xclosure_auto G (Xs ! d))\<close> using m0 by simp
        then show ?thesis using sb lR by blast
      qed
    qed
    have \<open>strack G Shn (NF # drop d Xs) ((Nt (fst pr), RA) # drop d \<alpha>) (p' # drop d istk)\<close>
    proof (rule strack_push[OF trd NF_def p'eq mt'])
      show \<open>\<And>a. Nt (fst pr) = Tm a \<Longrightarrow> \<exists>c. RA = FinRep [c]\<close> by simp
      show \<open>\<And>B. Nt (fst pr) = Nt B \<Longrightarrow> B \<in> set (anchored_nts G) \<Longrightarrow> \<exists>c. irep_set RA \<subseteq> {c}\<close>
        using sng0 by simp
      show \<open>\<And>B l. Nt (fst pr) = Nt B \<Longrightarrow> l \<in> irep_set RA \<Longrightarrow> \<exists>pra R\<^sub>0. fst pra = B \<and>
          (pra, 0, R\<^sub>0) \<in> set (xclosure_auto G (hd (drop d Xs))) \<and> l \<in> irep_set R\<^sub>0\<close>
        using slot0 unfolding hdd by simp
    qed
    then show ?thesis unfolding ic' fst_conv snd_conv gc'2 istk'2 by blast
  qed
qed

section \<open>The descent to the start state\<close>

text \<open>The entry pool of the top frame of a tracked stack: the goto label's
  anchors, or \<open>istart_ind\<close> at the bottom frame.\<close>

definition epool :: \<open>('n, 't) is_cfg \<Rightarrow> (('n, 't) sym \<times> indrep) list \<Rightarrow> nat set\<close> where
  \<open>epool G \<alpha> = (case \<alpha> of [] \<Rightarrow> {istart_ind G} | (X, RA) # _ \<Rightarrow> irep_set RA)\<close>

lemma pin_edgesI:
  \<open>p < length gt \<Longrightarrow> (X, s) \<in> set (gt ! p) \<Longrightarrow> (p, X) \<in> set (pin_edges gt s)\<close>
  unfolding pin_edges_def by fastforce

text \<open>A cursor realised in a frame: its item is in the frame's closure with an
  indentation the class holds at, for the lookahead column \<open>c\<close>.\<close>

definition icur :: \<open>('n, 't) is_cfg \<Rightarrow> ('n, 't) xitem list \<Rightarrow> nat \<Rightarrow> ('n, 't) witem \<Rightarrow> bool\<close>
  where
  \<open>icur G X c = (\<lambda>(pr, m, \<sigma>). \<exists>R j. (pr, m, R) \<in> set (xclosure_auto G X) \<and>
      j \<in> irep_set R \<and> wsat \<sigma> c j)\<close>

text \<open>A cursor realised in a frame at round \<open>t\<close> of its closure: the item is
  among the frame's slots after \<open>t\<close> rounds, with an indentation the class holds
  at for the lookahead column \<open>c\<close>.  \<^const>\<open>icur\<close> is the fuelled round.  The
  descent counts rounds down within a frame (a dot-0 item's indentation comes from
  a predicting item of an earlier round) and frames down across a pop.\<close>

definition icur_at :: \<open>('n, 't) is_cfg \<Rightarrow> ('n, 't) xitem list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow>
    ('n, 't) witem \<Rightarrow> bool\<close> where
  \<open>icur_at G X t c = (\<lambda>(pr, m, \<sigma>). \<exists>R j. (pr, m, R) \<in> set (xslots G X (xiter G X t)) \<and>
      j \<in> irep_set R \<and> wsat \<sigma> c j)\<close>

lemma icur_at_fuel: \<open>icur G X c cur \<longleftrightarrow> icur_at G X (xfuel G X) c cur\<close>
  unfolding icur_def icur_at_def xclosure_auto_def xclosure_def by (cases cur) simp

text \<open>Where a slot's indentation comes from: an element of a dot-0 pool at round
  \<open>t\<close> is the image of an element of a predicting item's pool at an earlier round.\<close>

lemma xiter_pred:
  assumes p: \<open>p < length (iprods G)\<close> and j: \<open>j \<in> irep_set (xiter G xs t ! p)\<close>
  shows \<open>\<exists>t' pr' m' R' j'. t' < t \<and> (pr', m', R') \<in> set (xslots G xs (xiter G xs t')) \<and>
      m' < length (snd pr') \<and> fst (snd pr' ! m') = Nt (fst (iprods G ! p)) \<and>
      j' \<in> irep_set R' \<and> irel_sat (snd (snd pr' ! m')) j j'\<close>
proof -
  have \<open>p < length (iprods G) \<Longrightarrow> j \<in> irep_set (xiter G xs t ! p) \<Longrightarrow>
      \<exists>t' pr' m' R' j'. t' < t \<and> (pr', m', R') \<in> set (xslots G xs (xiter G xs t')) \<and>
      m' < length (snd pr') \<and> fst (snd pr' ! m') = Nt (fst (iprods G ! p)) \<and>
      j' \<in> irep_set R' \<and> irel_sat (snd (snd pr' ! m')) j j'\<close>
  proof (induction t arbitrary: p j)
    case 0
    then show ?case by simp
  next
    case (Suc t)
    have eq: \<open>xiter G xs (Suc t) ! p =
        fold (xcontrib (iprods G ! p)) (xslots G xs (xiter G xs t)) (xiter G xs t ! p)\<close>
      using xround_nth[OF xiter_length Suc.prems(1)] by simp
    have \<open>j \<in> irep_set (xiter G xs t ! p) \<union>
        \<Union> (ximg (iprods G ! p) ` set (xslots G xs (xiter G xs t)))\<close>
      using Suc.prems(2) unfolding eq fold_xcontrib_set .
    then show ?case
    proof
      assume \<open>j \<in> irep_set (xiter G xs t ! p)\<close>
      from Suc.IH[OF Suc.prems(1) this] show ?thesis by (meson less_SucI)
    next
      assume \<open>j \<in> \<Union> (ximg (iprods G ! p) ` set (xslots G xs (xiter G xs t)))\<close>
      then show ?thesis by (fastforce split: if_splits)
    qed
  qed
  from this[OF p j] show ?thesis .
qed

text \<open>The pooled width invariant of \<open>xclosure_auto_pool\<close>, at any round.\<close>

lemma xslots_pool:
  assumes kern: \<open>\<And>pr m R j. (pr, m, R) \<in> set xs \<Longrightarrow> j \<in> irep_set R \<Longrightarrow>
      \<exists>\<rho> l. (pr, m, \<rho>) \<in> set (wreach G s) \<and> l \<in> P \<and> wsat \<rho> l j\<close>
    and mem: \<open>(pr, m, R) \<in> set (xslots G xs (xiter G xs t))\<close>
    and jR: \<open>j \<in> irep_set R\<close>
  shows \<open>\<exists>\<rho> l. (pr, m, \<rho>) \<in> set (wreach G s) \<and> l \<in> P \<and> wsat \<rho> l j\<close>
  using mem
proof (rule xslots_memE)
  assume mem2: \<open>(pr, m, R) \<in> set xs\<close>
  from kern[OF mem2 jR] show ?thesis .
next
  fix q assume q: \<open>q < length (iprods G)\<close>
    and \<open>q < length (xiter G xs t)\<close>
    and eq: \<open>(pr, m, R) = (iprods G ! q, 0, xiter G xs t ! q)\<close>
  have \<open>j \<in> irep_set (xiter G xs t ! q)\<close> using jR eq by simp
  from xiter_pool[OF kern q this] show ?thesis using eq by simp
qed

text \<open>The frame-0 pooled width invariant, packaged: every item of the top frame's
  slots at any round carries a \<open>wreach\<close> class at the tracked precise state,
  anchored at some element of the top entry pool.\<close>

lemma strack_pool_at:
  assumes tr: \<open>strack G Shn Xs \<alpha> pstk\<close> and live: \<open>lcore (hd Xs) \<noteq> {}\<close>
    and mem: \<open>(pr, m, R) \<in> set (xslots G (hd Xs) (xiter G (hd Xs) t))\<close>
    and jR: \<open>j \<in> irep_set R\<close>
  shows \<open>\<exists>\<rho> l. (pr, m, \<rho>) \<in> set (wreach G (pr0_states G Shn ! (pstk ! 0))) \<and>
        l \<in> epool G \<alpha> \<and> wsat \<rho> l j\<close>
proof -
  note sh = strackD(1)[OF tr] and mt = strackD(2)[OF tr]
  note lenX = dshapeD(1)[OF sh] and bot = dshapeD(2)[OF sh] and shp = dshapeD(3)[OF sh]
  have Xs_ne: \<open>Xs \<noteq> []\<close> using lenX by auto
  have hd0: \<open>hd Xs = Xs ! 0\<close> using Xs_ne by (simp add: hd_conv_nth)
  have z_lt: \<open>0 < length Xs\<close> using Xs_ne by auto
  have live0: \<open>lcore (Xs ! 0) \<noteq> {}\<close> using live hd0 by simp
  have cover0: \<open>lcore (Xs ! 0) \<subseteq> set (pr0_states G Shn ! (pstk ! 0))\<close>
    using didx_okD[OF mt z_lt live0] by blast
  have kern0: \<open>\<And>pr' m' R' j'. (pr', m', R') \<in> set (Xs ! 0) \<Longrightarrow>
      j' \<in> irep_set R' \<Longrightarrow>
      \<exists>\<rho> l. (pr', m', \<rho>) \<in> set (wreach G (pr0_states G Shn ! (pstk ! 0))) \<and>
            l \<in> epool G \<alpha> \<and> wsat \<rho> l j'\<close>
  proof -
    fix pr' m' R' j' assume a: \<open>(pr', m', R') \<in> set (Xs ! 0)\<close>
      and b: \<open>j' \<in> irep_set R'\<close>
    have cov: \<open>(pr', m') \<in> set (pr0_states G Shn ! (pstk ! 0))\<close>
      by (rule lcore_subD[OF cover0 a b])
    show \<open>\<exists>\<rho> l. (pr', m', \<rho>) \<in> set (wreach G (pr0_states G Shn ! (pstk ! 0))) \<and>
        l \<in> epool G \<alpha> \<and> wsat \<rho> l j'\<close>
    proof (cases \<alpha>)
      case Nil
      have x0: \<open>Xs ! 0 = xinit G Shn\<close> using bot unfolding Nil by simp
      from wanch_pool_xinit[OF a[unfolded x0] b cov] obtain \<rho> where
        \<open>(pr', m', \<rho>) \<in> set (wreach G (pr0_states G Shn ! (pstk ! 0)))\<close>
        and \<open>wsat \<rho> (istart_ind G) j'\<close> by blast
      then show ?thesis unfolding epool_def Nil by auto
    next
      case (Cons e \<alpha>')
      obtain X\<^sub>0 RA where e: \<open>e = (X\<^sub>0, RA)\<close> by (cases e)
      have z_la: \<open>0 < length \<alpha>\<close> unfolding Cons by simp
      have f0: \<open>Xs ! 0 = lgoto (xclosure_auto G (Xs ! Suc 0)) X\<^sub>0 RA\<close>
        using shp[OF z_la] unfolding Cons e by simp
      have covL: \<open>\<And>pra ma Ra ja. (pra, ma, Ra)
          \<in> set (lgoto (xclosure_auto G (Xs ! Suc 0)) X\<^sub>0 RA) \<Longrightarrow>
          ja \<in> irep_set Ra \<Longrightarrow>
          (pra, ma) \<in> set (pr0_states G Shn ! (pstk ! 0))\<close>
      proof -
        fix pra ma Ra ja
        assume aa: \<open>(pra, ma, Ra)
            \<in> set (lgoto (xclosure_auto G (Xs ! Suc 0)) X\<^sub>0 RA)\<close>
          and bb: \<open>ja \<in> irep_set Ra\<close>
        have \<open>(pra, ma, Ra) \<in> set (Xs ! 0)\<close> using aa f0 by simp
        then show \<open>(pra, ma) \<in> set (pr0_states G Shn ! (pstk ! 0))\<close>
          using bb by (rule lcore_subD[OF cover0])
      qed
      have ex: \<open>\<exists>\<rho> l. (pr', m', \<rho>)
            \<in> set (wreach G (pr0_states G Shn ! (pstk ! 0))) \<and>
          l \<in> irep_set RA \<and> wsat \<rho> l j'\<close>
        by (rule wanch_pool_lgoto[OF _ a[unfolded f0] b]) (rule covL)
      then show ?thesis unfolding epool_def Cons e by auto
    qed
  qed
  show ?thesis
    by (rule xslots_pool[OF _ mem[unfolded hd0] jR]) (rule kern0)
qed

lemma strack_pool:
  assumes tr: \<open>strack G Shn Xs \<alpha> pstk\<close> and live: \<open>lcore (hd Xs) \<noteq> {}\<close>
    and mem: \<open>(pr, m, R) \<in> set (xclosure_auto G (hd Xs))\<close>
    and jR: \<open>j \<in> irep_set R\<close>
  shows \<open>\<exists>\<rho> l. (pr, m, \<rho>) \<in> set (wreach G (pr0_states G Shn ! (pstk ! 0))) \<and>
        l \<in> epool G \<alpha> \<and> wsat \<rho> l j\<close>
  using mem unfolding xclosure_auto_def xclosure_def
  by (rule strack_pool_at[OF tr live _ jR])

text \<open>A dot-0 item of the fresh start name is the start item of the bottom frame,
  whose pool is \<open>{istart_ind}\<close>: no production has the start name on its left (so it
  is no slot), and every kernel item above the bottom frame has its dot past 0.\<close>

lemma strack_start_item:
  assumes tr: \<open>strack G Shn Xs \<alpha> pstk\<close> and fresh: \<open>fresh_name G Shn\<close>
    and mem: \<open>(pr, 0, R) \<in> set (xslots G (hd Xs) (xiter G (hd Xs) t))\<close>
    and shn: \<open>fst pr = Shn\<close>
  shows \<open>\<alpha> = [] \<and> irep_set R = {istart_ind G}\<close>
proof -
  note sh = strackD(1)[OF tr]
  note lenX = dshapeD(1)[OF sh] and bot = dshapeD(2)[OF sh] and shp = dshapeD(3)[OF sh]
  have Xs_ne: \<open>Xs \<noteq> []\<close> using lenX by auto
  have hd0: \<open>hd Xs = Xs ! 0\<close> using Xs_ne by (simp add: hd_conv_nth)
  have kern: \<open>(pr, 0, R) \<in> set (hd Xs)\<close>
  proof (rule xslots_memE[OF mem])
    assume \<open>(pr, 0, R) \<in> set (hd Xs)\<close>
    then show ?thesis .
  next
    fix p assume \<open>(pr, 0, R) = (iprods G ! p, 0, xiter G (hd Xs) t ! p)\<close>
      and \<open>p < length (iprods G)\<close>
    then have \<open>pr \<in> set (iprods G)\<close> by auto
    then have \<open>Shn \<in> fst ` set (iprods G)\<close> using shn by force
    then show ?thesis using fresh unfolding fresh_name_def by blast
  qed
  show ?thesis
  proof (cases \<alpha>)
    case Nil
    have x0: \<open>Xs ! 0 = xinit G Shn\<close> using bot unfolding Nil by simp
    then show ?thesis using kern hd0 unfolding Nil xinit_def by auto
  next
    case (Cons e \<alpha>')
    obtain X\<^sub>0 RA where e: \<open>e = (X\<^sub>0, RA)\<close> by (cases e)
    have z_la: \<open>0 < length \<alpha>\<close> unfolding Cons by simp
    have f0: \<open>Xs ! 0 = lgoto (xclosure_auto G (Xs ! Suc 0)) X\<^sub>0 RA\<close>
      using shp[OF z_la] unfolding Cons e by simp
    have \<open>(pr, 0, R) \<in> set (lgoto (xclosure_auto G (Xs ! Suc 0)) X\<^sub>0 RA)\<close>
      using kern hd0 f0 by simp
    from lgoto_dot_pos[OF this] show ?thesis by simp
  qed
qed

text \<open>A kernel item of the top frame is the goto image of an item of the frame
  below: the symbol before its dot is the entry's, its pool is the lower item's
  filtered by the dot's relation against the entry pool.\<close>

lemma strack_pop:
  assumes tr: \<open>strack G Shn Xs \<alpha> pstk\<close>
    and mem: \<open>(pr, Suc m, R) \<in> set (xslots G (hd Xs) (xiter G (hd Xs) t))\<close>
    and jR: \<open>j \<in> irep_set R\<close>
  obtains X\<^sub>0 RA \<alpha>' R' l where \<open>\<alpha> = (X\<^sub>0, RA) # \<alpha>'\<close> and \<open>m < length (snd pr)\<close>
    and \<open>fst (snd pr ! m) = X\<^sub>0\<close> and \<open>(pr, m, R') \<in> set (xclosure_auto G (Xs ! 1))\<close>
    and \<open>j \<in> irep_set R'\<close> and \<open>l \<in> irep_set RA\<close> and \<open>irel_sat (snd (snd pr ! m)) l j\<close>
proof -
  have sh: \<open>dshape G Shn Xs \<alpha>\<close> using strackD(1)[OF tr] .
  have len: \<open>length Xs = length \<alpha> + 1\<close> by (rule dshapeD(1)[OF sh])
  have last: \<open>Xs ! length \<alpha> = xinit G Shn\<close> by (rule dshapeD(2)[OF sh])
  have hd: \<open>hd Xs = Xs ! 0\<close> using len by (cases Xs) auto
  have mem0: \<open>(pr, Suc m, R) \<in> set (Xs ! 0)\<close>
    using mem unfolding hd by (auto dest: xslots_memE)
  obtain X\<^sub>0 RA \<alpha>' where \<alpha>: \<open>\<alpha> = (X\<^sub>0, RA) # \<alpha>'\<close>
  proof (cases \<alpha>)
    case Nil
    then have \<open>Xs ! 0 = xinit G Shn\<close> using last by simp
    with mem0 show thesis unfolding xinit_def by simp
  next
    case (Cons a \<alpha>')
    then show thesis using that by (cases a) auto
  qed
  have \<open>0 < length \<alpha>\<close> unfolding \<alpha> by simp
  from dshapeD(3)[OF sh this] have X0eq:
    \<open>Xs ! 0 = lgoto (xclosure_auto G (Xs ! Suc 0)) (fst (\<alpha> ! 0)) (snd (\<alpha> ! 0))\<close> .
  from mem0 have \<open>(pr, Suc m, R) \<in> set (lgoto (xclosure_auto G (Xs ! 1)) X\<^sub>0 RA)\<close>
    unfolding X0eq \<alpha> by simp
  from lgoto_kernel_step[OF this] obtain R\<^sub>s where
    m_lt: \<open>m < length (snd pr)\<close> and fstm: \<open>fst (snd pr ! m) = X\<^sub>0\<close>
    and Rs: \<open>(pr, m, R\<^sub>s) \<in> set (xclosure_auto G (Xs ! 1))\<close>
    and Req: \<open>R = irep_inter R\<^sub>s (irep_pre (snd (snd pr ! m)) RA)\<close> .
  from jR obtain l where \<open>j \<in> irep_set R\<^sub>s\<close> and \<open>l \<in> irep_set RA\<close>
    and \<open>irel_sat (snd (snd pr ! m)) l j\<close> unfolding Req by auto
  then show thesis by (rule that[OF \<alpha> m_lt fstm Rs, of l])
qed

text \<open>The tracked indices of the two top frames are adjacent along the entry
  symbol, so the edge is in \<^const>\<open>pin_edges\<close>: the lower item is in the lower
  state's LR(0) closure, hence the goto entry is in its row of the table.\<close>

lemma strack_edge:
  assumes tr: \<open>strack G Shn Xs ((X\<^sub>0, RA) # \<alpha>') pstk\<close>
    and mem: \<open>(pr, m, R) \<in> set (xclosure_auto G (Xs ! 1))\<close> and jR: \<open>j \<in> irep_set R\<close>
    and m: \<open>m < length (snd pr)\<close> and X: \<open>fst (snd pr ! m) = X\<^sub>0\<close>
  shows \<open>pstk ! 1 < length (pr0_states G Shn) \<and>
      (pstk ! 1, X\<^sub>0) \<in> set (pin_edges (pgtab G (pr0_states G Shn)) (pstk ! 0))\<close>
proof -
  have live1: \<open>lcore (Xs ! 1) \<noteq> {}\<close> using closure_live_kernel[OF mem jR] .
  have len: \<open>length Xs = length ((X\<^sub>0, RA) # \<alpha>') + 1\<close>
    using dshapeD(1)[OF strackD(1)[OF tr]] .
  then have lt: \<open>1 < length Xs\<close> by simp
  have ok: \<open>didx_ok G (pr0_states G Shn) Xs pstk\<close> using strackD(2)[OF tr] .
  from didx_okD[OF ok lt live1]
  have lt1: \<open>pstk ! 1 < length (pr0_states G Shn)\<close>
    and cover1: \<open>lcore (Xs ! 1) \<subseteq> set (pr0_states G Shn ! (pstk ! 1))\<close> by blast+
  have kern: \<open>\<And>pr m R. (pr, m, R) \<in> set (Xs ! 1) \<Longrightarrow> irep_nonempty R \<Longrightarrow>
      (pr, m) \<in> set (pr0_states G Shn ! (pstk ! 1))\<close>
    using lcore_subD_ne[OF cover1] .
  have creach: \<open>(pr, m) \<in> set (creach G (pr0_states G Shn ! (pstk ! 1)))\<close>
    using xclosure_auto_live_creach[OF kern mem jR] .
  have tab: \<open>(X\<^sub>0, st_find (pr0_states G Shn)
        (cgoto (creach G (pr0_states G Shn ! (pstk ! 1))) X\<^sub>0))
      \<in> set (pgtab G (pr0_states G Shn) ! (pstk ! 1))\<close>
    using pgtab_mem[OF lt1 creach m] X by simp
  have p0: \<open>pstk ! 0 = st_find (pr0_states G Shn)
      (cgoto (creach G (pr0_states G Shn ! (pstk ! 1))) X\<^sub>0)\<close>
    using strackD(7)[OF tr, rule_format, of 0] by simp
  show ?thesis
    using lt1 tab p0 pin_edgesI[of \<open>pstk ! 1\<close> \<open>pgtab G (pr0_states G Shn)\<close>] by simp
qed

text \<open>A rigid entry's pool is a singleton: a token's column, or an anchored
  nonterminal's.\<close>

lemma strack_rigid:
  assumes tr: \<open>strack G Shn Xs ((X\<^sub>0, RA) # \<alpha>') pstk\<close>
    and rig: \<open>irigid (anchored_nts G) X\<^sub>0\<close>
  shows \<open>\<exists>col. irep_set RA \<subseteq> {col}\<close>
proof (cases X\<^sub>0)
  case (Tm a)
  from strackD(4)[OF tr] Tm obtain c where \<open>RA = FinRep [c]\<close> by fastforce
  then show ?thesis by simp
next
  case (Nt B)
  from rig Nt have \<open>B \<in> set (anchored_nts G)\<close> by (simp add: irigid_def)
  with strackD(5)[OF tr] Nt show ?thesis by fastforce
qed

text \<open>The prediction step: a realised dot-0 cursor of a production has a realised
  predecessor among \<^const>\<open>ipreds\<close>, at an earlier round of the same frame.\<close>

lemma strack_predict:
  assumes tr: \<open>strack G Shn Xs \<alpha> pstk\<close> and live: \<open>lcore (hd Xs) \<noteq> {}\<close>
    and cur: \<open>icur_at G (hd Xs) t c (pr, 0, \<sigma>)\<close> and shn: \<open>fst pr \<noteq> Shn\<close>
  shows \<open>\<exists>t' cur'. t' < t \<and> icur_at G (hd Xs) t' c cur' \<and>
      cur' \<in> set (ipreds (map (wreach G) (pr0_states G Shn)) (pstk ! 0) (fst pr) \<sigma>)\<close>
proof -
  note sh = strackD(1)[OF tr] and mt = strackD(2)[OF tr]
  note lenX = dshapeD(1)[OF sh] and bot = dshapeD(2)[OF sh] and shp = dshapeD(3)[OF sh]
  have Xs_ne: \<open>Xs \<noteq> []\<close> using lenX by auto
  have hd0: \<open>hd Xs = Xs ! 0\<close> using Xs_ne by (simp add: hd_conv_nth)
  have z_lt: \<open>0 < length Xs\<close> using Xs_ne by auto
  have live0: \<open>lcore (Xs ! 0) \<noteq> {}\<close> using live hd0 by simp
  obtain R j where mem: \<open>(pr, 0, R) \<in> set (xslots G (hd Xs) (xiter G (hd Xs) t))\<close>
    and jR: \<open>j \<in> irep_set R\<close> and wj: \<open>wsat \<sigma> c j\<close>
    using cur unfolding icur_at_def by auto
  have nokern: \<open>(pr, 0, R) \<notin> set (hd Xs)\<close>
  proof
    assume kern: \<open>(pr, 0, R) \<in> set (hd Xs)\<close>
    show False
    proof (cases \<alpha>)
      case Nil
      have x0: \<open>Xs ! 0 = xinit G Shn\<close> using bot unfolding Nil by simp
      then show ?thesis using kern hd0 shn unfolding Nil xinit_def by auto
    next
      case (Cons e \<alpha>')
      obtain X\<^sub>0 RA where e: \<open>e = (X\<^sub>0, RA)\<close> by (cases e)
      have z_la: \<open>0 < length \<alpha>\<close> unfolding Cons by simp
      have f0: \<open>Xs ! 0 = lgoto (xclosure_auto G (Xs ! Suc 0)) X\<^sub>0 RA\<close>
        using shp[OF z_la] unfolding Cons e by simp
      have \<open>(pr, 0, R) \<in> set (lgoto (xclosure_auto G (Xs ! Suc 0)) X\<^sub>0 RA)\<close>
        using kern hd0 f0 by simp
      from lgoto_dot_pos[OF this] show False by simp
    qed
  qed
  obtain p where p: \<open>p < length (iprods G)\<close> and pr: \<open>pr = iprods G ! p\<close>
      and R: \<open>R = xiter G (hd Xs) t ! p\<close>
    using mem nokern by (auto elim!: xslots_memE)
  obtain t' pr' m' R' j' where tt: \<open>t' < t\<close>
    and mem': \<open>(pr', m', R') \<in> set (xslots G (hd Xs) (xiter G (hd Xs) t'))\<close>
    and m': \<open>m' < length (snd pr')\<close> and nt: \<open>fst (snd pr' ! m') = Nt (fst pr)\<close>
    and j'R: \<open>j' \<in> irep_set R'\<close> and rel: \<open>irel_sat (snd (snd pr' ! m')) j j'\<close>
    using xiter_pred[OF p jR[unfolded R]] unfolding pr by blast
  obtain \<rho> where rho: \<open>(pr', m', \<rho>) \<in> set (wreach G (pr0_states G Shn ! (pstk ! 0)))\<close>
    using strack_pool_at[OF tr live mem' j'R] by blast
  have idx: \<open>pstk ! 0 < length (pr0_states G Shn)\<close>
    using didx_okD[OF mt z_lt live0] by blast
  have rho': \<open>(pr', m', \<rho>) \<in> set (map (wreach G) (pr0_states G Shn) ! (pstk ! 0))\<close>
    using rho idx by simp
  define cur' where \<open>cur' = (pr', m', wcomp (w_of (snd (snd pr' ! m'))) \<sigma>)\<close>
  have \<open>cur' \<in> set (ipreds (map (wreach G) (pr0_states G Shn)) (pstk ! 0) (fst pr) \<sigma>)\<close>
    unfolding ipreds_def cur'_def set_remdups
    by (rule map_filterI[OF rho']) (simp add: m' nt)
  moreover have \<open>icur_at G (hd Xs) t' c cur'\<close>
    unfolding icur_at_def cur'_def
    using mem' j'R wcomp_sound[OF wj w_of_sound[OF rel]] by auto
  ultimately show ?thesis using tt by blast
qed

text \<open>The pop step: two realised kernel cursors have the entry symbol before
  their dots, are not disjoint at a rigid entry, and pop to realised cursors of the
  frame below along an edge of \<^const>\<open>pin_edges\<close>, both items in the lower
  state's closure.\<close>

lemma strack_pop_step:
  assumes tr: \<open>strack G Shn Xs \<alpha> pstk\<close> and live: \<open>lcore (hd Xs) \<noteq> {}\<close>
    and c1: \<open>icur_at G (hd Xs) t\<^sub>1 c (pr\<^sub>1, Suc m\<^sub>1, \<sigma>\<^sub>1)\<close>
    and c2: \<open>icur_at G (hd Xs) t\<^sub>2 c (pr\<^sub>2, Suc m\<^sub>2, \<sigma>\<^sub>2)\<close>
  shows \<open>\<exists>X\<^sub>0 RA \<alpha>'. \<alpha> = (X\<^sub>0, RA) # \<alpha>' \<and>
      fst (snd pr\<^sub>1 ! m\<^sub>1) = X\<^sub>0 \<and> fst (snd pr\<^sub>2 ! m\<^sub>2) = X\<^sub>0 \<and>
      (irigid (anchored_nts G) X\<^sub>0 \<longrightarrow>
         \<not> wdisjoint (itrans (pr\<^sub>1, Suc m\<^sub>1, \<sigma>\<^sub>1)) (itrans (pr\<^sub>2, Suc m\<^sub>2, \<sigma>\<^sub>2))) \<and>
      strack G Shn (tl Xs) \<alpha>' (tl pstk) \<and> lcore (hd (tl Xs)) \<noteq> {} \<and>
      icur G (hd (tl Xs)) c (pr\<^sub>1, m\<^sub>1, \<sigma>\<^sub>1) \<and> icur G (hd (tl Xs)) c (pr\<^sub>2, m\<^sub>2, \<sigma>\<^sub>2) \<and>
      (pstk ! 1, X\<^sub>0) \<in> set (pin_edges (pgtab G (pr0_states G Shn)) (pstk ! 0)) \<and>
      ihas (map (wreach G) (pr0_states G Shn) ! (pstk ! 1)) pr\<^sub>1 m\<^sub>1 \<and>
      ihas (map (wreach G) (pr0_states G Shn) ! (pstk ! 1)) pr\<^sub>2 m\<^sub>2\<close>
proof -
  from c1 obtain R\<^sub>1 j\<^sub>1 where
      mem1: \<open>(pr\<^sub>1, Suc m\<^sub>1, R\<^sub>1) \<in> set (xslots G (hd Xs) (xiter G (hd Xs) t\<^sub>1))\<close>
    and j1: \<open>j\<^sub>1 \<in> irep_set R\<^sub>1\<close> and w1: \<open>wsat \<sigma>\<^sub>1 c j\<^sub>1\<close>
    by (auto simp: icur_at_def)
  from c2 obtain R\<^sub>2 j\<^sub>2 where
      mem2: \<open>(pr\<^sub>2, Suc m\<^sub>2, R\<^sub>2) \<in> set (xslots G (hd Xs) (xiter G (hd Xs) t\<^sub>2))\<close>
    and j2: \<open>j\<^sub>2 \<in> irep_set R\<^sub>2\<close> and w2: \<open>wsat \<sigma>\<^sub>2 c j\<^sub>2\<close>
    by (auto simp: icur_at_def)
  obtain X\<^sub>0 RA \<alpha>' R\<^sub>1' l\<^sub>1 where \<alpha>1: \<open>\<alpha> = (X\<^sub>0, RA) # \<alpha>'\<close>
    and lt1: \<open>m\<^sub>1 < length (snd pr\<^sub>1)\<close> and X1: \<open>fst (snd pr\<^sub>1 ! m\<^sub>1) = X\<^sub>0\<close>
    and mem1': \<open>(pr\<^sub>1, m\<^sub>1, R\<^sub>1') \<in> set (xclosure_auto G (Xs ! 1))\<close>
    and j1': \<open>j\<^sub>1 \<in> irep_set R\<^sub>1'\<close> and l1: \<open>l\<^sub>1 \<in> irep_set RA\<close>
    and rel1: \<open>irel_sat (snd (snd pr\<^sub>1 ! m\<^sub>1)) l\<^sub>1 j\<^sub>1\<close>
    by (rule strack_pop[OF tr mem1 j1])
  obtain X\<^sub>0' RA' \<alpha>'' R\<^sub>2' l\<^sub>2 where \<alpha>2: \<open>\<alpha> = (X\<^sub>0', RA') # \<alpha>''\<close>
    and lt2: \<open>m\<^sub>2 < length (snd pr\<^sub>2)\<close> and X2: \<open>fst (snd pr\<^sub>2 ! m\<^sub>2) = X\<^sub>0'\<close>
    and mem2': \<open>(pr\<^sub>2, m\<^sub>2, R\<^sub>2') \<in> set (xclosure_auto G (Xs ! 1))\<close>
    and j2': \<open>j\<^sub>2 \<in> irep_set R\<^sub>2'\<close> and l2: \<open>l\<^sub>2 \<in> irep_set RA'\<close>
    and rel2: \<open>irel_sat (snd (snd pr\<^sub>2 ! m\<^sub>2)) l\<^sub>2 j\<^sub>2\<close>
    by (rule strack_pop[OF tr mem2 j2])
  from \<alpha>1 \<alpha>2 have eq: \<open>X\<^sub>0' = X\<^sub>0\<close> \<open>RA' = RA\<close> by simp_all
  have tr1: \<open>strack G Shn Xs ((X\<^sub>0, RA) # \<alpha>') pstk\<close> using tr unfolding \<alpha>1 .
  have tr': \<open>strack G Shn (tl Xs) \<alpha>' (tl pstk)\<close> using strack_tl[OF tr1] .
  have len: \<open>length Xs = length \<alpha> + 1\<close> using dshapeD(1)[OF strackD(1)[OF tr]] .
  have lenp: \<open>length pstk = length Xs\<close> using didx_ok_len[OF strackD(2)[OF tr]] .
  have hdtl: \<open>hd (tl Xs) = Xs ! 1\<close> using len \<alpha>1 by (cases Xs; cases \<open>tl Xs\<close>) auto
  have tlp: \<open>tl pstk ! 0 = pstk ! 1\<close> using lenp len \<alpha>1 by (cases pstk) auto
  have rig: \<open>irigid (anchored_nts G) X\<^sub>0 \<Longrightarrow>
      \<not> wdisjoint (itrans (pr\<^sub>1, Suc m\<^sub>1, \<sigma>\<^sub>1)) (itrans (pr\<^sub>2, Suc m\<^sub>2, \<sigma>\<^sub>2))\<close>
  proof -
    assume rg: \<open>irigid (anchored_nts G) X\<^sub>0\<close>
    from strack_rigid[OF tr1 rg] obtain col where sub: \<open>irep_set RA \<subseteq> {col}\<close> ..
    with l1 l2 eq have lc: \<open>l\<^sub>1 = col\<close> \<open>l\<^sub>2 = col\<close> by auto
    have s1: \<open>wsat (itrans (pr\<^sub>1, Suc m\<^sub>1, \<sigma>\<^sub>1)) c l\<^sub>1\<close>
      using wcomp_sound[OF w1 winv_sound[OF w_of_sound[OF rel1]]] by (simp add: itrans_def)
    have s2: \<open>wsat (itrans (pr\<^sub>2, Suc m\<^sub>2, \<sigma>\<^sub>2)) c l\<^sub>2\<close>
      using wcomp_sound[OF w2 winv_sound[OF w_of_sound[OF rel2]]] by (simp add: itrans_def)
    show \<open>\<not> wdisjoint (itrans (pr\<^sub>1, Suc m\<^sub>1, \<sigma>\<^sub>1)) (itrans (pr\<^sub>2, Suc m\<^sub>2, \<sigma>\<^sub>2))\<close>
      by (rule wdisjoint_sound[where l = col, OF s1[unfolded lc(1)] s2[unfolded lc(2)]])
  qed
  have live': \<open>lcore (hd (tl Xs)) \<noteq> {}\<close>
    unfolding hdtl by (rule closure_live_kernel[OF mem1' j1'])
  have ic1: \<open>icur G (hd (tl Xs)) c (pr\<^sub>1, m\<^sub>1, \<sigma>\<^sub>1)\<close>
    using mem1' j1' w1 unfolding hdtl icur_def by auto
  have ic2: \<open>icur G (hd (tl Xs)) c (pr\<^sub>2, m\<^sub>2, \<sigma>\<^sub>2)\<close>
    using mem2' j2' w2 unfolding hdtl icur_def by auto
  have edge1: \<open>pstk ! 1 < length (pr0_states G Shn) \<and>
      (pstk ! 1, X\<^sub>0) \<in> set (pin_edges (pgtab G (pr0_states G Shn)) (pstk ! 0))\<close>
    using strack_edge[OF tr1 mem1' j1' lt1 X1] .
  have pool: \<open>\<And>pr m R j. (pr, m, R) \<in> set (xclosure_auto G (Xs ! 1)) \<Longrightarrow>
      j \<in> irep_set R \<Longrightarrow> ihas (map (wreach G) (pr0_states G Shn) ! (pstk ! 1)) pr m\<close>
  proof -
    fix pr m R j
    assume mm: \<open>(pr, m, R) \<in> set (xclosure_auto G (Xs ! 1))\<close> and jj: \<open>j \<in> irep_set R\<close>
    from strack_pool[OF tr' live' mm[folded hdtl] jj] obtain \<rho> where
      \<open>(pr, m, \<rho>) \<in> set (wreach G (pr0_states G Shn ! (tl pstk ! 0)))\<close> by blast
    then have \<open>(pr, m, \<rho>) \<in> set (map (wreach G) (pr0_states G Shn) ! (pstk ! 1))\<close>
      using edge1 tlp by simp
    then show \<open>ihas (map (wreach G) (pr0_states G Shn) ! (pstk ! 1)) pr m\<close>
      unfolding ihas_def list_ex_iff by auto
  qed
  have h1: \<open>ihas (map (wreach G) (pr0_states G Shn) ! (pstk ! 1)) pr\<^sub>1 m\<^sub>1\<close>
    by (rule pool[OF mem1' j1'])
  have h2: \<open>ihas (map (wreach G) (pr0_states G Shn) ! (pstk ! 1)) pr\<^sub>2 m\<^sub>2\<close>
    by (rule pool[OF mem2' j2'])
  show ?thesis
    using \<alpha>1 X1 X2 eq rig tr' live' ic1 ic2 edge1 h1 h2 by auto
qed

text \<open>One step of the descent: a realised triple fires, or has a realised
  successor with fewer frames, or as many frames and fewer rounds.\<close>

lemma strack_step:
  assumes tr: \<open>strack G Shn Xs \<alpha> pstk\<close> and fresh: \<open>fresh_name G Shn\<close>
    and live: \<open>lcore (hd Xs) \<noteq> {}\<close>
    and c1: \<open>icur_at G (hd Xs) t\<^sub>1 c cur\<^sub>1\<close> and c2: \<open>icur_at G (hd Xs) t\<^sub>2 c cur\<^sub>2\<close>
  shows \<open>ifires Shn (anchored_nts G) (pstk ! 0, cur\<^sub>1, cur\<^sub>2) \<or>
    (\<exists>Xs' \<alpha>' pstk' t\<^sub>1' t\<^sub>2' cur\<^sub>1' cur\<^sub>2'.
       (pstk' ! 0, cur\<^sub>1', cur\<^sub>2') \<in> set (isuccs Shn (map (wreach G) (pr0_states G Shn))
          (pgtab G (pr0_states G Shn)) (anchored_nts G) (pstk ! 0, cur\<^sub>1, cur\<^sub>2)) \<and>
       strack G Shn Xs' \<alpha>' pstk' \<and> lcore (hd Xs') \<noteq> {} \<and>
       icur_at G (hd Xs') t\<^sub>1' c cur\<^sub>1' \<and> icur_at G (hd Xs') t\<^sub>2' c cur\<^sub>2' \<and>
       (length Xs' < length Xs \<or> length Xs' = length Xs \<and> t\<^sub>1' + t\<^sub>2' < t\<^sub>1 + t\<^sub>2))\<close>
proof -
  obtain pr\<^sub>1 m\<^sub>1 \<sigma>\<^sub>1 where cur1: \<open>cur\<^sub>1 = (pr\<^sub>1, m\<^sub>1, \<sigma>\<^sub>1)\<close> by (cases cur\<^sub>1) auto
  obtain pr\<^sub>2 m\<^sub>2 \<sigma>\<^sub>2 where cur2: \<open>cur\<^sub>2 = (pr\<^sub>2, m\<^sub>2, \<sigma>\<^sub>2)\<close> by (cases cur\<^sub>2) auto
  have len: \<open>length Xs = length \<alpha> + 1\<close> using dshapeD(1)[OF strackD(1)[OF tr]] .
  have plen: \<open>length pstk = length Xs\<close> using didx_ok_len[OF strackD(2)[OF tr]] .
  have c1': \<open>icur_at G (hd Xs) t\<^sub>1 c (pr\<^sub>1, m\<^sub>1, \<sigma>\<^sub>1)\<close> using c1 cur1 by simp
  have c2': \<open>icur_at G (hd Xs) t\<^sub>2 c (pr\<^sub>2, m\<^sub>2, \<sigma>\<^sub>2)\<close> using c2 cur2 by simp
  consider (A) \<open>m\<^sub>1 = 0\<close> \<open>fst pr\<^sub>1 \<noteq> Shn\<close>
    | (B) \<open>\<not> (m\<^sub>1 = 0 \<and> fst pr\<^sub>1 \<noteq> Shn)\<close> \<open>m\<^sub>2 = 0\<close> \<open>fst pr\<^sub>2 \<noteq> Shn\<close>
    | (C) \<open>m\<^sub>1 = 0\<close> \<open>fst pr\<^sub>1 = Shn\<close> \<open>m\<^sub>2 = 0\<close> \<open>fst pr\<^sub>2 = Shn\<close>
    | (D1) \<open>m\<^sub>1 = 0\<close> \<open>fst pr\<^sub>1 = Shn\<close> \<open>m\<^sub>2 \<noteq> 0\<close>
    | (D2) \<open>m\<^sub>2 = 0\<close> \<open>fst pr\<^sub>2 = Shn\<close> \<open>m\<^sub>1 \<noteq> 0\<close>
    | (E) \<open>m\<^sub>1 \<noteq> 0\<close> \<open>m\<^sub>2 \<noteq> 0\<close>
    by auto
  then show ?thesis
  proof cases
    case A
    have c1z: \<open>icur_at G (hd Xs) t\<^sub>1 c (pr\<^sub>1, 0, \<sigma>\<^sub>1)\<close> using c1' A(1) by simp
    obtain t' cur' where lt: \<open>t' < t\<^sub>1\<close> and ic: \<open>icur_at G (hd Xs) t' c cur'\<close>
      and mem: \<open>cur' \<in> set (ipreds (map (wreach G) (pr0_states G Shn)) (pstk ! 0)
        (fst pr\<^sub>1) \<sigma>\<^sub>1)\<close>
      using strack_predict[OF tr live c1z A(2)] by blast
    have succ: \<open>(pstk ! 0, cur', cur\<^sub>2) \<in> set (isuccs Shn (map (wreach G) (pr0_states G Shn))
      (pgtab G (pr0_states G Shn)) (anchored_nts G) (pstk ! 0, cur\<^sub>1, cur\<^sub>2))\<close>
      using mem A by (simp add: cur1 cur2)
    show ?thesis using succ tr live ic c2 lt
      by (intro disjI2 exI[of _ Xs] exI[of _ \<alpha>] exI[of _ pstk] exI[of _ t'] exI[of _ t\<^sub>2]
          exI[of _ cur'] exI[of _ cur\<^sub>2] conjI) auto
  next
    case B
    have c2z: \<open>icur_at G (hd Xs) t\<^sub>2 c (pr\<^sub>2, 0, \<sigma>\<^sub>2)\<close> using c2' B(2) by simp
    obtain t' cur' where lt: \<open>t' < t\<^sub>2\<close> and ic: \<open>icur_at G (hd Xs) t' c cur'\<close>
      and mem: \<open>cur' \<in> set (ipreds (map (wreach G) (pr0_states G Shn)) (pstk ! 0)
        (fst pr\<^sub>2) \<sigma>\<^sub>2)\<close>
      using strack_predict[OF tr live c2z B(3)] by blast
    have succ: \<open>(pstk ! 0, cur\<^sub>1, cur') \<in> set (isuccs Shn (map (wreach G) (pr0_states G Shn))
      (pgtab G (pr0_states G Shn)) (anchored_nts G) (pstk ! 0, cur\<^sub>1, cur\<^sub>2))\<close>
      using mem B by (simp add: cur1 cur2 B(1))
    show ?thesis using succ tr live ic c1 lt
      by (intro disjI2 exI[of _ Xs] exI[of _ \<alpha>] exI[of _ pstk] exI[of _ t\<^sub>1] exI[of _ t']
          exI[of _ cur\<^sub>1] exI[of _ cur'] conjI) auto
  next
    case C
    have c1z: \<open>icur_at G (hd Xs) t\<^sub>1 c (pr\<^sub>1, 0, \<sigma>\<^sub>1)\<close> using c1' C(1) by simp
    have c2z: \<open>icur_at G (hd Xs) t\<^sub>2 c (pr\<^sub>2, 0, \<sigma>\<^sub>2)\<close> using c2' C(3) by simp
    obtain R\<^sub>1 j\<^sub>1 where s1: \<open>(pr\<^sub>1, 0, R\<^sub>1) \<in> set (xslots G (hd Xs) (xiter G (hd Xs) t\<^sub>1))\<close>
      and j1: \<open>j\<^sub>1 \<in> irep_set R\<^sub>1\<close> and w1: \<open>wsat \<sigma>\<^sub>1 c j\<^sub>1\<close>
      using c1z unfolding icur_at_def by auto
    obtain R\<^sub>2 j\<^sub>2 where s2: \<open>(pr\<^sub>2, 0, R\<^sub>2) \<in> set (xslots G (hd Xs) (xiter G (hd Xs) t\<^sub>2))\<close>
      and j2: \<open>j\<^sub>2 \<in> irep_set R\<^sub>2\<close> and w2: \<open>wsat \<sigma>\<^sub>2 c j\<^sub>2\<close>
      using c2z unfolding icur_at_def by auto
    have r1: \<open>irep_set R\<^sub>1 = {istart_ind G}\<close>
      using strack_start_item[OF tr fresh s1 C(2)] by simp
    have r2: \<open>irep_set R\<^sub>2 = {istart_ind G}\<close>
      using strack_start_item[OF tr fresh s2 C(4)] by simp
    have \<open>j\<^sub>1 = j\<^sub>2\<close> using j1 j2 r1 r2 by simp
    then have nd: \<open>\<not> wdisjoint \<sigma>\<^sub>1 \<sigma>\<^sub>2\<close> using wdisjoint_sound w1 w2 by blast
    show ?thesis using nd by (simp add: cur1 cur2 C)
  next
    case D1
    show ?thesis using D1 by (simp add: cur1 cur2)
  next
    case D2
    show ?thesis using D2 by (simp add: cur1 cur2)
  next
    case E
    obtain m\<^sub>1' where m1: \<open>m\<^sub>1 = Suc m\<^sub>1'\<close> using E(1) by (cases m\<^sub>1) auto
    obtain m\<^sub>2' where m2: \<open>m\<^sub>2 = Suc m\<^sub>2'\<close> using E(2) by (cases m\<^sub>2) auto
    have c1s: \<open>icur_at G (hd Xs) t\<^sub>1 c (pr\<^sub>1, Suc m\<^sub>1', \<sigma>\<^sub>1)\<close> using c1' m1 by simp
    have c2s: \<open>icur_at G (hd Xs) t\<^sub>2 c (pr\<^sub>2, Suc m\<^sub>2', \<sigma>\<^sub>2)\<close> using c2' m2 by simp
    obtain X\<^sub>0 RA \<alpha>' where al: \<open>\<alpha> = (X\<^sub>0, RA) # \<alpha>'\<close>
      and x1: \<open>fst (snd pr\<^sub>1 ! m\<^sub>1') = X\<^sub>0\<close> and x2: \<open>fst (snd pr\<^sub>2 ! m\<^sub>2') = X\<^sub>0\<close>
      and rig: \<open>irigid (anchored_nts G) X\<^sub>0 \<longrightarrow>
        \<not> wdisjoint (itrans (pr\<^sub>1, Suc m\<^sub>1', \<sigma>\<^sub>1)) (itrans (pr\<^sub>2, Suc m\<^sub>2', \<sigma>\<^sub>2))\<close>
      and tr': \<open>strack G Shn (tl Xs) \<alpha>' (tl pstk)\<close> and live': \<open>lcore (hd (tl Xs)) \<noteq> {}\<close>
      and ic1: \<open>icur G (hd (tl Xs)) c (pr\<^sub>1, m\<^sub>1', \<sigma>\<^sub>1)\<close>
      and ic2: \<open>icur G (hd (tl Xs)) c (pr\<^sub>2, m\<^sub>2', \<sigma>\<^sub>2)\<close>
      and edge: \<open>(pstk ! 1, X\<^sub>0) \<in> set (pin_edges (pgtab G (pr0_states G Shn)) (pstk ! 0))\<close>
      and h1: \<open>ihas (map (wreach G) (pr0_states G Shn) ! (pstk ! 1)) pr\<^sub>1 m\<^sub>1'\<close>
      and h2: \<open>ihas (map (wreach G) (pr0_states G Shn) ! (pstk ! 1)) pr\<^sub>2 m\<^sub>2'\<close>
      using strack_pop_step[OF tr live c1s c2s] by blast
    have hlen: \<open>length Xs = length \<alpha>' + 2\<close> using len al by simp
    have nth1: \<open>tl pstk ! 0 = pstk ! 1\<close> using plen hlen by (simp add: nth_tl)
    have mf: \<open>(pstk ! 1, (pr\<^sub>1, m\<^sub>1', \<sigma>\<^sub>1), (pr\<^sub>2, m\<^sub>2', \<sigma>\<^sub>2)) \<in> set (List.map_filter
      (\<lambda>(p, X'). if X' = X\<^sub>0 \<and> ihas (map (wreach G) (pr0_states G Shn) ! p) pr\<^sub>1 m\<^sub>1'
          \<and> ihas (map (wreach G) (pr0_states G Shn) ! p) pr\<^sub>2 m\<^sub>2'
        then Some (p, (pr\<^sub>1, m\<^sub>1', \<sigma>\<^sub>1), (pr\<^sub>2, m\<^sub>2', \<sigma>\<^sub>2)) else None)
      (pin_edges (pgtab G (pr0_states G Shn)) (pstk ! 0)))\<close>
      by (rule map_filterI[OF edge])
        (simp add: h1[unfolded One_nat_def] h2[unfolded One_nat_def])
    have succ: \<open>(pstk ! 1, (pr\<^sub>1, m\<^sub>1', \<sigma>\<^sub>1), (pr\<^sub>2, m\<^sub>2', \<sigma>\<^sub>2)) \<in> set (isuccs Shn
      (map (wreach G) (pr0_states G Shn)) (pgtab G (pr0_states G Shn)) (anchored_nts G)
      (pstk ! 0, cur\<^sub>1, cur\<^sub>2))\<close>
      using rig mf by (simp add: cur1 cur2 m1 m2 x1 x2 cong: if_cong)
    have ict1: \<open>icur_at G (hd (tl Xs)) (xfuel G (hd (tl Xs))) c (pr\<^sub>1, m\<^sub>1', \<sigma>\<^sub>1)\<close>
      using ic1 icur_at_fuel by blast
    have ict2: \<open>icur_at G (hd (tl Xs)) (xfuel G (hd (tl Xs))) c (pr\<^sub>2, m\<^sub>2', \<sigma>\<^sub>2)\<close>
      using ic2 icur_at_fuel by blast
    have shorter: \<open>length (tl Xs) < length Xs\<close> using hlen by simp
    show ?thesis
      by (rule disjI2, rule exI[of _ \<open>tl Xs\<close>], rule exI[of _ \<alpha>'],
          rule exI[of _ \<open>tl pstk\<close>], rule exI[of _ \<open>xfuel G (hd (tl Xs))\<close>],
          rule exI[of _ \<open>xfuel G (hd (tl Xs))\<close>],
          rule exI[of _ \<open>(pr\<^sub>1, m\<^sub>1', \<sigma>\<^sub>1)\<close>],
          rule exI[of _ \<open>(pr\<^sub>2, m\<^sub>2', \<sigma>\<^sub>2)\<close>], intro conjI)
        (use succ tr' live' ict1 ict2 shorter nth1 in auto)
  qed
qed

text \<open>The descent, by induction on the frames and then on the rounds: from a
  tracked stack whose top frame realises both cursors of a triple, the walk's
  successor relation reaches a triple that fires.\<close>

lemma strack_fires_at:
  \<open>\<forall>Xs \<alpha> pstk t\<^sub>1 t\<^sub>2 cur\<^sub>1 cur\<^sub>2. length Xs = n \<longrightarrow> t\<^sub>1 + t\<^sub>2 = k \<longrightarrow>
     strack G Shn Xs \<alpha> pstk \<longrightarrow> fresh_name G Shn \<longrightarrow> lcore (hd Xs) \<noteq> {} \<longrightarrow>
     icur_at G (hd Xs) t\<^sub>1 c cur\<^sub>1 \<longrightarrow> icur_at G (hd Xs) t\<^sub>2 c cur\<^sub>2 \<longrightarrow>
     (\<exists>t'. (\<lambda>t t'. t' \<in> set (isuccs Shn (map (wreach G) (pr0_states G Shn))
          (pgtab G (pr0_states G Shn)) (anchored_nts G) t))\<^sup>*\<^sup>* (pstk ! 0, cur\<^sub>1, cur\<^sub>2) t' \<and>
        ifires Shn (anchored_nts G) t')\<close>
proof (induction n arbitrary: k rule: less_induct)
  case (less n)
  note IHn = less.IH
  show ?case
  proof (induction k rule: less_induct)
    case (less k)
    note IHk = less.IH
    let ?R = \<open>\<lambda>t t'. t' \<in> set (isuccs Shn (map (wreach G) (pr0_states G Shn))
          (pgtab G (pr0_states G Shn)) (anchored_nts G) t)\<close>
    show ?case
    proof (intro allI impI)
      fix Xs \<alpha> pstk t\<^sub>1 t\<^sub>2 cur\<^sub>1 cur\<^sub>2
      assume len: \<open>length Xs = n\<close> and sum: \<open>t\<^sub>1 + t\<^sub>2 = k\<close>
        and tr: \<open>strack G Shn Xs \<alpha> pstk\<close>
        and fresh: \<open>fresh_name G Shn\<close> and live: \<open>lcore (hd Xs) \<noteq> {}\<close>
        and c1: \<open>icur_at G (hd Xs) t\<^sub>1 c cur\<^sub>1\<close> and c2: \<open>icur_at G (hd Xs) t\<^sub>2 c cur\<^sub>2\<close>
      from strack_step[OF tr fresh live c1 c2]
      show \<open>\<exists>t'. ?R\<^sup>*\<^sup>* (pstk ! 0, cur\<^sub>1, cur\<^sub>2) t' \<and> ifires Shn (anchored_nts G) t'\<close>
      proof
        assume \<open>ifires Shn (anchored_nts G) (pstk ! 0, cur\<^sub>1, cur\<^sub>2)\<close>
        then show ?thesis by blast
      next
        assume \<open>\<exists>Xs' \<alpha>' pstk' t\<^sub>1' t\<^sub>2' cur\<^sub>1' cur\<^sub>2'.
          (pstk' ! 0, cur\<^sub>1', cur\<^sub>2') \<in> set (isuccs Shn (map (wreach G) (pr0_states G Shn))
            (pgtab G (pr0_states G Shn)) (anchored_nts G) (pstk ! 0, cur\<^sub>1, cur\<^sub>2)) \<and>
          strack G Shn Xs' \<alpha>' pstk' \<and> lcore (hd Xs') \<noteq> {} \<and>
          icur_at G (hd Xs') t\<^sub>1' c cur\<^sub>1' \<and> icur_at G (hd Xs') t\<^sub>2' c cur\<^sub>2' \<and>
          (length Xs' < length Xs \<or> length Xs' = length Xs \<and> t\<^sub>1' + t\<^sub>2' < t\<^sub>1 + t\<^sub>2)\<close>
        then obtain Xs' \<alpha>' pstk' t\<^sub>1' t\<^sub>2' cur\<^sub>1' cur\<^sub>2'
          where succ: \<open>(pstk' ! 0, cur\<^sub>1', cur\<^sub>2') \<in> set (isuccs Shn
              (map (wreach G) (pr0_states G Shn)) (pgtab G (pr0_states G Shn))
              (anchored_nts G) (pstk ! 0, cur\<^sub>1, cur\<^sub>2))\<close>
            and tr': \<open>strack G Shn Xs' \<alpha>' pstk'\<close> and live': \<open>lcore (hd Xs') \<noteq> {}\<close>
            and c1': \<open>icur_at G (hd Xs') t\<^sub>1' c cur\<^sub>1'\<close>
            and c2': \<open>icur_at G (hd Xs') t\<^sub>2' c cur\<^sub>2'\<close>
            and dec: \<open>length Xs' < length Xs \<or>
              length Xs' = length Xs \<and> t\<^sub>1' + t\<^sub>2' < t\<^sub>1 + t\<^sub>2\<close>
          by blast
        from dec have \<open>\<exists>t'. ?R\<^sup>*\<^sup>* (pstk' ! 0, cur\<^sub>1', cur\<^sub>2') t' \<and>
            ifires Shn (anchored_nts G) t'\<close>
        proof
          assume lt: \<open>length Xs' < length Xs\<close>
          from IHn[of \<open>length Xs'\<close> \<open>t\<^sub>1' + t\<^sub>2'\<close>] lt len
          show ?thesis using tr' fresh live' c1' c2' by blast
        next
          assume \<open>length Xs' = length Xs \<and> t\<^sub>1' + t\<^sub>2' < t\<^sub>1 + t\<^sub>2\<close>
          with IHk[of \<open>t\<^sub>1' + t\<^sub>2'\<close>] len sum
          show ?thesis using tr' fresh live' c1' c2' by blast
        qed
        then show ?thesis using succ by (meson converse_rtranclp_into_rtranclp)
      qed
    qed
  qed
qed

theorem strack_fires:
  assumes tr: \<open>strack G Shn Xs \<alpha> pstk\<close>
    and fresh: \<open>fresh_name G Shn\<close>
    and live: \<open>lcore (hd Xs) \<noteq> {}\<close>
    and c1: \<open>icur G (hd Xs) c cur\<^sub>1\<close> and c2: \<open>icur G (hd Xs) c cur\<^sub>2\<close>
  shows \<open>\<exists>t'. (\<lambda>t t'. t' \<in> set (isuccs Shn (map (wreach G) (pr0_states G Shn))
        (pgtab G (pr0_states G Shn)) (anchored_nts G) t))\<^sup>*\<^sup>* (pstk ! 0, cur\<^sub>1, cur\<^sub>2) t' \<and>
      ifires Shn (anchored_nts G) t'\<close>
  using strack_fires_at[rule_format, OF refl refl tr fresh live] c1 c2
  unfolding icur_at_fuel by blast


section \<open>Sufficiency of the item-relative check\<close>

text \<open>The final assembly: \<open>rlalr_conflicts G Shn = []\<close> plus
  \<^const>\<open>fresh_name\<close> implies \<^const>\<open>mdet\<close>.  A determinism violation
  yields two live candidates at a tracked, live top frame; each candidate's
  runtime license transports to a static seed at the tracked state
  (\<^const>\<open>ireds_at\<close> / \<^const>\<open>ishifts\<close>) that the frame realises
  (\<^const>\<open>icur\<close>), the pair of cursors is in \<^const>\<open>ipairs_at\<close>, the
  empty report makes the walk return \<open>False\<close>, and \<open>strack_fires\<close> +
  \<open>ifire_sound\<close> close the contradiction.  \<open>None\<close>/\<open>None\<close> pairs are
  refuted by \<^const>\<open>rr_none_at\<close> directly; a reduce of the fresh start
  name cannot have a live successor.\<close>

text \<open>Membership constructors for the static seeds.\<close>

lemma ireds_at_memI:
  assumes cell: \<open>(i, (pr, length (snd pr)), t, \<tau>) \<in> set L\<close>
    and shn: \<open>fst pr \<noteq> Shn\<close>
    and wmem: \<open>(pr, length (snd pr), \<rho>) \<in> set (wreach G (sp ! i))\<close>
  shows \<open>(t, (pr, length (snd pr), \<tau>)) \<in> set (ireds_at G Shn sp L i)\<close>
  unfolding ireds_at_def Let_def
  by (rule map_filterI[OF cell]) (use shn wmem in \<open>auto simp: list_ex_iff\<close>)

lemma ishifts_memI:
  assumes \<open>(pr, m, \<rho>) \<in> set ws\<close> and \<open>m < length (snd pr)\<close>
    and \<open>fst (snd pr ! m) = Tm a\<close>
  shows \<open>(a, (pr, m, w_of (snd (snd pr ! m)))) \<in> set (ishifts ws)\<close>
  unfolding ishifts_def set_remdups
  by (rule map_filterI[OF assms(1)]) (use assms(2,3) in simp)

lemma ipairs_at_srI:
  assumes red: \<open>(Some a, c) \<in> set (ireds_at G Shn sp L i)\<close>
    and sh: \<open>(a, c') \<in> set (ishifts (wreach G (sp ! i)))\<close>
  shows \<open>(c, c') \<in> set (ipairs_at G Shn sp L i)\<close>
proof -
  have \<open>(c, c') \<in> set (concat (map (\<lambda>(t, c). case t of
        Some a \<Rightarrow> map (\<lambda>(a', c'). (c, c'))
            (filter (\<lambda>(a', c'). a' = a) (ishifts (wreach G (sp ! i))))
      | None \<Rightarrow> []) (ireds_at G Shn sp L i)))\<close>
    by (rule concat_map_memI[OF red]) (use sh in force)
  then show ?thesis unfolding ipairs_at_def Let_def by simp
qed

lemma ipairs_at_rrI:
  assumes r1: \<open>(Some a, (pr\<^sub>1, m\<^sub>1, \<tau>\<^sub>1)) \<in> set (ireds_at G Shn sp L i)\<close>
    and r2: \<open>(Some a, (pr\<^sub>2, m\<^sub>2, \<tau>\<^sub>2)) \<in> set (ireds_at G Shn sp L i)\<close>
    and ne: \<open>pr\<^sub>2 \<noteq> pr\<^sub>1\<close>
  shows \<open>((pr\<^sub>1, m\<^sub>1, \<tau>\<^sub>1), (pr\<^sub>2, m\<^sub>2, \<tau>\<^sub>2)) \<in> set (ipairs_at G Shn sp L i)\<close>
proof -
  have inner: \<open>((pr\<^sub>1, m\<^sub>1, \<tau>\<^sub>1), (pr\<^sub>2, m\<^sub>2, \<tau>\<^sub>2)) \<in> set (List.map_filter (\<lambda>(t', c').
      if fst c' \<noteq> fst (pr\<^sub>1, m\<^sub>1, \<tau>\<^sub>1) \<and> t' = Some a \<and> Some a \<noteq> None
      then Some ((pr\<^sub>1, m\<^sub>1, \<tau>\<^sub>1), c') else None)
      (ireds_at G Shn sp L i))\<close>
    by (rule map_filterI[OF r2]) (use ne in simp)
  have \<open>((pr\<^sub>1, m\<^sub>1, \<tau>\<^sub>1), (pr\<^sub>2, m\<^sub>2, \<tau>\<^sub>2)) \<in> set (concat (map (\<lambda>(t, c).
        List.map_filter (\<lambda>(t', c').
          if fst c' \<noteq> fst c \<and> t' = t \<and> t \<noteq> None then Some (c, c') else None)
          (ireds_at G Shn sp L i)) (ireds_at G Shn sp L i)))\<close>
    by (rule concat_map_memI[OF r1]) (use inner in simp)
  then show ?thesis unfolding ipairs_at_def Let_def by simp
qed

lemma rr_none_atI:
  assumes r1: \<open>(None, (pr\<^sub>1, m\<^sub>1, \<tau>\<^sub>1)) \<in> set (ireds_at G Shn sp L i)\<close>
    and r2: \<open>(None, (pr\<^sub>2, m\<^sub>2, \<tau>\<^sub>2)) \<in> set (ireds_at G Shn sp L i)\<close>
    and ne: \<open>pr\<^sub>2 \<noteq> pr\<^sub>1\<close>
  shows \<open>rr_none_at G Shn sp L i\<close>
proof -
  have inner: \<open>list_ex (\<lambda>(t', c'). fst c' \<noteq> fst (pr\<^sub>1, m\<^sub>1, \<tau>\<^sub>1) \<and> t' = None)
      (ireds_at G Shn sp L i)\<close>
    unfolding list_ex_iff by (rule bexI[OF _ r2]) (use ne in simp)
  have outer: \<open>list_ex (\<lambda>(t, c). t = None \<and>
      list_ex (\<lambda>(t', c'). fst c' \<noteq> fst c \<and> t' = None)
        (ireds_at G Shn sp L i)) (ireds_at G Shn sp L i)\<close>
    unfolding list_ex_iff
    by (rule bexI[OF _ r1]) (use inner in \<open>fastforce simp: list_ex_iff\<close>)
  show ?thesis unfolding rr_none_at_def Let_def using outer by simp
qed

lemma dcands_shift_or_reduce:
  assumes \<open>a \<in> set (dcands G i cells CL (Xs, w))\<close>
  shows \<open>a = DShift \<and> w \<noteq> [] \<or> (\<exists>pr. a = DReduce pr \<and>
      irep_nonempty (red_set CL pr) \<and> dlic i cells w pr (red_set CL pr))\<close>
  using assms unfolding dcands_def
  by (auto simp: Let_def split: if_splits list.splits)

text \<open>A reduce of the fresh start name has no live successor: the goto
  frame's kernel items would need \<open>Nt Shn\<close> at a dot of the exposed frame's
  closure, but \<open>Shn\<close> occurs in no grammar symbol.\<close>

lemma shn_reduce_dead:
  assumes tr: \<open>strack G Shn Xs \<alpha> pstk\<close>
    and fresh: \<open>fresh_name G Shn\<close>
    and step: \<open>mstep G (Xs, w) (DReduce pr) = Some gc'\<close>
    and shn: \<open>fst pr = Shn\<close>
    and lv: \<open>dlive gc'\<close>
  shows False
proof -
  note mt = strackD(2)[OF tr]
  have step': \<open>mstep_cached G (map (xclosure_auto G) Xs) (Xs, w) (DReduce pr) = Some gc'\<close>
    using step unfolding mstep_def by simp
  define d where \<open>d = length (snd pr)\<close>
  have d_lt: \<open>d < length Xs\<close>
    unfolding d_def by (rule mstep_reduce_shape[OF step']) blast
  have gc': \<open>gc' = (lgoto (map (xclosure_auto G) Xs ! d) (Nt (fst pr))
        (red_set (hd (map (xclosure_auto G) Xs)) pr) # drop d Xs, w)\<close>
    unfolding d_def by (rule mstep_reduce_shape[OF step']) blast
  have lvt: \<open>dlive (lgoto (xclosure_auto G (Xs ! d)) (Nt Shn)
      (red_set (hd (map (xclosure_auto G) Xs)) pr) # drop d Xs, w)\<close>
    using lv unfolding gc' shn using d_lt by simp
  from lvt obtain pr\<^sub>1 m\<^sub>1 R\<^sub>1 j\<^sub>1 where
    itm0: \<open>(pr\<^sub>1, m\<^sub>1, R\<^sub>1) \<in> set (hd (lgoto (xclosure_auto G (Xs ! d)) (Nt Shn)
        (red_set (hd (map (xclosure_auto G) Xs)) pr) # drop d Xs))\<close>
    and jR1: \<open>j\<^sub>1 \<in> irep_set R\<^sub>1\<close>
    by (blast elim: dliveE)
  have itm: \<open>(pr\<^sub>1, m\<^sub>1, R\<^sub>1) \<in> set (lgoto (xclosure_auto G (Xs ! d)) (Nt Shn)
      (red_set (hd (map (xclosure_auto G) Xs)) pr))\<close>
    using itm0 by simp
  obtain m\<^sub>0 where m1: \<open>m\<^sub>1 = Suc m\<^sub>0\<close>
    using lgoto_dot_pos[OF itm] by (cases m\<^sub>1) auto
  from lgoto_kernel_step[OF itm[unfolded m1]] obtain R\<^sub>s where
    src: \<open>(pr\<^sub>1, m\<^sub>0, R\<^sub>s) \<in> set (xclosure_auto G (Xs ! d))\<close>
    and m0lt: \<open>m\<^sub>0 < length (snd pr\<^sub>1)\<close>
    and dsym: \<open>fst (snd pr\<^sub>1 ! m\<^sub>0) = Nt Shn\<close>
    and Req: \<open>R\<^sub>1 = irep_inter R\<^sub>s (irep_pre (snd (snd pr\<^sub>1 ! m\<^sub>0))
        (red_set (hd (map (xclosure_auto G) Xs)) pr))\<close> .
  have jRs: \<open>j\<^sub>1 \<in> irep_set R\<^sub>s\<close> using jR1 unfolding Req by simp
  have lived: \<open>lcore (Xs ! d) \<noteq> {}\<close> by (rule closure_live_kernel[OF src jRs])
  have pd_lt: \<open>pstk ! d < length (pr0_states G Shn)\<close>
    and coverd: \<open>lcore (Xs ! d) \<subseteq> set (pr0_states G Shn ! (pstk ! d))\<close>
    using didx_okD[OF mt d_lt lived] by blast+
  have kernD: \<open>\<And>pr' m' R'. (pr', m', R') \<in> set (Xs ! d) \<Longrightarrow>
      irep_nonempty R' \<Longrightarrow> (pr', m') \<in> set (pr0_states G Shn ! (pstk ! d))\<close>
    by (blast intro: lcore_subD_ne[OF coverd])
  have srcC: \<open>(pr\<^sub>1, m\<^sub>0) \<in> set (creach G (pr0_states G Shn ! (pstk ! d)))\<close>
    by (rule xclosure_auto_live_creach[OF kernD src jRs])
  have crU: \<open>set (creach G (pr0_states G Shn ! (pstk ! d))) \<subseteq> cuniv G Shn\<close>
    by (rule creach_univ[OF pr0_states_univ[OF nth_mem[OF pd_lt]]])
  have \<open>fst (snd pr\<^sub>1 ! m\<^sub>0) \<in> set (gram_syms G)\<close>
    by (rule dot_sym_gram[OF crU srcC m0lt])
  then have inG: \<open>Nt Shn \<in> set (gram_syms G)\<close> unfolding dsym .
  have \<open>Nt Shn \<notin> set (gram_syms G)\<close>
  proof
    assume mem: \<open>Nt Shn \<in> set (gram_syms G)\<close>
    show False
    proof (cases \<open>Nt Shn = Nt (istart G)\<close>)
      case True
      then show False using fresh unfolding fresh_name_def by simp
    next
      case False
      have inL: \<open>Nt Shn \<in> set (concat (map (\<lambda>(A, y). map fst y) (iprods G)))\<close>
        using mem False unfolding gram_syms_def by (auto split: if_splits)
      from inL obtain A rhs where pmem: \<open>(A, rhs) \<in> set (iprods G)\<close>
        and inrhs: \<open>Nt Shn \<in> set (map fst rhs)\<close> by fastforce
      from inrhs obtain e where emem: \<open>e \<in> set rhs\<close>
        and efst: \<open>fst e = Nt Shn\<close> by auto
      obtain X r where eeq: \<open>e = (X, r)\<close> by (cases e)
      have ball2: \<open>\<forall>(X', r') \<in> set rhs. X' \<noteq> Nt Shn\<close>
        using fresh pmem unfolding fresh_name_def by fastforce
      have \<open>X \<noteq> Nt Shn\<close> using ball2 emem unfolding eeq by fastforce
      then show False using efst eeq by simp
    qed
  qed
  then show False using inG by simp
qed

text \<open>Each runtime license transports to a static seed at the tracked
  state: the driver's reduce cell is a cell of \<^const>\<open>la_fix\<close> at the
  top frame's index, the item it licenses is in the top frame's closure with
  an indentation the cell's relation holds at (\<^const>\<open>icur\<close>), and
  \<^text>\<open>strack_pool\<close> places the item in the state's \<^const>\<open>wreach\<close>.\<close>

lemma reduce_seed_Some:
  assumes tr: \<open>strack G Shn Xs \<alpha> pstk\<close>
    and live: \<open>lcore (hd Xs) \<noteq> {}\<close>
    and ne: \<open>Xs \<noteq> []\<close>
    and lic: \<open>dlic (pstk ! 0) (red_buckets G Shn (length (pr0_states G Shn)) ! (pstk ! 0))
        ((a, c) # w') pr (red_set (xclosure_auto G (hd Xs)) pr)\<close>
    and shn: \<open>fst pr \<noteq> Shn\<close>
  shows \<open>\<exists>\<tau>. (Some a, (pr, length (snd pr), \<tau>)) \<in> set (ireds_at G Shn (pr0_states G Shn)
          (la_fix G Shn) (pstk ! 0)) \<and>
        icur G (hd Xs) c (pr, length (snd pr), \<tau>)\<close>
proof -
  note mt = strackD(2)[OF tr]
  have z_lt: \<open>0 < length Xs\<close> using ne by auto
  have hd0: \<open>hd Xs = Xs ! 0\<close> using ne by (simp add: hd_conv_nth)
  have i_lt: \<open>pstk ! 0 < length (pr0_states G Shn)\<close>
    using didx_okD[OF mt z_lt] live unfolding hd0 by blast
  from dlicE[OF lic] obtain \<tau> where
    cellb: \<open>(pstk ! 0, (pr, length (snd pr)), Some a, \<tau>)
        \<in> set (red_buckets G Shn (length (pr0_states G Shn)) ! (pstk ! 0))\<close>
    and sat: \<open>irep_ex_wsat \<tau> c (red_set (xclosure_auto G (hd Xs)) pr)\<close> .
  have cell: \<open>(pstk ! 0, (pr, length (snd pr)), Some a, \<tau>) \<in> set (la_fix G Shn)\<close>
    using red_buckets_memD[OF i_lt cellb] by blast
  from sat obtain j\<^sub>r where
    jr: \<open>j\<^sub>r \<in> irep_set (red_set (xclosure_auto G (hd Xs)) pr)\<close>
    and wt: \<open>wsat \<tau> c j\<^sub>r\<close>
    unfolding irep_ex_wsat_correct by blast
  from jr obtain R\<^sub>r where
    mem: \<open>(pr, length (snd pr), R\<^sub>r) \<in> set (xclosure_auto G (hd Xs))\<close>
    and jrR: \<open>j\<^sub>r \<in> irep_set R\<^sub>r\<close>
    unfolding red_set_correct by blast
  from strack_pool[OF tr live mem jrR] obtain \<rho> where
    wr: \<open>(pr, length (snd pr), \<rho>) \<in> set (wreach G (pr0_states G Shn ! (pstk ! 0)))\<close>
    by blast
  have \<open>icur G (hd Xs) c (pr, length (snd pr), \<tau>)\<close>
    unfolding icur_def using mem jrR wt by auto
  then show ?thesis using ireds_at_memI[OF cell shn wr] by blast
qed

lemma reduce_seed_None:
  assumes tr: \<open>strack G Shn Xs \<alpha> pstk\<close>
    and live: \<open>lcore (hd Xs) \<noteq> {}\<close>
    and ne: \<open>Xs \<noteq> []\<close>
    and lic: \<open>dlic (pstk ! 0) (red_buckets G Shn (length (pr0_states G Shn)) ! (pstk ! 0))
        [] pr (red_set (xclosure_auto G (hd Xs)) pr)\<close>
    and nonvac: \<open>irep_nonempty (red_set (xclosure_auto G (hd Xs)) pr)\<close>
    and shn: \<open>fst pr \<noteq> Shn\<close>
  shows \<open>\<exists>\<tau>. (None, (pr, length (snd pr), \<tau>)) \<in> set (ireds_at G Shn (pr0_states G Shn)
          (la_fix G Shn) (pstk ! 0))\<close>
proof -
  note mt = strackD(2)[OF tr]
  have z_lt: \<open>0 < length Xs\<close> using ne by auto
  have hd0: \<open>hd Xs = Xs ! 0\<close> using ne by (simp add: hd_conv_nth)
  have i_lt: \<open>pstk ! 0 < length (pr0_states G Shn)\<close>
    using didx_okD[OF mt z_lt] live unfolding hd0 by blast
  from dlic_NilE[OF lic] obtain \<tau> where
    cellb: \<open>(pstk ! 0, (pr, length (snd pr)), None, \<tau>)
        \<in> set (red_buckets G Shn (length (pr0_states G Shn)) ! (pstk ! 0))\<close> .
  have cell: \<open>(pstk ! 0, (pr, length (snd pr)), None, \<tau>) \<in> set (la_fix G Shn)\<close>
    using red_buckets_memD[OF i_lt cellb] by blast
  obtain j\<^sub>r where jr: \<open>j\<^sub>r \<in> irep_set (red_set (xclosure_auto G (hd Xs)) pr)\<close>
    using nonvac unfolding irep_nonempty_correct by blast
  from jr obtain R\<^sub>r where
    mem: \<open>(pr, length (snd pr), R\<^sub>r) \<in> set (xclosure_auto G (hd Xs))\<close>
    and jrR: \<open>j\<^sub>r \<in> irep_set R\<^sub>r\<close>
    unfolding red_set_correct by blast
  from strack_pool[OF tr live mem jrR] obtain \<rho> where
    wr: \<open>(pr, length (snd pr), \<rho>) \<in> set (wreach G (pr0_states G Shn ! (pstk ! 0)))\<close>
    by blast
  show ?thesis using ireds_at_memI[OF cell shn wr] by blast
qed

lemma shift_seed:
  assumes tr: \<open>strack G Shn Xs \<alpha> pstk\<close>
    and ne: \<open>Xs \<noteq> []\<close>
    and step: \<open>mstep G (Xs, w) DShift = Some gc'\<close>
    and lv: \<open>dlive gc'\<close>
  shows \<open>\<exists>a c w' c\<^sub>s. w = (a, c) # w' \<and>
      (a, c\<^sub>s) \<in> set (ishifts (wreach G (pr0_states G Shn ! (pstk ! 0)))) \<and>
      icur G (hd Xs) c c\<^sub>s\<close>
proof -
  have step': \<open>mstep_cached G (map (xclosure_auto G) Xs) (Xs, w) DShift = Some gc'\<close>
    using step unfolding mstep_def by simp
  from shift_live_srcE[OF step' lv] obtain a c w' pr m R j where
    w: \<open>w = (a, c) # w'\<close>
    and src0: \<open>(pr, m, R) \<in> set (hd (map (xclosure_auto G) Xs))\<close>
    and m_lt: \<open>m < length (snd pr)\<close>
    and sym: \<open>fst (snd pr ! m) = Tm a\<close>
    and jR: \<open>j \<in> irep_set R\<close>
    and rel: \<open>irel_sat (snd (snd pr ! m)) c j\<close> .
  have src: \<open>(pr, m, R) \<in> set (xclosure_auto G (hd Xs))\<close>
    using src0 ne by (simp add: hd_map)
  have live0: \<open>lcore (hd Xs) \<noteq> {}\<close> by (rule closure_live_kernel[OF src jR])
  from strack_pool[OF tr live0 src jR] obtain \<rho> where
    wr: \<open>(pr, m, \<rho>) \<in> set (wreach G (pr0_states G Shn ! (pstk ! 0)))\<close> by blast
  have memS: \<open>(a, (pr, m, w_of (snd (snd pr ! m)))) \<in>
      set (ishifts (wreach G (pr0_states G Shn ! (pstk ! 0))))\<close>
    by (rule ishifts_memI[OF wr m_lt sym])
  have \<open>icur G (hd Xs) c (pr, m, w_of (snd (snd pr ! m)))\<close>
    unfolding icur_def using src jR w_of_sound[OF rel] by auto
  then show ?thesis using w memS by blast
qed

text \<open>The sufficiency theorem: an empty report makes the pooled machine
  deterministic.  Cf.\ Barthwal (2010, Thm 5.4.4: conflict freedom on
  reachable states suffices) and Jourdan et al. (2012, Thm 4: validator
  soundness); the item-relative walk replaces their single-anchor comparison,
  which the test grammar \<open>xag\<close> refutes for the pooled machine.  The index
  the driver consulted is the top of the tracked stack, so the check at that
  one index covers both candidates.\<close>


theorem rlalr_sufficient:
  assumes chk: \<open>rlalr_conflicts G Shn = []\<close> and fresh: \<open>fresh_name G Shn\<close>
  shows \<open>mdet G Shn\<close>
  unfolding mdet_def
proof (intro allI impI)
  fix gc istk i redtab CL a\<^sub>1 a\<^sub>2 gc\<^sub>1 gc\<^sub>2
  assume reach: \<open>imreach G Shn (pgtab G (pr0_states G Shn)) (pr0_states G Shn) (gc, istk)\<close>
    and idef: \<open>i = hd istk\<close>
    and rdef: \<open>redtab = red_buckets G Shn (length (pr0_states G Shn)) ! i\<close>
    and cldef: \<open>CL = xclosure_auto G (hd (fst gc))\<close>
    and c1: \<open>a\<^sub>1 \<in> set (dcands G i redtab CL gc)\<close>
    and c2: \<open>a\<^sub>2 \<in> set (dcands G i redtab CL gc)\<close>
    and ne12: \<open>a\<^sub>1 \<noteq> a\<^sub>2\<close>
    and s1: \<open>mstep G gc a\<^sub>1 = Some gc\<^sub>1\<close> and s2: \<open>mstep G gc a\<^sub>2 = Some gc\<^sub>2\<close>
    and lv1: \<open>dlive gc\<^sub>1\<close> and lv2: \<open>dlive gc\<^sub>2\<close>
  obtain Xs w where gc: \<open>gc = (Xs, w)\<close> by (cases gc)
  have ne: \<open>Xs \<noteq> []\<close> and live0: \<open>lcore (hd Xs) \<noteq> {}\<close>
    using imreach_dlive[OF reach] unfolding gc dlive_def by (simp_all add: live_lcore)
  have clX: \<open>CL = xclosure_auto G (hd Xs)\<close> using cldef unfolding gc by simp
  from imreach_strack[OF reach fresh] obtain \<alpha> where
    tr: \<open>strack G Shn Xs \<alpha> istk\<close> unfolding gc by auto
  note mt = strackD(2)[OF tr]
  have z_lt: \<open>0 < length Xs\<close> using ne by auto
  have hd0: \<open>hd Xs = Xs ! 0\<close> using ne by (simp add: hd_conv_nth)
  have istk_ne: \<open>istk \<noteq> []\<close> using didx_ok_len[OF mt] ne by auto
  have hdi: \<open>hd istk = istk ! 0\<close> using istk_ne by (simp add: hd_conv_nth)
  have i_lt: \<open>istk ! 0 < length (pr0_states G Shn)\<close>
    using didx_okD[OF mt z_lt] live0 unfolding hd0 by blast
  have cs1: \<open>a\<^sub>1 = DShift \<and> w \<noteq> [] \<or> (\<exists>pr. a\<^sub>1 = DReduce pr \<and>
      irep_nonempty (red_set CL pr) \<and> dlic i redtab w pr (red_set CL pr))\<close>
    using dcands_shift_or_reduce c1 unfolding gc by blast
  have cs2: \<open>a\<^sub>2 = DShift \<and> w \<noteq> [] \<or> (\<exists>pr. a\<^sub>2 = DReduce pr \<and>
      irep_nonempty (red_set CL pr) \<and> dlic i redtab w pr (red_set CL pr))\<close>
    using dcands_shift_or_reduce c2 unfolding gc by blast
  have nc: \<open>\<not> rlalr_conflict_at G Shn (pr0_states G Shn) (la_fix G Shn) (istk ! 0)\<close>
  proof
    assume \<open>rlalr_conflict_at G Shn (pr0_states G Shn) (la_fix G Shn) (istk ! 0)\<close>
    then have \<open>istk ! 0 \<in> set (rlalr_conflicts G Shn)\<close>
      unfolding rlalr_conflicts_def Let_def using i_lt by simp
    then show False using chk by simp
  qed
  have no_none: \<open>\<not> rr_none_at G Shn (pr0_states G Shn) (la_fix G Shn) (istk ! 0)\<close>
    using nc unfolding rlalr_conflict_at_def by (auto simp: list_ex_iff)
  have walkF: \<open>\<And>c\<^sub>1 c\<^sub>2. (c\<^sub>1, c\<^sub>2) \<in> set (ipairs_at G Shn (pr0_states G Shn)
        (la_fix G Shn) (istk ! 0)) \<Longrightarrow>
      ifire Shn (map (wreach G) (pr0_states G Shn)) (pgtab G (pr0_states G Shn))
        (anchored_nts G) (ifuel (map (wreach G) (pr0_states G Shn)))
        [] [(istk ! 0, c\<^sub>1, c\<^sub>2)] = False\<close>
    using nc unfolding rlalr_conflict_at_def
    by (auto simp: list_ex_iff simp del: ifire.simps ifire_Cons)
  have kill: \<open>\<And>c c\<^sub>1 c\<^sub>2. (c\<^sub>1, c\<^sub>2) \<in> set (ipairs_at G Shn (pr0_states G Shn)
        (la_fix G Shn) (istk ! 0)) \<Longrightarrow>
      icur G (hd Xs) c c\<^sub>1 \<Longrightarrow> icur G (hd Xs) c c\<^sub>2 \<Longrightarrow> False\<close>
  proof -
    fix c c\<^sub>1 c\<^sub>2
    assume pm: \<open>(c\<^sub>1, c\<^sub>2) \<in> set (ipairs_at G Shn (pr0_states G Shn)
        (la_fix G Shn) (istk ! 0))\<close>
      and i1: \<open>icur G (hd Xs) c c\<^sub>1\<close> and i2: \<open>icur G (hd Xs) c c\<^sub>2\<close>
    from strack_fires[OF tr fresh live0 i1 i2] obtain t' where
      chain: \<open>(\<lambda>t t'. t' \<in> set (isuccs Shn (map (wreach G) (pr0_states G Shn))
          (pgtab G (pr0_states G Shn)) (anchored_nts G) t))\<^sup>*\<^sup>* (istk ! 0, c\<^sub>1, c\<^sub>2) t'\<close>
      and fi: \<open>ifires Shn (anchored_nts G) t'\<close> by blast
    show False using ifire_sound[OF walkF[OF pm] chain] fi by simp
  qed
  have sr_case: \<open>mstep G gc DShift = Some gc\<^sub>s \<Longrightarrow> dlive gc\<^sub>s \<Longrightarrow>
      mstep G gc (DReduce pr) = Some gc\<^sub>r \<Longrightarrow> dlive gc\<^sub>r \<Longrightarrow>
      dlic i redtab w pr (red_set CL pr) \<Longrightarrow> False\<close> for gc\<^sub>s gc\<^sub>r pr
  proof -
    fix gc\<^sub>s gc\<^sub>r pr
    assume ss: \<open>mstep G gc DShift = Some gc\<^sub>s\<close> and lvs: \<open>dlive gc\<^sub>s\<close>
      and sr: \<open>mstep G gc (DReduce pr) = Some gc\<^sub>r\<close> and lvr: \<open>dlive gc\<^sub>r\<close>
      and lic: \<open>dlic i redtab w pr (red_set CL pr)\<close>
    from shift_seed[OF tr ne ss[unfolded gc] lvs] obtain a c w' c\<^sub>s where
      w: \<open>w = (a, c) # w'\<close>
      and shm: \<open>(a, c\<^sub>s) \<in> set (ishifts (wreach G (pr0_states G Shn ! (istk ! 0))))\<close>
      and ics: \<open>icur G (hd Xs) c c\<^sub>s\<close> by blast
    show False
    proof (cases \<open>fst pr = Shn\<close>)
      case True
      show False by (rule shn_reduce_dead[OF tr fresh sr[unfolded gc] True lvr])
    next
      case False
      have lic': \<open>dlic (istk ! 0) (red_buckets G Shn (length (pr0_states G Shn)) ! (istk ! 0))
          ((a, c) # w') pr (red_set (xclosure_auto G (hd Xs)) pr)\<close>
        using lic unfolding idef rdef clX w hdi by simp
      from reduce_seed_Some[OF tr live0 ne lic' False] obtain \<tau> where
        rdm: \<open>(Some a, (pr, length (snd pr), \<tau>)) \<in> set (ireds_at G Shn (pr0_states G Shn)
            (la_fix G Shn) (istk ! 0))\<close>
        and icr: \<open>icur G (hd Xs) c (pr, length (snd pr), \<tau>)\<close> by blast
      have pm: \<open>((pr, length (snd pr), \<tau>), c\<^sub>s) \<in> set (ipairs_at G Shn (pr0_states G Shn)
          (la_fix G Shn) (istk ! 0))\<close>
        by (rule ipairs_at_srI[OF rdm shm])
      show False by (rule kill[OF pm icr ics])
    qed
  qed
  consider
      (SS) \<open>a\<^sub>1 = DShift\<close> and \<open>a\<^sub>2 = DShift\<close>
    | (SR) pr\<^sub>2 where \<open>a\<^sub>1 = DShift\<close> \<open>a\<^sub>2 = DReduce pr\<^sub>2\<close>
        \<open>irep_nonempty (red_set CL pr\<^sub>2)\<close> \<open>dlic i redtab w pr\<^sub>2 (red_set CL pr\<^sub>2)\<close>
    | (RS) pr\<^sub>1 where \<open>a\<^sub>2 = DShift\<close> \<open>a\<^sub>1 = DReduce pr\<^sub>1\<close>
        \<open>irep_nonempty (red_set CL pr\<^sub>1)\<close> \<open>dlic i redtab w pr\<^sub>1 (red_set CL pr\<^sub>1)\<close>
    | (RR) pr\<^sub>1 pr\<^sub>2 where \<open>a\<^sub>1 = DReduce pr\<^sub>1\<close> \<open>a\<^sub>2 = DReduce pr\<^sub>2\<close>
        \<open>irep_nonempty (red_set CL pr\<^sub>1)\<close> \<open>dlic i redtab w pr\<^sub>1 (red_set CL pr\<^sub>1)\<close>
        \<open>irep_nonempty (red_set CL pr\<^sub>2)\<close> \<open>dlic i redtab w pr\<^sub>2 (red_set CL pr\<^sub>2)\<close>
    using cs1 cs2 by blast
  then show False
  proof cases
    case SS
    then show False using ne12 by simp
  next
    case (SR pr\<^sub>2)
    show False by (rule sr_case[OF s1[unfolded SR(1)] lv1 s2[unfolded SR(2)] lv2 SR(4)])
  next
    case (RS pr\<^sub>1)
    show False by (rule sr_case[OF s2[unfolded RS(1)] lv2 s1[unfolded RS(2)] lv1 RS(4)])
  next
    case (RR pr\<^sub>1 pr\<^sub>2)
    have prne: \<open>pr\<^sub>2 \<noteq> pr\<^sub>1\<close> using ne12 unfolding RR(1) RR(2) by auto
    show False
    proof (cases \<open>fst pr\<^sub>1 = Shn\<close>)
      case True
      show False
        by (rule shn_reduce_dead[OF tr fresh s1[unfolded gc RR(1)] True lv1])
    next
      case False
      note shn1 = False
      show False
      proof (cases \<open>fst pr\<^sub>2 = Shn\<close>)
        case True
        show False
          by (rule shn_reduce_dead[OF tr fresh s2[unfolded gc RR(2)] True lv2])
      next
        case False
        note shn2 = False
        show False
        proof (cases w)
          case Nil
          have lic1: \<open>dlic (istk ! 0) (red_buckets G Shn
              (length (pr0_states G Shn)) ! (istk ! 0))
              [] pr\<^sub>1 (red_set (xclosure_auto G (hd Xs)) pr\<^sub>1)\<close>
            using RR(4) unfolding idef rdef clX Nil hdi by simp
          have lic2: \<open>dlic (istk ! 0) (red_buckets G Shn
              (length (pr0_states G Shn)) ! (istk ! 0))
              [] pr\<^sub>2 (red_set (xclosure_auto G (hd Xs)) pr\<^sub>2)\<close>
            using RR(6) unfolding idef rdef clX Nil hdi by simp
          have nv1: \<open>irep_nonempty (red_set (xclosure_auto G (hd Xs)) pr\<^sub>1)\<close>
            using RR(3) unfolding clX .
          have nv2: \<open>irep_nonempty (red_set (xclosure_auto G (hd Xs)) pr\<^sub>2)\<close>
            using RR(5) unfolding clX .
          from reduce_seed_None[OF tr live0 ne lic1 nv1 shn1] obtain \<tau>\<^sub>1 where
            m1: \<open>(None, (pr\<^sub>1, length (snd pr\<^sub>1), \<tau>\<^sub>1)) \<in> set (ireds_at G Shn
                (pr0_states G Shn) (la_fix G Shn) (istk ! 0))\<close> by blast
          from reduce_seed_None[OF tr live0 ne lic2 nv2 shn2] obtain \<tau>\<^sub>2 where
            m2: \<open>(None, (pr\<^sub>2, length (snd pr\<^sub>2), \<tau>\<^sub>2)) \<in> set (ireds_at G Shn
                (pr0_states G Shn) (la_fix G Shn) (istk ! 0))\<close> by blast
          have \<open>rr_none_at G Shn (pr0_states G Shn) (la_fix G Shn) (istk ! 0)\<close>
            by (rule rr_none_atI[OF m1 m2 prne])
          then show False using no_none by simp
        next
          case (Cons ac w')
          obtain a c where ac: \<open>ac = (a, c)\<close> by (cases ac)
          have weq: \<open>w = (a, c) # w'\<close> unfolding Cons ac by simp
          have lic1: \<open>dlic (istk ! 0) (red_buckets G Shn
              (length (pr0_states G Shn)) ! (istk ! 0))
              ((a, c) # w') pr\<^sub>1 (red_set (xclosure_auto G (hd Xs)) pr\<^sub>1)\<close>
            using RR(4) unfolding idef rdef clX weq hdi by simp
          have lic2: \<open>dlic (istk ! 0) (red_buckets G Shn
              (length (pr0_states G Shn)) ! (istk ! 0))
              ((a, c) # w') pr\<^sub>2 (red_set (xclosure_auto G (hd Xs)) pr\<^sub>2)\<close>
            using RR(6) unfolding idef rdef clX weq hdi by simp
          from reduce_seed_Some[OF tr live0 ne lic1 shn1] obtain \<tau>\<^sub>1 where
            m1: \<open>(Some a, (pr\<^sub>1, length (snd pr\<^sub>1), \<tau>\<^sub>1)) \<in> set (ireds_at G Shn
                (pr0_states G Shn) (la_fix G Shn) (istk ! 0))\<close>
            and ic1: \<open>icur G (hd Xs) c (pr\<^sub>1, length (snd pr\<^sub>1), \<tau>\<^sub>1)\<close> by blast
          from reduce_seed_Some[OF tr live0 ne lic2 shn2] obtain \<tau>\<^sub>2 where
            m2: \<open>(Some a, (pr\<^sub>2, length (snd pr\<^sub>2), \<tau>\<^sub>2)) \<in> set (ireds_at G Shn
                (pr0_states G Shn) (la_fix G Shn) (istk ! 0))\<close>
            and ic2: \<open>icur G (hd Xs) c (pr\<^sub>2, length (snd pr\<^sub>2), \<tau>\<^sub>2)\<close> by blast
          have pm: \<open>((pr\<^sub>1, length (snd pr\<^sub>1), \<tau>\<^sub>1), (pr\<^sub>2, length (snd pr\<^sub>2), \<tau>\<^sub>2))
              \<in> set (ipairs_at G Shn (pr0_states G Shn) (la_fix G Shn) (istk ! 0))\<close>
            by (rule ipairs_at_rrI[OF m1 m2 prne])
          show False by (rule kill[OF pm ic1 ic2])
        qed
      qed
    qed
  qed
qed

section \<open>The cells cover the LR(1) lookahead\<close>

text \<open>Algorithm 8 at \<open>k = 1\<close> keeps, per item, the set of one-token lookaheads
  (with their columns); the cells keep, per LR(0) item and state, a token
  with a width relation to the item's anchor.  Along any viable prefix
  \<open>\<gamma>\<close> the cells cover the lookaheads: the LR(0) index is reached by following
  the goto table from the start state along the erased \<open>\<gamma>\<close> (the cells are
  LALR: the index forgets everything about \<open>\<gamma>\<close> but the merged state), and
  every item of the closure of the LR(1) state carrying the lookahead
  \<open>(a, c)\<close> has a cell for \<open>a\<close> whose relation admits the column \<open>c\<close> against
  the item's anchor.  The padded end marker of the abstract machine is the
  \<open>None\<close> cell.  The proof mirrors the cell propagation: \<^const>\<open>la_next\<close>
  for \<^const>\<open>igoto\<close>, and \<^text>\<open>first1_complete\<close> for the lookahead of a
  predicted item, where \<^const>\<open>fscan\<close> stands in for \<^const>\<open>Hk\<close> of the
  remainder.\<close>

definition la_index :: \<open>('n, 't) is_cfg \<Rightarrow> 'n \<Rightarrow> ('n \<times> nat, 't \<times> nat) syms \<Rightarrow> nat\<close> where
  \<open>la_index G Shn \<gamma> =
     fold (\<lambda>Z p. la_next (pgtab G (pr0_states G Shn)) (pr0_states G Shn) p (unann Z)) \<gamma>
       (st_find (pr0_states G Shn) (lr0_start G Shn))\<close>

lemma la_index_Nil [simp]:
  \<open>la_index G Shn [] = st_find (pr0_states G Shn) (lr0_start G Shn)\<close>
  unfolding la_index_def by simp

lemma la_index_snoc [simp]:
  \<open>la_index G Shn (\<gamma> @ [Z]) =
     la_next (pgtab G (pr0_states G Shn)) (pr0_states G Shn) (la_index G Shn \<gamma>) (unann Z)\<close>
  unfolding la_index_def by simp

definition lk :: \<open>'t \<times> nat \<Rightarrow> ('t \<times> nat) list \<Rightarrow> ('t \<times> nat) list\<close> where
  \<open>lk dm u = (if u = [dm] then [] else u)\<close>

abbreviation lr1_start :: \<open>('n, 't) is_cfg \<Rightarrow> 'n \<Rightarrow> ('n \<times> nat) \<times> ('n \<times> nat, 't \<times> nat) syms\<close> where
  \<open>lr1_start G Shn \<equiv> ((Shn, istart_ind G), [Nt (istart G, istart_ind G)])\<close>

abbreviation lr1_init :: \<open>('n, 't) is_cfg \<Rightarrow> 'n \<Rightarrow> 't \<times> nat \<Rightarrow> ('n \<times> nat, 't \<times> nat) item set\<close> where
  \<open>lr1_init G Shn dm \<equiv> {init_item (Shn, istart_ind G) (istart G, istart_ind G) dm (Suc 0)}\<close>

text \<open>A production of the augmented infinite grammar is a production of \<open>G\<close>
  (or the augmenting one) under an annotation.\<close>

lemma lr1_prod_cases:
  assumes fn: \<open>fresh_name G Shn\<close> and pr: \<open>((A, i), arhs) \<in> insert (lr1_start G Shn) (infG G)\<close>
  obtains rhs where \<open>(A, rhs) \<in> insert (start_prod G Shn) (set (iprods G))\<close>
    and \<open>annotates i rhs arhs\<close>
proof -
  from pr consider \<open>((A, i), arhs) = lr1_start G Shn\<close> | \<open>((A, i), arhs) \<in> infG G\<close> by blast
  then show thesis
  proof cases
    case 1
    then have \<open>A = Shn\<close> \<open>i = istart_ind G\<close> \<open>arhs = [Nt (istart G, istart_ind G)]\<close> by simp_all
    then show thesis by (intro that[of \<open>snd (start_prod G Shn)\<close>]) (simp_all add: start_prod_def)
  next
    case 2
    then show thesis using that unfolding infG_alt by blast
  qed
qed

lemma gram_terms_of_prod:
  assumes \<open>(A, rhs) \<in> insert (start_prod G Shn) (set (iprods G))\<close> and \<open>(Tm a, r) \<in> set rhs\<close>
  shows \<open>a \<in> set (gram_terms G)\<close>
  using assms gram_termsI unfolding start_prod_def by fastforce

text \<open>The closure step: a kernel whose items are covered at index \<open>p\<close> has
  its closure covered at \<open>p\<close>.\<close>

lemma la_fix_closure_cells:
  assumes fn: \<open>fresh_name G Shn\<close> and dm: \<open>fst dm \<notin> set (gram_terms G)\<close>
    and ok: \<open>items_ok (insert (lr1_start G Shn) (infG G)) \<gamma> S\<close>
    and kernel: \<open>\<And>A i arhs m u rhs. (((A, i), arhs), m, u) \<in> S \<Longrightarrow>
        (A, rhs) \<in> insert (start_prod G Shn) (set (iprods G)) \<Longrightarrow> annotates i rhs arhs \<Longrightarrow>
        length u = Suc 0 \<and> cell_ok (la_fix G Shn) p (A, rhs) m (lk dm u) i\<close>
    and item: \<open>(((A, i), arhs), m, u) \<in> iclosure (infG G) (Suc 0) S\<close>
    and pr: \<open>(A, rhs) \<in> insert (start_prod G Shn) (set (iprods G))\<close>
    and ann: \<open>annotates i rhs arhs\<close>
  shows \<open>length u = Suc 0 \<and> cell_ok (la_fix G Shn) p (A, rhs) m (lk dm u) i\<close>
proof -
  let ?sts = \<open>pr0_states G Shn\<close> and ?gt = \<open>pgtab G (pr0_states G Shn)\<close> and ?L = \<open>la_fix G Shn\<close>
  have tab: \<open>tables_ok G Shn ?sts ?gt ?L\<close> by (rule tables_ok_concrete)
  have okc: \<open>items_ok (insert (lr1_start G Shn) (infG G)) \<gamma> (iclosure (infG G) (Suc 0) S)\<close>
    by (rule items_ok_iclosure[OF ok subset_insertI])
  have \<open>\<forall>A i arhs m u rhs. it = (((A, i), arhs), m, u) \<longrightarrow>
      (A, rhs) \<in> insert (start_prod G Shn) (set (iprods G)) \<longrightarrow> annotates i rhs arhs \<longrightarrow>
      length u = Suc 0 \<and> cell_ok ?L p (A, rhs) m (lk dm u) i\<close>
    if \<open>it \<in> iclosure (infG G) (Suc 0) S\<close> for it
    using that
  proof (induction rule: iclosure.induct)
    case (iclosure_base it)
    then show ?case using kernel by blast
  next
    case (iclosure_step Ai arhs m u Bj brhs v)
    show ?case
    proof (intro allI impI)
      fix B' j brhs' m' v' rhsB
      assume eq: \<open>((Bj, brhs), 0::nat, v) = (((B', j), brhs'), m', v')\<close>
        and prB: \<open>(B', rhsB) \<in> insert (start_prod G Shn) (set (iprods G))\<close>
        and annB: \<open>annotates j rhsB brhs'\<close>
      have Bj: \<open>Bj = (B', j)\<close> and m': \<open>m' = 0\<close> and v': \<open>v' = v\<close> using eq by simp_all
      obtain A i where Ai: \<open>Ai = (A, i)\<close> by (cases Ai)
      have prod: \<open>((A, i), arhs) \<in> insert (lr1_start G Shn) (infG G)\<close>
        using items_okD[OF okc iclosure_step.hyps(1)[unfolded Ai]] by blast
      from lr1_prod_cases[OF fn prod] obtain rhs where
        prG: \<open>(A, rhs) \<in> insert (start_prod G Shn) (set (iprods G))\<close>
        and ann: \<open>annotates i rhs arhs\<close> .
      from iclosure_step.IH[rule_format, OF _ prG ann] have
        lenu: \<open>length u = Suc 0\<close> and cell: \<open>cell_ok ?L p (A, rhs) m (lk dm u) i\<close>
        unfolding Ai by auto
      have m_lt: \<open>m < length rhs\<close> using iclosure_step.hyps(2) annotates_length[OF ann] by simp
      from annotates_nthD[OF ann m_lt] obtain jj where
        nth: \<open>arhs ! m = annsym (fst (rhs ! m), jj)\<close> and sat: \<open>irel_sat (snd (rhs ! m)) jj i\<close>
        by blast
      have nxtjj: \<open>fst (rhs ! m) = Nt B' \<and> jj = j\<close>
        using iclosure_step.hyps(3) nth unfolding Bj by (cases \<open>fst (rhs ! m)\<close>) auto
      note nxt = conjunct1[OF nxtjj] and jj = conjunct2[OF nxtjj]
      have m_lt': \<open>m < length (snd (A, rhs))\<close> and nxt': \<open>fst (snd (A, rhs) ! m) = Nt B'\<close>
        using m_lt nxt by simp_all
      \<comment> \<open>the predicted nonterminal is one of \<open>G\<close>: its production is in \<open>iprods\<close>\<close>
      have \<open>B' \<in> fst ` set (iprods G)\<close>
        using iclosure_step.hyps(4) unfolding Bj infG_alt by force
      then have brG: \<open>(B', rhsB) \<in> set (iprods G)\<close>
        using prB fn unfolding fresh_name_def start_prod_def by auto
      have vH: \<open>v \<in> fHk G (Suc 0) (drop (Suc m) rhs) i u\<close>
        by (rule fHkI[OF annotates_drop[OF ann] iclosure_step.hyps(5)])
      from cell obtain \<tau> where mem: \<open>(p, ((A, rhs), m), tok_of (lk dm u), \<tau>) \<in> set ?L\<close>
        and rel: \<open>case lk dm u of [] \<Rightarrow> True | (a, c) # _ \<Rightarrow> wsat \<tau> c i\<close>
        unfolding cell_ok_def by blast
      from first1_complete[OF vH] show \<open>length v' = Suc 0 \<and> cell_ok ?L p (B', rhsB) m' (lk dm v') j\<close>
      proof (elim disjE exE conjE)
        fix b c \<sigma>
        assume veq: \<open>v = [(b, c)]\<close>
          and fs: \<open>(b, \<sigma>) \<in> set (fscan (ffix G) (nullables G) (drop (Suc m) rhs))\<close>
          and cs: \<open>csat \<sigma> c i\<close>
        have terms: \<open>(Tm a, r) \<in> set (drop (Suc m) rhs) \<Longrightarrow> a \<in> set (gram_terms G)\<close> for a r
          using gram_terms_of_prod[OF prG, OF in_set_dropD] by blast
        have bT: \<open>b \<in> set (gram_terms G)\<close>
        proof (rule fscan_inU[OF ffix_inU _ fs, THEN conjunct1], goal_cases)
          case 1 then show ?case by (rule terms)
        qed
        have vdm: \<open>v \<noteq> [dm]\<close> using bT dm veq by auto
        have inL: \<open>(p, ((B', rhsB), 0), Some b, wcomp (winv (w_of (snd (rhs ! m)))) (wemb \<sigma>)) \<in> set ?L\<close>
          using cell_child_first[OF tab mem m_lt' nxt' brG fst_conv] fs by simp
        have ws: \<open>wsat (wcomp (winv (w_of (snd (rhs ! m)))) (wemb \<sigma>)) c j\<close>
          by (rule wsat_reanchor[OF sat[unfolded jj] wemb_sound[OF cs]])
        show ?thesis
          unfolding v' m' lk_def using vdm veq inL ws unfolding cell_ok_def by auto
      next
        assume nul: \<open>list_all (\<lambda>(X, r). nsym (nullables G) X) (drop (Suc m) rhs)\<close>
          and veq: \<open>v = take (Suc 0) u\<close>
        have vu: \<open>v = u\<close> using veq lenu by simp
        have inL: \<open>(p, ((B', rhsB), 0), tok_of (lk dm u), wcomp (winv (w_of (snd (rhs ! m)))) \<tau>) \<in> set ?L\<close>
          using cell_child_inherit[OF tab mem m_lt' nxt' brG fst_conv] nul by simp
        have ws: \<open>case lk dm u of [] \<Rightarrow> True
            | (a, c) # _ \<Rightarrow> wsat (wcomp (winv (w_of (snd (rhs ! m)))) \<tau>) c j\<close>
          using rel by (auto split: list.splits intro: wsat_reanchor[OF sat[unfolded jj]])
        show ?thesis
          unfolding v' m' vu using lenu inL ws unfolding cell_ok_def by auto
      qed
    qed
  qed
  then show ?thesis using item pr ann by blast
qed

theorem la_fix_covers_lr1:
  assumes fn: \<open>fresh_name G Shn\<close> and dm: \<open>fst dm \<notin> set (gram_terms G)\<close>
    and item: \<open>(((A, i), arhs), m, u) \<in>
      iclosure (infG G) (Suc 0) (lrstate (infG G) (Suc 0) (lr1_init G Shn dm) \<gamma>)\<close>
    and pr: \<open>(A, rhs) \<in> insert (start_prod G Shn) (set (iprods G))\<close>
    and ann: \<open>annotates i rhs arhs\<close>
  shows \<open>cell_ok (la_fix G Shn) (la_index G Shn \<gamma>) (A, rhs) m (lk dm u) i\<close>
proof -
  let ?sts = \<open>pr0_states G Shn\<close> and ?gt = \<open>pgtab G (pr0_states G Shn)\<close> and ?L = \<open>la_fix G Shn\<close>
  let ?P = \<open>infG G\<close> and ?Q = \<open>insert (lr1_start G Shn) (infG G)\<close>
  have tab: \<open>tables_ok G Shn ?sts ?gt ?L\<close> by (rule tables_ok_concrete)
  have ok: \<open>items_ok ?Q \<gamma> (lrstate ?P (Suc 0) (lr1_init G Shn dm) \<gamma>)\<close> for \<gamma>
    by (rule items_ok_lrstate[OF items_ok_init subset_insertI])
  have K: \<open>(((A, i), arhs), m, u) \<in> lrstate ?P (Suc 0) (lr1_init G Shn dm) \<gamma> \<Longrightarrow>
      (A, rhs) \<in> insert (start_prod G Shn) (set (iprods G)) \<Longrightarrow> annotates i rhs arhs \<Longrightarrow>
      length u = Suc 0 \<and> cell_ok ?L (la_index G Shn \<gamma>) (A, rhs) m (lk dm u) i\<close>
    for \<gamma> A i arhs m u rhs
  proof (induction \<gamma> arbitrary: A i arhs m u rhs rule: rev_induct)
    case Nil
    then have A: \<open>A = Shn\<close> and i: \<open>i = istart_ind G\<close> and arhs: \<open>arhs = [Nt (istart G, istart_ind G)]\<close>
      and m: \<open>m = 0\<close> and u: \<open>u = [dm]\<close>
      unfolding init_item_def by simp_all
    have rhs: \<open>rhs = [(Nt (istart G), Eq)]\<close>
    proof -
      have \<open>(Shn, rhs) \<notin> set (iprods G)\<close> using fn unfolding fresh_name_def by force
      then show ?thesis using Nil.prems(2) unfolding A start_prod_def by simp
    qed
    have \<open>(st_find ?sts (lr0_start G Shn), (start_prod G Shn, 0), None, WAny) \<in> set ?L\<close>
      using tab unfolding tables_ok_def la_start_def by auto
    then show ?case
      unfolding A i m u rhs lk_def cell_ok_def start_prod_def by auto
  next
    case (snoc Z \<gamma>)
    from snoc.prems(1) obtain m\<^sub>0 where m: \<open>m = Suc m\<^sub>0\<close>
      and parent: \<open>(((A, i), arhs), m\<^sub>0, u) \<in> iclosure ?P (Suc 0) (lrstate ?P (Suc 0) (lr1_init G Shn dm) \<gamma>)\<close>
      and m0_lt: \<open>m\<^sub>0 < length arhs\<close> and Z: \<open>arhs ! m\<^sub>0 = Z\<close>
      unfolding lrstate_snoc igoto_def by blast
    have \<open>length u = Suc 0 \<and> cell_ok ?L (la_index G Shn \<gamma>) (A, rhs) m\<^sub>0 (lk dm u) i\<close>
    proof (rule la_fix_closure_cells[OF fn dm ok _ parent snoc.prems(2,3)], goal_cases)
      case 1 then show ?case by (rule snoc.IH)
    qed
    then have lenu: \<open>length u = Suc 0\<close>
      and cell: \<open>cell_ok ?L (la_index G Shn \<gamma>) (A, rhs) m\<^sub>0 (lk dm u) i\<close> by blast+
    have m0_lt': \<open>m\<^sub>0 < length (snd (A, rhs))\<close>
      using m0_lt annotates_length[OF snoc.prems(3)] by simp
    from annotates_nthD[OF snoc.prems(3) m0_lt'[simplified]] obtain jj where
      nth: \<open>arhs ! m\<^sub>0 = annsym (fst (rhs ! m\<^sub>0), jj)\<close> by blast
    have Zeq: \<open>unann Z = fst (snd (A, rhs) ! m\<^sub>0)\<close> using nth Z by simp
    show ?case
      using cell_ok_step[OF tab cell m0_lt'] lenu unfolding m la_index_snoc Zeq by simp
  qed
  show ?thesis
  proof (rule la_fix_closure_cells[OF fn dm ok _ item pr ann, THEN conjunct2], goal_cases)
    case 1 then show ?case by (rule K)
  qed
qed


section \<open>Executable packaging: the automaton computed once\<close>

text \<open>The checks above are written for reading: each one names the
  automaton, the goto tables and the saturated cell table it needs, and the
  evaluator recomputes every one of them at every occurrence. At the size of
  a real grammar that dominates the cost of the \<^text>\<open>parser\<close>
  command, so this section restates them against precomputed arguments, in
  the manner of \<^const>\<open>la_fix_gen\<close>, and proves the restatements
  equal to the originals. Nothing changes meaning: the \<open>_gen\<close>
  forms are definitions and every bridge below is a theorem.

  \<^const>\<open>rlalr_conflict_at\<close> is the worst offender - it names
  \<^const>\<open>pgtab\<close>, \<^const>\<open>anchored_nts\<close>, the states' \<^const>\<open>wreach\<close>
  lists and \<^const>\<open>ifuel\<close> under the \<^const>\<open>list_ex\<close>, so they are
  rebuilt once per candidate pair of every state.  The restatement reads the
  state's closure from the shared list, so it agrees with the original on the
  states of the automaton only, which is all \<^const>\<open>rlalr_conflicts\<close>
  asks about.\<close>

definition ireds_gen :: \<open>'n \<Rightarrow> ('n, 't) witem list \<Rightarrow> ('n, 't) lacell list \<Rightarrow> nat \<Rightarrow>
    ('t option \<times> ('n, 't) witem) list\<close> where
  \<open>ireds_gen Shn ws L i =
     List.map_filter (\<lambda>(i', (pr, m), t, \<tau>).
       if i' = i \<and> m = length (snd pr) \<and> fst pr \<noteq> Shn \<and>
          list_ex (\<lambda>(pr', m', \<rho>). pr' = pr \<and> m' = m) ws
       then Some (t, (pr, m, \<tau>)) else None) L\<close>

lemma ireds_at_gen:
  \<open>ireds_at G Shn sp L i = ireds_gen Shn (wreach G (sp ! i)) L i\<close>
  by (simp add: ireds_at_def ireds_gen_def Let_def)

definition rr_none_gen :: \<open>('t option \<times> ('n, 't) witem) list \<Rightarrow> bool\<close> where
  \<open>rr_none_gen reds =
     list_ex (\<lambda>(t, c). t = None \<and>
       list_ex (\<lambda>(t', c'). fst c' \<noteq> fst c \<and> t' = None) reds) reds\<close>

lemma rr_none_at_gen:
  \<open>rr_none_at G Shn sp L i = rr_none_gen (ireds_at G Shn sp L i)\<close>
  by (simp add: rr_none_at_def rr_none_gen_def Let_def)

definition ipairs_gen :: \<open>('n, 't) witem list \<Rightarrow> ('t option \<times> ('n, 't) witem) list \<Rightarrow>
    (('n, 't) witem \<times> ('n, 't) witem) list\<close> where
  \<open>ipairs_gen ws reds =
     (let shifts = ishifts ws;
          srs = concat (map (\<lambda>(t, c). case t of
              Some a \<Rightarrow> map (\<lambda>(a', c'). (c, c')) (filter (\<lambda>(a', c'). a' = a) shifts)
            | None \<Rightarrow> []) reds);
          rrs = concat (map (\<lambda>(t, c). List.map_filter (\<lambda>(t', c').
                 if fst c' \<noteq> fst c \<and> t' = t \<and> t \<noteq> None then Some (c, c') else None) reds)
                 reds)
      in remdups (srs @ rrs))\<close>

lemma ipairs_at_gen:
  \<open>ipairs_at G Shn sp L i = ipairs_gen (wreach G (sp ! i)) (ireds_at G Shn sp L i)\<close>
  by (simp add: ipairs_at_def ipairs_gen_def Let_def)

definition rlalr_conflict_at_gen :: \<open>'n \<Rightarrow> ('n, 't) witem list list \<Rightarrow>
    (('n, 't) sym \<times> nat) list list \<Rightarrow> 'n list \<Rightarrow> nat \<Rightarrow> ('n, 't) lacell list \<Rightarrow>
    nat \<Rightarrow> bool\<close> where
  \<open>rlalr_conflict_at_gen Shn wrs gp ants fuel L i \<longleftrightarrow>
     (let ws = wrs ! i; reds = ireds_gen Shn ws L i
      in rr_none_gen reds \<or>
         list_ex (\<lambda>(c\<^sub>1, c\<^sub>2). ifire Shn wrs gp ants fuel [] [(i, c\<^sub>1, c\<^sub>2)])
           (ipairs_gen ws reds))\<close>

lemma rlalr_conflict_at_pointwise:
  assumes \<open>i < length sp\<close>
  shows \<open>rlalr_conflict_at G Shn sp L i =
     rlalr_conflict_at_gen Shn (map (wreach G) sp) (pgtab G sp) (anchored_nts G)
       (ifuel (map (wreach G) sp)) L i\<close>
  using assms by (simp add: rlalr_conflict_at_def rlalr_conflict_at_gen_def Let_def
        ireds_at_gen rr_none_at_gen ipairs_at_gen)

lemma rlalr_conflicts_code [code]:
  \<open>rlalr_conflicts G Shn =
     (let sp = pr0_states G Shn; gp = pgtab G sp; L = la_fix_gen G Shn gp sp;
          wrs = map (wreach G) sp
      in filter (rlalr_conflict_at_gen Shn wrs gp (anchored_nts G) (ifuel wrs) L)
           [0..<length sp])\<close>
  unfolding rlalr_conflicts_def la_fix_def Let_def
  by (rule filter_cong[OF refl]) (simp add: rlalr_conflict_at_pointwise)

lemma acc_conflicts_code [code]:
  \<open>acc_conflicts G Shn =
     (let sts = pr0_states G Shn; L = la_fix_gen G Shn (pgtab G sts) sts;
          p0 = start_prod G Shn
      in filter (\<lambda>i. (p0, Suc 0) \<in> set (sts ! i) \<and>
           list_ex (\<lambda>(i', (pr, m), t, \<tau>). i' = i \<and> m = length (snd pr) \<and>
                     t = None \<and> pr \<noteq> p0) L)
          [0..<length sts])\<close>
  by (simp add: acc_conflicts_def la_fix_def Let_def)

text \<open>The bundle the \<^text>\<open>parser\<close> command evaluates: the six
  tables its parse body is specialised to, followed by the two conflict
  reports it discharges \<^text>\<open>mdet\<close> and the accept/reduce premise
  with. Sharing across the eight components is the point - the automaton,
  its goto table and the saturated cell table are each built once for all
  of them.\<close>

definition lr_tables :: \<open>('n, 't) is_cfg \<Rightarrow> 'n \<Rightarrow>
    ('n, 't) citem list list \<times> (('n, 't) sym \<times> nat) list list \<times>
    ('n, 't) lacell list list \<times> ('n, 't) xitem list \<times> ('n, 't) xitem list \<times>
    nat \<times> nat list \<times> nat list\<close> where
  \<open>lr_tables G Shn =
     (let sp = pr0_states G Shn; gp = pgtab G sp; L = la_fix_gen G Shn gp sp;
          ants = anchored_nts G; wrs = map (wreach G) sp; fuel = ifuel wrs;
          s0 = start_prod G Shn; xi = xinit G Shn
      in (sp, gp, cell_buckets L (length sp), xi, xclosure_auto G xi,
          st_find sp (lr0_start G Shn),
          filter (rlalr_conflict_at_gen Shn wrs gp ants fuel L) [0..<length sp],
          filter (\<lambda>i. (s0, Suc 0) \<in> set (sp ! i) \<and>
                    list_ex (\<lambda>(i', (pr, m), t, \<tau>). i' = i \<and> m = length (snd pr) \<and>
                              t = None \<and> pr \<noteq> s0) L)
            [0..<length sp]))\<close>

theorem lr_tables_eq:
  \<open>lr_tables G Shn =
     (pr0_states G Shn,
      pgtab G (pr0_states G Shn),
      red_buckets G Shn (length (pr0_states G Shn)),
      xinit G Shn,
      xclosure_auto G (xinit G Shn),
      st_find (pr0_states G Shn) (lr0_start G Shn),
      rlalr_conflicts G Shn,
      acc_conflicts G Shn)\<close>
  by (simp add: lr_tables_def red_buckets_def la_fix_def rlalr_conflicts_code
        acc_conflicts_code Let_def)

end
