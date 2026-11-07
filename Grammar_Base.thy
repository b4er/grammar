theory Grammar_Base
  imports Indentation_Sensitive
begin

text \<open>Facts and the decoder recursion combinator used by the grammar and
  parser commands (\<^file>\<open>command/Grammar_Command.thy\<close>). They live below
  the LR theories so that the command layer can sit above the proofs.\<close>

lemma lang_of_complete:
  fixes G :: \<open>('n, 'tok) is_cfg\<close>
    and P :: \<open>('m, 'ch, 'tok) tword \<Rightarrow> 'a \<Rightarrow> bool\<close>
  assumes mem: \<open>w \<in> ilang G\<close>
    and complete: \<open>\<And>pt. wf_ptree G pt \<Longrightarrow> proot pt = (Nt (istart G), istart_ind G) \<Longrightarrow> \<exists>x. P (pyield pt) x\<close>
  shows \<open>\<exists>x. P w x\<close>
proof -
  let ?A = \<open>istart G\<close> and ?i = \<open>istart_ind G\<close>
  from mem obtain pt where
    \<open>wf_ptree G pt\<close> \<open>proot pt = (Nt ?A, ?i)\<close> \<open>pyield pt = w\<close>
    by (auto simp: ilang_iff_ast ast_of_def)

  with complete show ?thesis by blast
qed

lemma wf_ptree_Tm_leaf:
  assumes \<open>fst (proot pt) = Tm t\<close> \<open>wf_ptree G pt\<close>
  shows \<open>\<exists>t'. pt = PLeaf t' \<and> tok t' = t\<close>
  using assms by (cases pt) auto

lemma erase_Nt_E2:
  assumes \<open>proot pt = (Nt A, i)\<close>
  obtains ts where \<open>erase pt = Node A ts\<close>
  using assms by (cases pt) auto

text \<open>The two rules behind the linear decoder proofs (\<^file>\<open>command/parser_dec_total.ML\<close>,
  \<^file>\<open>command/parser_rel_bridge.ML\<close>):\<close>

lemma proot_Tm_E:
  assumes \<open>fst (proot pt) = Tm t\<close>
  obtains sp m where \<open>erase pt = Leaf \<lparr>tok = t, span = sp, \<dots> = m\<rparr>\<close>
    and \<open>pyield pt = [\<lparr>tok = t, span = sp, \<dots> = m\<rparr>]\<close> and \<open>snd (proot pt) = s_col sp\<close>
proof -
  from assms have \<open>\<exists>sp m. pt = PLeaf \<lparr>tok = t, span = sp, \<dots> = m\<rparr>\<close>
  proof (cases pt)
    case (PLeaf r)
    then have \<open>pt = PLeaf \<lparr>tok = t, span = span r, \<dots> = token.more r\<rparr>\<close>
      using assms by (cases r) auto
    then show ?thesis by blast
  qed (use assms in simp)

  then obtain sp m
    where \<open>pt = PLeaf \<lparr>tok = t, span = sp, \<dots> = m\<rparr>\<close> by blast
  then show thesis by (intro that[of sp m]) simp_all
qed

lemma case_ast_Nt_None:
  \<open>asym a = Nt B \<Longrightarrow> (case a of Leaf x \<Rightarrow> f x | Node n xs \<Rightarrow> None) = None\<close>
  by (cases a) auto

text \<open>The decoders of a grammar are defined through this recursion combinator,
  which restricts the recursive calls to the children of a node: the functional
  of a grammar is then an ordinary definition.\<close>

function ast_rec ::
  \<open>(('i \<Rightarrow> ('m, 'ch, 'n, 'tok) ast \<Rightarrow> 'r) \<Rightarrow> 'i \<Rightarrow> 'n \<Rightarrow> ('m, 'ch, 'n, 'tok) ast list \<Rightarrow> 'r) \<Rightarrow>
    'r \<Rightarrow> 'i \<Rightarrow> ('m, 'ch, 'n, 'tok) ast \<Rightarrow> 'r\<close> where
  \<open>ast_rec F d i (Node n xs) = F (\<lambda>j c. if c \<in> set xs then ast_rec F d j c else d) i n xs\<close>
| \<open>ast_rec F d i (Leaf w) = d\<close>
  by pat_completeness auto
termination
  by (relation \<open>measure (\<lambda>(F, d, i, t). size t)\<close>)
    (auto intro: le_imp_less_Suc size_list_estimation')

declare ast_rec.simps [simp del, code del]

end
