theory Indentation_Sensitive
  imports
    Token
    "Context_Free_Grammar.Parse_Tree"
    "Context_Free_Grammar.Epsilon_Elimination"
    "HOL-Library.Extended_Nat"
begin

(*<*)
setup \<open>Sign.hide_const true \<^unchecked_name>\<open>Real_Vector_Spaces.span\<close>\<close>
(*>*)

section \<open>Indentation-sensitive context-free grammars\<close>

text \<open>
  A formalization of the grammar formalism of M. D. Adams, \<^emph>\<open>Principled
  Parsing for Indentation-Sensitive Languages: Revisiting Landin's Offside
  Rule\<close>, POPL 2013. Section numbers below refer to that paper.

  In an IS-CFG every symbol on the right-hand side of a production carries an
  indentation relation, one of \<^text>\<open>=\<close>, \<^text>\<open>>\<close>,
  \<^text>\<open>\<ge>\<close> and the unconstrained \<^text>\<open>\<star>\<close>. Input terminals
  carry the column at which they occur, every symbol occurrence in a derivation
  carries an indentation, and a production
  \<^text>\<open>A \<rightarrow> X\<^sub>1\<^sup>\<Zrres>\<^sup>1 \<dots> X\<^sub>n\<^sup>\<Zrres>\<^sup>n\<close> may rewrite
  \<^text>\<open>A\<^sup>i\<close> to \<^text>\<open>X\<^sub>1\<^sup>j\<^sup>1 \<dots> X\<^sub>n\<^sup>j\<^sup>n\<close> only if
  \<^text>\<open>j\<^sub>k \<Zrres>\<^sub>k i\<close> holds for every \<^text>\<open>k\<close>.

  Two semantics are given, the paper's rewrite relation and annotated parse
  trees, and proved equivalent. On top of them sits an executable parser
  returning indentation-erased ASTs, sound and complete against both.

  Symbols, ordinary context-free grammars, their derivation relations and their
  parse trees are those of \<^theory>\<open>Context_Free_Grammar.Parse_Tree\<close> and its
  parent: \<^const>\<open>Nt\<close> and \<^const>\<open>Tm\<close>, here over the tokens of theory
  \<^theory>\<open>Grammar_Command.Token\<close>, \<^const>\<open>derive\<close> and \<^const>\<open>deriver\<close> over a
  production set, and \<^const>\<open>parse_tree\<close>.
\<close>

subsection \<open>Indentation relations\<close>

text \<open>
  The paper's four relations, fixed as a datatype so that grammars stay
  executable. \<^text>\<open>irel_sat r j i\<close> is the paper's
  \<^text>\<open>j \<Zrres> i\<close>: the child indentation \<^text>\<open>j\<close> relates by
  \<^text>\<open>r\<close> to the parent indentation \<^text>\<open>i\<close>.
\<close>

datatype irel = Eq | Gt | Ge | Any

fun irel_sat :: \<open>irel \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool\<close> where
  \<open>irel_sat Eq j i \<longleftrightarrow> j = i\<close>
| \<open>irel_sat Gt j i \<longleftrightarrow> j > i\<close>
| \<open>irel_sat Ge j i \<longleftrightarrow> j \<ge> i\<close>
| \<open>irel_sat Any j i \<longleftrightarrow> True\<close>

subsection \<open>Grammars\<close>

text \<open>
  A right-hand side pairs each symbol with its indentation relation.
  Productions are lists so that grammars are executable (the semantics
  only reads \<^term>\<open>set (iprods G)\<close>).

  The start symbol comes with a fixed start indentation.
\<close>

type_synonym ('n, 'tok) rhs = \<open>(('n, 'tok) sym \<times> irel) list\<close>

record ('n, 'tok) is_cfg =
  iprods :: \<open>('n \<times> ('n, 'tok) rhs) list\<close>
  istart :: 'n
  istart_ind :: nat

subsection \<open>The rewrite relation\<close>

text \<open>
  Every token carries a source span, only its column takes part in the
  indentation logic. Indentations of non-terminals stay bare columns, a
  non-terminal having no source location of its own.

  Sentential forms are sequences of indentation-annotated symbols, input words
  sequences of indentation-annotated terminals. A rewrite step expands one
  annotated non-terminal by a production, choosing for each rhs symbol an
  indentation compatible with the parent's.
\<close>

type_synonym ('n, 'tok) sform = \<open>(('n, 'tok) sym \<times> nat) list\<close>

definition word_of :: \<open>('m, 'ch, 'tok) tword \<Rightarrow> ('n, 'tok) sform\<close> where
  \<open>word_of w = map (\<lambda>t. (Tm (tok t), s_col (token.span t))) w\<close>

inductive istep :: \<open>('n, 'tok) is_cfg \<Rightarrow> ('n, 'tok) sform \<Rightarrow> ('n, 'tok) sform \<Rightarrow> bool\<close> for G where
  istepI: \<open>(A, rhs) \<in> set (iprods G) \<Longrightarrow>
    list_all2 (\<lambda>(X, r) (Y, j). Y = X \<and> irel_sat r j i) rhs rhs' \<Longrightarrow>
    istep G (U @ (Nt A, i) # V) (U @ rhs' @ V)\<close>

abbreviation iderives :: \<open>('n, 'tok) is_cfg \<Rightarrow> ('n, 'tok) sform \<Rightarrow> ('n, 'tok) sform \<Rightarrow> bool\<close> where
  \<open>iderives G \<equiv> (istep G)\<^sup>*\<^sup>*\<close>

subsection \<open>The ordinary-CFG model (Sect. 5.2) and Lemma 6\<close>

text \<open>
  Sect. 5.2 of the paper reads an IS-CFG over non-terminals \<^text>\<open>N\<close> as an
  ordinary, indentation-insensitive CFG over the infinite non-terminal set
  \<^text>\<open>N \<times> \<nat>\<close> and terminal set \<^text>\<open>\<Sigma> \<times> \<nat>\<close>, carrying a production
  \<^text>\<open>A\<^sup>i \<rightarrow> X\<^sub>1\<^sup>j\<^sup>1 \<dots> X\<^sub>n\<^sup>j\<^sup>n\<close> for every admissible choice of the \<^text>\<open>j\<^sub>k\<close>.

  \<^const>\<open>derive\<close> takes a production \<^typ>\<open>('n, 't) Prods\<close> as a set, so the infinite
  model is expressible.

  Lemma 6, that the two rewrite relations agree, is proved here and lets the
  development use the library's \<^const>\<open>derive\<close>, \<^const>\<open>deriver\<close>, \<^const>\<open>Lang\<close> and
  parse trees instead of a private theory of indentation-annotated derivations.
\<close>

fun annsym :: \<open>('n, 'tok) sym \<times> nat \<Rightarrow> ('n \<times> nat, 'tok \<times> nat) sym\<close> where
  \<open>annsym (Nt A, i) = Nt (A, i)\<close>
| \<open>annsym (Tm t, j) = Tm (t, j)\<close>

definition infG :: \<open>('n, 'tok) is_cfg \<Rightarrow> ('n \<times> nat, 'tok \<times> nat) Prods\<close> where
  \<open>infG G = {
    ((A, i), map annsym rhs') | A i rhs'.
     \<exists>rhs. (A, rhs) \<in> set (iprods G) \<and>
           list_all2 (\<lambda>(X, r) (Y, j). Y = X \<and> irel_sat r j i) rhs rhs'
  }\<close>

lemma inj_annsym: \<open>inj annsym\<close>
  by (rule injI; case_tac x rule: annsym.cases; case_tac y rule: annsym.cases) auto

lemmas map_annsym_injective = map_injective[OF _ inj_annsym]

lemma annsym_eq_Nt: \<open>annsym x = Nt (A, i) \<longleftrightarrow> x = (Nt A, i)\<close>
  by (cases x rule: annsym.cases) auto

lemma annsym_word_of: \<open>map annsym (word_of w) = map Tm (tcols w)\<close>
  by (simp add: word_of_def tcols_def)

lemma derive_infG_imageI[intro]:
  assumes \<open>istep G u v\<close>
  shows \<open>infG G \<turnstile> map annsym u \<Rightarrow> map annsym v\<close>
proof -
  from assms obtain A rhs rhs' i U V where
      \<open>(A, rhs) \<in> set (iprods G)\<close>
      \<open>list_all2 (\<lambda>(X, r) (Y, j). Y = X \<and> irel_sat r j i) rhs rhs'\<close>
    and uv: \<open>u = U @ (Nt A, i) # V\<close> \<open>v = U @ rhs' @ V\<close>
    by (cases rule: istep.cases) (auto simp add: infG_def)

  hence \<open>((A, i), map annsym rhs') \<in> infG G\<close> by (auto simp: infG_def)

  with derive.intros show ?thesis by (simp add: uv)
qed

lemma derive_infG_imageD[dest]:
  assumes \<open>infG G \<turnstile> map annsym u \<Rightarrow> z\<close>
  shows \<open>\<exists>v. z = map annsym v \<and> istep G u v\<close>
proof -
  from assms obtain B rhs\<^sub>B U' V' where \<open>(B, rhs\<^sub>B) \<in> infG G\<close> and
    x: \<open>map annsym u = U' @ Nt B # V'\<close> and z: \<open>z = U' @ rhs\<^sub>B @ V'\<close>
    by (cases rule: derive.cases) auto

  then obtain A i rhs rhs' where
    B: \<open>B = (A, i)\<close> and rhs\<^sub>B: \<open>rhs\<^sub>B = map annsym rhs'\<close>
    and p: \<open>(A, rhs) \<in> set (iprods G)\<close>
    and la: \<open>list_all2 (\<lambda>(X, r) (Y, j). Y = X \<and> irel_sat r j i) rhs rhs'\<close>
    by (auto simp: infG_def)

  let ?U = \<open>take (length U') u\<close> and ?rest = \<open>drop (length U') u\<close>

  have u_split: \<open>u = ?U @ ?rest\<close> by (simp)
  have U: \<open>map annsym ?U = U'\<close>
    using x by (metis append_eq_conv_conj take_map)

  from x have \<open>map annsym ?rest = Nt B # V'\<close>
    by (metis append_eq_conv_conj drop_map)
  then obtain s V where \<open>annsym s = Nt B\<close> and
    rest_split: \<open>?rest = s # V\<close> and V: \<open>map annsym V = V'\<close>
    by (auto simp: map_eq_Cons_conv)
  hence s': \<open>s = (Nt A, i)\<close> using B by (simp add: annsym_eq_Nt)

  have \<open>istep G (?U @ (Nt A, i) # V) (?U @ rhs' @ V)\<close>
    by (rule istepI[OF p la])
  moreover have \<open>z = map annsym (?U @ rhs' @ V)\<close>
    using z U V rhs\<^sub>B by simp
  ultimately show ?thesis using u_split by (fastforce simp: rest_split s')
qed

theorem inf_cfg_step:
  \<open>infG G \<turnstile> map annsym u \<Rightarrow> map annsym v \<longleftrightarrow> istep G u v\<close>
  by (fastforce dest: map_annsym_injective)

lemma derives_infG_imageD[dest]:
  assumes \<open>infG G \<turnstile> map annsym u \<Rightarrow>* z\<close>
  shows \<open>\<exists>v. z = map annsym v \<and> iderives G u v\<close>
  using assms by (induction rule: rtranclp_induct) (auto intro: rtranclp.rtrancl_into_rtrancl)

theorem inf_cfg_derives:
  \<open>infG G \<turnstile> map annsym u \<Rightarrow>* map annsym v \<longleftrightarrow> iderives G u v\<close> 
proof
  assume \<open>iderives G u v\<close> thus \<open>infG G \<turnstile> map annsym u \<Rightarrow>* map annsym v\<close>
    by (induction rule: rtranclp_induct) (auto intro: rtranclp.rtrancl_into_rtrancl)
qed (fastforce dest: map_annsym_injective)

text \<open>
  The language of an IS-CFG, taken as that of the model read through the column
  projection \<^const>\<open>tcols\<close>. Lemma 6 recovers the paper's reading, the
  annotated terminal words derivable from the start symbol at the start
  indentation.
\<close>

definition ilang :: \<open>('n, 'tok) is_cfg \<Rightarrow> ('m, 'ch, 'tok) tword set\<close> where
  \<open>ilang G = {w. tcols w \<in> Lang (infG G) (istart G, istart_ind G)}\<close>

lemma ilang_derives:
  \<open>w \<in> ilang G \<longleftrightarrow> infG G \<turnstile> [Nt (istart G, istart_ind G)] \<Rightarrow>* map Tm (tcols w)\<close>
  by (simp add: ilang_def Lang_def)

corollary ilang_iderives:
  \<open>w \<in> ilang G \<longleftrightarrow> iderives G [(Nt (istart G), istart_ind G)] (word_of w)\<close>
  using inf_cfg_derives[of G \<open>[(Nt (istart G), istart_ind G)]\<close> \<open>word_of w\<close>]
  by (simp add: ilang_derives annsym_word_of)

subsection \<open>The indentation-erased grammar\<close>

text \<open>
  Forgetting the indentations of \<^const>\<open>infG\<close> leaves the ordinary CFG whose
  productions are those of the IS-grammar with the relations dropped, and whose
  terminals the library's \<^const>\<open>tms\<close> collects. Erasure is a homomorphism on
  derivations, so what the erased grammar cannot do the model cannot do either.
  This turns questions insensitive to indentation, such as nullability below,
  into ordinary CFG questions the library answers.
\<close>

fun unann :: \<open>('n \<times> nat, 'tok \<times> nat) sym \<Rightarrow> ('n, 'tok) sym\<close> where
  \<open>unann (Nt A\<^sub>i) = Nt (fst A\<^sub>i)\<close>
| \<open>unann (Tm aj) = Tm (fst aj)\<close>

lemma unann_annsym[simp]: \<open>unann (annsym Xj) = fst Xj\<close>
  by (cases Xj rule: annsym.cases) auto

definition derel :: \<open>('n \<times> ('n, 'tok) rhs) list \<Rightarrow> ('n, 'tok) prods\<close> where
  \<open>derel = map (\<lambda>(A, rhs). (A, map fst rhs))\<close>

definition gram_terms :: \<open>('n, 'tok) is_cfg \<Rightarrow> 'tok list\<close> where
  \<open>gram_terms G = tms (derel (iprods G))\<close>

lemma gram_termsI:
  \<open>(A, rhs) \<in> set (iprods G) \<Longrightarrow> (Tm t, r) \<in> set rhs \<Longrightarrow> t \<in> set (gram_terms G)\<close>
  unfolding gram_terms_def derel_def set_tms Tms_def Tms_syms_def by force

lemma derelI: \<open>(A, rhs) \<in> set (iprods G) \<Longrightarrow> (A, map fst rhs) \<in> set (derel (iprods G))\<close>
  unfolding derel_def by force

lemma unann_annsym_fst[simp]: \<open>unann \<circ> annsym = fst\<close>
  by (rule ext; case_tac x; simp)

lemma infG_unann:
  assumes \<open>(A\<^sub>i, arhs) \<in> infG G\<close>
  shows \<open>(fst A\<^sub>i, map unann arhs) \<in> set (derel (iprods G))\<close>
proof -
  from assms obtain A i rhs rhs' where
    A\<^sub>i: \<open>A\<^sub>i = (A, i)\<close> \<open>arhs = map annsym rhs'\<close> \<open>(A, rhs) \<in> set (iprods G)\<close>
   and
    rhs: \<open>list_all2 (\<lambda>(X, r) (Y, j). Y = X \<and> irel_sat r j i) rhs rhs'\<close>
    unfolding infG_def by blast

  from rhs have \<open>map fst rhs = map fst rhs'\<close>
    by (induction rule: list.rel_induct) auto

  with A\<^sub>i show ?thesis by (auto dest: derelI)
qed

lemma derive_unann:
  assumes \<open>infG G \<turnstile> \<alpha> \<Rightarrow> \<beta>\<close>
  shows \<open>set (derel (iprods G)) \<turnstile> map unann \<alpha> \<Rightarrow> map unann \<beta>\<close>
proof -
  from assms obtain A\<^sub>i arhs U V where p: \<open>(A\<^sub>i, arhs) \<in> infG G\<close>
    and \<alpha>: \<open>\<alpha> = U @ Nt A\<^sub>i # V\<close> and \<beta>: \<open>\<beta> = U @ arhs @ V\<close>
    by (cases rule: derive.cases) auto
  thus ?thesis
    using derive.intros[OF infG_unann[OF p], of \<open>map unann U\<close> \<open>map unann V\<close>]
    by simp
qed

lemma derives_unann:
  assumes \<open>infG G \<turnstile> \<alpha> \<Rightarrow>* \<beta>\<close>
  shows \<open>set (derel (iprods G)) \<turnstile> map unann \<alpha> \<Rightarrow>* map unann \<beta>\<close>
  using assms
  by (induction rule: rtranclp_induct) (auto intro: rtranclp.rtrancl_into_rtrancl derive_unann)

subsection \<open>Indentation-insensitive grammars\<close>
thm derives_unann
text \<open>
  A grammar whose relations are all \<^const>\<open>Any\<close> is an ordinary CFG in disguise: its
  language is exactly the set of words whose token projection the erased grammar
  derives. The inclusion holds for every grammar by \<open>derives_unann\<close>. The
  converse (\<open>ilang_insensitive\<close>) among the language-level corollaries, annotates
  a parse tree of the erased grammar with arbitrary indentations. \<open>is_cfg_of\<close>
  embeds the library's \<^typ>\<open>('n, 'tok) cfg\<close>, so its results and the parsers below
  apply to plain CFGs.
\<close>

definition ii :: \<open>('n, 'tok) is_cfg \<Rightarrow> bool\<close> where
  \<open>ii G \<longleftrightarrow> (\<forall>(A, rhs) \<in> set (iprods G). list_all ((=) Any \<circ> snd) rhs)\<close>

definition cfg_of :: \<open>('n, 'tok) is_cfg \<Rightarrow> ('n, 'tok) cfg\<close> where
  \<open>cfg_of G = cfg (derel (iprods G)) (istart G)\<close>

definition is_cfg_of :: \<open>('n, 'tok) cfg \<Rightarrow> nat \<Rightarrow> ('n, 'tok) is_cfg\<close> where
  \<open>is_cfg_of C i = \<lparr>
    iprods = map (\<lambda>(A, rhs). (A, map (\<lambda>X. (X, Any)) rhs)) (prods C),
    istart = start C,
    istart_ind = i
  \<rparr>\<close>

lemma insensitive_is_cfg_of[simp]: \<open>ii (is_cfg_of C i)\<close>
  by (auto simp: ii_def is_cfg_of_def list_all_iff)

lemma cfg_of_is_cfg_of[simp]: \<open>cfg_of (is_cfg_of C i) = C\<close>
  by (simp add: cfg_of_def is_cfg_of_def derel_def comp_def case_prod_beta)

lemma ilang_langS: \<open>w \<in> ilang G \<Longrightarrow> map tok w \<in> langS (cfg_of G)\<close>
  using derives_unann[OF ilang_derives[THEN iffD1]] by (simp add: cfg_of_def Lang_def tcols_def comp_def)

subsection \<open>Annotated parse trees\<close>

text \<open>
  Parse trees annotate every node with an indentation: leaves with the column
  of their terminal, inner nodes with their own. A tree is well-formed when each
  inner node expands by a production of the grammar and the indentation of each
  child relates to the node's as that production prescribes.
\<close>

datatype ('m, 'ch, 'n, 'tok) ptree =
    PLeaf \<open>('tok, 'ch, 'm) token_scheme\<close>
  | PNode 'n nat \<open>('m, 'ch, 'n, 'tok) ptree list\<close>

fun proot :: \<open>('m, 'ch, 'n, 'tok) ptree \<Rightarrow> ('n, 'tok) sym \<times> nat\<close> where
  \<open>proot (PLeaf t) = (Tm (tok t), s_col (token.span t))\<close>
| \<open>proot (PNode A i pts) = (Nt A, i)\<close>

fun pyield :: \<open>('m, 'ch, 'n, 'tok) ptree \<Rightarrow> ('m, 'ch, 'tok) tword\<close> where
  \<open>pyield (PLeaf t) = [t]\<close>
| \<open>pyield (PNode A i pts) = concat (map pyield pts)\<close>

lemma fst_proot_Tm_iff: \<open>fst (proot q) = Tm t \<longleftrightarrow> (\<exists>tk. q = PLeaf tk \<and> tok tk = t)\<close>
  by (cases q) auto

inductive wf_ptree :: \<open>('n, 'tok) is_cfg \<Rightarrow> ('m, 'ch, 'n, 'tok) ptree \<Rightarrow> bool\<close> for G where
  wf_leaf: \<open>wf_ptree G (PLeaf t)\<close>
| wf_node: \<open>(A, rhs) \<in> set (iprods G) \<Longrightarrow>
    list_all2 (\<lambda>Xr pt. fst (proot pt) = fst Xr \<and> irel_sat (snd Xr) (snd (proot pt)) i \<and>
      wf_ptree G pt) rhs pts \<Longrightarrow>
    wf_ptree G (PNode A i pts)\<close>

text \<open>Tree height, the fuel the parser needs to find the tree.\<close>

fun pheight :: \<open>('m, 'ch, 'n, 'tok) ptree \<Rightarrow> nat\<close> where
  \<open>pheight (PLeaf t) = 1\<close>
| \<open>pheight (PNode A i pts) = Suc (foldr (\<lambda>pt. max (pheight pt)) pts 0)\<close>

subsection \<open>Indentation-erased ASTs\<close>

text \<open>
  What the parser returns: parse trees without indentations. An AST is a parse
  of a word when it can be annotated to a well-formed parse tree. The annotation
  is existential because a subtree constraining nothing, via
  \<^const>\<open>Any\<close>, admits infinitely many.
\<close>

datatype ('m, 'ch, 'n, 'tok) ast =
    Leaf \<open>('tok, 'ch, 'm) token_scheme\<close>
  | Node 'n \<open>('m, 'ch, 'n, 'tok) ast list\<close>

fun erase :: \<open>('m, 'ch, 'n, 'tok) ptree \<Rightarrow> ('m, 'ch, 'n, 'tok) ast\<close> where
  \<open>erase (PLeaf t) = Leaf t\<close>
| \<open>erase (PNode A i pts) = Node A (map erase pts)\<close>

fun asym :: \<open>('m, 'ch, 'n, 'tok) ast \<Rightarrow> ('n, 'tok) sym\<close> where
  \<open>asym (Leaf t) = Tm (tok t)\<close>
| \<open>asym (Node A ts) = Nt A\<close>

lemma asym_erase: \<open>asym (erase pt) = fst (proot pt)\<close>
  by (cases pt) auto

definition ast_of ::
  \<open>('n, 'tok) is_cfg \<Rightarrow> ('n, 'tok) sym \<Rightarrow> nat \<Rightarrow> ('m, 'ch, 'n, 'tok) ast \<Rightarrow> ('m, 'ch, 'tok) tword \<Rightarrow> bool\<close> where
  \<open>ast_of G X i a w \<longleftrightarrow>
    (\<exists>pt. wf_ptree G pt \<and> proot pt = (X, i) \<and> erase pt = a \<and> pyield pt = w)\<close>

subsection \<open>Feasible-indentation intervals\<close>

text \<open>
  Lemma 4 of the paper: the set of indentations at which a fixed parse of a
  fixed word is well-formed is \<^text>\<open>\<nat>\<close>, a singleton, or bounded. For
  the four relations these sets are half-open intervals \<^text>\<open>[lo, hi)\<close>
  with \<^text>\<open>hi \<le> \<infinity>\<close>, closed under the two operations the parser
  needs: intersection, which joins the constraints of siblings, and the inverse
  image of a relation, which passes a child's constraint up to its parent.
\<close>

type_synonym iv = \<open>nat \<times> enat\<close>

definition iv_mem :: \<open>nat \<Rightarrow> iv \<Rightarrow> bool\<close> where
  \<open>iv_mem i I \<longleftrightarrow> fst I \<le> i \<and> enat i < snd I\<close>

definition iv_full :: iv where
  \<open>iv_full = (0, \<infinity>)\<close>

definition iv_inter :: \<open>iv \<Rightarrow> iv \<Rightarrow> iv\<close> where
  \<open>iv_inter I J = (max (fst I) (fst J), min (snd I) (snd J))\<close>

definition iv_nonempty :: \<open>iv \<Rightarrow> bool\<close> where
  \<open>iv_nonempty I \<longleftrightarrow> enat (fst I) < snd I\<close>

text \<open>For nonempty \<^text>\<open>J\<close>, \<^text>\<open>iv_parent r J\<close> is the
  set of parent indentations admitted by some child indentation in
  \<^text>\<open>J\<close>.\<close>

fun iv_parent :: \<open>irel \<Rightarrow> iv \<Rightarrow> iv\<close> where
  \<open>iv_parent Eq I = I\<close>
| \<open>iv_parent Gt I = (0, snd I - 1)\<close>
| \<open>iv_parent Ge I = (0, snd I)\<close>
| \<open>iv_parent Any I = iv_full\<close>

lemma iv_mem_full[simp]: \<open>iv_mem i iv_full\<close>
  by (simp add: iv_mem_def iv_full_def)

lemma iv_mem_inter[simp]: \<open>iv_mem i (iv_inter I J) \<longleftrightarrow> iv_mem i I \<and> iv_mem i J\<close>
  by (auto simp: iv_mem_def iv_inter_def)

lemma iv_nonempty_iff: \<open>iv_nonempty I \<longleftrightarrow> (\<exists>i. iv_mem i I)\<close>
  by (cases \<open>snd I\<close>) (auto simp: iv_nonempty_def iv_mem_def)

lemma iv_mem_parent:
  assumes \<open>iv_nonempty J\<close>
  shows \<open>iv_mem i (iv_parent r J) \<longleftrightarrow> (\<exists>j. iv_mem j J \<and> irel_sat r j i)\<close>
  using assms
  by (cases r; cases J; cases \<open>snd J\<close>;
      auto simp: iv_nonempty_def iv_mem_def iv_full_def one_enat_def; presburger)

subsection \<open>The parser\<close>

text \<open>
  A non-deterministic recursive-descent parser. \<^text>\<open>parse_sym n G X w\<close>
  returns every triple \<^text>\<open>(a, I, rest)\<close> whose prefix of
  \<^text>\<open>w\<close> before \<^text>\<open>rest\<close> parses as symbol \<^text>\<open>X\<close> with
  AST \<^text>\<open>a\<close>, where \<^text>\<open>I\<close> holds the indentations at which that
  parse is well-formed. The fuel \<^text>\<open>n\<close> bounds the height of the trees
  considered, making the parser total; completeness is relative to it.

  \<^text>\<open>parse_seq\<close> does the same along a right-hand side and returns the
  feasible indentations of the parent: each child contributes the inverse image
  of its interval under its relation, and those constraints are intersected.
  Empty intervals are pruned, so every interval returned is nonempty.
\<close>

fun parse_sym and parse_seq where
  \<open>parse_sym 0 G X w = []\<close>
| \<open>parse_sym (Suc n) G (Tm t) [] = []\<close>
| \<open>parse_sym (Suc n) G (Tm t) (t' # w) =
    (if t = tok t'
     then [(Leaf t', (s_col (token.span t'), enat (Suc (s_col (token.span t')))), w)] else [])\<close>
| \<open>parse_sym (Suc n) G (Nt A) w =
    concat (map (\<lambda>(B, rhs).
      if B = A
      then map (\<lambda>(as, I, rest). (Node A as, I, rest)) (parse_seq n G rhs w)
      else []) (iprods G))\<close>
| \<open>parse_seq n G [] w = [([], iv_full, w)]\<close>
| \<open>parse_seq n G ((X, r) # rhs) w =
    concat (map (\<lambda>(a, J, w').
      concat (map (\<lambda>(as, K, w'').
        (let I = iv_inter (iv_parent r J) K in
         if iv_nonempty I then [(a # as, I, w'')] else []))
        (parse_seq n G rhs w')))
      (parse_sym n G X w))\<close>

text \<open>The top-level parser keeps the parses that consume the whole
  input and admit the start indentation.\<close>

definition parse :: \<open>nat \<Rightarrow> ('n, 'tok) is_cfg \<Rightarrow> ('m, 'ch, 'tok) tword \<Rightarrow> ('m, 'ch, 'n, 'tok) ast list\<close> where
  \<open>parse n G w = map (\<lambda>(a, I, rest). a)
     (filter (\<lambda>(a, I, rest). rest = [] \<and> iv_mem (istart_ind G) I)
       (parse_sym n G (Nt (istart G)) w))\<close>

subsection \<open>Soundness and completeness against parse trees\<close>

text \<open>Set-level forms of the two parser equations. The correctness proofs
  go through these rather than the list code.\<close>

lemma parse_sym_Nt_set:
  \<open>set (parse_sym (Suc n) G (Nt A) w) =
    {(Node A as, I, rest) | as I rest rhs.
      (A, rhs) \<in> set (iprods G) \<and> (as, I, rest) \<in> set (parse_seq n G rhs w)}\<close>
  by (fastforce split: if_splits)

lemma parse_seq_cons_set:
  \<open>set (parse_seq n G ((X, r) # rhs) w) =
    {(a # as, iv_inter (iv_parent r J) K, w'') | a J w' as K w''.
      (a, J, w') \<in> set (parse_sym n G X w) \<and> (as, K, w'') \<in> set (parse_seq n G rhs w') \<and>
      iv_nonempty (iv_inter (iv_parent r J) K)}\<close>
  by (fastforce simp: Let_def split: if_splits)

lemma parse_iv_nonempty:
  fixes G H :: \<open>('n, 'tok) is_cfg\<close>
  shows \<open>\<And>(a :: ('m, 'ch, 'n, 'tok) ast) I rest.
           (a, I, rest) \<in> set (parse_sym n G X w) \<Longrightarrow> iv_nonempty I\<close>
    and \<open>\<And>(as :: ('m, 'ch, 'n, 'tok) ast list) I rest.
          (as, I, rest) \<in> set (parse_seq m H rhs v) \<Longrightarrow> iv_nonempty I\<close>
  by (induction n G X w and m H rhs v rule: parse_sym_parse_seq.induct)
    (auto simp: Let_def iv_nonempty_def iv_full_def split: if_splits)

text \<open>
  Soundness: every parser result comes from a well-formed annotated parse tree,
  at every indentation of the returned interval. For \<^text>\<open>parse_seq\<close> the
  statement yields the list of child trees together with the side conditions
  \<^text>\<open>wf_node\<close> asks for.
\<close>

lemma parse_sound:
  fixes G H :: \<open>('n, 'tok) is_cfg\<close>
  shows \<open>\<And>(a :: ('m, 'ch, 'n, 'tok) ast) I rest i.
          (a, I, rest) \<in> set (parse_sym n G X w) \<Longrightarrow> iv_mem i I \<Longrightarrow>
          \<exists>pt. wf_ptree G pt \<and> proot pt = (X, i) \<and> erase pt = a \<and> w = pyield pt @ rest\<close>
    and \<open>\<And>(as :: ('m, 'ch, 'n, 'tok) ast list) I rest i.
          (as, I, rest) \<in> set (parse_seq m H rhs v) \<Longrightarrow> iv_mem i I \<Longrightarrow>
          \<exists>pts. list_all2 (\<lambda>Xr pt. fst (proot pt) = fst Xr \<and>
              irel_sat (snd Xr) (snd (proot pt)) i \<and> wf_ptree H pt) rhs pts \<and>
              map erase pts = as \<and> v = concat (map pyield pts) @ rest\<close>
proof (induction n G X w and m H rhs v rule: parse_sym_parse_seq.induct)
  case (3 n G t t' w a I rest i)
  from "3.prems" have
    I: \<open>I = (s_col (token.span t'), enat (Suc (s_col (token.span t'))))\<close> and
    \<open>tok t' = t\<close> \<open>a = Leaf t'\<close> \<open>rest = w\<close>
    by (auto split: if_splits)

  moreover from 3 I have ij: \<open>i = s_col (token.span t')\<close>
    by (simp add: iv_mem_def)

  ultimately show ?case
    by (intro exI[of _ \<open>PLeaf t'\<close>]) (simp add: wf_leaf)
next
  case (4 n G A w a I rest i)

  from "4.prems"[unfolded parse_sym_Nt_set] obtain as rhs where
    a: \<open>a = Node A as\<close> and
    A: \<open>(A, rhs) \<in> set (iprods G)\<close> and
    s: \<open>(as, I, rest) \<in> set (parse_seq n G rhs w)\<close>
    by blast

  from "4.IH"[OF A refl refl s] "4.prems" obtain pts where
    rhs: \<open>list_all2 (\<lambda>Xr pt. fst (proot pt) = fst Xr \<and>
            irel_sat (snd Xr) (snd (proot pt)) i \<and> wf_ptree G pt) rhs pts\<close> and
    \<open>map erase pts = as\<close> \<open>w = concat (map pyield pts) @ rest\<close>
    by blast

  with wf_node[OF A] a show ?case
    by (intro exI[of _ \<open>PNode A i pts\<close>]) simp
next
  case (6 n G X r rhs w as I rest i)

  from "6.prems"[unfolded parse_seq_cons_set] obtain a J w' as' K where
    as: \<open>as = a # as'\<close> and I: \<open>I = iv_inter (iv_parent r J) K\<close> and
    J: \<open>(a, J, w') \<in> set (parse_sym n G X w)\<close> and
    K: \<open>(as', K, rest) \<in> set (parse_seq n G rhs w')\<close>
    by blast

  from "6.prems"(2) I have iv: \<open>iv_mem i (iv_parent r J)\<close> \<open>iv_mem i K\<close>
    by auto
  from iv(1) parse_iv_nonempty(1)[OF J] obtain j where \<open>iv_mem j J\<close> and sat: \<open>irel_sat r j i\<close>
    using iv_mem_parent by blast

  with "6.IH"(1)[OF J] obtain pt where
    \<open>wf_ptree G pt\<close> \<open>proot pt = (X, j)\<close> \<open>erase pt = a\<close> \<open>w = pyield pt @ w'\<close>
    by blast

  moreover from "6.IH"(2)[OF J refl refl K iv(2)] obtain pts where
     \<open>list_all2
        (\<lambda>Xr pt. fst (proot pt) = fst Xr \<and> irel_sat (snd Xr) (snd (proot pt)) i \<and> wf_ptree G pt)
        rhs pts\<close>
     \<open>map erase pts = as'\<close> \<open>w' = concat (map pyield pts) @ rest\<close>
    by blast
  ultimately show ?case
    using sat as by (intro exI[of _ \<open>pt # pts\<close>]) simp
qed simp_all

lemma pheight_pos: \<open>1 \<le> pheight pt\<close> by (cases pt) simp_all

lemma pheight_child_le: \<open>pt \<in> set pts \<Longrightarrow> pheight pt \<le> foldr (\<lambda>pt. max (pheight pt)) pts 0\<close>
  by (induction pts) auto

text \<open>
  Completeness: every well-formed annotated parse tree of height at most
  \<^text>\<open>n\<close> is found, its erasure returned with an interval containing the
  root indentation. For an inner node, an induction along the right-hand side
  assembles the \<^text>\<open>parse_seq\<close> run from the parses of the children.
\<close>

lemma parse_complete:
  \<open>wf_ptree G pt \<Longrightarrow> proot pt = (X, i) \<Longrightarrow> pheight pt \<le> n \<Longrightarrow>
   \<exists>I. (erase pt, I, rest) \<in> set (parse_sym n G X (pyield pt @ rest)) \<and> iv_mem i I\<close>
proof (induction n arbitrary: pt X i rest)
  case 0
  then show ?case using pheight_pos[of pt] by simp
next
  case (Suc n)
  show ?case proof (cases pt)
    case (PLeaf t)
    with Suc.prems(2) have \<open>X = Tm (tok t)\<close> \<open>i = s_col (token.span t)\<close> by simp_all
    thus ?thesis
      by (intro exI[of _ \<open>(s_col (token.span t), enat (Suc (s_col (token.span t))))\<close>])
         (simp add: PLeaf iv_mem_def)
  next
    case (PNode A i' pts)
    with Suc.prems(2) have X: \<open>X = Nt A\<close> and i: \<open>i = i'\<close> by simp_all
    have \<open>wf_ptree G (PNode A i' pts)\<close> using Suc.prems(1) PNode by simp
    then obtain rhs where p: \<open>(A, rhs) \<in> set (iprods G)\<close>
      and la: \<open>list_all2 (\<lambda>Xr q. fst (proot q) = fst Xr \<and>
                 irel_sat (snd Xr) (snd (proot q)) i' \<and> wf_ptree G q) rhs pts\<close>
      by (auto elim: wf_ptree.cases)
    have hts: \<open>\<And>q. q \<in> set pts \<Longrightarrow> pheight q \<le> n\<close>
      using Suc.prems(3) PNode pheight_child_le[of _ pts] by fastforce
    have la': \<open>list_all2 (\<lambda>Xr q. (fst (proot q) = fst Xr \<and>
                 irel_sat (snd Xr) (snd (proot q)) i' \<and> wf_ptree G q) \<and>
                 pheight q \<le> n) rhs pts\<close>
      using la hts by (auto simp: list_all2_conv_all_nth)
    have seq: \<open>\<And>rest'. \<exists>K. (map erase pts, K, rest') \<in>
        set (parse_seq n G rhs (concat (map pyield pts) @ rest')) \<and> iv_mem i' K\<close>
      using la'
    proof (induction rhs pts rule: list_all2_induct)
      case Nil
      show ?case by (auto simp: iv_mem_def iv_full_def)
    next
      case (Cons Xr rhs' pt\<^sub>0 pts')
      fix rest'
      obtain X\<^sub>0 r\<^sub>0 where Xr: \<open>Xr = (X\<^sub>0, r\<^sub>0)\<close> by (cases Xr)
      define j\<^sub>0 where \<open>j\<^sub>0 = snd (proot pt\<^sub>0)\<close>
      from Cons.hyps(1) Xr have root\<^sub>0: \<open>fst (proot pt\<^sub>0) = X\<^sub>0\<close>
        and sat\<^sub>0: \<open>irel_sat r\<^sub>0 j\<^sub>0 i'\<close> and wf\<^sub>0: \<open>wf_ptree G pt\<^sub>0\<close> and h\<^sub>0: \<open>pheight pt\<^sub>0 \<le> n\<close>
        by (auto simp: j\<^sub>0_def)
      have proot\<^sub>0: \<open>proot pt\<^sub>0 = (X\<^sub>0, j\<^sub>0)\<close>
        using root\<^sub>0 by (simp add: j\<^sub>0_def prod_eq_iff)
      from Suc.IH[OF wf\<^sub>0 proot\<^sub>0 h\<^sub>0] obtain J where
        J: \<open>(erase pt\<^sub>0, J, concat (map pyield pts') @ rest') \<in>
            set (parse_sym n G X\<^sub>0 (pyield pt\<^sub>0 @ concat (map pyield pts') @ rest'))\<close>
        and jJ: \<open>iv_mem j\<^sub>0 J\<close> by blast
      from Cons.IH obtain K where
        K: \<open>(map erase pts', K, rest') \<in>
            set (parse_seq n G rhs' (concat (map pyield pts') @ rest'))\<close>
        and iK: \<open>iv_mem i' K\<close> by blast
      have \<open>iv_mem i' (iv_parent r\<^sub>0 J)\<close>
        using iv_mem_parent[of J i' r\<^sub>0] jJ sat\<^sub>0 iv_nonempty_iff by blast
      hence iv: \<open>iv_mem i' (iv_inter (iv_parent r\<^sub>0 J) K)\<close> using iK by simp
      hence ne: \<open>iv_nonempty (iv_inter (iv_parent r\<^sub>0 J) K)\<close>
        using iv_nonempty_iff by blast
      hence \<open>(erase pt\<^sub>0 # map erase pts', iv_inter (iv_parent r\<^sub>0 J) K, rest')
            \<in> set (parse_seq n G ((X\<^sub>0, r\<^sub>0) # rhs')
                (pyield pt\<^sub>0 @ concat (map pyield pts') @ rest'))\<close>
        unfolding parse_seq_cons_set using J K by blast
      with iv Xr show \<open>\<exists>K.
          (map erase (pt\<^sub>0 # pts'), K, rest') \<in>
          set (parse_seq n G (Xr # rhs') (concat (map pyield (pt\<^sub>0 # pts')) @ rest')) \<and> iv_mem i' K\<close>
        by (intro exI[of _ \<open>iv_inter (iv_parent r\<^sub>0 J) K\<close>]) (simp del: parse_sym.simps parse_seq.simps)
    qed

    from seq[of rest] obtain K where \<open>iv_mem i' K\<close> and
        K: \<open>(map erase pts, K, rest) \<in> set (parse_seq n G rhs (concat (map pyield pts) @ rest))\<close>
      by blast
    moreover have
        \<open>(Node A (map erase pts), K, rest) \<in> set (parse_sym (Suc n) G (Nt A) (concat (map pyield pts) @ rest))\<close>
      unfolding parse_sym_Nt_set using p K by blast
    ultimately show ?thesis
      by (intro exI[of _ K]) (simp add: PNode X i del: parse_sym.simps parse_seq.simps)
  qed
qed

subsection \<open>Correctness of the top-level parser\<close>

theorem parse_sound_ast:
  assumes \<open>a \<in> set (parse n G w)\<close>
  shows \<open>ast_of G (Nt (istart G)) (istart_ind G) a w\<close>
proof -
  from assms obtain I where
    \<open>(a, I, []) \<in> set (parse_sym n G (Nt (istart G)) w)\<close> \<open>iv_mem (istart_ind G) I\<close>
    by (auto simp: parse_def)
  with parse_sound(1) show ?thesis
    unfolding ast_of_def by blast
qed

theorem parse_complete_ast:
  assumes
    \<open>wf_ptree G pt\<close>
    \<open>proot pt = (Nt (istart G), istart_ind G)\<close>
    \<open>pheight pt \<le> n\<close>
  shows \<open>erase pt \<in> set (parse n G (pyield pt))\<close>
proof -
  from parse_complete[OF assms, of \<open>[]\<close>] obtain I where
    \<open>(erase pt, I, []) \<in> set (parse_sym n G (Nt (istart G)) (pyield pt))\<close> \<open>iv_mem (istart_ind G) I\<close>
    by auto
  then show ?thesis by (force simp: parse_def)
qed

corollary parse_complete_ast_ex:
  assumes \<open>ast_of G (Nt (istart G)) (istart_ind G) a w\<close>
  shows \<open>\<exists>n. a \<in> set (parse n G w)\<close>
  using assms parse_complete_ast unfolding ast_of_def by blast


subsection \<open>The parse depends on the word only through its columns\<close>

text \<open>
  The parser copies each token into the corresponding AST leaf and otherwise
  reads only the token identity and its span's column. So \<^const>\<open>parse\<close>
  commutes with any column-preserving relabelling of the spans: a
  reformatting that leaves every column intact cannot change the parse
  beyond the same relabelling of its leaves.
\<close>

fun astmap :: \<open>('ch span \<Rightarrow> 'ch span) \<Rightarrow> ('m, 'ch, 'n, 'tok) ast \<Rightarrow> ('m, 'ch, 'n, 'tok) ast\<close> where
  \<open>astmap f (Leaf t) = Leaf (t\<lparr>span := f (token.span t)\<rparr>)\<close>
| \<open>astmap f (Node A as) = Node A (map (astmap f) as)\<close>

definition wsub :: \<open>('ch span \<Rightarrow> 'ch span) \<Rightarrow> ('m, 'ch, 'tok) tword \<Rightarrow> ('m, 'ch, 'tok) tword\<close> where
  \<open>wsub f w = map (\<lambda>t. t\<lparr>span := f (token.span t)\<rparr>) w\<close>

lemma wsub_Nil[simp]: \<open>wsub f [] = []\<close>
  by (simp add: wsub_def)

lemma wsub_Cons[simp]: \<open>wsub f (t # w) = t\<lparr>span := f (token.span t)\<rparr> # wsub f w\<close>
  by (simp add: wsub_def)

lemma wsub_eq_Nil[simp]: \<open>(wsub f w = []) = (w = [])\<close>
  by (simp add: wsub_def)

lemma parse_relabel:
  fixes G H :: \<open>('n, 'tok) is_cfg\<close>
    and w v :: \<open>('m, 'ch, 'tok) tword\<close>
  assumes \<open>\<And>sp. s_col (f sp) = s_col sp\<close>
  shows \<open>parse_sym n G X (wsub f w) = map (\<lambda>(a, I, r). (astmap f a, I, wsub f r)) (parse_sym n G X w)\<close>
    and \<open>parse_seq m H rhs (wsub f v) = map (\<lambda>(as, I, r). (map (astmap f) as, I, wsub f r)) (parse_seq m H rhs v)\<close>
proof (induction n G X w and m H rhs v rule: parse_sym_parse_seq.induct)
  case (3 n G t t' w)
  show ?case using assms by (simp add: wsub_def)
next
  case (4 n G A w)
  have key: \<open>(if B = A then map (\<lambda>(as, I, rest). (Node A as, I, rest)) 
                (parse_seq n G rhs (wsub f w)) else []) =
             map (\<lambda>(a, I, r). (astmap f a, I, wsub f r))
               (if B = A then map (\<lambda>(as, I, rest). (Node A as, I, rest))
                  (parse_seq n G rhs w) else [])\<close>
    if p: \<open>(B, rhs) \<in> set (iprods G)\<close> for B rhs
  proof (cases \<open>B = A\<close>)
    case True
    have \<open>parse_seq n G rhs (wsub f w) =
          map (\<lambda>(as, I, r). (map (astmap f) as, I, wsub f r)) (parse_seq n G rhs w)\<close>
      using "4.IH"[OF p refl True] .
    then show ?thesis by (simp add: True o_def case_prod_beta)
  qed simp
  have \<open>parse_sym (Suc n) G (Nt A) (wsub f w) =
        concat (map (\<lambda>(B, rhs). if B = A then map (\<lambda>(as, I, rest). (Node A as, I, rest))
                  (parse_seq n G rhs (wsub f w)) else []) (iprods G))\<close>
    by simp
  also have \<open>\<dots> = concat (map (\<lambda>(B, rhs). map (\<lambda>(a, I, r). (astmap f a, I, wsub f r))
                  (if B = A then map (\<lambda>(as, I, rest). (Node A as, I, rest))
                     (parse_seq n G rhs w) else [])) (iprods G))\<close>
    by (intro arg_cong[where f = concat] map_cong refl)
       (use key in \<open>auto simp: case_prod_beta\<close>)
  also have \<open>\<dots> = map (\<lambda>(a, I, r). (astmap f a, I, wsub f r))
                    (parse_sym (Suc n) G (Nt A) w)\<close>
    by (simp only: parse_sym.simps map_concat map_map)
       (rule arg_cong[where f = concat], rule map_cong[OF refl],
        simp add: o_def split: prod.splits)
  finally show ?case .
next
  case (6 n G X r rhs w)
  have key: \<open>concat (map (\<lambda>(as, K, w''). let I = iv_inter (iv_parent r J) K in
                  if iv_nonempty I then [(astmap f a # as, I, w'')] else [])
               (parse_seq n G rhs (wsub f w'))) =
             map (\<lambda>(as, I, rr). (map (astmap f) as, I, wsub f rr))
               (concat (map (\<lambda>(as, K, w''). let I = iv_inter (iv_parent r J) K in
                  if iv_nonempty I then [(a # as, I, w'')] else [])
                 (parse_seq n G rhs w')))\<close>
    if q: \<open>(a, J, w') \<in> set (parse_sym n G X w)\<close> for a J w'
  proof -
    have ih\<^sub>2: \<open>parse_seq n G rhs (wsub f w') =
          map (\<lambda>(as, I, rr). (map (astmap f) as, I, wsub f rr)) (parse_seq n G rhs w')\<close>
      using "6.IH"(2)[OF q refl refl] .
    show ?thesis
      unfolding ih\<^sub>2
      by (simp only: map_map map_concat)
         (rule arg_cong[where f = concat], rule map_cong[OF refl],
          auto simp: o_def Let_def split: prod.splits)
  qed
  have \<open>parse_seq n G ((X, r) # rhs) (wsub f w) =
        concat (map (\<lambda>(a, J, w'). concat (map (\<lambda>(as, K, w''). let I = iv_inter (iv_parent r J) K in
                  if iv_nonempty I then [(a # as, I, w'')] else []) (parse_seq n G rhs w')))
             (parse_sym n G X (wsub f w)))\<close>
    by simp
  also have \<open>\<dots> = concat (map (\<lambda>(a, J, w'). concat (map (\<lambda>(as, K, w''). let I = iv_inter (iv_parent r J) K in
                  if iv_nonempty I then [(astmap f a # as, I, w'')] else []) (parse_seq n G rhs (wsub f w'))))
             (parse_sym n G X w))\<close>
    unfolding "6.IH"(1)
    by (simp only: map_map)
       (rule arg_cong[where f = concat], rule map_cong[OF refl],
        simp add: o_def Let_def split: prod.splits)
  also have \<open>\<dots> = map (\<lambda>(as, I, rr). (map (astmap f) as, I, wsub f rr))
                    (parse_seq n G ((X, r) # rhs) w)\<close>
    by (simp only: parse_seq.simps map_concat map_map)
       (rule arg_cong[where f = concat], rule map_cong[OF refl],
        use key in \<open>fastforce simp: o_def split: prod.splits\<close>)
  finally show ?case .
qed simp_all

lemma parse_relabel_parse:
  assumes \<open>\<And>sp. s_col (f sp) = s_col sp\<close>
  shows \<open>parse n G (wsub f w) = map (astmap f) (parse n G w)\<close>
proof -
  have \<open>parse n G (wsub f w) = map (\<lambda>(a, I, r). a)
          (filter (\<lambda>(a, I, r). r = [] \<and> iv_mem (istart_ind G) I)
            (map (\<lambda>(a, I, r). (astmap f a, I, wsub f r)) (parse_sym n G (Nt (istart G)) w)))\<close>
    unfolding parse_def parse_relabel(1)[OF assms] ..
  also have \<open>\<dots> = map (astmap f) (parse n G w)\<close>
    by (simp add: parse_def filter_map o_def case_prod_beta cong: filter_cong)
  finally show ?thesis .
qed

text \<open>Any extension of the token record (the \<^text>\<open>'m\<close> of \<^typ>\<open>('tok, 'ch, 'm) token_scheme\<close>)
  is invisible to the parser: it is copied into leaves and otherwise ignored.\<close>

subsection \<open>Parse trees agree with the rewrite relation\<close>

text \<open>
  The two semantics coincide: a word is derivable from an annotated non-terminal
  iff it is the yield of a well-formed parse tree rooted there. Together with the
  parser theorems this connects \<^const>\<open>parse\<close> to \<^const>\<open>ilang\<close>.

  Both directions are the library's, via \<^const>\<open>infG\<close>: annotating a parse
  tree turns it into a \<^typ>\<open>('n \<times> nat, 'tok \<times> nat) Parse_Tree.ptree\<close> of that grammar, and
  \<^text>\<open>derives_fringe_if_parse_tree\<close> and \<^text>\<open>parse_tree_if_derives\<close>
  relate those to derivations. Only the spans have to be put back by hand, a
  \<^const>\<open>PLeaf\<close> carrying the full source span where the corresponding
  \<^const>\<open>Tm\<close> carries just the column.
\<close>

fun anntree :: \<open>('m, 'ch, 'n, 'tok) ptree \<Rightarrow> ('n \<times> nat, 'tok \<times> nat) Parse_Tree.ptree\<close> where
  \<open>anntree (PLeaf t) = Sym (Tm (tok t, s_col (token.span t)))\<close>
| \<open>anntree (PNode A i pts) = Prod (A, i) (map anntree pts)\<close>

lemma root_anntree[simp]: \<open>Parse_Tree.root (anntree pt) = annsym (proot pt)\<close>
  by (cases pt) auto

lemma fringe_anntree[simp]: \<open>fringe (anntree pt) = map Tm (tcols (pyield pt))\<close>
proof (induction pt)
  case (PNode A i pts)
  then show ?case by (induction pts) auto
qed simp

lemma parse_tree_anntree[simp]: \<open>parse_tree (infG G) (anntree pt) \<longleftrightarrow> wf_ptree G pt\<close>
proof (induction pt)
  case (PLeaf t)
  show ?case by (simp add: wf_ptree.wf_leaf)
next
  case (PNode A i pts)
  have roots: \<open>map Parse_Tree.root (map anntree pts) = map annsym (map proot pts)\<close>
    by (simp add: o_def)
  have infG: \<open>((A, i), map annsym (map proot pts)) \<in> infG G \<longleftrightarrow>
        (\<exists>rhs. (A, rhs) \<in> set (iprods G) \<and>
           list_all2 (\<lambda>(X, r) (Y, j). Y = X \<and> irel_sat r j i) rhs (map proot pts))\<close>
    by (auto simp: infG_def simp del: map_map dest!: map_annsym_injective)
  have wf: \<open>wf_ptree G (PNode A i pts) \<longleftrightarrow>
        (\<exists>rhs. (A, rhs) \<in> set (iprods G) \<and>
           list_all2 (\<lambda>(X, r) (Y, j). Y = X \<and> irel_sat r j i) rhs (map proot pts)) \<and>
        (\<forall>q \<in> set pts. wf_ptree G q)\<close>
    by (subst wf_ptree.simps)
       (auto simp: list_all2_map2 list_all2_conv_all_nth case_prod_beta prod_eq_iff all_set_conv_all_nth)
  show ?case
    using PNode.IH by (auto simp del: map_map simp add: roots infG wf)
qed

text \<open>Every annotated tree over \<^const>\<open>infG\<close> whose fringe is the column
  projection of \<^text>\<open>w\<close> comes from a parse tree yielding \<^text>\<open>w\<close>: the
  fringe fixes the leaf order, so the spans of \<^text>\<open>w\<close> can be handed back
  to the leaves in that order.\<close>

lemma ex_anntree:
  fixes t :: \<open>('n \<times> nat, 'tok \<times> nat) Parse_Tree.ptree\<close> and w :: \<open>('m, 'ch, 'tok) tword\<close>
  shows \<open>fringe t = map Tm (tcols w) \<Longrightarrow>
         \<exists>pt::('m, 'ch, 'n, 'tok) ptree. anntree pt = t \<and> pyield pt = w\<close>
proof (induction t arbitrary: w)
  case (Sym s)
  then obtain a where \<open>w = [a]\<close> \<open>s = Tm (tok a, s_col (token.span a))\<close>
    by (cases w) (auto simp: tcols_def)
  then show ?case by (intro exI[of _ \<open>PLeaf a\<close>]) simp
next
  case (Prod B ts)
  have \<open>\<exists>pts::('m, 'ch, 'n, 'tok) ptree list.
          map anntree pts = ts' \<and> concat (map pyield pts) = w'\<close>
    if \<open>set ts' \<subseteq> set ts\<close> and \<open>fringes ts' = map Tm (tcols w')\<close>
    for ts' and w' :: \<open>('m, 'ch, 'tok) tword\<close>
    using that
  proof (induction ts' arbitrary: w')
    case Nil
    then show ?case by (auto simp: tcols_def)
  next
    case (Cons t ts')
    let ?w\<^sub>1 = \<open>take (length (fringe t)) w'\<close> and ?w\<^sub>2 = \<open>drop (length (fringe t)) w'\<close>
    from Cons.prems have \<open>fringe t @ fringes ts' = map Tm (tcols w')\<close> by simp
    then have \<open>fringe t = take (length (fringe t)) (map Tm (tcols w'))\<close>
      and \<open>fringes ts' = drop (length (fringe t)) (map Tm (tcols w'))\<close>
      unfolding append_eq_conv_conj by auto
    then have f\<^sub>1: \<open>fringe t = map Tm (tcols ?w\<^sub>1)\<close> and f\<^sub>2: \<open>fringes ts' = map Tm (tcols ?w\<^sub>2)\<close>
      by (simp_all add: tcols_take tcols_drop take_map drop_map)
    from Cons.prems have \<open>t \<in> set ts\<close> and \<open>set ts' \<subseteq> set ts\<close> by simp_all
    from Prod.IH[OF \<open>t \<in> set ts\<close> f\<^sub>1] obtain pt :: \<open>('m, 'ch, 'n, 'tok) ptree\<close> where
      \<open>anntree pt = t\<close> \<open>pyield pt = ?w\<^sub>1\<close> by blast
    moreover from Cons.IH[OF \<open>set ts' \<subseteq> set ts\<close> f\<^sub>2] obtain pts where
      \<open>map anntree pts = ts'\<close> \<open>concat (map pyield pts) = ?w\<^sub>2\<close> by blast
    ultimately show ?case by (intro exI[of _ \<open>pt # pts\<close>]) simp
  qed
  from this[OF subset_refl] Prod.prems obtain pts where
    \<open>map anntree pts = ts\<close> \<open>concat (map pyield pts) = w\<close> by auto
  then show ?case by (intro exI[of _ \<open>PNode (fst B) (snd B) pts\<close>]) simp
qed

theorem derives_iff_ptree:
  \<open>infG G \<turnstile> [Nt (A, i)] \<Rightarrow>* map Tm (tcols w) \<longleftrightarrow>
   (\<exists>pt. wf_ptree G pt \<and> proot pt = (Nt A, i) \<and> pyield pt = w)\<close>
proof
  assume \<open>infG G \<turnstile> [Nt (A, i)] \<Rightarrow>* map Tm (tcols w)\<close>
  from parse_tree_if_derives[OF this] obtain t where
    t: \<open>parse_tree (infG G) t\<close> \<open>fringe t = map Tm (tcols w)\<close>
       \<open>Parse_Tree.root t = Nt (A, i)\<close> by blast
  from ex_anntree[OF t(2)] obtain pt where pt: \<open>t = anntree pt\<close> \<open>pyield pt = w\<close> by metis
  from t(1,3) show \<open>\<exists>pt. wf_ptree G pt \<and> proot pt = (Nt A, i) \<and> pyield pt = w\<close>
    unfolding pt(1) using pt(2) by (auto simp: annsym_eq_Nt)
next
  assume \<open>\<exists>pt. wf_ptree G pt \<and> proot pt = (Nt A, i) \<and> pyield pt = w\<close>
  then obtain pt where pt: \<open>wf_ptree G pt\<close> \<open>proot pt = (Nt A, i)\<close> \<open>pyield pt = w\<close> by blast
  from derives_fringe_if_parse_tree[of \<open>infG G\<close> \<open>anntree pt\<close>] pt
  show \<open>infG G \<turnstile> [Nt (A, i)] \<Rightarrow>* map Tm (tcols w)\<close> by simp
qed

corollary iderives_iff_ptree:
  \<open>iderives G [(Nt A, i)] (word_of w) \<longleftrightarrow>
   (\<exists>pt. wf_ptree G pt \<and> proot pt = (Nt A, i) \<and> pyield pt = w)\<close>
  using inf_cfg_derives[of G \<open>[(Nt A, i)]\<close> \<open>word_of w\<close>]
  by (simp add: derives_iff_ptree[symmetric] annsym_word_of)

subsection \<open>Language-level corollaries\<close>

corollary ilang_iff_ast:
  \<open>w \<in> ilang G \<longleftrightarrow> (\<exists>a. ast_of G (Nt (istart G)) (istart_ind G) a w)\<close>
  unfolding ilang_derives ast_of_def
  using derives_iff_ptree[of G \<open>istart G\<close> \<open>istart_ind G\<close> w] by auto

text \<open>The converse of \<open>ilang_langS\<close> for insensitive grammars: a parse tree of
  the erased grammar lifts to a well-formed parse tree at any indentation.\<close>

lemma wf_ptree_if_parse_tree:
  fixes t :: \<open>('n, 'tok) Parse_Tree.ptree\<close> and w :: \<open>('m, 'ch, 'tok) tword\<close>
  assumes \<open>ii G\<close>
  shows \<open>parse_tree (set (derel (iprods G))) t \<Longrightarrow> fringe t = map Tm (map tok w) \<Longrightarrow>
         \<exists>pt::('m, 'ch, 'n, 'tok) ptree. wf_ptree G pt \<and> pyield pt = w \<and> fst (proot pt) = Parse_Tree.root t \<and>
           (\<forall>A. Parse_Tree.root t = Nt A \<longrightarrow> snd (proot pt) = i)\<close>
proof (induction t arbitrary: w i)
  case (Sym s)
  then obtain a where \<open>w = [a]\<close> \<open>s = Tm (tok a)\<close> by (cases w) auto
  then show ?case by (intro exI[of _ \<open>PLeaf a\<close>]) (simp add: wf_leaf)
next
  case (Prod B ts)
  have \<open>\<exists>pts::('m, 'ch, 'n, 'tok) ptree list.
          list_all2 (\<lambda>t pt. wf_ptree G pt \<and> fst (proot pt) = Parse_Tree.root t) ts' pts \<and> concat (map pyield pts) = w'\<close>
    if \<open>set ts' \<subseteq> set ts\<close> and \<open>fringes ts' = map Tm (map tok w')\<close>
    for ts' and w' :: \<open>('m, 'ch, 'tok) tword\<close>
    using that
  proof (induction ts' arbitrary: w')
    case Nil
    then show ?case by auto
  next
    case (Cons t ts')
    let ?w\<^sub>1 = \<open>take (length (fringe t)) w'\<close> and ?w\<^sub>2 = \<open>drop (length (fringe t)) w'\<close>
    from Cons.prems have \<open>fringe t @ fringes ts' = map Tm (map tok w')\<close> by simp
    then have \<open>fringe t = take (length (fringe t)) (map Tm (map tok w'))\<close>
      and \<open>fringes ts' = drop (length (fringe t)) (map Tm (map tok w'))\<close>
      unfolding append_eq_conv_conj by auto
    then have f\<^sub>1: \<open>fringe t = map Tm (map tok ?w\<^sub>1)\<close> and f\<^sub>2: \<open>fringes ts' = map Tm (map tok ?w\<^sub>2)\<close>
      by (simp_all add: take_map drop_map)
    from Cons.prems have \<open>t \<in> set ts\<close> and \<open>set ts' \<subseteq> set ts\<close> by simp_all
    with Prod.prems(1) have \<open>parse_tree (set (derel (iprods G))) t\<close> by simp
    from Prod.IH[OF \<open>t \<in> set ts\<close> this f\<^sub>1] obtain pt :: \<open>('m, 'ch, 'n, 'tok) ptree\<close> where
      \<open>wf_ptree G pt\<close> \<open>pyield pt = ?w\<^sub>1\<close> \<open>fst (proot pt) = Parse_Tree.root t\<close> by blast
    moreover from Cons.IH[OF \<open>set ts' \<subseteq> set ts\<close> f\<^sub>2] obtain pts :: \<open>('m, 'ch, 'n, 'tok) ptree list\<close> where
      \<open>list_all2 (\<lambda>t pt. wf_ptree G pt \<and> fst (proot pt) = Parse_Tree.root t) ts' pts\<close> \<open>concat (map pyield pts) = ?w\<^sub>2\<close>
      by blast
    ultimately show ?case by (intro exI[of _ \<open>pt # pts\<close>]) simp
  qed
  from this[OF subset_refl] Prod.prems(2) obtain pts :: \<open>('m, 'ch, 'n, 'tok) ptree list\<close> where
    pts: \<open>list_all2 (\<lambda>t pt. wf_ptree G pt \<and> fst (proot pt) = Parse_Tree.root t) ts pts\<close> \<open>concat (map pyield pts) = w\<close>
    by auto
  from Prod.prems(1) obtain rhs where rhs: \<open>(B, rhs) \<in> set (iprods G)\<close> \<open>map fst rhs = map Parse_Tree.root ts\<close>
    by (auto simp: derel_def)
  then have len: \<open>length rhs = length ts\<close> by (auto dest: map_eq_imp_length_eq)
  have \<open>fst (rhs ! k) = Parse_Tree.root (ts ! k)\<close> if \<open>k < length ts\<close> for k
    using arg_cong[OF rhs(2), of \<open>\<lambda>l. l ! k\<close>] that len by simp
  moreover have \<open>snd Xr = Any\<close> if \<open>Xr \<in> set rhs\<close> for Xr
    using assms rhs(1) that by (auto simp: ii_def list_all_iff)
  ultimately have \<open>wf_ptree G (PNode B i pts)\<close>
    using pts(1) len by (intro wf_node[OF rhs(1)]) (auto simp: list_all2_conv_all_nth)
  then show ?case using pts(2) by (intro exI[of _ \<open>PNode B i pts\<close>]) simp
qed

theorem ilang_insensitive:
  fixes G :: \<open>('n, 'tok) is_cfg\<close>
  assumes \<open>ii G\<close>
  shows \<open>ilang G = ({w. map tok w \<in> langS (cfg_of G)})\<close>
proof (intro set_eqI iffI)
  fix w :: \<open>('m, 'ch, 'tok) tword\<close>
  assume \<open>w \<in> {w. map tok w \<in> langS (cfg_of G)}\<close>
  then have \<open>set (derel (iprods G)) \<turnstile> [Nt (istart G)] \<Rightarrow>* map Tm (map tok w)\<close>
    by (simp add: cfg_of_def Lang_def)
  from parse_tree_if_derives[OF this] obtain t where
    t: \<open>parse_tree (set (derel (iprods G))) t\<close> \<open>fringe t = map Tm (map tok w)\<close> \<open>Parse_Tree.root t = Nt (istart G)\<close>
    by blast
  from wf_ptree_if_parse_tree[OF assms t(1,2), of \<open>istart_ind G\<close>] t(3)
  obtain pt where \<open>wf_ptree G pt\<close> \<open>pyield pt = w\<close> \<open>proot pt = (Nt (istart G), istart_ind G)\<close>
    by (auto simp: prod_eq_iff)
  then show \<open>w \<in> ilang G\<close> unfolding ilang_derives derives_iff_ptree by blast
qed (simp add: ilang_langS)

corollary ilang_is_cfg_of: \<open>ilang (is_cfg_of C i) = {w. map tok w \<in> langS C}\<close>
  by (simp add: ilang_insensitive)

theorem parse_sound_lang:
  \<open>a \<in> set (parse n G w) \<Longrightarrow> w \<in> ilang G\<close>
  using parse_sound_ast ilang_iff_ast by blast

theorem parse_complete_lang:
  \<open>w \<in> ilang G \<Longrightarrow> \<exists>n a. a \<in> set (parse n G w)\<close>
  using ilang_iff_ast parse_complete_ast_ex by blast

corollary parse_decides_lang:
  \<open>(\<exists>n. parse n G w \<noteq> []) \<longleftrightarrow> w \<in> ilang G\<close>
  using parse_sound_lang parse_complete_lang
  by (metis ex_in_conv set_empty)

section \<open>The first-token desugaring (Sect. 2)\<close>

subsection \<open>Nullable symbols\<close>

text \<open>
  Definition 1 of the paper: a non-terminal is nullable if it derives
  \<^text>\<open>\<epsilon>\<close> at every indentation. Quantifying over all indentations
  lets \<^text>\<open>\<epsilon>\<close>-subtrees be rebuilt at a fresh indentation and costs
  nothing: an \<^text>\<open>\<epsilon>\<close>-tree has no leaves, so its indentation
  constraints can be re-solved at any root indentation.
\<close>

definition eps_tree :: \<open>('n, 'tok) is_cfg \<Rightarrow> ('n, 'tok) sym \<Rightarrow> nat \<Rightarrow> bool\<close> where
  \<open>eps_tree G X i \<longleftrightarrow>
     (\<exists>pt::(unit, unit, 'n, 'tok) ptree. wf_ptree G pt \<and> proot pt = (X, i) \<and> pyield pt = [])\<close>

definition nullable :: \<open>('n, 'tok) is_cfg \<Rightarrow> ('n, 'tok) sym \<Rightarrow> bool\<close> where
  \<open>nullable G X \<longleftrightarrow> (\<forall>i. eps_tree G X i)\<close>

text \<open>Every indentation relation is serial:
  \<^text>\<open>irel_wit r i\<close> is a witness related to \<^text>\<open>i\<close> by
  \<^text>\<open>r\<close>.\<close>

fun irel_wit :: \<open>irel \<Rightarrow> nat \<Rightarrow> nat\<close> where
  \<open>irel_wit Eq i = i\<close>
| \<open>irel_wit Gt i = Suc i\<close>
| \<open>irel_wit Ge i = i\<close>
| \<open>irel_wit Any i = 0\<close>

lemma irel_wit_sat[simp]: \<open>irel_sat r (irel_wit r i) i\<close>
  by (cases r) simp_all

lemma eps_tree_Tm[simp]:
  fixes G :: \<open>('n, 'tok) is_cfg\<close>
  shows \<open>\<not> eps_tree G (Tm t) i\<close>
  unfolding eps_tree_def by (auto; case_tac pt; simp)

text \<open>An \<^text>\<open>\<epsilon>\<close>-tree has no leaves, so neither its indentation nor its
  spans matter: any well-formed empty-yield parse tree can be re-rooted at
  any indentation and reparametrized to any token type.\<close>

lemma list_all2_exE:
  assumes \<open>list_all2 (\<lambda>x y. \<exists>z. P x z) xs ys\<close>
  obtains zs where \<open>list_all2 P xs zs\<close>
proof -
  from assms have \<open>\<exists>zs. list_all2 P xs zs\<close>
    by (induction rule: list_all2_induct) (blast, metis list_all2_Cons)
  with that show thesis by blast
qed

lemma list_all2_map_exE:
  assumes \<open>list_all2 (\<lambda>x y. \<exists>z. P x z \<and> f z = y) xs ys\<close>
  obtains zs where \<open>list_all2 P xs zs\<close> and \<open>map f zs = ys\<close>
proof -
  from assms have \<open>\<exists>zs. list_all2 P xs zs \<and> map f zs = ys\<close>
    by (induction rule: list_all2_induct) (fastforce simp: list_all2_Cons1)+
  with that show thesis by blast
qed

lemma eps_ptree_any:
  fixes G :: \<open>('n, 'tok) is_cfg\<close> and pt :: \<open>('m\<^sub>1, 'ch\<^sub>1, 'n, 'tok) ptree\<close>
  assumes \<open>wf_ptree G pt\<close> and \<open>pyield pt = []\<close>
  shows \<open>\<exists>pt'::('m\<^sub>2, 'ch\<^sub>2, 'n, 'tok) ptree.
           wf_ptree G pt' \<and> proot pt' = (fst (proot pt), i') \<and> pyield pt' = []\<close>
  using assms
proof (induction pt arbitrary: i' rule: wf_ptree.induct)
  case (wf_node A rhs i qs)
  from wf_node.prems have eps: \<open>pyield q = []\<close> if \<open>q \<in> set qs\<close> for q using that by auto
  from wf_node.IH have \<open>list_all2 (\<lambda>Xr q. \<exists>q'::('m\<^sub>2, 'ch\<^sub>2, 'n, 'tok) ptree.
      fst (proot q') = fst Xr \<and> irel_sat (snd Xr) (snd (proot q')) i' \<and> wf_ptree G q' \<and> pyield q' = []) rhs qs\<close>
    by (rule list.rel_mono_strong) (metis eps fst_conv snd_conv irel_wit_sat)
  then obtain qs' :: \<open>('m\<^sub>2, 'ch\<^sub>2, 'n, 'tok) ptree list\<close> where
    qs': \<open>list_all2 (\<lambda>Xr q'. fst (proot q') = fst Xr \<and> irel_sat (snd Xr) (snd (proot q')) i' \<and>
            wf_ptree G q' \<and> pyield q' = []) rhs qs'\<close>
    by (rule list_all2_exE)

  have \<open>wf_ptree G (PNode A i' qs')\<close>
    by (rule wf_ptree.wf_node[OF wf_node.hyps(1)]) (use qs' in \<open>auto simp: list_all2_conv_all_nth\<close>)
  moreover have \<open>pyield (PNode A i' qs') = []\<close>
    using qs' by (auto simp: list_all2_conv_all_nth in_set_conv_nth)
  ultimately show ?case by (intro exI[of _ \<open>PNode A i' qs'\<close>]) simp
qed simp

lemma eps_tree_any:
  fixes G :: \<open>('n, 'tok) is_cfg\<close> and pt :: \<open>(unit, unit, 'n, 'tok) ptree\<close>
  assumes \<open>wf_ptree G pt\<close> and \<open>pyield pt = []\<close>
  obtains pt' :: \<open>(unit, unit, 'n, 'tok) ptree\<close> where
    \<open>wf_ptree G pt'\<close> \<open>proot pt' = (fst (proot pt), i')\<close> \<open>pyield pt' = []\<close>
  using eps_ptree_any[OF assms, of i'] that by blast

lemma eps_ptree_reparam:
  fixes G :: \<open>('n, 'tok) is_cfg\<close> and pt :: \<open>('m\<^sub>1, 'ch\<^sub>1, 'n, 'tok) ptree\<close>
  assumes \<open>wf_ptree G pt\<close> and \<open>pyield pt = []\<close>
  shows \<open>\<exists>pt'::('m\<^sub>2, 'ch\<^sub>2, 'n, 'tok) ptree.
           wf_ptree G pt' \<and> proot pt' = proot pt \<and> pyield pt' = []\<close>
  using eps_ptree_any[OF assms, of \<open>snd (proot pt)\<close>] by simp

lemma nullable_iff_eps_tree:
  fixes G :: \<open>('n, 'tok) is_cfg\<close>
  shows \<open>nullable G X \<longleftrightarrow> (\<exists>i. eps_tree G X i)\<close>
  unfolding nullable_def eps_tree_def by (metis eps_ptree_any fst_conv)

text \<open>
  Indentation does not bear on nullability: a symbol is nullable iff it is
  nullable in the erased grammar, an \<^text>\<open>eps\<close>-subtree having no leaf whose
  column could constrain anything. So the library's \<^const>\<open>Nullable\<close> decides
  it, which makes \<^text>\<open>desugar\<close> below executable.
\<close>

lemma eps_tree_iff_derives:
  fixes G :: \<open>('n, 'tok) is_cfg\<close>
  shows \<open>eps_tree G (Nt A) i \<longleftrightarrow> infG G \<turnstile> [Nt (A, i)] \<Rightarrow>* []\<close>
  using derives_iff_ptree[of G A i \<open>[]::(unit, unit, 'tok) tword\<close>]
  by (simp add: eps_tree_def)

theorem nullable_iff_Nullable[code]:
  fixes G :: \<open>('n, 'tok) is_cfg\<close>
  shows \<open>nullable G X \<longleftrightarrow> Nullable (set (derel (iprods G))) X\<close>
proof
  assume null: \<open>nullable G X\<close>
  then obtain A where X: \<open>X = Nt A\<close> by (cases X) (auto simp: nullable_def)
  from null have \<open>infG G \<turnstile> [Nt (A, 0)] \<Rightarrow>* []\<close>
    unfolding X nullable_def eps_tree_iff_derives by blast
  from derives_unann[OF this] show \<open>Nullable (set (derel (iprods G))) X\<close>
    unfolding X by (simp add: nullable_if)
next
  assume \<open>Nullable (set (derel (iprods G))) X\<close>
  then show \<open>nullable G X\<close>
  proof (induction rule: Nullable.induct)
    case (NullableSym A w)
    then obtain rhs where A: \<open>(A, rhs) \<in> set (iprods G)\<close> and w: \<open>w = map fst rhs\<close>
      by (auto simp: derel_def)

    have \<open>eps_tree G (Nt A) i\<close> for i
    proof -
      have \<open>\<exists>q::(unit, unit, 'n, 'tok) ptree.
              wf_ptree G q \<and> proot q = (fst Xr, irel_wit (snd Xr) i) \<and> pyield q = []\<close>
        if \<open>Xr \<in> set rhs\<close> for Xr
        using NullableSym.IH that unfolding w by (fastforce simp: nullable_def eps_tree_def)
      then obtain f :: \<open>_ \<Rightarrow> (unit, unit, 'n, 'tok) ptree\<close> where
        f: \<open>\<And>Xr. Xr \<in> set rhs \<Longrightarrow>
          wf_ptree G (f Xr) \<and> proot (f Xr) = (fst Xr, irel_wit (snd Xr) i) \<and> pyield (f Xr) = []\<close>
        by metis

      have \<open>wf_ptree G (PNode A i (map f rhs))\<close>
        by (rule wf_node[OF A]) (use f in \<open>auto simp: list_all2_conv_all_nth\<close>)
      moreover have \<open>pyield (PNode A i (map f rhs)) = []\<close> using f by simp
      ultimately show ?thesis unfolding eps_tree_def by force
    qed
    then show ?case by (simp add: nullable_def)
  qed
qed

subsection \<open>The desugared grammar\<close>

text \<open>
  For every symbol \<^text>\<open>X\<close> of \<^text>\<open>G\<close> the desugared grammar has a
  non-terminal \<^text>\<open>|X|\<close> (constructor \<^text>\<open>Bar\<close>) behaving like
  \<^text>\<open>X\<close> anchored at the column of its first token, beside a copy of
  \<^text>\<open>G\<close> itself (constructor \<^text>\<open>Plain\<close>). Following Sect. 2:

    \<^item> \<^text>\<open>|t| \<rightarrow> t\<^sup>=\<close> for every terminal \<^text>\<open>t\<close>
      occurring in \<^text>\<open>G\<close>;
    \<^item> \<^text>\<open>|A| \<rightarrow> |X\<^sub>m|\<^sup>= X\<^sub>m\<^sub>+\<^sub>1\<^sup>\<Zrres>\<^sup>(\<^sup>m\<^sup>+\<^sup>1\<^sup>) \<dots> X\<^sub>n\<^sup>\<Zrres>\<^sup>n\<close>
      for every production
      \<^text>\<open>A \<rightarrow> X\<^sub>1\<^sup>\<Zrres>\<^sup>1 \<dots> X\<^sub>n\<^sup>\<Zrres>\<^sup>n\<close> and every position
      \<^text>\<open>m\<close> whose prefix \<^text>\<open>X\<^sub>1 \<dots> X\<^sub>m\<^sub>-\<^sub>1\<close> is nullable
      throughout, the prefix being dropped and the relation
      \<^text>\<open>\<Zrres>\<^sub>m\<close> replaced by \<^text>\<open>=\<close>.

  Positions are 0-based, so \<^term>\<open>take m rhs\<close> is the dropped prefix.
\<close>

datatype ('n, 'tok) bsym = Plain 'n | Bar \<open>('n, 'tok) sym\<close>

fun embed :: \<open>('n, 'tok) sym \<Rightarrow> (('n, 'tok) bsym, 'tok) sym\<close> where
  \<open>embed (Nt A) = Nt (Plain A)\<close>
| \<open>embed (Tm t) = Tm t\<close>

definition embed_rhs :: \<open>('n, 'tok) rhs \<Rightarrow> (('n, 'tok) bsym, 'tok) rhs\<close> where
  \<open>embed_rhs = map (\<lambda>(X, r). (embed X, r))\<close>

lemma length_embed_rhs[simp]: \<open>length (embed_rhs rhs) = length rhs\<close>
  by (simp add: embed_rhs_def)

lemma embed_rhs_nth:
  \<open>k < length rhs \<Longrightarrow> embed_rhs rhs ! k = (embed (fst (rhs ! k)), snd (rhs ! k))\<close>
  by (simp add: embed_rhs_def split_beta)

lemma embed_eq_Tm[simp]: \<open>embed X = Tm t \<longleftrightarrow> X = Tm t\<close>
  by (cases X) auto

lemma embed_eq_Nt_Plain[simp]: \<open>embed X = Nt (Plain A) \<longleftrightarrow> X = Nt A\<close>
  by (cases X) auto

lemma embed_neq_Bar[simp]: \<open>embed X \<noteq> Nt (Bar Y)\<close>
  by (cases X) auto

definition desugar :: \<open>('n, 'tok) is_cfg \<Rightarrow> (('n, 'tok) bsym, 'tok) is_cfg\<close> where
  \<open>desugar G = \<lparr>
     iprods =
       map (\<lambda>(A, rhs). (Plain A, embed_rhs rhs)) (iprods G) @
       concat (map (\<lambda>(A, rhs).
         map (\<lambda>m. (Bar (Nt A),
                   (Nt (Bar (fst (rhs ! m))), Eq) # embed_rhs (drop (Suc m) rhs)))
           (filter (\<lambda>m. \<forall>k<m. nullable G (fst (rhs ! k))) [0..<length rhs]))
         (iprods G)) @
       map (\<lambda>t. (Bar (Tm t), [(Tm t, Eq)])) (gram_terms G),
     istart = Plain (istart G),
     istart_ind = istart_ind G \<rparr>\<close>

lemma desugar_plainI:
  \<open>(A, rhs) \<in> set (iprods G) \<Longrightarrow>
   (Plain A, embed_rhs rhs) \<in> set (iprods (desugar G))\<close>
  unfolding desugar_def by force

lemma desugar_barI:
  \<open>(A, rhs) \<in> set (iprods G) \<Longrightarrow> m < length rhs \<Longrightarrow>
   (\<And>k. k < m \<Longrightarrow> nullable G (fst (rhs ! k))) \<Longrightarrow>
   (Bar (Nt A), (Nt (Bar (fst (rhs ! m))), Eq) # embed_rhs (drop (Suc m) rhs))
     \<in> set (iprods (desugar G))\<close>
  unfolding desugar_def by force

lemma desugar_tmI:
  \<open>t \<in> set (gram_terms G) \<Longrightarrow> (Bar (Tm t), [(Tm t, Eq)]) \<in> set (iprods (desugar G))\<close>
  unfolding desugar_def by force

lemma desugar_prodE:
  assumes \<open>(B, rhs\<^sub>B) \<in> set (iprods (desugar G))\<close>
  obtains
    (plain) A rhs where \<open>B = Plain A\<close> \<open>rhs\<^sub>B = embed_rhs rhs\<close> \<open>(A, rhs) \<in> set (iprods G)\<close>
  | (bar) A rhs m where \<open>B = Bar (Nt A)\<close>
      \<open>rhs\<^sub>B = (Nt (Bar (fst (rhs ! m))), Eq) # embed_rhs (drop (Suc m) rhs)\<close>
      \<open>(A, rhs) \<in> set (iprods G)\<close> \<open>m < length rhs\<close> \<open>\<And>k. k < m \<Longrightarrow> nullable G (fst (rhs ! k))\<close>
  | (tm) t where \<open>B = Bar (Tm t)\<close> \<open>rhs\<^sub>B = [(Tm t, Eq)]\<close> \<open>t \<in> set (gram_terms G)\<close>
  using assms unfolding desugar_def by (auto split: prod.splits)

subsection \<open>Conservativity of the \<^text>\<open>Plain\<close> copy\<close>

fun bmap :: \<open>('m, 'ch, 'n, 'tok) ptree \<Rightarrow> ('m, 'ch, ('n, 'tok) bsym, 'tok) ptree\<close> where
  \<open>bmap (PLeaf t) = PLeaf t\<close>
| \<open>bmap (PNode A i pts) = PNode (Plain A) i (map bmap pts)\<close>

lemma proot_bmap: \<open>proot (bmap pt) = (embed (fst (proot pt)), snd (proot pt))\<close>
  by (cases pt) simp_all

lemma pyield_bmap[simp]: \<open>pyield (bmap pt) = pyield pt\<close>
  by (induction pt) (auto cong: map_cong)

lemma wf_bmap:
  assumes \<open>wf_ptree G pt\<close>
  shows \<open>wf_ptree (desugar G) (bmap pt)\<close>
  using assms
proof (induction rule: wf_ptree.induct)
  case (wf_node A rhs i pts)
  have \<open>list_all2 (\<lambda>Xr pt'. fst (proot pt') = fst Xr \<and> irel_sat (snd Xr) (snd (proot pt')) i \<and>
          wf_ptree (desugar G) pt') (embed_rhs rhs) (map bmap pts)\<close>
    using wf_node.IH by (auto simp: list_all2_conv_all_nth embed_rhs_nth proot_bmap)
  with desugar_plainI[OF wf_node.hyps(1)] show ?case by (auto intro: wf_ptree.wf_node)
qed (simp add: wf_ptree.wf_leaf)

text \<open>Splitting a run of children shaped like \<^text>\<open>embed_rhs\<close> back into
  \<open>G\<close>, elementwise from a per-child inversion hypothesis \<open>P\<close>: the
  induction hypothesis of \<^text>\<open>wf_plain_inv\<close> below, and that lemma
  itself afterwards.\<close>

lemma embed_rhs_inv_gen:
  assumes \<open>list_all2 (\<lambda>Xr pt'. fst (proot pt') = fst Xr \<and>
             irel_sat (snd Xr) (snd (proot pt')) i' \<and> P pt') (embed_rhs rhs\<^sub>0) qs\<^sub>0\<close>
    and \<open>\<And>q X i. q \<in> set qs\<^sub>0 \<Longrightarrow> P q \<Longrightarrow> proot q = (embed X, i) \<Longrightarrow>
       \<exists>pt. wf_ptree G pt \<and> proot pt = (X, i) \<and> bmap pt = q\<close>
  shows \<open>\<exists>pts. list_all2 (\<lambda>Xr pt'. fst (proot pt') = fst Xr \<and>
           irel_sat (snd Xr) (snd (proot pt')) i' \<and> wf_ptree G pt') rhs\<^sub>0 pts \<and>
         map bmap pts = qs\<^sub>0\<close>
proof -
  from assms(1) have \<open>list_all2 (\<lambda>Xr q. \<exists>pt.
      (fst (proot pt) = fst Xr \<and> irel_sat (snd Xr) (snd (proot pt)) i' \<and> wf_ptree G pt) \<and> bmap pt = q)
    rhs\<^sub>0 qs\<^sub>0\<close>
    unfolding embed_rhs_def list_all2_map1
    by (rule list.rel_mono_strong) (use assms(2) in \<open>fastforce simp: prod_eq_iff\<close>)
  then obtain pts where
    \<open>list_all2 (\<lambda>Xr pt'. fst (proot pt') = fst Xr \<and> irel_sat (snd Xr) (snd (proot pt')) i' \<and> wf_ptree G pt') rhs\<^sub>0 pts\<close>
    \<open>map bmap pts = qs\<^sub>0\<close>
    by (rule list_all2_map_exE)
  thus ?thesis by blast
qed

lemma wf_plain_inv:
  assumes \<open>wf_ptree (desugar G) qt\<close> and \<open>proot qt = (embed X, i)\<close>
  shows \<open>\<exists>pt. wf_ptree G pt \<and> proot pt = (X, i) \<and> bmap pt = qt\<close>
  using assms
proof (induction arbitrary: X i rule: wf_ptree.induct)
  case (wf_leaf t)
  then show ?case by (cases X) (auto intro!: exI[of _ \<open>PLeaf t\<close>] wf_ptree.wf_leaf)
next
  case (wf_node B rhs\<^sub>B i' qs)
  from wf_node.prems obtain A where B: \<open>B = Plain A\<close> and X: \<open>X = Nt A\<close> and i: \<open>i = i'\<close>
    by (cases X) auto
  with wf_node.hyps(1) obtain rhs where A: \<open>(A, rhs) \<in> set (iprods G)\<close> and rhs\<^sub>B: \<open>rhs\<^sub>B = embed_rhs rhs\<close>
    by (elim desugar_prodE) auto

  from embed_rhs_inv_gen[OF wf_node.IH[unfolded rhs\<^sub>B]] obtain pts where
    \<open>list_all2 (\<lambda>Xr pt'. fst (proot pt') = fst Xr \<and> irel_sat (snd Xr) (snd (proot pt')) i' \<and> wf_ptree G pt') rhs pts\<close>
    \<open>map bmap pts = qs\<close>
    by blast
  with wf_ptree.wf_node[OF A] show ?case
    unfolding X i B by (intro exI[of _ \<open>PNode A i' pts\<close>]) simp
qed

corollary plain_lang_iff:
  \<open>(\<exists>qt. wf_ptree (desugar G) qt \<and> proot qt = (Nt (Plain A), i) \<and> pyield qt = w) \<longleftrightarrow>
   (\<exists>pt. wf_ptree G pt \<and> proot pt = (Nt A, i) \<and> pyield pt = w)\<close>
proof
  assume \<open>\<exists>pt. wf_ptree G pt \<and> proot pt = (Nt A, i) \<and> pyield pt = w\<close>
  thus \<open>\<exists>qt. wf_ptree (desugar G) qt \<and> proot qt = (Nt (Plain A), i) \<and> pyield qt = w\<close>
    using wf_bmap proot_bmap pyield_bmap by (metis embed.simps(1) fst_conv snd_conv)
qed (use wf_plain_inv[of G _ \<open>Nt A\<close> i] in fastforce)

subsection \<open>Anchored parse trees\<close>

text \<open>
  \<^text>\<open>anchored i pt\<close>: every node on the path from the root of
  \<^text>\<open>pt\<close> to its first token, the leftmost spine skipping
  \<^text>\<open>\<epsilon>\<close>-children, carries indentation \<^text>\<open>i\<close>; in
  particular the first token sits at column \<^text>\<open>i\<close>. This is the
  tree-level reading of the paper's \<^text>\<open>|X|\<close>: like \<^text>\<open>X\<close>, but
  with its indentation tied to that of its first token.
\<close>

inductive anchored :: \<open>nat \<Rightarrow> ('m, 'ch, 'n, 'tok) ptree \<Rightarrow> bool\<close> where
  anch_leaf: \<open>anchored (s_col (token.span t)) (PLeaf t)\<close>
| anch_node: \<open>(\<And>pt'. pt' \<in> set pts\<^sub>1 \<Longrightarrow> pyield pt' = []) \<Longrightarrow> anchored i pt \<Longrightarrow>
    anchored i (PNode A i (pts\<^sub>1 @ pt # pts\<^sub>2))\<close>

text \<open>Every \<^text>\<open>|X|\<close>-parse is nonempty, and its
  first token sits at the indentation of the \<^text>\<open>|X|\<close>-node.\<close>

theorem bar_first_token:
  assumes \<open>wf_ptree (desugar G) qt\<close> and \<open>proot qt = (Nt (Bar X), i)\<close>
  shows \<open>\<exists>t w'. pyield qt = t # w' \<and> s_col (token.span t) = i\<close>
  using assms
proof (induction arbitrary: X i rule: wf_ptree.induct)
  case (wf_node B rhs\<^sub>B i' qs)
  from wf_node.prems have B: \<open>B = Bar X\<close> and i: \<open>i = i'\<close> by auto
  from wf_node.hyps(1) show ?case
  proof (cases rule: desugar_prodE)
    case (bar A rhs m)
    from wf_node.IH[unfolded bar(2)] obtain q\<^sub>0 qs' where
      \<open>qs = q\<^sub>0 # qs'\<close> \<open>proot q\<^sub>0 = (Nt (Bar (fst (rhs ! m))), i')\<close> and
      ih\<^sub>0: \<open>\<And>X i. proot q\<^sub>0 = (Nt (Bar X), i) \<Longrightarrow> \<exists>t w'. pyield q\<^sub>0 = t # w' \<and> s_col (token.span t) = i\<close>
      by (auto simp: list_all2_Cons1 prod_eq_iff)
    with ih\<^sub>0 i show ?thesis by auto
  next
    case (tm t)
    from wf_node.IH[unfolded tm(2)] show ?thesis
      by (auto simp: list_all2_Cons1 fst_proot_Tm_iff i)
  qed (use B in simp)
qed simp

lemma embed_rhs_inv:
  assumes \<open>list_all2 (\<lambda>Xr pt'. fst (proot pt') = fst Xr \<and>
             irel_sat (snd Xr) (snd (proot pt')) i' \<and> wf_ptree (desugar G) pt')
           (embed_rhs rhs\<^sub>0) qs\<^sub>0\<close>
  shows \<open>\<exists>pts. list_all2 (\<lambda>Xr pt'. fst (proot pt') = fst Xr \<and>
           irel_sat (snd Xr) (snd (proot pt')) i' \<and> wf_ptree G pt') rhs\<^sub>0 pts \<and>
         map bmap pts = qs\<^sub>0\<close>
  by (rule embed_rhs_inv_gen[OF assms]) (rule wf_plain_inv)

text \<open>Trees with empty yield for a nullable prefix, at indentations
  compatible with the parent's.\<close>

lemma nullable_prefix_trees:
  fixes G :: \<open>('n, 'tok) is_cfg\<close> and rhs :: \<open>('n, 'tok) rhs\<close>
  assumes \<open>\<And>k. k < m \<Longrightarrow> nullable G (fst (rhs ! k))\<close> and \<open>m \<le> length rhs\<close>
  shows \<open>\<exists>ets::('m, 'ch, 'n, 'tok) ptree list.
           list_all2 (\<lambda>Xr pt'. fst (proot pt') = fst Xr \<and>
             irel_sat (snd Xr) (snd (proot pt')) i' \<and> wf_ptree G pt') (take m rhs) ets \<and>
           (\<forall>pt' \<in> set ets. pyield pt' = [])\<close>
  using assms
proof (induction m)
  case (Suc m)
  from Suc.IH Suc.prems obtain ets :: \<open>('m, 'ch, 'n, 'tok) ptree list\<close> where
    ets: \<open>list_all2 (\<lambda>Xr pt'. fst (proot pt') = fst Xr \<and>
           irel_sat (snd Xr) (snd (proot pt')) i' \<and> wf_ptree G pt') (take m rhs) ets\<close>
    \<open>\<forall>pt' \<in> set ets. pyield pt' = []\<close>
    by auto

  from Suc.prems(1) obtain et\<^sub>u :: \<open>(unit, unit, 'n, 'tok) ptree\<close> where
    \<open>wf_ptree G et\<^sub>u\<close> \<open>proot et\<^sub>u = (fst (rhs ! m), irel_wit (snd (rhs ! m)) i')\<close> \<open>pyield et\<^sub>u = []\<close>
    unfolding nullable_def eps_tree_def by blast
  with eps_ptree_reparam obtain et :: \<open>('m, 'ch, 'n, 'tok) ptree\<close> where
    et: \<open>wf_ptree G et\<close> \<open>proot et = (fst (rhs ! m), irel_wit (snd (rhs ! m)) i')\<close> \<open>pyield et = []\<close>
    by metis

  have \<open>take (Suc m) rhs = take m rhs @ [rhs ! m]\<close>
    using Suc.prems(2) by (simp add: take_Suc_conv_app_nth)
  with ets et show ?case
    by (intro exI[of _ \<open>ets @ [et]\<close>]) (auto intro!: list_all2_appendI simp: prod_eq_iff)
qed simp

text \<open>
  Completeness of the desugaring: every anchored well-formed
  \<^text>\<open>G\<close>-tree is captured by the matching \<^text>\<open>|X|\<close>
  non-terminal. A terminal root has to occur in \<^text>\<open>G\<close>, the recipe
  generating \<^text>\<open>|t| \<rightarrow> t\<^sup>=\<close> only for terminals that do.
\<close>

theorem anchored_to_bar:
  fixes pt :: \<open>('m, 'ch, 'n, 'tok) ptree\<close>
  assumes \<open>anchored i pt\<close> and \<open>wf_ptree G pt\<close>
    and \<open>\<And>t. fst (proot pt) = Tm t \<Longrightarrow> t \<in> set (gram_terms G)\<close>
  shows \<open>\<exists>qt::('m, 'ch, ('n, 'tok) bsym, 'tok) ptree.
           wf_ptree (desugar G) qt \<and> proot qt = (Nt (Bar (fst (proot pt))), i) \<and>
           pyield qt = pyield pt\<close>
  using assms
proof (induction rule: anchored.induct)
  case (anch_leaf t)
  hence \<open>wf_ptree (desugar G) (PNode (Bar (Tm (tok t))) (s_col (token.span t)) [PLeaf t])\<close>
    by (intro wf_ptree.wf_node[OF desugar_tmI]) (auto intro: wf_ptree.wf_leaf)
  thus ?case by (intro exI[of _ \<open>PNode (Bar (Tm (tok t))) (s_col (token.span t)) [PLeaf t]\<close>]) simp
next
  case (anch_node pts\<^sub>1 i pt' A pts\<^sub>2)
  from anch_node.prems(1) obtain rhs where A: \<open>(A, rhs) \<in> set (iprods G)\<close> and
    \<open>list_all2 (\<lambda>Xr pt'. fst (proot pt') = fst Xr \<and> irel_sat (snd Xr) (snd (proot pt')) i \<and> wf_ptree G pt')
      rhs (pts\<^sub>1 @ pt' # pts\<^sub>2)\<close>
    by (auto elim: wf_ptree.cases)
  then obtain rhs\<^sub>1 Xm rhs\<^sub>2 where
    rhs: \<open>rhs = rhs\<^sub>1 @ Xm # rhs\<^sub>2\<close> and len\<^sub>1: \<open>length rhs\<^sub>1 = length pts\<^sub>1\<close> and
    la\<^sub>1: \<open>list_all2 (\<lambda>Xr pt'. fst (proot pt') = fst Xr \<and> irel_sat (snd Xr) (snd (proot pt')) i \<and> wf_ptree G pt') rhs\<^sub>1 pts\<^sub>1\<close> and
    hd: \<open>fst (proot pt') = fst Xm\<close> and wft: \<open>wf_ptree G pt'\<close> and
    la\<^sub>2: \<open>list_all2 (\<lambda>Xr pt'. fst (proot pt') = fst Xr \<and> irel_sat (snd Xr) (snd (proot pt')) i \<and> wf_ptree G pt') rhs\<^sub>2 pts\<^sub>2\<close>
    by (auto simp: list_all2_append2 list_all2_Cons2)
  let ?m = \<open>length pts\<^sub>1\<close>
  have m: \<open>?m < length rhs\<close> \<open>rhs ! ?m = Xm\<close> \<open>drop (Suc ?m) rhs = rhs\<^sub>2\<close>
    by (auto simp: rhs len\<^sub>1 nth_append)

  have nullables: \<open>nullable G (fst (rhs ! k))\<close> if k: \<open>k < ?m\<close> for k
  proof -
    from la\<^sub>1 k have \<open>fst (proot (pts\<^sub>1 ! k)) = fst (rhs\<^sub>1 ! k)\<close> \<open>wf_ptree G (pts\<^sub>1 ! k)\<close>
      by (auto simp: list_all2_conv_all_nth)
    moreover from anch_node.hyps(1) k have \<open>pyield (pts\<^sub>1 ! k) = []\<close> by simp
    ultimately have \<open>eps_tree G (fst (rhs\<^sub>1 ! k)) (snd (proot (pts\<^sub>1 ! k)))\<close>
      unfolding eps_tree_def using eps_ptree_reparam by (metis prod.collapse)
    with k show ?thesis by (auto simp: rhs nth_append len\<^sub>1 nullable_iff_eps_tree)
  qed
  have tm_occ: \<open>t \<in> set (gram_terms G)\<close> if \<open>fst (proot pt') = Tm t\<close> for t
    using gram_termsI[OF A, of t \<open>snd Xm\<close>] that hd by (simp add: rhs prod_eq_iff)

  from anch_node.IH[OF wft tm_occ] obtain qt\<^sub>0 where
    qt\<^sub>0: \<open>wf_ptree (desugar G) qt\<^sub>0\<close> \<open>proot qt\<^sub>0 = (Nt (Bar (fst (proot pt'))), i)\<close> \<open>pyield qt\<^sub>0 = pyield pt'\<close>
    by blast
  have \<open>list_all2 (\<lambda>Xr pt'. fst (proot pt') = fst Xr \<and> irel_sat (snd Xr) (snd (proot pt')) i \<and>
          wf_ptree (desugar G) pt') (embed_rhs rhs\<^sub>2) (map bmap pts\<^sub>2)\<close>
    using la\<^sub>2 by (auto simp: list_all2_conv_all_nth embed_rhs_nth proot_bmap wf_bmap)
  hence \<open>wf_ptree (desugar G) (PNode (Bar (Nt A)) i (qt\<^sub>0 # map bmap pts\<^sub>2))\<close>
    by (intro wf_ptree.wf_node[OF desugar_barI[OF A m(1) nullables]]) (auto simp: m qt\<^sub>0 hd)
  moreover have \<open>concat (map pyield pts\<^sub>1) = []\<close>
    using anch_node.hyps(1) by (induction pts\<^sub>1) auto
  hence \<open>pyield (PNode (Bar (Nt A)) i (qt\<^sub>0 # map bmap pts\<^sub>2)) = pyield (PNode A i (pts\<^sub>1 @ pt' # pts\<^sub>2))\<close>
    using qt\<^sub>0(3) by (auto simp: o_def)
  ultimately show ?case
    by (intro exI[of _ \<open>PNode (Bar (Nt A)) i (qt\<^sub>0 # map bmap pts\<^sub>2)\<close>]) simp
qed

text \<open>
  Soundness of the desugaring. Since the recipe replaces the relation
  \<^text>\<open>\<Zrres>\<^sub>m\<close> at the split position by \<^text>\<open>=\<close>,
  an \<^text>\<open>|X|\<close>-parse re-enters \<^text>\<open>G\<close> only where those relations
  tolerate equal indentations. \<^text>\<open>lead_refl\<close> is that condition as a
  syntactic restriction on the grammar; it holds for the ISWIM (Fig. 2) and
  Haskell (Fig. 5) grammars of the paper, whose split positions carry
  \<^text>\<open>=\<close> or \<^text>\<open>\<ge>\<close>.
\<close>

definition refl_irel :: \<open>irel \<Rightarrow> bool\<close> where
  \<open>refl_irel r \<longleftrightarrow> (\<forall>i. irel_sat r i i)\<close>

lemma refl_irel_simps[simp]:
  \<open>refl_irel Eq\<close> \<open>refl_irel Ge\<close> \<open>refl_irel Any\<close> \<open>\<not> refl_irel Gt\<close>
  by (auto simp: refl_irel_def)

definition lead_refl :: \<open>('n, 'tok) is_cfg \<Rightarrow> bool\<close> where
  \<open>lead_refl G \<longleftrightarrow> (\<forall>(A, rhs) \<in> set (iprods G). \<forall>m < length rhs.
      (\<forall>k<m. nullable G (fst (rhs ! k))) \<longrightarrow> refl_irel (snd (rhs ! m)))\<close>

theorem bar_to_anchored:
  fixes qt :: \<open>('m, 'ch, ('n, 'tok) bsym, 'tok) ptree\<close>
  assumes lr: \<open>lead_refl G\<close>
    and \<open>wf_ptree (desugar G) qt\<close> and \<open>proot qt = (Nt (Bar X), i)\<close>
  shows \<open>\<exists>pt::('m, 'ch, 'n, 'tok) ptree. wf_ptree G pt \<and> proot pt = (X, i) \<and> anchored i pt \<and>
              pyield pt = pyield qt\<close>
  using assms(2,3)
proof (induction arbitrary: X i rule: wf_ptree.induct)
  case (wf_node B rhs\<^sub>B i' qs)
  from wf_node.prems have B: \<open>B = Bar X\<close> and i: \<open>i = i'\<close> by auto
  from wf_node.hyps(1) show ?case
  proof (cases rule: desugar_prodE)
    case (tm t)
    from wf_node.IH[unfolded tm(2)] obtain tk where
      \<open>qs = [PLeaf tk]\<close> \<open>tok tk = t\<close> and sc: \<open>s_col (token.span tk) = i'\<close>
      by (auto simp: list_all2_Cons1 fst_proot_Tm_iff)
    moreover have \<open>X = Tm t\<close> using B tm(1) wf_node.prems by auto
    moreover have \<open>anchored i (PLeaf tk)\<close> using anch_leaf[of tk] sc i by simp
    ultimately show ?thesis using i by (intro exI[of _ \<open>PLeaf tk\<close>]) (auto intro: wf_ptree.wf_leaf)
  next
    case (bar A rhs m)
    from wf_node.IH[unfolded bar(2)] obtain q\<^sub>0 qs' where
      qs: \<open>qs = q\<^sub>0 # qs'\<close> and \<open>proot q\<^sub>0 = (Nt (Bar (fst (rhs ! m))), i')\<close> and
      ih\<^sub>0: \<open>\<And>X i. proot q\<^sub>0 = (Nt (Bar X), i) \<Longrightarrow>
        \<exists>pt. wf_ptree G pt \<and> proot pt = (X, i) \<and> anchored i pt \<and> pyield pt = pyield q\<^sub>0\<close> and
      la': \<open>list_all2 (\<lambda>Xr pt'. fst (proot pt') = fst Xr \<and> irel_sat (snd Xr) (snd (proot pt')) i' \<and>
              wf_ptree (desugar G) pt' \<and>
              (\<forall>X i. proot pt' = (Nt (Bar X), i) \<longrightarrow>
                (\<exists>pt. wf_ptree G pt \<and> proot pt = (X, i) \<and> anchored i pt \<and> pyield pt = pyield pt')))
            (embed_rhs (drop (Suc m) rhs)) qs'\<close>
      by (auto simp: list_all2_Cons1 prod_eq_iff)
    from ih\<^sub>0[OF this(2)] obtain pt\<^sub>0 where
      pt\<^sub>0: \<open>wf_ptree G pt\<^sub>0\<close> \<open>proot pt\<^sub>0 = (fst (rhs ! m), i')\<close> \<open>anchored i' pt\<^sub>0\<close> \<open>pyield pt\<^sub>0 = pyield q\<^sub>0\<close>
      by blast
    from embed_rhs_inv_gen[OF la'] obtain pts\<^sub>2 where
      la\<^sub>2: \<open>list_all2 (\<lambda>Xr pt'. fst (proot pt') = fst Xr \<and> irel_sat (snd Xr) (snd (proot pt')) i' \<and> wf_ptree G pt')
              (drop (Suc m) rhs) pts\<^sub>2\<close> and
      pts\<^sub>2: \<open>map bmap pts\<^sub>2 = qs'\<close>
      by (blast intro: wf_plain_inv)
    from nullable_prefix_trees[where i' = i', OF bar(5) less_imp_le[OF bar(4)]]
    obtain ets :: \<open>('m, 'ch, 'n, 'tok) ptree list\<close> where
      la\<^sub>1: \<open>list_all2 (\<lambda>Xr pt'. fst (proot pt') = fst Xr \<and> irel_sat (snd Xr) (snd (proot pt')) i' \<and> wf_ptree G pt')
              (take m rhs) ets\<close> and
      eps: \<open>\<forall>pt' \<in> set ets. pyield pt' = []\<close>
      by blast

    have \<open>refl_irel (snd (rhs ! m))\<close> using lr bar(3,4,5) unfolding lead_refl_def by fast
    with pt\<^sub>0(1,2) have la_m:
      \<open>list_all2 (\<lambda>Xr pt'. fst (proot pt') = fst Xr \<and> irel_sat (snd Xr) (snd (proot pt')) i' \<and> wf_ptree G pt')
        [rhs ! m] [pt\<^sub>0]\<close>
      by (auto simp: refl_irel_def)
    have rhs_conv: \<open>rhs = take m rhs @ [rhs ! m] @ drop (Suc m) rhs\<close>
      using bar(4) by (simp add: id_take_nth_drop)
    have \<open>wf_ptree G (PNode A i' (ets @ pt\<^sub>0 # pts\<^sub>2))\<close>
      by (intro wf_ptree.wf_node[OF bar(3)])
         (subst rhs_conv, use la\<^sub>1 la_m la\<^sub>2 in \<open>auto intro!: list_all2_appendI\<close>)
    moreover have \<open>anchored i' (PNode A i' (ets @ pt\<^sub>0 # pts\<^sub>2))\<close>
      using eps pt\<^sub>0(3) by (auto intro: anchored.intros)
    moreover have \<open>pyield (PNode A i' (ets @ pt\<^sub>0 # pts\<^sub>2)) = pyield (PNode B i' qs)\<close>
      using eps pt\<^sub>0(4) pts\<^sub>2 qs by (auto cong: map_cong)
    ultimately show ?thesis
      using B bar(1) i by (intro exI[of _ \<open>PNode A i' (ets @ pt\<^sub>0 # pts\<^sub>2)\<close>]) simp
  qed (use B in simp)
qed simp

text \<open>Under \<^text>\<open>lead_refl\<close> the parses of \<^text>\<open>|X|\<close> at
  indentation \<^text>\<open>i\<close> are the anchored \<^text>\<open>G\<close>-parses at
  \<^text>\<open>i\<close>.\<close>

corollary bar_iff_anchored:
  assumes \<open>lead_refl G\<close>
  shows \<open>(\<exists>qt. wf_ptree (desugar G) qt \<and> proot qt = (Nt (Bar (Nt A)), i) \<and> pyield qt = w) \<longleftrightarrow>
         (\<exists>pt. wf_ptree G pt \<and> proot pt = (Nt A, i) \<and> anchored i pt \<and> pyield pt = w)\<close>
proof
  assume \<open>\<exists>qt. wf_ptree (desugar G) qt \<and> proot qt = (Nt (Bar (Nt A)), i) \<and> pyield qt = w\<close>
  thus \<open>\<exists>pt. wf_ptree G pt \<and> proot pt = (Nt A, i) \<and> anchored i pt \<and> pyield pt = w\<close>
    using bar_to_anchored[OF assms] by blast
qed (use anchored_to_bar in fastforce)

section \<open>LR(k) and GLR parsing (Sect. 5)\<close>

text \<open>
  Sect. 5 of the paper derives GLR and LR(k) parsers in layers, and this section
  follows them: properties of the indentation relations (Sect. 5.1, Lemmas 2 and
  3), rightmost derivations and handles (Sect. 5.3), items, lookaheads and the
  LR(k) stack machine of Algorithm 8 (Sect. 5.4), item-set completeness
  (Definition 9, Lemma 10), the factored item sets of Sect. 5.5 together with
  their commutation theorems and a lockstep bisimulation with Algorithm 8, the
  finite representation of indentation sets (Sect. 5.5, 5.6), and the LR(k)
  condition with uniqueness of handles (Sect. 5.6).

  Two results the paper does not prove are proved here: that Algorithm 8
  accepts the language, for every lookahead length, which the paper cites to
  Knuth, and that the GLR machine at the end of Sect. 5.5 can be run as an
  executable, certificate-checking machine that is sound and complete.  The
  executable machine has no lookahead (\<open>k = 0\<close>); the closing text of this
  section says where the parser's lookahead comes from instead.
\<close>

subsection \<open>Composition and closure of indentation relations (Lemmas 2 and 3)\<close>

text \<open>
  \<^text>\<open>path_rel rs k i\<close> composes the edge relations along a path from an
  ancestor at indentation \<^text>\<open>i\<close> down to a descendant at
  \<^text>\<open>k\<close>, topmost edge first. Lemma 2: every such composition falls
  into one of six classes, represented by \<^text>\<open>cirel\<close>.
  \<^text>\<open>CGt n\<close> is \<^text>\<open>>\<^sup>n\<close>, i.e.
  \<^text>\<open>k \<ge> i + n\<close>; \<^text>\<open>CGtAny n\<close> is
  \<^text>\<open>>\<^sup>n\<star>\<close>, i.e. \<^text>\<open>k \<ge> n\<close> with the ancestor
  unconstrained; and \<^text>\<open>CAny\<close> covers \<^text>\<open>\<star>\<close> as well as
  \<^text>\<open>\<ge>\<star>\<close>, which agree over \<^text>\<open>\<nat>\<close>.
\<close>

fun path_rel :: \<open>irel list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool\<close> where
  \<open>path_rel [] k i \<longleftrightarrow> k = i\<close>
| \<open>path_rel (r # rs) k i \<longleftrightarrow> (\<exists>j. path_rel rs k j \<and> irel_sat r j i)\<close>

datatype cirel = CEq | CGe | CGt nat | CAny | CGtAny nat

fun csat :: \<open>cirel \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool\<close> where
  \<open>csat CEq k i \<longleftrightarrow> k = i\<close>
| \<open>csat CGe k i \<longleftrightarrow> k \<ge> i\<close>
| \<open>csat (CGt n) k i \<longleftrightarrow> k \<ge> i + n\<close>
| \<open>csat CAny k i \<longleftrightarrow> True\<close>
| \<open>csat (CGtAny n) k i \<longleftrightarrow> k \<ge> n\<close>

fun cirel_of :: \<open>irel \<Rightarrow> cirel\<close> where
  \<open>cirel_of Eq = CEq\<close>
| \<open>cirel_of Gt = CGt 1\<close>
| \<open>cirel_of Ge = CGe\<close>
| \<open>cirel_of Any = CAny\<close>

lemma csat_cirel_of[simp]: \<open>csat (cirel_of r) k i \<longleftrightarrow> irel_sat r k i\<close>
  by (cases r) auto

text \<open>Composition of classes, the first argument being the relation
  nearer the root.\<close>

fun ccomp :: \<open>cirel \<Rightarrow> cirel \<Rightarrow> cirel\<close> where
  \<open>ccomp CEq d = d\<close>
| \<open>ccomp c CEq = c\<close>
| \<open>ccomp c CAny = CAny\<close>
| \<open>ccomp c (CGtAny n) = CGtAny n\<close>
| \<open>ccomp CGe CGe = CGe\<close>
| \<open>ccomp CGe (CGt n) = CGt n\<close>
| \<open>ccomp (CGt n) CGe = CGt n\<close>
| \<open>ccomp (CGt n) (CGt m) = CGt (n + m)\<close>
| \<open>ccomp CAny CGe = CAny\<close>
| \<open>ccomp CAny (CGt n) = CGtAny n\<close>
| \<open>ccomp (CGtAny n) CGe = CGtAny n\<close>
| \<open>ccomp (CGtAny n) (CGt m) = CGtAny (n + m)\<close>

lemma csat_ccomp: \<open>csat (ccomp c d) k i \<longleftrightarrow> (\<exists>j. csat d k j \<and> csat c j i)\<close>
  by (cases c; cases d; auto; presburger)

text \<open>Lemma 2: composing along a path stays within the six classes.\<close>

fun cpath :: \<open>irel list \<Rightarrow> cirel\<close> where
  \<open>cpath [] = CEq\<close>
| \<open>cpath (r # rs) = ccomp (cirel_of r) (cpath rs)\<close>

theorem path_rel_cpath: \<open>path_rel rs k i \<longleftrightarrow> csat (cpath rs) k i\<close>
  by (induction rs arbitrary: i) (auto simp: csat_ccomp)

text \<open>
  Lemma 3: closing the relations under composition and arbitrary unions needs
  only finitely many classes, at most one of each kind, because
  \<^text>\<open>>\<^sup>n\<close> subsumes \<^text>\<open>>\<^sup>m\<close> for
  \<^text>\<open>n \<le> m\<close>, and likewise with \<^text>\<open>\<star>\<close>. This makes the
  indentation sets of Sect. 5.5 and 5.6 finitely representable.
\<close>

theorem cirel_union_finite:
  fixes S :: \<open>cirel set\<close>
  shows \<open>\<exists>C \<subseteq> S. finite C \<and> card C \<le> 5 \<and>
         (\<forall>k i. (\<exists>c \<in> S. csat c k i) \<longleftrightarrow> (\<exists>c \<in> C. csat c k i))\<close>
proof -
  define CGT where \<open>CGT = (if \<exists>n. CGt n \<in> S then {CGt (LEAST n. CGt n \<in> S)} else {})\<close>
  define CGA where \<open>CGA = (if \<exists>n. CGtAny n \<in> S then {CGtAny (LEAST n. CGtAny n \<in> S)} else {})\<close>
  define C where \<open>C = (S \<inter> {CEq}) \<union> (S \<inter> {CGe}) \<union> (S \<inter> {CAny}) \<union> CGT \<union> CGA\<close>

  have \<open>C \<subseteq> S\<close> unfolding C_def CGT_def CGA_def by (auto intro: LeastI split: if_splits)
  moreover have \<open>finite C\<close> unfolding C_def CGT_def CGA_def by auto
  moreover have \<open>card C \<le> 5\<close>
  proof -
    have \<open>C \<subseteq> {CEq, CGe, CAny} \<union> CGT \<union> CGA\<close> unfolding C_def by auto
    hence \<open>card C \<le> card ({CEq, CGe, CAny} \<union> CGT \<union> CGA)\<close>
      by (intro card_mono) (auto simp: CGT_def CGA_def)
    also have \<open>\<dots> \<le> 5\<close> unfolding CGT_def CGA_def by (auto simp: card_insert_if split: if_splits)
    finally show ?thesis .
  qed
  moreover have \<open>(\<exists>c \<in> S. csat c k i) \<longleftrightarrow> (\<exists>c \<in> C. csat c k i)\<close> for k i
  proof
    assume \<open>\<exists>c \<in> S. csat c k i\<close>
    then obtain c where cS: \<open>c \<in> S\<close> and sat: \<open>csat c k i\<close> by blast
    show \<open>\<exists>c \<in> C. csat c k i\<close>
    proof (cases c)
      case (CGt n)
      with cS have \<open>(LEAST n. CGt n \<in> S) \<le> n\<close> by (intro Least_le) blast
      with cS sat CGt show ?thesis unfolding C_def CGT_def by force
    next
      case (CGtAny n)
      with cS have \<open>(LEAST n. CGtAny n \<in> S) \<le> n\<close> by (intro Least_le) blast
      with cS sat CGtAny show ?thesis unfolding C_def CGA_def by force
    qed (use cS sat in \<open>auto simp: C_def\<close>)
  qed (use \<open>C \<subseteq> S\<close> in blast)
  ultimately show ?thesis by blast
qed

subsection \<open>Rightmost derivations and handles (Sect. 5.3)\<close>

text \<open>
  LR(k) parsing runs a rightmost derivation backwards: each step expands the
  rightmost non-terminal, so everything right of the rewritten occurrence is
  terminal. That relation is \<^const>\<open>deriver\<close>, again over a production set,
  so it applies to the infinite II-CFG of Sect. 5.2, and
  \<^text>\<open>derivers_iff_derives\<close> is the classical result that every derivation
  of a terminal word can be reordered into a rightmost one.
\<close>

corollary ilang_derivers:
  \<open>w \<in> ilang G \<longleftrightarrow>
   infG G \<turnstile> [Nt (istart G, istart_ind G)] \<Rightarrow>r* map Tm (tcols w)\<close>
  by (simp add: ilang_derives derivers_iff_derives)

text \<open>
  Handles (Sect. 5.3): if
  \<^text>\<open>S \<Rightarrow>\<^sup>*\<^sub>r\<^sub>m U (Nt A) V \<Rightarrow>\<^sub>r\<^sub>m U rhs V\<close>, the occurrence of
  \<^text>\<open>rhs\<close> at position \<^text>\<open>|U|\<close> is a handle of
  \<^text>\<open>U rhs V\<close>. LR parsing searches for a handle and reduces it, so
  Algorithm 7 of the paper is the reflexive-transitive closure of reversed
  rightmost steps.

  A tail is terminal iff it has no non-terminals, which
  \<^const>\<open>Nts_syms\<close> expresses and \<^text>\<open>Nts_syms_empty_iff\<close> converts to the
  \<^term>\<open>map Tm\<close> form \<^const>\<open>deriver\<close> is stated in.
\<close>

definition handle :: \<open>('nn, 'tt) Prods \<Rightarrow> 'nn \<Rightarrow>
    ('nn, 'tt) syms \<Rightarrow> ('nn, 'tt) prod \<Rightarrow> nat \<Rightarrow> bool\<close> where
  \<open>handle P St w pr pos \<longleftrightarrow>
     (\<exists>U V. w = U @ snd pr @ V \<and> length U = pos \<and> Nts_syms V = {} \<and> pr \<in> P \<and>
            P \<turnstile> [Nt St] \<Rightarrow>r* U @ Nt (fst pr) # V)\<close>

lemma handle_reduce:
  assumes \<open>handle P St w (A, rhs) pos\<close>
  shows \<open>P \<turnstile> take pos w @ Nt A # drop (pos + length rhs) w \<Rightarrow>r w\<close>
    and \<open>P \<turnstile> [Nt St] \<Rightarrow>r* take pos w @ Nt A # drop (pos + length rhs) w\<close>
proof -
  from assms obtain U V where w: \<open>w = U @ rhs @ V\<close> and \<open>length U = pos\<close> and
    V: \<open>Nts_syms V = {}\<close> \<open>(A, rhs) \<in> P\<close> \<open>P \<turnstile> [Nt St] \<Rightarrow>r* U @ Nt A # V\<close>
    unfolding handle_def by auto
  hence UV: \<open>take pos w = U\<close> \<open>drop (pos + length rhs) w = V\<close> by simp_all
  from V(3) show \<open>P \<turnstile> [Nt St] \<Rightarrow>r* take pos w @ Nt A # drop (pos + length rhs) w\<close> unfolding UV .
  from V(1,2) have \<open>P \<turnstile> U @ Nt A # V \<Rightarrow>r w\<close>
    unfolding w by (auto simp: Nts_syms_empty_iff intro: deriver.intros)
  thus \<open>P \<turnstile> take pos w @ Nt A # drop (pos + length rhs) w \<Rightarrow>r w\<close> unfolding UV .
qed

theorem algorithm7:
  \<open>((deriver P)\<inverse>\<inverse>)\<^sup>*\<^sup>* w [Nt St] \<longleftrightarrow> P \<turnstile> [Nt St] \<Rightarrow>r* w\<close>
  by (simp add: rtranclp_conversep)


subsection \<open>Items and the LR(k) stack machine (Sect. 5.4, Algorithm 8)\<close>

text \<open>
  An item \<^text>\<open>[A \<rightarrow> X\<^sub>1\<dots>X\<^sub>m . X\<^sub>m\<^sub>+\<^sub>1\<dots>X\<^sub>n; u]\<close> is a production, a
  dot position, and a lookahead word \<^text>\<open>u\<close> of length
  \<^text>\<open>k\<close>. As in the paper the machine is defined over an arbitrary
  production set, so it applies verbatim to \<^term>\<open>infG G\<close>.
  \<^text>\<open>Hk P k W\<close> is the paper's \<^text>\<open>Hk(W)\<close>: the
  length-\<^text>\<open>k\<close> terminal prefixes derivable from \<^text>\<open>W\<close>.

  Stacks grow to the left, so the head is the paper's \<^text>\<open>S\<^sub>n\<close>.
  Stack entries are kernel item sets, and the closure is taken whenever an
  entry is consulted, as in step 1 of Algorithm 8.
\<close>

type_synonym ('nn, 'tt) item = \<open>('nn, 'tt) prod \<times> nat \<times> 'tt list\<close>

definition Hk :: \<open>('nn, 'tt) Prods \<Rightarrow> nat \<Rightarrow>
    ('nn, 'tt) syms \<Rightarrow> 'tt list set\<close> where
  \<open>Hk P k W = {u. length u = k \<and> (\<exists>V. P \<turnstile> W \<Rightarrow>* map Tm u @ V)}\<close>

lemma HkI: \<open>length u = k \<Longrightarrow> P \<turnstile> W \<Rightarrow>* map Tm u @ V \<Longrightarrow> u \<in> Hk P k W\<close>
  unfolding Hk_def by blast

lemma Hk_zero[simp]: \<open>Hk P 0 W = {[]}\<close>
  unfolding Hk_def by auto

text \<open>
  The length-\<^text>\<open>k\<close> prefix of an input continuation is an acceptable
  lookahead for any item whose remaining right-hand side derives the next part
  of that continuation. Only the first \<^text>\<open>k\<close> symbols of the tail
  matter, the classical FIRST-set truncation. The completeness proof below
  rests on this lemma.
\<close>

lemma take_append_take: \<open>take k (ys @ take k zs) = take k (ys @ zs)\<close>
  by simp

lemma Hk_take_appendI:
  assumes \<open>P \<turnstile> X \<Rightarrow>* map Tm ys\<close> and \<open>k \<le> length zs\<close>
  shows \<open>take k (ys @ zs) \<in> Hk P k (X @ map Tm (take k zs))\<close>
proof (rule HkI)
  have eq: \<open>map Tm (take k (ys @ zs)) @ drop k (map Tm (ys @ take k zs)) = map Tm (ys @ take k zs)\<close>
    by (metis append_take_drop_id take_append_take take_map)
  show \<open>P \<turnstile> X @ map Tm (take k zs) \<Rightarrow>* map Tm (take k (ys @ zs)) @ drop k (map Tm (ys @ take k zs))\<close>
    unfolding eq using derives_append[OF assms(1), of \<open>map Tm (take k zs)\<close>] by simp
qed (use assms(2) in simp)

inductive_set iclosure :: \<open>('nn, 'tt) Prods \<Rightarrow> nat \<Rightarrow>
    ('nn, 'tt) item set \<Rightarrow> ('nn, 'tt) item set\<close>
  for P :: \<open>('nn, 'tt) Prods\<close> and k :: nat
    and S :: \<open>('nn, 'tt) item set\<close>
  where
    iclosure_base: \<open>it \<in> S \<Longrightarrow> it \<in> iclosure P k S\<close>
  | iclosure_step: \<open>((A, rhs), m, u) \<in> iclosure P k S \<Longrightarrow> m < length rhs \<Longrightarrow>
      rhs ! m = Nt B \<Longrightarrow> (B, rhs\<^sub>B) \<in> P \<Longrightarrow>
      v \<in> Hk P k (drop (Suc m) rhs @ map Tm u) \<Longrightarrow>
      ((B, rhs\<^sub>B), 0, v) \<in> iclosure P k S\<close>

definition igoto :: \<open>('nn, 'tt) item set \<Rightarrow> ('nn, 'tt) sym \<Rightarrow> ('nn, 'tt) item set\<close> where
  \<open>igoto S Z = {((A, rhs), Suc m, u) | A rhs m u.
     ((A, rhs), m, u) \<in> S \<and> m < length rhs \<and> rhs ! m = Z}\<close>

text \<open>
  The acceptable-lookahead sets of steps 2 and 3 of Algorithm 8:
  \<^text>\<open>Kset\<close> is the paper's \<^text>\<open>K\<close>, where any item may
  continue, and \<^text>\<open>Kprod\<close> the per-production reduce set given by the
  completed items.
\<close>

definition Kset :: \<open>('nn, 'tt) Prods \<Rightarrow> nat \<Rightarrow>
    ('nn, 'tt) item set \<Rightarrow> 'tt list set\<close> where
  \<open>Kset P k S = {v. \<exists>A rhs m u. ((A, rhs), m, u) \<in> S \<and>
                     v \<in> Hk P k (drop m rhs @ map Tm u)}\<close>

definition Kprod :: \<open>('nn, 'tt) item set \<Rightarrow> ('nn, 'tt) prod \<Rightarrow> 'tt list set\<close> where
  \<open>Kprod S pr = {u. (pr, length (snd pr), u) \<in> S}\<close>

lemma Kprod_iff: \<open>u \<in> Kprod S (A, rhs) \<longleftrightarrow> ((A, rhs), length rhs, u) \<in> S\<close>
  unfolding Kprod_def by simp

text \<open>
  Algorithm 8. A configuration is a stack of kernel item sets together with the
  remaining input, whose first \<^text>\<open>k\<close> symbols form the lookahead. A
  shift pushes \<^text>\<open>GOTO(S', t)\<close>; a reduce for
  \<^text>\<open>A \<rightarrow> rhs\<close> pops \<^text>\<open>|rhs|\<close> entries and pushes
  \<^text>\<open>GOTO(closure(S\<^sub>n\<^sub>-\<^sub>m), A)\<close>.
\<close>

type_synonym ('nn, 'tt) lr_config = \<open>('nn, 'tt) item set list \<times> 'tt list\<close>

inductive lr_step :: \<open>('nn, 'tt) Prods \<Rightarrow> nat \<Rightarrow>
    ('nn, 'tt) lr_config \<Rightarrow> ('nn, 'tt) lr_config \<Rightarrow> bool\<close> for P k where
  lr_shift: \<open>Ss \<noteq> [] \<Longrightarrow> take k (t # w) \<in> Kset P k (iclosure P k (hd Ss)) \<Longrightarrow>
     lr_step P k (Ss, t # w) (igoto (iclosure P k (hd Ss)) (Tm t) # Ss, w)\<close>
| lr_reduce: \<open>Ss \<noteq> [] \<Longrightarrow> take k w \<in> Kprod (iclosure P k (hd Ss)) (A, rhs) \<Longrightarrow>
     length rhs < length Ss \<Longrightarrow>
     lr_step P k (Ss, w) (igoto (iclosure P k (Ss ! length rhs)) (Nt A) # drop (length rhs) Ss, w)\<close>

text \<open>
  Initial configuration and acceptance, with a fresh start symbol
  \<^text>\<open>Sh\<close> and an end marker \<^text>\<open>dm\<close> (the paper's
  \<^text>\<open>\<stileturn>\<close>); the input is padded with \<^text>\<open>k\<close> end
  markers.
\<close>

definition init_item :: \<open>'nn \<Rightarrow> 'nn \<Rightarrow> 'tt \<Rightarrow> nat \<Rightarrow> ('nn, 'tt) item\<close> where
  \<open>init_item Sh St dm k = ((Sh, [Nt St]), 0, replicate k dm)\<close>

definition lr_accepts :: \<open>('nn, 'tt) Prods \<Rightarrow> nat \<Rightarrow>
    'nn \<Rightarrow> 'nn \<Rightarrow> 'tt \<Rightarrow> 'tt list \<Rightarrow> bool\<close> where
  \<open>lr_accepts P k Sh St dm w \<longleftrightarrow>
     (\<exists>Ss u. (lr_step P k)\<^sup>*\<^sup>* ([{init_item Sh St dm k}], w @ replicate k dm)
                              (Ss, replicate k dm) \<and>
             Ss \<noteq> [] \<and> ((Sh, [Nt St]), Suc 0, u) \<in> hd Ss)\<close>


subsection \<open>Annotated right-hand sides\<close>

text \<open>
  \<^text>\<open>annotates i rhs arhs\<close>: the annotated symbol list
  \<^text>\<open>arhs\<close> is an instance of the right-hand side \<^text>\<open>rhs\<close>
  for left-hand-side indentation \<^text>\<open>i\<close>, every symbol carrying an
  indentation that satisfies its relation. The productions of
  \<^term>\<open>infG G\<close> are the annotated instances of the original productions.
\<close>

definition annotates :: \<open>nat \<Rightarrow> ('n, 'tok) rhs \<Rightarrow> ('n \<times> nat, 'tok \<times> nat) syms \<Rightarrow> bool\<close> where
  \<open>annotates i rhs arhs \<longleftrightarrow>
     list_all2 (\<lambda>(X, r) Y. \<exists>j. Y = annsym (X, j) \<and> irel_sat r j i) rhs arhs\<close>

lemma annotates_Nil[simp]: \<open>annotates i [] arhs \<longleftrightarrow> arhs = []\<close>
  unfolding annotates_def by auto

lemma annotates_Cons[simp]:
  \<open>annotates i ((X, r) # rest) (Y # arest) \<longleftrightarrow>
   (\<exists>j. Y = annsym (X, j) \<and> irel_sat r j i) \<and> annotates i rest arest\<close>
  unfolding annotates_def by auto

lemma annotates_length: \<open>annotates i rhs arhs \<Longrightarrow> length arhs = length rhs\<close>
  unfolding annotates_def by (auto dest: list_all2_lengthD)

lemma annotates_unann: \<open>annotates i rhs arhs \<Longrightarrow> map unann arhs = map fst rhs\<close>
  unfolding annotates_def
  by (auto simp: list_all2_conv_all_nth case_prod_beta intro!: nth_equalityI)

lemma annotates_take: \<open>annotates i rhs arhs \<Longrightarrow> annotates i (take m rhs) (take m arhs)\<close>
  unfolding annotates_def by (rule list_all2_takeI)

lemma annotates_drop: \<open>annotates i rhs arhs \<Longrightarrow> annotates i (drop m rhs) (drop m arhs)\<close>
  unfolding annotates_def by (rule list_all2_dropI)

lemma annotates_appendI:
  \<open>annotates i r\<^sub>1 a\<^sub>1 \<Longrightarrow> annotates i r\<^sub>2 a\<^sub>2 \<Longrightarrow> annotates i (r\<^sub>1 @ r\<^sub>2) (a\<^sub>1 @ a\<^sub>2)\<close>
  unfolding annotates_def by (rule list_all2_appendI)
lemma annotates_nthD:
  assumes \<open>annotates i rhs arhs\<close> and \<open>p < length rhs\<close>
  shows \<open>\<exists>j. arhs ! p = annsym (fst (rhs ! p), j) \<and> irel_sat (snd (rhs ! p)) j i\<close>
  using list_all2_nthD[OF assms[unfolded annotates_def]]
  by (auto split: prod.splits)

lemma annotates_wit: \<open>annotates i rhs (map (\<lambda>(X, r). annsym (X, irel_wit r i)) rhs)\<close>
  unfolding annotates_def by (induction rhs) auto

lemma annotates_ex: \<open>\<exists>arhs. annotates i rhs arhs\<close>
  using annotates_wit by blast

lemma annotates_iff_map:
  \<open>annotates i rhs arhs \<longleftrightarrow> (\<exists>rhs'. arhs = map annsym rhs' \<and>
     list_all2 (\<lambda>(X, r) (Y, j). Y = X \<and> irel_sat r j i) rhs rhs')\<close>
    (is \<open>?L \<longleftrightarrow> ?R\<close>)
proof
  assume ?L
  hence \<open>list_all2 (\<lambda>Xr Y. \<exists>Yj. (\<lambda>(X, r) (Y, j). Y = X \<and> irel_sat r j i) Xr Yj \<and> annsym Yj = Y) rhs arhs\<close>
    unfolding annotates_def by (rule list_all2_mono) (auto split: prod.splits)
  from list_all2_map_exE[OF this] show ?R by blast
next
  assume ?R
  then obtain rhs' where \<open>arhs = map annsym rhs'\<close> \<open>list_all2 (\<lambda>(X, r) (Y, j). Y = X \<and> irel_sat r j i) rhs rhs'\<close>
    by blast
  from this(2) show ?L
    unfolding annotates_def \<open>arhs = _\<close> list_all2_map2 by (rule list_all2_mono) (auto split: prod.splits)
qed

lemma infG_alt:
  \<open>((A, i), arhs) \<in> infG G \<longleftrightarrow> (\<exists>rhs. (A, rhs) \<in> set (iprods G) \<and> annotates i rhs arhs)\<close>
  by (auto simp: infG_def annotates_iff_map)


subsection \<open>Item-set completeness (Definition 9) and Lemma 10\<close>

text \<open>
  Definition 9 of the paper: an item set over \<^term>\<open>infG G\<close> is
  \<^emph>\<open>complete\<close> if, for every item whose right-hand side is an annotated
  instance of an original production, every re-annotation of the part after the
  dot is present too, with the same lookahead and the same pre-dot part. Lemma
  10 states that closure and GOTO, hence every step of Algorithm 8, preserve
  completeness of all stack entries. This licenses factoring the post-dot
  indentations out of the representation.
\<close>

definition iset_complete :: \<open>('n, 'tok) is_cfg \<Rightarrow> ('n \<times> nat, 'tok \<times> nat) item set \<Rightarrow> bool\<close> where
  \<open>iset_complete G S \<longleftrightarrow> (\<forall>A i rhs pre post post' u.
     (A, rhs) \<in> set (iprods G) \<longrightarrow>
     annotates i (take (length pre) rhs) pre \<longrightarrow>
     annotates i (drop (length pre) rhs) post \<longrightarrow>
     annotates i (drop (length pre) rhs) post' \<longrightarrow>
     (((A, i), pre @ post), length pre, u) \<in> S \<longrightarrow>
     (((A, i), pre @ post'), length pre, u) \<in> S)\<close>

lemma iset_completeD:
  assumes \<open>iset_complete G S\<close> and \<open>(A, rhs) \<in> set (iprods G)\<close>
    and \<open>m = length pre\<close>
    and \<open>annotates i (take m rhs) pre\<close>
    and \<open>annotates i (drop m rhs) post\<close> and \<open>annotates i (drop m rhs) post'\<close>
    and \<open>(((A, i), pre @ post), m, u) \<in> S\<close>
  shows \<open>(((A, i), pre @ post'), m, u) \<in> S\<close>
  using assms unfolding iset_complete_def by blast

lemma iclosure_complete:
  assumes \<open>iset_complete G S\<close>
  shows \<open>iset_complete G (iclosure (infG G) k S)\<close>
  unfolding iset_complete_def
proof (intro allI impI)
  fix A i rhs pre post post' u
  assume A: \<open>(A, rhs) \<in> set (iprods G)\<close>
    and ann: \<open>annotates i (take (length pre) rhs) pre\<close> \<open>annotates i (drop (length pre) rhs) post\<close>
      \<open>annotates i (drop (length pre) rhs) post'\<close>
    and mem: \<open>(((A, i), pre @ post), length pre, u) \<in> iclosure (infG G) k S\<close>
  from mem show \<open>(((A, i), pre @ post'), length pre, u) \<in> iclosure (infG G) k S\<close>
  proof (cases rule: iclosure.cases)
    case iclosure_base
    from iset_completeD[OF assms A refl ann this] show ?thesis by (rule iclosure.iclosure_base)
  next
    case (iclosure_step A\<^sub>2 rhs\<^sub>2 m\<^sub>2 u\<^sub>2)
    hence \<open>pre = []\<close> by simp
    with A ann(3) have \<open>((A, i), post') \<in> infG G\<close> by (auto simp: infG_alt)
    with iclosure_step \<open>pre = []\<close> show ?thesis by (auto intro: iclosure.iclosure_step)
  qed
qed

lemma igoto_complete:
  assumes \<open>iset_complete G S\<close>
  shows \<open>iset_complete G (igoto S Z)\<close>
  unfolding iset_complete_def
proof (intro allI impI)
  fix A i rhs pre post post' u
  assume A: \<open>(A, rhs) \<in> set (iprods G)\<close>
    and apre: \<open>annotates i (take (length pre) rhs) pre\<close>
    and apost: \<open>annotates i (drop (length pre) rhs) post\<close> \<open>annotates i (drop (length pre) rhs) post'\<close>
    and \<open>(((A, i), pre @ post), length pre, u) \<in> igoto S Z\<close>
  then obtain m where m: \<open>length pre = Suc m\<close> and src: \<open>(((A, i), pre @ post), m, u) \<in> S\<close>
    and Z: \<open>pre ! m = Z\<close>
    unfolding igoto_def by (auto simp: nth_append)
  then obtain pre\<^sub>0 where pre: \<open>pre = pre\<^sub>0 @ [Z]\<close> and len\<^sub>0: \<open>length pre\<^sub>0 = m\<close>
    by (cases pre rule: rev_cases) (auto simp: nth_append)
  have mrhs: \<open>m < length rhs\<close> using annotates_length[OF apre] m by simp

  from annotates_nthD[OF apre, of m] Z obtain j where
    \<open>Z = annsym (fst (rhs ! m), j)\<close> \<open>irel_sat (snd (rhs ! m)) j i\<close>
    by (auto simp: m mrhs)
  with apost have \<open>annotates i (drop m rhs) (Z # post)\<close> \<open>annotates i (drop m rhs) (Z # post')\<close>
    by (cases \<open>rhs ! m\<close>; auto simp: m Cons_nth_drop_Suc[OF mrhs, symmetric])+
  moreover have \<open>annotates i (take m rhs) pre\<^sub>0\<close>
    using annotates_take[OF apre, of m] by (auto simp: pre len\<^sub>0 min_def)
  ultimately have \<open>(((A, i), pre\<^sub>0 @ Z # post'), m, u) \<in> S\<close>
    by (rule iset_completeD[OF assms A len\<^sub>0[symmetric] _ _ _ src[unfolded pre, simplified], rotated])
  thus \<open>(((A, i), pre @ post'), length pre, u) \<in> igoto S Z\<close>
    unfolding igoto_def pre by (auto simp: len\<^sub>0 nth_append)
qed

text \<open>Lemma 10: every step of Algorithm 8 preserves completeness of
  the stack.\<close>

theorem lemma10:
  assumes \<open>lr_step (infG G) k (Ss, w) (Ss', w')\<close>
    and \<open>\<And>S. S \<in> set Ss \<Longrightarrow> iset_complete G S\<close>
    and \<open>S' \<in> set Ss'\<close>
  shows \<open>iset_complete G S'\<close>
  using assms(1)
proof (cases rule: lr_step.cases)
  case (lr_shift t)
  have \<open>iset_complete G (igoto (iclosure (infG G) k (hd Ss)) (Tm t))\<close>
    by (intro igoto_complete iclosure_complete assms(2) hd_in_set lr_shift(3))
  with assms(2,3) lr_shift(2) show ?thesis by auto
next
  case (lr_reduce A rhs)
  from lr_reduce(5) have \<open>iset_complete G (igoto (iclosure (infG G) k (Ss ! length rhs)) (Nt A))\<close>
    by (intro igoto_complete iclosure_complete assms(2) nth_mem)
  with assms(2,3) lr_reduce(1) show ?thesis by (auto dest: in_set_dropD)
qed

lemma init_complete:
  assumes \<open>fst Sh \<notin> fst ` set (iprods G)\<close>
  shows \<open>iset_complete G {init_item Sh St dm k}\<close>
  using assms unfolding iset_complete_def init_item_def
  by (fastforce simp: rev_image_eqI)

corollary lr_run_complete:
  assumes \<open>(lr_step (infG G) k)\<^sup>*\<^sup>* ([{init_item Sh St dm k}], w\<^sub>0) (Ss, w)\<close>
    and \<open>fst Sh \<notin> fst ` set (iprods G)\<close>
    and \<open>S \<in> set Ss\<close>
  shows \<open>iset_complete G S\<close>
  using assms(1,3)
proof (induction arbitrary: S rule: rtranclp_induct2)
  case refl
  thus ?case using init_complete[OF assms(2)] by simp
qed (blast intro: lemma10)


subsection \<open>Item cores: pre-dot indentations are irrelevant\<close>

text \<open>
  Sect. 5.5 observes that the indentations left of the dot do not affect parsing.
  The \<^emph>\<open>core\<close> of an item makes that precise: it keeps the annotated
  left-hand side, the lookahead, the dot and the annotated post-dot part, and
  strips the annotations of the pre-dot part. All machine operations are
  congruences for core-equivalence \<^text>\<open>\<approx>\<close> of item sets; the reduce
  action, popping \<^text>\<open>|rhs|\<close> entries, needs a well-formed dot on top of
  that.
\<close>

fun icore :: \<open>('n \<times> nat, 'tok \<times> nat) item \<Rightarrow>
    ('n \<times> nat) \<times> ('n, 'tok) syms \<times> ('n \<times> nat, 'tok \<times> nat) syms \<times>
    ('tok \<times> nat) list\<close> where
  \<open>icore ((A\<^sub>i, arhs), m, u) = (A\<^sub>i, map unann (take m arhs), drop m arhs, u)\<close>

definition iequiv :: \<open>('n \<times> nat, 'tok \<times> nat) item set \<Rightarrow>
    ('n \<times> nat, 'tok \<times> nat) item set \<Rightarrow> bool\<close>  (infix \<open>\<approx>\<close> 50) where
  \<open>S \<approx> T \<longleftrightarrow> icore ` S = icore ` T\<close>

lemma iequiv_refl[simp]: \<open>S \<approx> S\<close>
  unfolding iequiv_def by simp

lemma iequiv_sym: \<open>S \<approx> T \<Longrightarrow> T \<approx> S\<close>
  unfolding iequiv_def by simp

lemma iequiv_trans: \<open>S \<approx> T \<Longrightarrow> T \<approx> U \<Longrightarrow> S \<approx> U\<close>
  unfolding iequiv_def by simp

lemma icore_image_D:
  assumes \<open>icore ((A\<^sub>i, arhs), m, u) \<in> icore ` T\<close>
  obtains arhs' m' where \<open>((A\<^sub>i, arhs'), m', u) \<in> T\<close>
    and \<open>map unann (take m' arhs') = map unann (take m arhs)\<close>
    and \<open>drop m' arhs' = drop m arhs\<close>
proof -
  from assms obtain it' where \<open>icore ((A\<^sub>i, arhs), m, u) = icore it'\<close> \<open>it' \<in> T\<close> by (rule imageE)
  thus thesis by (cases it' rule: icore.cases) (auto intro: that)
qed
lemma drop_eq_ConsD:
  assumes \<open>drop m xs = y # ys\<close>
  shows \<open>m < length xs\<close> and \<open>xs ! m = y\<close> and \<open>drop (Suc m) xs = ys\<close>
proof -
  from assms have \<open>drop m xs \<noteq> []\<close> by simp
  thus m: \<open>m < length xs\<close> by simp
  from Cons_nth_drop_Suc[OF m] assms show \<open>xs ! m = y\<close> \<open>drop (Suc m) xs = ys\<close> by simp_all
qed

lemma Kset_cong_sub:
  assumes \<open>icore ` S \<subseteq> icore ` T\<close>
  shows \<open>Kset P k S \<subseteq> Kset P k T\<close>
proof
  fix v assume \<open>v \<in> Kset P k S\<close>
  then obtain A rhs m u where \<open>((A, rhs), m, u) \<in> S\<close> and v: \<open>v \<in> Hk P k (drop m rhs @ map Tm u)\<close>
    unfolding Kset_def by blast
  with assms have \<open>icore ((A, rhs), m, u) \<in> icore ` T\<close> by blast
  then obtain rhs' m' where \<open>((A, rhs'), m', u) \<in> T\<close> \<open>drop m' rhs' = drop m rhs\<close>
    by (rule icore_image_D)
  with v show \<open>v \<in> Kset P k T\<close> unfolding Kset_def \<open>drop m' rhs' = _\<close>[symmetric] by blast
qed

lemma Kset_cong: \<open>S \<approx> T \<Longrightarrow> Kset P k S = Kset P k T\<close>
  unfolding iequiv_def
  by (intro equalityI Kset_cong_sub) simp_all

lemma iclosure_cong_sub:
  assumes \<open>icore ` S \<subseteq> icore ` T\<close>
  shows \<open>icore ` iclosure P k S \<subseteq> icore ` iclosure P k T\<close>
proof
  fix c assume \<open>c \<in> icore ` iclosure P k S\<close>
  then obtain it where \<open>it \<in> iclosure P k S\<close> and c: \<open>c = icore it\<close> by blast
  from this(1) show \<open>c \<in> icore ` iclosure P k T\<close> unfolding c
  proof (induction rule: iclosure.induct)
    case (iclosure_base it)
    with assms show ?case by (blast intro: iclosure.iclosure_base rev_image_eqI)
  next
    case (iclosure_step A rhs m u B rhs\<^sub>B v)
    from icore_image_D[OF iclosure_step.IH] obtain arhs' m' where
      T: \<open>((A, arhs'), m', u) \<in> iclosure P k T\<close> and \<open>drop m' arhs' = drop m rhs\<close> by blast
    with iclosure_step.hyps(3) have \<open>drop m' arhs' = Nt B # drop (Suc m) rhs\<close>
      by (simp add: Cons_nth_drop_Suc[OF iclosure_step.hyps(2), symmetric])
    from drop_eq_ConsD[OF this] iclosure_step.hyps(4,5)
    have \<open>((B, rhs\<^sub>B), 0, v) \<in> iclosure P k T\<close> by (auto intro: iclosure.iclosure_step[OF T])
    thus ?case by (rule imageI)
  qed
qed

lemma iclosure_cong: \<open>S \<approx> T \<Longrightarrow> iclosure P k S \<approx> iclosure P k T\<close>
  unfolding iequiv_def
  by (intro equalityI iclosure_cong_sub[unfolded iequiv_def]) simp_all

lemma igoto_cong_sub:
  assumes \<open>icore ` S \<subseteq> icore ` T\<close>
  shows \<open>icore ` igoto S Z \<subseteq> icore ` igoto T Z\<close>
proof
  fix c assume \<open>c \<in> icore ` igoto S Z\<close>
  then obtain A rhs m u where \<open>((A, rhs), m, u) \<in> S\<close> and m: \<open>m < length rhs\<close> and Z: \<open>rhs ! m = Z\<close>
    and c: \<open>c = icore ((A, rhs), Suc m, u)\<close>
    unfolding igoto_def by blast
  with assms have \<open>icore ((A, rhs), m, u) \<in> icore ` T\<close> by blast
  from icore_image_D[OF this] obtain rhs' m' where T: \<open>((A, rhs'), m', u) \<in> T\<close>
    and pre: \<open>map unann (take m' rhs') = map unann (take m rhs)\<close> and \<open>drop m' rhs' = drop m rhs\<close>
    by blast
  with Z have \<open>drop m' rhs' = Z # drop (Suc m) rhs\<close> by (simp add: Cons_nth_drop_Suc[OF m, symmetric])
  note d = drop_eq_ConsD[OF this]

  from T d have \<open>((A, rhs'), Suc m', u) \<in> igoto T Z\<close> unfolding igoto_def by blast
  moreover from d pre m Z have \<open>icore ((A, rhs'), Suc m', u) = c\<close>
    unfolding c by (simp add: take_Suc_conv_app_nth)
  ultimately show \<open>c \<in> icore ` igoto T Z\<close> by blast
qed

lemma igoto_cong: \<open>S \<approx> T \<Longrightarrow> igoto S Z \<approx> igoto T Z\<close>
  unfolding iequiv_def
  by (intro equalityI igoto_cong_sub[unfolded iequiv_def]) simp_all

text \<open>Wellformed items keep the dot inside the right-hand side.\<close>

definition wf_iset :: \<open>('nn, 'tt) item set \<Rightarrow> bool\<close> where
  \<open>wf_iset S \<longleftrightarrow> (\<forall>A rhs m u. ((A, rhs), m, u) \<in> S \<longrightarrow> m \<le> length rhs)\<close>

lemma wf_iset_iclosure: \<open>wf_iset S \<Longrightarrow> wf_iset (iclosure P k S)\<close>
  unfolding wf_iset_def
  by (intro allI impI) (erule iclosure.cases; force)

lemma wf_iset_igoto: \<open>wf_iset S \<Longrightarrow> wf_iset (igoto S Z)\<close>
  unfolding wf_iset_def igoto_def by fastforce

lemma completed_core_transfer:
  assumes \<open>icore ` S \<subseteq> icore ` T\<close> and \<open>wf_iset T\<close> and \<open>((pA, arhs), length arhs, u) \<in> S\<close>
  obtains arhs' where \<open>((pA, arhs'), length arhs', u) \<in> T\<close>
    and \<open>length arhs' = length arhs\<close> and \<open>map unann arhs' = map unann arhs\<close>
proof -
  from assms(1,3) have \<open>icore ((pA, arhs), length arhs, u) \<in> icore ` T\<close> by blast
  from icore_image_D[OF this] obtain arhs' m' where T: \<open>((pA, arhs'), m', u) \<in> T\<close>
    and pre: \<open>map unann (take m' arhs') = map unann arhs\<close> and \<open>drop m' arhs' = []\<close> by auto
  with assms(2) have m': \<open>m' = length arhs'\<close> unfolding wf_iset_def by fastforce
  with pre have eq: \<open>map unann arhs' = map unann arhs\<close> by simp
  hence \<open>length arhs' = length arhs\<close> by (metis length_map)
  from that[OF T[unfolded m'] this eq] show thesis .
qed


subsection \<open>Factored item sets (Sect. 5.5)\<close>

text \<open>
  A \<^emph>\<open>factored item\<close> \<^text>\<open>[A \<rightarrow> X\<^sub>1\<dots>X\<^sub>m . X\<^sub>m\<^sub>+\<^sub>1\<dots>X\<^sub>n; L]\<close>
  pairs a production of the original IS-grammar and a dot with the
  indentation-and-lookahead set
  \<^text>\<open>L \<subseteq> \<nat> \<times> (\<Sigma> \<times> \<nat>)\<^sup>k\<close> of the paper. Its
  concretization \<^text>\<open>fconc\<close> is the set of annotated items it stands for:
  all valid annotations of the right-hand side, for every
  \<^text>\<open>(i, u) \<in> L\<close>. The paper leaves the factored lookahead
  computation sketched; \<^text>\<open>fHk\<close> defines it semantically from
  \<^const>\<open>Hk\<close>.
\<close>

type_synonym ('n, 'tok) fitem =
  \<open>('n \<times> ('n, 'tok) rhs) \<times> nat \<times> (nat \<times> ('tok \<times> nat) list) set\<close>

definition fconc :: \<open>('n, 'tok) fitem \<Rightarrow> ('n \<times> nat, 'tok \<times> nat) item set\<close> where
  \<open>fconc fit = (case fit of ((A, rhs), m, L) \<Rightarrow>
     {(((A, i), arhs), m, u) | i arhs u. (i, u) \<in> L \<and> annotates i rhs arhs})\<close>

lemma fconc_iff:
  \<open>(((A, i), arhs), m, u) \<in> fconc ((A', rhs), m', L) \<longleftrightarrow>
   A' = A \<and> m' = m \<and> (i, u) \<in> L \<and> annotates i rhs arhs\<close>
  unfolding fconc_def by auto

definition fconcs :: \<open>('n, 'tok) fitem set \<Rightarrow> ('n \<times> nat, 'tok \<times> nat) item set\<close> where
  \<open>fconcs FS = \<Union> (fconc ` FS)\<close>

lemma fconcsI: \<open>fit \<in> FS \<Longrightarrow> it \<in> fconc fit \<Longrightarrow> it \<in> fconcs FS\<close>
  unfolding fconcs_def by blast

lemma fconcsE:
  assumes \<open>it \<in> fconcs FS\<close>
  obtains fit where \<open>fit \<in> FS\<close> and \<open>it \<in> fconc fit\<close>
  using assms unfolding fconcs_def by blast

definition fHk :: \<open>('n, 'tok) is_cfg \<Rightarrow> nat \<Rightarrow> ('n, 'tok) rhs \<Rightarrow> nat \<Rightarrow> ('tok \<times> nat) list \<Rightarrow>
    ('tok \<times> nat) list set\<close> where
  \<open>fHk G k rest i u =
     (\<Union>arest \<in> {arest. annotates i rest arest}. Hk (infG G) k (arest @ map Tm u))\<close>

lemma fHkI:
  \<open>annotates i rest arest \<Longrightarrow> v \<in> Hk (infG G) k (arest @ map Tm u) \<Longrightarrow>
   v \<in> fHk G k rest i u\<close>
  unfolding fHk_def by blast

lemma fHkE:
  assumes \<open>v \<in> fHk G k rest i u\<close>
  obtains arest where \<open>annotates i rest arest\<close>
    and \<open>v \<in> Hk (infG G) k (arest @ map Tm u)\<close>
  using assms unfolding fHk_def by blast

inductive_set fclosure :: \<open>('n, 'tok) is_cfg \<Rightarrow> nat \<Rightarrow> ('n, 'tok) fitem set \<Rightarrow> ('n, 'tok) fitem set\<close>
  for G :: \<open>('n, 'tok) is_cfg\<close> and k :: nat and FS :: \<open>('n, 'tok) fitem set\<close> where
  fclosure_base: \<open>fit \<in> FS \<Longrightarrow> fit \<in> fclosure G k FS\<close>
| fclosure_step: \<open>((A, rhs), m, L) \<in> fclosure G k FS \<Longrightarrow> m < length rhs \<Longrightarrow>
    fst (rhs ! m) = Nt B \<Longrightarrow> (B, rhs\<^sub>B) \<in> set (iprods G) \<Longrightarrow>
    L' = {(j, v). \<exists>(i, u) \<in> L. irel_sat (snd (rhs ! m)) j i \<and>
                   v \<in> fHk G k (drop (Suc m) rhs) i u} \<Longrightarrow>
    ((B, rhs\<^sub>B), 0, L') \<in> fclosure G k FS\<close>

definition fgoto :: \<open>('n, 'tok) fitem set \<Rightarrow> ('n, 'tok) sym \<Rightarrow> nat \<Rightarrow> ('n, 'tok) fitem set\<close> where
  \<open>fgoto FS X l = {((A, rhs), Suc m, {(i, u) \<in> L. irel_sat (snd (rhs ! m)) l i})
     | A rhs m L. ((A, rhs), m, L) \<in> FS \<and> m < length rhs \<and> fst (rhs ! m) = X}\<close>

definition fKset :: \<open>('n, 'tok) is_cfg \<Rightarrow> nat \<Rightarrow> ('n, 'tok) fitem set \<Rightarrow> ('tok \<times> nat) list set\<close> where
  \<open>fKset G k FS = {v. \<exists>A rhs m L i u. ((A, rhs), m, L) \<in> FS \<and> (i, u) \<in> L \<and>
                      v \<in> fHk G k (drop m rhs) i u}\<close>

definition wf_fitems :: \<open>('n, 'tok) fitem set \<Rightarrow> bool\<close> where
  \<open>wf_fitems FS \<longleftrightarrow> (\<forall>A rhs m L. ((A, rhs), m, L) \<in> FS \<longrightarrow> m \<le> length rhs)\<close>

lemma wf_fitems_fclosure: \<open>wf_fitems FS \<Longrightarrow> wf_fitems (fclosure G k FS)\<close>
  unfolding wf_fitems_def
  by (intro allI impI) (erule fclosure.cases; force)

lemma wf_fitems_fgoto: \<open>wf_fitems FS \<Longrightarrow> wf_fitems (fgoto FS X l)\<close>
  unfolding wf_fitems_def fgoto_def by fastforce

lemma wf_iset_fconcs: \<open>wf_fitems FS \<Longrightarrow> wf_iset (fconcs FS)\<close>
  unfolding wf_iset_def wf_fitems_def fconcs_def fconc_def
  by (fastforce dest: annotates_length)

subsection \<open>The factored operations model Algorithm 8 (Sect. 5.5, 5.7)\<close>

text \<open>
  The lookahead sets and the closure commute with concretization. GOTO commutes
  up to core-equivalence: the concrete GOTO records the indentation of the
  symbol just moved over the dot where the factored one forgets it, sound
  because pre-dot annotations do not matter. At this semantic level the
  factored representation loses nothing, settling the concern of Sect. 5.7 for
  the indentation-and-lookahead sets; over-approximation enters only with the
  finite representation of lookaheads in Sect. 5.6.
\<close>

theorem fKset_correct: \<open>Kset (infG G) k (fconcs FS) = fKset G k FS\<close>
proof (intro equalityI subsetI)
  fix v assume \<open>v \<in> Kset (infG G) k (fconcs FS)\<close>
  then obtain A\<^sub>i arhs m u where \<open>((A\<^sub>i, arhs), m, u) \<in> fconcs FS\<close>
    and v: \<open>v \<in> Hk (infG G) k (drop m arhs @ map Tm u)\<close>
    unfolding Kset_def by blast
  then obtain A rhs L i where \<open>((A, rhs), m, L) \<in> FS\<close> \<open>(i, u) \<in> L\<close> \<open>annotates i rhs arhs\<close>
    by (auto elim!: fconcsE simp: fconc_def split: prod.splits)
  with v annotates_drop[OF this(3)] show \<open>v \<in> fKset G k FS\<close>
    unfolding fKset_def by (blast intro: fHkI)
next
  fix v assume \<open>v \<in> fKset G k FS\<close>
  then obtain A rhs m L i u where fit: \<open>((A, rhs), m, L) \<in> FS\<close> and iu: \<open>(i, u) \<in> L\<close>
    and \<open>v \<in> fHk G k (drop m rhs) i u\<close>
    unfolding fKset_def by blast
  from this(3) obtain arest where arest: \<open>annotates i (drop m rhs) arest\<close>
    and v: \<open>v \<in> Hk (infG G) k (arest @ map Tm u)\<close>
    by (rule fHkE)

  let ?apre = \<open>map (\<lambda>(X, r). annsym (X, irel_wit r i)) (take m rhs)\<close>
  have \<open>annotates i rhs (?apre @ arest)\<close> using annotates_appendI[OF annotates_wit[where rhs = \<open>take m rhs\<close>] arest] by simp
  hence \<open>(((A, i), ?apre @ arest), m, u) \<in> fconcs FS\<close>
    using iu by (intro fconcsI[OF fit]) (simp add: fconc_iff)
  moreover have \<open>drop m (?apre @ arest) = arest\<close>
    using annotates_length[OF arest] by (cases \<open>m \<le> length rhs\<close>) auto
  hence \<open>v \<in> Hk (infG G) k (drop m (?apre @ arest) @ map Tm u)\<close> using v by simp
  ultimately show \<open>v \<in> Kset (infG G) k (fconcs FS)\<close> unfolding Kset_def by blast
qed

lemma fconc_fclosure_sub:
  assumes \<open>fit \<in> fclosure G k FS\<close>
  shows \<open>fconc fit \<subseteq> iclosure (infG G) k (fconcs FS)\<close>
  using assms
proof (induction rule: fclosure.induct)
  case (fclosure_step A rhs m L B rhs\<^sub>B L')
  show ?case
  proof
    fix it assume \<open>it \<in> fconc ((B, rhs\<^sub>B), 0, L')\<close>
    then obtain j v arhs\<^sub>B where it: \<open>it = (((B, j), arhs\<^sub>B), 0, v)\<close> and \<open>(j, v) \<in> L'\<close>
      and \<open>annotates j rhs\<^sub>B arhs\<^sub>B\<close>
      unfolding fconc_def by auto
    with fclosure_step.hyps(4) have B: \<open>((B, j), arhs\<^sub>B) \<in> infG G\<close> unfolding infG_alt by blast
    from \<open>(j, v) \<in> L'\<close>[unfolded fclosure_step.hyps(5)] obtain i u where iu: \<open>(i, u) \<in> L\<close>
      and sat: \<open>irel_sat (snd (rhs ! m)) j i\<close> and \<open>v \<in> fHk G k (drop (Suc m) rhs) i u\<close> by auto
    from this(3) obtain arest where arest: \<open>annotates i (drop (Suc m) rhs) arest\<close>
      and v: \<open>v \<in> Hk (infG G) k (arest @ map Tm u)\<close> by (rule fHkE)

    let ?apre = \<open>map (\<lambda>(X, r). annsym (X, irel_wit r i)) (take m rhs)\<close>
    have \<open>annotates i [rhs ! m] [Nt (B, j)]\<close> using fclosure_step.hyps(3) sat by (cases \<open>rhs ! m\<close>) auto
    with annotates_appendI[OF annotates_wit[where rhs = \<open>take m rhs\<close>] annotates_appendI[OF this arest]]
      id_take_nth_drop[OF fclosure_step.hyps(2)]
    have \<open>annotates i rhs (?apre @ Nt (B, j) # arest)\<close> by simp
    hence \<open>(((A, i), ?apre @ Nt (B, j) # arest), m, u) \<in> iclosure (infG G) k (fconcs FS)\<close>
      using fclosure_step.IH iu by (auto simp: fconc_iff)
    thus \<open>it \<in> iclosure (infG G) k (fconcs FS)\<close>
      unfolding it by (rule iclosure.iclosure_step[OF _ _ _ B])
                      (use fclosure_step.hyps(2) v in \<open>auto simp: nth_append\<close>)
  qed
qed (auto intro: iclosure.iclosure_base fconcsI)

lemma iclosure_fconcs_sub:
  \<open>iclosure (infG G) k (fconcs FS) \<subseteq> fconcs (fclosure G k FS)\<close>
proof
  fix it assume \<open>it \<in> iclosure (infG G) k (fconcs FS)\<close>
  then show \<open>it \<in> fconcs (fclosure G k FS)\<close>
  proof (induction rule: iclosure.induct)
    case (iclosure_step A\<^sub>i arhs m u Bj arhs\<^sub>B v)
    from iclosure_step.IH obtain A\<^sub>0 rhs\<^sub>0 L i where
      fit: \<open>((A\<^sub>0, rhs\<^sub>0), m, L) \<in> fclosure G k FS\<close> and A\<^sub>i: \<open>A\<^sub>i = (A\<^sub>0, i)\<close> and iu: \<open>(i, u) \<in> L\<close>
      and ann: \<open>annotates i rhs\<^sub>0 arhs\<close>
      by (auto elim!: fconcsE simp: fconc_def split: prod.splits)
    have m: \<open>m < length rhs\<^sub>0\<close> using annotates_length[OF ann] iclosure_step.hyps(2) by simp
    from annotates_nthD[OF ann m] iclosure_step.hyps(3) obtain B\<^sub>0 j\<^sub>0 where
      B\<^sub>0: \<open>fst (rhs\<^sub>0 ! m) = Nt B\<^sub>0\<close> \<open>Bj = (B\<^sub>0, j\<^sub>0)\<close> and sat: \<open>irel_sat (snd (rhs\<^sub>0 ! m)) j\<^sub>0 i\<close>
      by (cases \<open>fst (rhs\<^sub>0 ! m)\<close>) auto
    with iclosure_step.hyps(4) obtain rhs\<^sub>B\<^sub>0 where
      rhs\<^sub>B\<^sub>0: \<open>(B\<^sub>0, rhs\<^sub>B\<^sub>0) \<in> set (iprods G)\<close> \<open>annotates j\<^sub>0 rhs\<^sub>B\<^sub>0 arhs\<^sub>B\<close> by (auto simp: infG_alt)

    let ?L' = \<open>{(j, v). \<exists>(i, u) \<in> L. irel_sat (snd (rhs\<^sub>0 ! m)) j i \<and> v \<in> fHk G k (drop (Suc m) rhs\<^sub>0) i u}\<close>
    from fHkI[OF annotates_drop[OF ann] iclosure_step.hyps(5)] iu sat have \<open>(j\<^sub>0, v) \<in> ?L'\<close> by blast
    with rhs\<^sub>B\<^sub>0(2) have \<open>(((B\<^sub>0, j\<^sub>0), arhs\<^sub>B), 0, v) \<in> fconc ((B\<^sub>0, rhs\<^sub>B\<^sub>0), 0, ?L')\<close>
      by (simp add: fconc_iff)
    with fclosure.fclosure_step[OF fit m B\<^sub>0(1) rhs\<^sub>B\<^sub>0(1) refl] show ?case
      unfolding B\<^sub>0(2) by (rule fconcsI)
  qed (auto simp: fconcs_def intro: fclosure.fclosure_base)
qed

theorem fconcs_iclosure: \<open>iclosure (infG G) k (fconcs FS) = fconcs (fclosure G k FS)\<close>
  by (intro equalityI iclosure_fconcs_sub) (blast elim!: fconcsE intro: fconc_fclosure_sub[THEN subsetD])

theorem fconcs_igoto:
  \<open>igoto (fconcs FS) (annsym (X, l)) \<approx> fconcs (fgoto FS X l)\<close>
  unfolding iequiv_def
proof (intro equalityI subsetI)
  fix c assume \<open>c \<in> icore ` igoto (fconcs FS) (annsym (X, l))\<close>
  then obtain A\<^sub>i arhs m u where \<open>((A\<^sub>i, arhs), m, u) \<in> fconcs FS\<close>
    and mlt: \<open>m < length arhs\<close> and nth: \<open>arhs ! m = annsym (X, l)\<close>
    and c: \<open>c = icore ((A\<^sub>i, arhs), Suc m, u)\<close>
    unfolding igoto_def by blast
  then obtain A\<^sub>0 rhs\<^sub>0 L i where fit: \<open>((A\<^sub>0, rhs\<^sub>0), m, L) \<in> FS\<close> and A\<^sub>i: \<open>A\<^sub>i = (A\<^sub>0, i)\<close>
    and iu: \<open>(i, u) \<in> L\<close> and ann: \<open>annotates i rhs\<^sub>0 arhs\<close>
    by (auto elim!: fconcsE simp: fconc_def split: prod.splits)
  have m: \<open>m < length rhs\<^sub>0\<close> using annotates_length[OF ann] mlt by simp
  from annotates_nthD[OF ann m] nth have X: \<open>fst (rhs\<^sub>0 ! m) = X\<close> and sat: \<open>irel_sat (snd (rhs\<^sub>0 ! m)) l i\<close>
    by (auto dest: injD[OF inj_annsym])

  have \<open>((A\<^sub>0, rhs\<^sub>0), Suc m, {(i, u) \<in> L. irel_sat (snd (rhs\<^sub>0 ! m)) l i}) \<in> fgoto FS X l\<close>
    unfolding fgoto_def using fit m X by blast
  hence \<open>((A\<^sub>i, arhs), Suc m, u) \<in> fconcs (fgoto FS X l)\<close>
    unfolding A\<^sub>i by (rule fconcsI) (simp add: fconc_iff iu sat ann)
  thus \<open>c \<in> icore ` fconcs (fgoto FS X l)\<close> using c by blast
next
  fix c assume \<open>c \<in> icore ` fconcs (fgoto FS X l)\<close>
  then obtain it where \<open>it \<in> fconcs (fgoto FS X l)\<close> and c: \<open>c = icore it\<close> by blast
  then obtain A\<^sub>0 rhs\<^sub>0 m L i arhs' u where fit: \<open>((A\<^sub>0, rhs\<^sub>0), m, L) \<in> FS\<close> and m: \<open>m < length rhs\<^sub>0\<close>
    and X: \<open>fst (rhs\<^sub>0 ! m) = X\<close> and it: \<open>it = (((A\<^sub>0, i), arhs'), Suc m, u)\<close>
    and iu: \<open>(i, u) \<in> L\<close> and sat: \<open>irel_sat (snd (rhs\<^sub>0 ! m)) l i\<close> and ann': \<open>annotates i rhs\<^sub>0 arhs'\<close>
    by (auto elim!: fconcsE simp: fgoto_def fconc_def split: prod.splits)
  have mlt': \<open>m < length arhs'\<close> using annotates_length[OF ann'] m by simp

  let ?arhs = \<open>take m arhs' @ annsym (X, l) # drop (Suc m) arhs'\<close>
  have \<open>annotates i [rhs\<^sub>0 ! m] [annsym (X, l)]\<close> using X sat by (cases \<open>rhs\<^sub>0 ! m\<close>) auto
  with annotates_appendI[OF annotates_take[OF ann', of m]
      annotates_appendI[OF this annotates_drop[OF ann', of \<open>Suc m\<close>]]] id_take_nth_drop[OF m]
  have \<open>annotates i rhs\<^sub>0 ?arhs\<close> by (simp add: take_Suc_conv_app_nth)
  hence \<open>(((A\<^sub>0, i), ?arhs), m, u) \<in> fconcs FS\<close> using iu by (intro fconcsI[OF fit]) (simp add: fconc_iff)
  hence \<open>(((A\<^sub>0, i), ?arhs), Suc m, u) \<in> igoto (fconcs FS) (annsym (X, l))\<close>
    unfolding igoto_def using mlt' by (auto simp: nth_append)
  moreover have \<open>icore (((A\<^sub>0, i), ?arhs), Suc m, u) = icore it\<close>
    using annotates_nthD[OF ann' m] X mlt' unfolding it
    by (auto simp: take_Suc_conv_app_nth min_absorb2)
  ultimately show \<open>c \<in> icore ` igoto (fconcs FS) (annsym (X, l))\<close> unfolding c by (metis image_eqI)
qed

text \<open>Completed items and their factored counterparts, used by the
  reduce action.\<close>

lemma fconcs_completedD:
  assumes \<open>((A\<^sub>i, arhs), length arhs, u) \<in> fconcs FS\<close>
  obtains A\<^sub>0 i rhs\<^sub>0 L where \<open>A\<^sub>i = (A\<^sub>0, i)\<close>
    and \<open>((A\<^sub>0, rhs\<^sub>0), length rhs\<^sub>0, L) \<in> FS\<close> and \<open>(i, u) \<in> L\<close>
    and \<open>length rhs\<^sub>0 = length arhs\<close>
proof -
  from assms obtain A\<^sub>0 rhs\<^sub>0 L i where
    \<open>A\<^sub>i = (A\<^sub>0, i)\<close> \<open>((A\<^sub>0, rhs\<^sub>0), length arhs, L) \<in> FS\<close> \<open>(i, u) \<in> L\<close> \<open>annotates i rhs\<^sub>0 arhs\<close>
    by (auto elim!: fconcsE simp: fconc_def split: prod.splits)
  with annotates_length[OF this(4)] show thesis by (auto intro: that)
qed

lemma fconcs_completedI:
  assumes \<open>((A\<^sub>0, rhs\<^sub>0), length rhs\<^sub>0, L) \<in> FS\<close> and \<open>(i, u) \<in> L\<close>
  obtains arhs where \<open>length arhs = length rhs\<^sub>0\<close>
    and \<open>(((A\<^sub>0, i), arhs), length arhs, u) \<in> fconcs FS\<close>
proof -
  let ?arhs = \<open>map (\<lambda>(X, r). annsym (X, irel_wit r i)) rhs\<^sub>0\<close>
  have \<open>(((A\<^sub>0, i), ?arhs), length ?arhs, u) \<in> fconcs FS\<close>
    by (rule fconcsI[OF assms(1)]) (simp add: fconc_iff assms(2) annotates_wit)
  thus thesis by (rule that[rotated]) simp
qed


subsection \<open>The factored machine and its bisimulation with Algorithm 8\<close>

text \<open>
  The factored machine works on stacks of factored item sets, in lockstep
  bisimulation with Algorithm 8 on the infinite II-CFG: related stacks, meaning
  entrywise core-equivalent concretizations that are all well-formed, admit the
  same shift and reduce steps and stay related. This is the formal content of
  the claim in Sect. 5.5 that the algorithm models the same item sets as
  Algorithm 8.
\<close>

type_synonym ('n, 'tok) flr_config = \<open>('n, 'tok) fitem set list \<times> ('tok \<times> nat) list\<close>

inductive flr_step :: \<open>('n, 'tok) is_cfg \<Rightarrow> nat \<Rightarrow>
    ('n, 'tok) flr_config \<Rightarrow> ('n, 'tok) flr_config \<Rightarrow> bool\<close> for G k where
  flr_shift: \<open>Fs \<noteq> [] \<Longrightarrow> take k ((t, l) # w) \<in> fKset G k (fclosure G k (hd Fs)) \<Longrightarrow>
     flr_step G k (Fs, (t, l) # w) (fgoto (fclosure G k (hd Fs)) (Tm t) l # Fs, w)\<close>
| flr_reduce: \<open>Fs \<noteq> [] \<Longrightarrow> ((A, rhs), length rhs, L) \<in> fclosure G k (hd Fs) \<Longrightarrow>
     (i, take k w) \<in> L \<Longrightarrow> length rhs < length Fs \<Longrightarrow>
     flr_step G k (Fs, w)
       (fgoto (fclosure G k (Fs ! length rhs)) (Nt A) i # drop (length rhs) Fs, w)\<close>

definition stack_rel :: \<open>('n \<times> nat, 'tok \<times> nat) item set list \<Rightarrow>
    ('n, 'tok) fitem set list \<Rightarrow> bool\<close> where
  \<open>stack_rel Ss Fs \<longleftrightarrow>
     list_all2 (\<lambda>S FS. S \<approx> fconcs FS \<and> wf_iset S \<and> wf_fitems FS) Ss Fs\<close>

lemma stack_rel_length: \<open>stack_rel Ss Fs \<Longrightarrow> length Fs = length Ss\<close>
  unfolding stack_rel_def by (auto dest: list_all2_lengthD)

lemma stack_rel_nth:
  \<open>stack_rel Ss Fs \<Longrightarrow> n < length Ss \<Longrightarrow>
   Ss ! n \<approx> fconcs (Fs ! n) \<and> wf_iset (Ss ! n) \<and> wf_fitems (Fs ! n)\<close>
  unfolding stack_rel_def by (auto dest: list_all2_nthD)

lemma stack_rel_hd:
  assumes \<open>stack_rel Ss Fs\<close> and \<open>Ss \<noteq> []\<close>
  shows \<open>hd Ss \<approx> fconcs (hd Fs)\<close> and \<open>wf_iset (hd Ss)\<close> and \<open>wf_fitems (hd Fs)\<close>
proof -
  have \<open>Fs \<noteq> []\<close> using stack_rel_length[OF assms(1)] assms(2) by fastforce
  with stack_rel_nth[OF assms(1), of 0] assms(2)
  show \<open>hd Ss \<approx> fconcs (hd Fs)\<close> \<open>wf_iset (hd Ss)\<close> \<open>wf_fitems (hd Fs)\<close> by (auto simp: hd_conv_nth)
qed

lemma stack_rel_Cons:
  \<open>S \<approx> fconcs FS \<Longrightarrow> wf_iset S \<Longrightarrow> wf_fitems FS \<Longrightarrow> stack_rel Ss Fs \<Longrightarrow>
   stack_rel (S # Ss) (FS # Fs)\<close>
  unfolding stack_rel_def by simp

lemma stack_rel_drop: \<open>stack_rel Ss Fs \<Longrightarrow> stack_rel (drop n Ss) (drop n Fs)\<close>
  unfolding stack_rel_def by (rule list_all2_dropI)

text \<open>Transfer of the machine's primitives across the representation.\<close>

lemma closure_transfer:
  assumes \<open>S \<approx> fconcs FS\<close>
  shows \<open>iclosure (infG G) k S \<approx> fconcs (fclosure G k FS)\<close>
  using iclosure_cong[OF assms, of \<open>infG G\<close> k] fconcs_iclosure[of G k FS] by simp

lemma goto_transfer:
  assumes \<open>S \<approx> fconcs FS\<close>
  shows \<open>igoto (iclosure (infG G) k S) (annsym (X, l))
         \<approx> fconcs (fgoto (fclosure G k FS) X l)\<close>
  by (meson assms closure_transfer igoto_cong fconcs_igoto iequiv_trans)

lemma Kset_transfer:
  assumes \<open>S \<approx> fconcs FS\<close>
  shows \<open>Kset (infG G) k (iclosure (infG G) k S) = fKset G k (fclosure G k FS)\<close>
  using Kset_cong[OF closure_transfer[OF assms]] fKset_correct by simp

theorem lr_step_to_flr:
  assumes rel: \<open>stack_rel Ss Fs\<close>
    and \<open>lr_step (infG G) k (Ss, w) (Ss', w')\<close>
  obtains Fs' where \<open>flr_step G k (Fs, w) (Fs', w')\<close> and \<open>stack_rel Ss' Fs'\<close>
  using assms(2)
proof (cases rule: lr_step.cases)
  case (lr_shift t)
  obtain t\<^sub>0 l where t: \<open>t = (t\<^sub>0, l)\<close> by (metis prod.collapse)
  note hd_facts = stack_rel_hd[OF rel lr_shift(3)]
  have \<open>Fs \<noteq> []\<close> using lr_shift(3) stack_rel_length[OF rel] by fastforce
  moreover have \<open>take k (t # w') \<in> fKset G k (fclosure G k (hd Fs))\<close>
    using lr_shift(4) Kset_transfer[OF hd_facts(1)] by simp
  ultimately have \<open>flr_step G k (Fs, t # w') (fgoto (fclosure G k (hd Fs)) (Tm t\<^sub>0) l # Fs, w')\<close>
    unfolding t by (rule flr_step.flr_shift)
  moreover have \<open>stack_rel Ss' (fgoto (fclosure G k (hd Fs)) (Tm t\<^sub>0) l # Fs)\<close>
    unfolding lr_shift(2) t
    by (intro stack_rel_Cons goto_transfer[OF hd_facts(1), of G k \<open>Tm t\<^sub>0\<close> l, simplified]
          wf_iset_igoto wf_iset_iclosure wf_fitems_fgoto wf_fitems_fclosure hd_facts(2,3) rel)
  ultimately show thesis using that lr_shift(1) by blast
next
  case (lr_reduce A rhs)
  note hd_facts = stack_rel_hd[OF rel lr_reduce(3)]
  have \<open>Fs \<noteq> []\<close> using lr_reduce(3) stack_rel_length[OF rel] by fastforce
  have \<open>icore ` iclosure (infG G) k (hd Ss) \<subseteq> icore ` fconcs (fclosure G k (hd Fs))\<close>
    using closure_transfer[OF hd_facts(1)] unfolding iequiv_def by simp
  moreover have \<open>wf_iset (fconcs (fclosure G k (hd Fs)))\<close>
    by (intro wf_iset_fconcs wf_fitems_fclosure hd_facts(3))
  moreover have \<open>((A, rhs), length rhs, take k w) \<in> iclosure (infG G) k (hd Ss)\<close>
    using lr_reduce(4) by (simp add: Kprod_iff)
  ultimately obtain arhs' where
    \<open>((A, arhs'), length arhs', take k w) \<in> fconcs (fclosure G k (hd Fs))\<close> and len': \<open>length arhs' = length rhs\<close>
    by (rule completed_core_transfer)
  from this(1) obtain A\<^sub>0 i rhs\<^sub>0 L where A: \<open>A = (A\<^sub>0, i)\<close>
    and fcompl: \<open>((A\<^sub>0, rhs\<^sub>0), length rhs\<^sub>0, L) \<in> fclosure G k (hd Fs)\<close>
    and iuL: \<open>(i, take k w) \<in> L\<close> and \<open>length rhs\<^sub>0 = length arhs'\<close>
    by (rule fconcs_completedD)
  with len' have len\<^sub>0: \<open>length rhs\<^sub>0 = length rhs\<close> by simp

  have \<open>flr_step G k (Fs, w) (fgoto (fclosure G k (Fs ! length rhs)) (Nt A\<^sub>0) i # drop (length rhs) Fs, w)\<close>
    using flr_step.flr_reduce[OF \<open>Fs \<noteq> []\<close> fcompl iuL, unfolded len\<^sub>0] lr_reduce(5) stack_rel_length[OF rel]
    by simp
  moreover have \<open>stack_rel Ss' (fgoto (fclosure G k (Fs ! length rhs)) (Nt A\<^sub>0) i # drop (length rhs) Fs)\<close>
    unfolding lr_reduce(1) A
    by (intro stack_rel_Cons stack_rel_drop[OF rel] goto_transfer[of _ _ G k \<open>Nt A\<^sub>0\<close> i, simplified]
          wf_iset_igoto wf_iset_iclosure wf_fitems_fgoto wf_fitems_fclosure)
       (simp_all add: stack_rel_nth[OF rel lr_reduce(5)])
  ultimately show thesis using that lr_reduce(2) by blast
qed

theorem flr_step_to_lr:
  assumes rel: \<open>stack_rel Ss Fs\<close>
    and \<open>flr_step G k (Fs, w) (Fs', w')\<close>
  obtains Ss' where \<open>lr_step (infG G) k (Ss, w) (Ss', w')\<close> and \<open>stack_rel Ss' Fs'\<close>
  using assms(2)
proof (cases rule: flr_step.cases)
  case (flr_shift t l)
  have \<open>Ss \<noteq> []\<close> using flr_shift(3) stack_rel_length[OF rel] by fastforce
  note hd_facts = stack_rel_hd[OF rel this]
  have \<open>take k ((t, l) # w') \<in> Kset (infG G) k (iclosure (infG G) k (hd Ss))\<close>
    using flr_shift(4) Kset_transfer[OF hd_facts(1)] by simp
  with \<open>Ss \<noteq> []\<close> have
    \<open>lr_step (infG G) k (Ss, (t, l) # w') (igoto (iclosure (infG G) k (hd Ss)) (Tm (t, l)) # Ss, w')\<close>
    by (rule lr_step.lr_shift)
  moreover have \<open>stack_rel (igoto (iclosure (infG G) k (hd Ss)) (Tm (t, l)) # Ss) Fs'\<close>
    unfolding flr_shift(2)
    by (intro stack_rel_Cons goto_transfer[OF hd_facts(1), of G k \<open>Tm t\<close> l, simplified]
          wf_iset_igoto wf_iset_iclosure wf_fitems_fgoto wf_fitems_fclosure hd_facts(2,3) rel)
  ultimately show thesis using that flr_shift(1) by blast
next
  case (flr_reduce A rhs L i)
  have \<open>Ss \<noteq> []\<close> using flr_reduce(3) stack_rel_length[OF rel] by fastforce
  note hd_facts = stack_rel_hd[OF rel this]
  have nlt: \<open>length rhs < length Ss\<close> using flr_reduce(6) stack_rel_length[OF rel] by simp
  obtain arhs where len: \<open>length arhs = length rhs\<close>
    and mem: \<open>(((A, i), arhs), length arhs, take k w) \<in> fconcs (fclosure G k (hd Fs))\<close>
    by (rule fconcs_completedI[OF flr_reduce(4,5)])
  have \<open>icore ` fconcs (fclosure G k (hd Fs)) \<subseteq> icore ` iclosure (infG G) k (hd Ss)\<close>
    using closure_transfer[OF hd_facts(1)] unfolding iequiv_def by simp
  from completed_core_transfer[OF this wf_iset_iclosure[OF hd_facts(2)] mem] obtain arhs\<^sub>2 where
    \<open>(((A, i), arhs\<^sub>2), length arhs\<^sub>2, take k w) \<in> iclosure (infG G) k (hd Ss)\<close> \<open>length arhs\<^sub>2 = length arhs\<close>
    by blast
  hence \<open>take k w \<in> Kprod (iclosure (infG G) k (hd Ss)) ((A, i), arhs\<^sub>2)\<close> and len\<^sub>2: \<open>length arhs\<^sub>2 = length rhs\<close>
    by (simp_all add: Kprod_iff len)

  from lr_step.lr_reduce[OF \<open>Ss \<noteq> []\<close> this(1), unfolded len\<^sub>2] nlt have
    \<open>lr_step (infG G) k (Ss, w) (igoto (iclosure (infG G) k (Ss ! length rhs)) (Nt (A, i)) # drop (length rhs) Ss, w)\<close>
    by simp
  moreover have \<open>stack_rel (igoto (iclosure (infG G) k (Ss ! length rhs)) (Nt (A, i)) # drop (length rhs) Ss) Fs'\<close>
    unfolding flr_reduce(1)
    by (intro stack_rel_Cons stack_rel_drop[OF rel] goto_transfer[of _ _ G k \<open>Nt A\<close> i, simplified]
          wf_iset_igoto wf_iset_iclosure wf_fitems_fgoto wf_fitems_fclosure)
       (simp_all add: stack_rel_nth[OF rel nlt])
  ultimately show thesis using that flr_reduce(2) by blast
qed

text \<open>Whole runs correspond, in both directions.\<close>

theorem lr_run_to_flr:
  assumes \<open>(lr_step (infG G) k)\<^sup>*\<^sup>* (Ss, w) (Ss', w')\<close> and \<open>stack_rel Ss Fs\<close>
  obtains Fs' where \<open>(flr_step G k)\<^sup>*\<^sup>* (Fs, w) (Fs', w')\<close> and \<open>stack_rel Ss' Fs'\<close>
proof -
  have \<open>\<exists>Fs'. (flr_step G k)\<^sup>*\<^sup>* (Fs, w) (Fs', w') \<and> stack_rel Ss' Fs'\<close>
    using assms
  proof (induction arbitrary: Fs rule: rtranclp_induct2)
    case (step Ts v Ts' v')
    from step.IH[OF step.prems] obtain Fs\<^sub>1 where
      \<open>(flr_step G k)\<^sup>*\<^sup>* (Fs, w) (Fs\<^sub>1, v)\<close> \<open>stack_rel Ts Fs\<^sub>1\<close> by blast
    from lr_step_to_flr[OF this(2) step.hyps(2)] obtain Fs\<^sub>2 where
      \<open>flr_step G k (Fs\<^sub>1, v) (Fs\<^sub>2, v')\<close> \<open>stack_rel Ts' Fs\<^sub>2\<close> .
    with \<open>(flr_step G k)\<^sup>*\<^sup>* (Fs, w) (Fs\<^sub>1, v)\<close> show ?case by (meson rtranclp.rtrancl_into_rtrancl)
  qed blast
  thus thesis using that by blast
qed

theorem flr_run_to_lr:
  assumes \<open>(flr_step G k)\<^sup>*\<^sup>* (Fs, w) (Fs', w')\<close> and \<open>stack_rel Ss Fs\<close>
  obtains Ss' where \<open>(lr_step (infG G) k)\<^sup>*\<^sup>* (Ss, w) (Ss', w')\<close> and \<open>stack_rel Ss' Fs'\<close>
proof -
  have \<open>\<exists>Ss'. (lr_step (infG G) k)\<^sup>*\<^sup>* (Ss, w) (Ss', w') \<and> stack_rel Ss' Fs'\<close>
    using assms
  proof (induction arbitrary: Ss rule: rtranclp_induct2)
    case (step Ts v Ts' v')
    from step.IH[OF step.prems] obtain Ss\<^sub>1 where
      \<open>(lr_step (infG G) k)\<^sup>*\<^sup>* (Ss, w) (Ss\<^sub>1, v)\<close> \<open>stack_rel Ss\<^sub>1 Ts\<close> by blast
    from flr_step_to_lr[OF this(2) step.hyps(2)] obtain Ss\<^sub>2 where
      \<open>lr_step (infG G) k (Ss\<^sub>1, v) (Ss\<^sub>2, v')\<close> \<open>stack_rel Ss\<^sub>2 Ts'\<close> .
    with \<open>(lr_step (infG G) k)\<^sup>*\<^sup>* (Ss, w) (Ss\<^sub>1, v)\<close> show ?case by (meson rtranclp.rtrancl_into_rtrancl)
  qed blast
  thus thesis using that by blast
qed


subsection \<open>Finite representation of indentation sets (Sect. 5.5, 5.6)\<close>

text \<open>
  For the GLR case \<^text>\<open>k = 0\<close>, where lookaheads are trivial, the
  indentation sets occurring in the machine are always a finite set, or a finite
  set together with an upward-closed one, in line with Lemma 3.
  \<^text>\<open>indrep\<close> realizes that class, with executable membership, union, the
  constraint filter used by \<^const>\<open>fgoto\<close> and the relational image used by
  \<^const>\<open>fclosure\<close>. That the machine preserves the class is the paper's
  finite-representability claim.
\<close>

datatype indrep = FinRep \<open>nat list\<close> | UpRep \<open>nat list\<close> nat

fun irep_set :: \<open>indrep \<Rightarrow> nat set\<close> where
  \<open>irep_set (FinRep xs) = set xs\<close>
| \<open>irep_set (UpRep xs n) = set xs \<union> {m. n \<le> m}\<close>

fun irep_mem :: \<open>nat \<Rightarrow> indrep \<Rightarrow> bool\<close> where
  \<open>irep_mem i (FinRep xs) \<longleftrightarrow> i \<in> set xs\<close>
| \<open>irep_mem i (UpRep xs n) \<longleftrightarrow> i \<in> set xs \<or> n \<le> i\<close>

lemma irep_mem_correct[simp]: \<open>irep_mem i R \<longleftrightarrow> i \<in> irep_set R\<close>
  by (cases R) auto

fun irep_union :: \<open>indrep \<Rightarrow> indrep \<Rightarrow> indrep\<close> where
  \<open>irep_union (FinRep xs) (FinRep ys) = FinRep (xs @ ys)\<close>
| \<open>irep_union (FinRep xs) (UpRep ys n) = UpRep (xs @ ys) n\<close>
| \<open>irep_union (UpRep xs n) (FinRep ys) = UpRep (xs @ ys) n\<close>
| \<open>irep_union (UpRep xs n) (UpRep ys m) = UpRep (xs @ ys) (min n m)\<close>

lemma irep_union_correct[simp]:
  \<open>irep_set (irep_union R\<^sub>1 R\<^sub>2) = irep_set R\<^sub>1 \<union> irep_set R\<^sub>2\<close>
  by (cases R\<^sub>1; cases R\<^sub>2) auto

text \<open>The filter of \<^const>\<open>fgoto\<close>: the parent indentations
  compatible with a child at indentation \<^text>\<open>l\<close>.\<close>

fun irep_filter :: \<open>irel \<Rightarrow> nat \<Rightarrow> indrep \<Rightarrow> indrep\<close> where
  \<open>irep_filter Eq l R = (if irep_mem l R then FinRep [l] else FinRep [])\<close>
| \<open>irep_filter Gt l (FinRep xs) = FinRep (filter (\<lambda>i. i < l) xs)\<close>
| \<open>irep_filter Gt l (UpRep xs n) = FinRep (filter (\<lambda>i. i < l) xs @ [n..<l])\<close>
| \<open>irep_filter Ge l (FinRep xs) = FinRep (filter (\<lambda>i. i \<le> l) xs)\<close>
| \<open>irep_filter Ge l (UpRep xs n) = FinRep (filter (\<lambda>i. i \<le> l) xs @ [n..<Suc l])\<close>
| \<open>irep_filter Any l R = R\<close>

lemma irep_filter_correct[simp]:
  \<open>irep_set (irep_filter r l R) = irep_set R \<inter> {i. irel_sat r l i}\<close>
  by (cases r; cases R) auto

text \<open>The relational image of \<^const>\<open>fclosure\<close>: the child
  indentations compatible with some parent in \<^text>\<open>I\<close>. For
  \<^const>\<open>Gt\<close>, \<^const>\<open>Ge\<close> and \<^const>\<open>Any\<close> it is upward
  closed, determined by the least element of \<^text>\<open>I\<close>.\<close>

fun irep_min :: \<open>indrep \<Rightarrow> nat\<close> where
  \<open>irep_min (FinRep xs) = min_list xs\<close>
| \<open>irep_min (UpRep xs n) = min_list (n # xs)\<close>

lemma min_list_least:
  fixes xs :: \<open>nat list\<close>
  assumes \<open>xs \<noteq> []\<close>
  shows \<open>min_list xs \<in> set xs\<close> and \<open>\<And>y. y \<in> set xs \<Longrightarrow> min_list xs \<le> y\<close>
  using assms by (simp_all add: min_list_Min)

lemma irep_min_least:
  assumes \<open>irep_set R \<noteq> {}\<close>
  shows \<open>irep_min R \<in> irep_set R\<close> and \<open>\<And>i. i \<in> irep_set R \<Longrightarrow> irep_min R \<le> i\<close>
proof -
  have \<open>irep_min R \<in> irep_set R \<and> (\<forall>i \<in> irep_set R. irep_min R \<le> i)\<close>
  proof (cases R)
    case (FinRep ys)
    with assms show ?thesis by (auto simp: min_list_least)
  next
    case (UpRep ys n)
    have \<open>n # ys \<noteq> []\<close> by simp
    note least = min_list_least[OF this]
    have \<open>min_list (n # ys) \<le> i\<close> if \<open>i \<in> irep_set (UpRep ys n)\<close> for i
      using that least(2)[of i] order.trans[OF least(2)[of n], of i] by (auto simp del: min_list.simps)
    with UpRep least(1) show ?thesis by (auto simp del: min_list.simps)
  qed
  thus \<open>irep_min R \<in> irep_set R\<close> \<open>\<And>i. i \<in> irep_set R \<Longrightarrow> irep_min R \<le> i\<close> by auto
qed

lemma least_upset_lt:
  assumes \<open>m \<in> I\<close> and \<open>\<And>i. i \<in> I \<Longrightarrow> m \<le> i\<close>
  shows \<open>{j. Suc m \<le> j} = {j. \<exists>i \<in> I. i < j}\<close>
  using assms by (auto simp: Suc_le_eq intro: le_less_trans)

lemma least_upset_le:
  fixes m :: nat
  assumes \<open>m \<in> I\<close> and \<open>\<And>i. i \<in> I \<Longrightarrow> m \<le> i\<close>
  shows \<open>{j. m \<le> j} = {j. \<exists>i \<in> I. i \<le> j}\<close>
  using assms by (auto intro: le_trans)

fun irep_img :: \<open>irel \<Rightarrow> indrep \<Rightarrow> indrep\<close> where
  \<open>irep_img Eq R = R\<close>
| \<open>irep_img Gt (FinRep xs) =
    (if xs = [] then FinRep [] else UpRep [] (Suc (min_list xs)))\<close>
| \<open>irep_img Gt (UpRep xs n) = UpRep [] (Suc (min_list (n # xs)))\<close>
| \<open>irep_img Ge (FinRep xs) =
    (if xs = [] then FinRep [] else UpRep [] (min_list xs))\<close>
| \<open>irep_img Ge (UpRep xs n) = UpRep [] (min_list (n # xs))\<close>
| \<open>irep_img Any (FinRep xs) = (if xs = [] then FinRep [] else UpRep [] 0)\<close>
| \<open>irep_img Any (UpRep xs n) = UpRep [] 0\<close>

lemma irep_img_correct[simp]:
  \<open>irep_set (irep_img r R) = {j. \<exists>i \<in> irep_set R. irel_sat r j i}\<close>
proof (cases \<open>irep_set R = {}\<close>)
  case True
  then have \<open>R = FinRep []\<close> by (cases R) auto
  then show ?thesis by (cases r) auto
next
  case False
  note least = least_upset_lt[OF irep_min_least[OF False]] least_upset_le[OF irep_min_least[OF False]]
  have ne: \<open>R = FinRep xs \<Longrightarrow> xs \<noteq> []\<close> for xs using False by auto
  show ?thesis
  proof (cases r)
    case Gt
    have \<open>irep_set (irep_img Gt R) = {j. Suc (irep_min R) \<le> j}\<close> by (cases R) (auto simp: ne)
    with Gt least(1) show ?thesis by auto
  next
    case Ge
    have \<open>irep_set (irep_img Ge R) = {j. irep_min R \<le> j}\<close> by (cases R) (auto simp: ne)
    with Ge least(2) show ?thesis by auto
  next
    case Any
    have \<open>irep_set (irep_img Any R) = {j. 0 \<le> j}\<close> by (cases R) (auto simp: ne)
    with Any irep_min_least(1)[OF False] show ?thesis by auto
  qed auto
qed

text \<open>At \<^text>\<open>k = 0\<close> lookaheads are empty and the
  indentation-and-lookahead sets are plain indentation sets. Every such set the
  machine reaches stays in the representable class.\<close>

lemma fHk_zero[simp]: \<open>fHk G 0 rest i u = {[]}\<close>
  using annotates_ex unfolding fHk_def by fastforce

definition rep0 :: \<open>indrep \<Rightarrow> (nat \<times> ('tok \<times> nat) list) set \<Rightarrow> bool\<close> where
  \<open>rep0 R L \<longleftrightarrow> L = irep_set R \<times> {[]}\<close>

definition rep0_fitems :: \<open>('n, 'tok) fitem set \<Rightarrow> bool\<close> where
  \<open>rep0_fitems FS \<longleftrightarrow> (\<forall>A rhs m L. ((A, rhs), m, L) \<in> FS \<longrightarrow> (\<exists>R. rep0 R L))\<close>

lemma rep0_fclosure:
  assumes \<open>rep0_fitems FS\<close>
  shows \<open>rep0_fitems (fclosure G 0 FS)\<close>
proof -
  have \<open>\<exists>R. rep0 R (snd (snd fit))\<close> if \<open>fit \<in> fclosure G 0 FS\<close> for fit
    using that
  proof (induction rule: fclosure.induct)
    case (fclosure_base fit)
    with assms show ?case unfolding rep0_fitems_def by (metis prod.collapse)
  next
    case (fclosure_step A rhs m L B rhs\<^sub>B L')
    from fclosure_step.IH obtain R where \<open>rep0 R L\<close> by auto
    hence \<open>rep0 (irep_img (snd (rhs ! m)) R) L'\<close> unfolding fclosure_step.hyps(5) rep0_def by auto
    thus ?case by auto
  qed
  thus ?thesis unfolding rep0_fitems_def by fastforce
qed

lemma rep0_fgoto:
  assumes \<open>rep0_fitems FS\<close>
  shows \<open>rep0_fitems (fgoto FS X l)\<close>
  unfolding rep0_fitems_def
proof (intro allI impI)
  fix A rhs m L assume \<open>((A, rhs), m, L) \<in> fgoto FS X l\<close>
  then obtain m\<^sub>0 L\<^sub>0 where \<open>((A, rhs), m\<^sub>0, L\<^sub>0) \<in> FS\<close>
    and L: \<open>L = {(i, u) \<in> L\<^sub>0. irel_sat (snd (rhs ! m\<^sub>0)) l i}\<close>
    unfolding fgoto_def by blast
  with assms obtain R\<^sub>0 where \<open>rep0 R\<^sub>0 L\<^sub>0\<close> unfolding rep0_fitems_def by blast
  hence \<open>rep0 (irep_filter (snd (rhs ! m\<^sub>0)) l R\<^sub>0) L\<close> unfolding L rep0_def by auto
  thus \<open>\<exists>R. rep0 R L\<close> ..
qed

theorem rep0_flr_step:
  assumes \<open>flr_step G 0 (Fs, w) (Fs', w')\<close>
    and \<open>\<And>FS. FS \<in> set Fs \<Longrightarrow> rep0_fitems FS\<close>
    and \<open>FS' \<in> set Fs'\<close>
  shows \<open>rep0_fitems FS'\<close>
  using assms(1)
proof (cases rule: flr_step.cases)
  case (flr_shift t l)
  have \<open>rep0_fitems (fgoto (fclosure G 0 (hd Fs)) (Tm t) l)\<close>
    by (intro rep0_fgoto rep0_fclosure assms(2) hd_in_set flr_shift(3))
  with assms(2,3) flr_shift(2) show ?thesis by auto
next
  case (flr_reduce A rhs L i)
  from flr_reduce(6) have \<open>rep0_fitems (fgoto (fclosure G 0 (Fs ! length rhs)) (Nt A) i)\<close>
    by (intro rep0_fgoto rep0_fclosure assms(2) nth_mem)
  with assms(2,3) flr_reduce(1) show ?thesis by (auto dest: in_set_dropD)
qed


subsection \<open>LR(k) grammars (Sect. 5.6)\<close>

text \<open>
  Knuth's LR(k) condition: two rightmost derivation steps that agree up to the
  end of the handle plus \<^text>\<open>k\<close> symbols are the same step. In an LR(k)
  grammar every sentential form has at most one handle, which removes the
  nondeterminism from Algorithm 8 in Sect. 5.6.
\<close>

definition lrk :: \<open>('nn, 'tt) Prods \<Rightarrow> 'nn \<Rightarrow> nat \<Rightarrow> bool\<close> where
  \<open>lrk P St k \<longleftrightarrow> (\<forall>U V A rhs U' V' A' rhs'.
     P \<turnstile> [Nt St] \<Rightarrow>r* U @ Nt A # V \<longrightarrow> Nts_syms V = {} \<longrightarrow> (A, rhs) \<in> P \<longrightarrow>
     P \<turnstile> [Nt St] \<Rightarrow>r* U' @ Nt A' # V' \<longrightarrow> Nts_syms V' = {} \<longrightarrow> (A', rhs') \<in> P \<longrightarrow>
     take (length U + length rhs + k) (U @ rhs @ V) =
     take (length U + length rhs + k) (U' @ rhs' @ V') \<longrightarrow>
     U' = U \<and> A' = A \<and> rhs' = rhs)\<close>

lemma lrkD:
  assumes \<open>lrk P St k\<close>
    and \<open>P \<turnstile> [Nt St] \<Rightarrow>r* U @ Nt A # V\<close> and \<open>Nts_syms V = {}\<close>
    and \<open>(A, rhs) \<in> P\<close>
    and \<open>P \<turnstile> [Nt St] \<Rightarrow>r* U' @ Nt A' # V'\<close> and \<open>Nts_syms V' = {}\<close>
    and \<open>(A', rhs') \<in> P\<close>
    and \<open>take (length U + length rhs + k) (U @ rhs @ V) =
         take (length U + length rhs + k) (U' @ rhs' @ V')\<close>
  shows \<open>U' = U\<close> and \<open>A' = A\<close> and \<open>rhs' = rhs\<close>
  using assms unfolding lrk_def by blast+

theorem lrk_handle_unique:
  assumes \<open>lrk P St k\<close>
    and \<open>handle P St w pr pos\<close> and \<open>handle P St w pr' pos'\<close>
  shows \<open>pr' = pr\<close> and \<open>pos' = pos\<close>
proof -
  from assms(2) obtain U V where w: \<open>w = U @ snd pr @ V\<close> and U: \<open>length U = pos\<close>
    and V: \<open>Nts_syms V = {}\<close> and P: \<open>(fst pr, snd pr) \<in> P\<close> and d: \<open>P \<turnstile> [Nt St] \<Rightarrow>r* U @ Nt (fst pr) # V\<close>
    unfolding handle_def by auto
  from assms(3) obtain U' V' where w': \<open>w = U' @ snd pr' @ V'\<close> and U': \<open>length U' = pos'\<close>
    and V': \<open>Nts_syms V' = {}\<close> and P': \<open>(fst pr', snd pr') \<in> P\<close> and d': \<open>P \<turnstile> [Nt St] \<Rightarrow>r* U' @ Nt (fst pr') # V'\<close>
    unfolding handle_def by auto
  have \<open>take (length U + length (snd pr) + k) (U @ snd pr @ V) =
        take (length U + length (snd pr) + k) (U' @ snd pr' @ V')\<close>
    using w w' by simp
  from lrkD[OF assms(1) d V P d' V' P' this] show \<open>pr' = pr\<close> \<open>pos' = pos\<close>
    by (simp_all add: prod_eq_iff U[symmetric] U'[symmetric])
qed


subsection \<open>Correctness of Algorithm 8: the canonical stack\<close>

text \<open>
  The canonical machine stack of a \<^emph>\<open>viable prefix\<close>
  \<^text>\<open>\<gamma>\<close>: \<^text>\<open>lrstate P k I \<gamma>\<close> is the kernel item set
  reached from the initial kernel \<^text>\<open>I\<close> by GOTO along
  \<^text>\<open>\<gamma>\<close>, on closures, and \<^text>\<open>lr_frames\<close> is the stack
  holding the states of all prefixes of \<^text>\<open>\<gamma>\<close>, that of
  \<^text>\<open>\<gamma>\<close> itself on top. Every reachable configuration of Algorithm 8
  has this shape.
\<close>

definition lrstate :: \<open>('nn, 'tt) Prods \<Rightarrow> nat \<Rightarrow>
    ('nn, 'tt) item set \<Rightarrow> ('nn, 'tt) syms \<Rightarrow> ('nn, 'tt) item set\<close> where
  \<open>lrstate P k I \<gamma> = fold (\<lambda>Z S. igoto (iclosure P k S) Z) \<gamma> I\<close>

lemma lrstate_Nil[simp]: \<open>lrstate P k I [] = I\<close>
  unfolding lrstate_def by simp

lemma lrstate_snoc[simp]:
  \<open>lrstate P k I (\<gamma> @ [Z]) = igoto (iclosure P k (lrstate P k I \<gamma>)) Z\<close>
  unfolding lrstate_def by simp

definition lr_frames :: \<open>('nn, 'tt) Prods \<Rightarrow> nat \<Rightarrow>
    ('nn, 'tt) item set \<Rightarrow> ('nn, 'tt) syms \<Rightarrow> ('nn, 'tt) item set list\<close> where
  \<open>lr_frames P k I \<gamma> = map (\<lambda>j. lrstate P k I (take j \<gamma>)) (rev [0..<Suc (length \<gamma>)])\<close>

lemma lr_frames_Nil[simp]: \<open>lr_frames P k I [] = [I]\<close>
  unfolding lr_frames_def by simp

lemma lr_frames_length[simp]: \<open>length (lr_frames P k I \<gamma>) = Suc (length \<gamma>)\<close>
  unfolding lr_frames_def by simp

lemma lr_frames_ne[simp]: \<open>lr_frames P k I \<gamma> \<noteq> []\<close>
  unfolding lr_frames_def by simp

lemma lr_frames_hd[simp]: \<open>hd (lr_frames P k I \<gamma>) = lrstate P k I \<gamma>\<close>
  unfolding lr_frames_def by (simp add: hd_map)

lemma lr_frames_snoc[simp]:
  \<open>lr_frames P k I (\<gamma> @ [Z]) =
   igoto (iclosure P k (lrstate P k I \<gamma>)) Z # lr_frames P k I \<gamma>\<close>
proof -
  have \<open>rev [0..<Suc (length (\<gamma> @ [Z]))] =
        Suc (length \<gamma>) # rev [0..<Suc (length \<gamma>)]\<close> by simp
  moreover have \<open>take j (\<gamma> @ [Z]) = take j \<gamma>\<close> if \<open>j \<in> set (rev [0..<Suc (length \<gamma>)])\<close> for j
    using that by auto
  ultimately show ?thesis
    unfolding lr_frames_def by simp
qed

lemma lr_frames_nth:
  \<open>j \<le> length \<gamma> \<Longrightarrow> lr_frames P k I \<gamma> ! j = lrstate P k I (take (length \<gamma> - j) \<gamma>)\<close>
  by (simp add: lr_frames_def rev_nth del: upt_Suc)

lemma lr_frames_drop:
  \<open>j \<le> length \<gamma> \<Longrightarrow> drop j (lr_frames P k I \<gamma>) = lr_frames P k I (take (length \<gamma> - j) \<gamma>)\<close>
proof (induction \<gamma> arbitrary: j rule: rev_induct)
  case (snoc Z \<gamma>)
  thus ?case by (cases j) auto
qed simp


text \<open>
  The invariant of canonical stacks: every item in the closure of the state of
  \<^text>\<open>\<gamma>\<close> has its production in the augmented production set
  \<^text>\<open>Q = insert (Sh, [Nt St]) P\<close>, has its dot inside its right-hand
  side, and (the part soundness rests on) has its pre-dot part equal to the
  corresponding suffix of \<^text>\<open>\<gamma>\<close>.
\<close>

definition items_ok :: \<open>('nn, 'tt) Prods \<Rightarrow>
    ('nn, 'tt) syms \<Rightarrow> ('nn, 'tt) item set \<Rightarrow> bool\<close> where
  \<open>items_ok Q \<gamma> S \<longleftrightarrow> (\<forall>A rhs m u. ((A, rhs), m, u) \<in> S \<longrightarrow>
     (A, rhs) \<in> Q \<and> m \<le> length rhs \<and> m \<le> length \<gamma> \<and>
     drop (length \<gamma> - m) \<gamma> = take m rhs)\<close>

lemma items_okD:
  \<open>items_ok Q \<gamma> S \<Longrightarrow> ((A, rhs), m, u) \<in> S \<Longrightarrow>
   (A, rhs) \<in> Q \<and> m \<le> length rhs \<and> m \<le> length \<gamma> \<and>
   drop (length \<gamma> - m) \<gamma> = take m rhs\<close>
  unfolding items_ok_def by blast

text \<open>Whatever the closure adds is a dot-0 item for a production of
  \<^text>\<open>P\<close>.\<close>

lemma iclosure_subset_cases:
  assumes \<open>it \<in> iclosure P k S\<close>
  obtains \<open>it \<in> S\<close> | B rhs\<^sub>B v where \<open>it = ((B, rhs\<^sub>B), 0, v)\<close> and \<open>(B, rhs\<^sub>B) \<in> P\<close>
  using assms by (cases rule: iclosure.cases) auto

lemma items_ok_iclosure:
  assumes \<open>items_ok Q \<gamma> S\<close> and \<open>P \<subseteq> Q\<close>
  shows \<open>items_ok Q \<gamma> (iclosure P k S)\<close>
  using assms unfolding items_ok_def by (auto elim!: iclosure_subset_cases)

lemma items_ok_igoto:
  assumes \<open>items_ok Q \<gamma> S\<close>
  shows \<open>items_ok Q (\<gamma> @ [Z]) (igoto S Z)\<close>
  unfolding items_ok_def
proof (intro allI impI)
  fix A rhs m u assume \<open>((A, rhs), m, u) \<in> igoto S Z\<close>
  then obtain m' where m: \<open>m = Suc m'\<close> and \<open>((A, rhs), m', u) \<in> S\<close>
    and lt: \<open>m' < length rhs\<close> and Z: \<open>rhs ! m' = Z\<close>
    unfolding igoto_def by blast
  from items_okD[OF assms this(2)] lt Z
  show \<open>(A, rhs) \<in> Q \<and> m \<le> length rhs \<and> m \<le> length (\<gamma> @ [Z]) \<and>
        drop (length (\<gamma> @ [Z]) - m) (\<gamma> @ [Z]) = take m rhs\<close>
    by (simp add: m take_Suc_conv_app_nth)
qed

lemma items_ok_init:
  \<open>items_ok (insert (Sh, [Nt St]) P) [] {init_item Sh St dm k}\<close>
  unfolding items_ok_def init_item_def by auto

lemma items_ok_lrstate:
  assumes \<open>items_ok Q [] I\<close> and \<open>P \<subseteq> Q\<close>
  shows \<open>items_ok Q \<gamma> (lrstate P k I \<gamma>)\<close>
proof (induction \<gamma> rule: rev_induct)
  case (snoc Z \<gamma>)
  show ?case unfolding lrstate_snoc by (intro items_ok_igoto items_ok_iclosure snoc.IH assms(2))
qed (simp add: assms(1))

lemma items_ok_closure_lrstate:
  \<open>items_ok (insert (Sh, [Nt St]) P) \<gamma>
     (iclosure P k (lrstate P k {init_item Sh St dm k} \<gamma>))\<close>
  by (intro items_ok_iclosure items_ok_lrstate items_ok_init subset_insertI)

text \<open>
  Freshness of the auxiliary start symbol \<^text>\<open>Sh\<close>: it heads no
  production of \<^text>\<open>P\<close>, occurs in no right-hand side, and differs from
  the start symbol. Under freshness, items for the augmented production
  \<^text>\<open>Sh \<rightarrow> St\<close> occur only in the two canonical places, dot 0 in
  the initial state and dot 1 in the state of \<^text>\<open>[Nt St]\<close>.
\<close>

definition fresh_start :: \<open>('nn, 'tt) Prods \<Rightarrow> 'nn \<Rightarrow> 'nn \<Rightarrow> bool\<close> where
  \<open>fresh_start P Sh St \<longleftrightarrow> Sh \<notin> Nts P \<and> Sh \<noteq> St\<close>

lemma fresh_startD:
  assumes \<open>fresh_start P Sh St\<close>
  shows \<open>Sh \<notin> fst ` P\<close>
    and \<open>(A, rhs) \<in> P \<Longrightarrow> Nt Sh \<notin> set rhs\<close>
    and \<open>Sh \<noteq> St\<close>
  using assms unfolding fresh_start_def Nts_def Nts_syms_def by force+

lemma iclosure_sh:
  assumes \<open>Sh \<notin> fst ` P\<close> and \<open>((Sh, srhs), m, u) \<in> iclosure P k S\<close>
  shows \<open>((Sh, srhs), m, u) \<in> S\<close>
  using assms(2) by (cases rule: iclosure_subset_cases) (use assms(1) in force)+

lemma lrstate_sh:
  assumes \<open>Sh \<notin> fst ` P\<close>
    and \<open>((Sh, srhs), m, u) \<in> iclosure P k (lrstate P k {init_item Sh St dm k} \<gamma>)\<close>
  shows \<open>srhs = [Nt St] \<and> (m = 0 \<and> \<gamma> = [] \<or> m = 1 \<and> \<gamma> = [Nt St])\<close>
  using assms(2)
proof (induction \<gamma> arbitrary: m u rule: rev_induct)
  case Nil
  from iclosure_sh[OF assms(1) Nil.prems] show ?case unfolding init_item_def by auto
next
  case (snoc Z \<gamma>)
  from iclosure_sh[OF assms(1) snoc.prems] obtain m' where \<open>m = Suc m'\<close>
    and \<open>((Sh, srhs), m', u) \<in> iclosure P k (lrstate P k {init_item Sh St dm k} \<gamma>)\<close>
    and \<open>m' < length srhs\<close> and \<open>srhs ! m' = Z\<close>
    unfolding lrstate_snoc igoto_def by blast
  with snoc.IH[OF this(2)] show ?case by auto
qed

text \<open>Derivations in the augmented grammar that start below
  \<^text>\<open>Sh\<close> never use the augmented production. Freshness gives the
  disjointness of \<^text>\<open>Sh\<close> from the left-hand sides of \<^text>\<open>P\<close>
  that \<^text>\<open>derives_Un_disj_Lhss\<close> asks for.\<close>

lemma derives_fresh_elim:
  assumes \<open>insert (Sh, [Nt St]) P \<turnstile> u \<Rightarrow>* v\<close> and \<open>Nt Sh \<notin> set u\<close> and \<open>fresh_start P Sh St\<close>
  shows \<open>P \<turnstile> u \<Rightarrow>* v\<close>
proof -
  have \<open>P \<union> {(Sh, [Nt St])} \<turnstile> u \<Rightarrow>* v \<longleftrightarrow> P \<turnstile> u \<Rightarrow>* v\<close>
    using assms(2,3) by (intro derives_Un_disj_Lhss) (auto simp: fresh_start_def Nts_Lhss_Rhs_Nts Nts_syms_def)
  with assms(1) show ?thesis by auto
qed


text \<open>
  Every reachable configuration of Algorithm 8 is the canonical stack of some
  viable prefix \<^text>\<open>\<gamma>\<close>, and \<^text>\<open>\<gamma>\<close> derives the consumed
  input in the augmented grammar. Soundness follows: at acceptance, freshness
  pins \<^text>\<open>\<gamma>\<close> to \<^text>\<open>[Nt St]\<close>.
\<close>

lemma lr_run_frames:
  assumes \<open>(lr_step P k)\<^sup>*\<^sup>* ([{init_item Sh St dm k}], w\<^sub>0) (Ss, v)\<close>
  shows \<open>\<exists>\<gamma> c. Ss = lr_frames P k {init_item Sh St dm k} \<gamma> \<and> w\<^sub>0 = c @ v \<and>
               insert (Sh, [Nt St]) P \<turnstile> \<gamma> \<Rightarrow>* map Tm c\<close>
  using assms
proof (induction rule: rtranclp_induct2)
  case refl
  thus ?case by (intro exI[of _ \<open>[]\<close>]) simp
next
  case (step Ss\<^sub>1 v\<^sub>1 Ss\<^sub>2 v\<^sub>2)
  from step.IH obtain \<gamma> c where Ss\<^sub>1: \<open>Ss\<^sub>1 = lr_frames P k {init_item Sh St dm k} \<gamma>\<close>
    and w\<^sub>0: \<open>w\<^sub>0 = c @ v\<^sub>1\<close> and d: \<open>insert (Sh, [Nt St]) P \<turnstile> \<gamma> \<Rightarrow>* map Tm c\<close> by blast
  from step.hyps(2) show ?case
  proof (cases rule: lr_step.cases)
    case (lr_shift t)
    hence \<open>Ss\<^sub>2 = lr_frames P k {init_item Sh St dm k} (\<gamma> @ [Tm t])\<close> by (simp add: Ss\<^sub>1)
    moreover have \<open>insert (Sh, [Nt St]) P \<turnstile> \<gamma> @ [Tm t] \<Rightarrow>* map Tm (c @ [t])\<close>
      using derives_append[OF d, of \<open>[Tm t]\<close>] by simp
    moreover have \<open>w\<^sub>0 = (c @ [t]) @ v\<^sub>2\<close> using w\<^sub>0 lr_shift(1) by simp
    ultimately show ?thesis by blast
  next
    case (lr_reduce A rhs)
    let ?\<gamma>\<^sub>0 = \<open>take (length \<gamma> - length rhs) \<gamma>\<close>
    have \<open>((A, rhs), length rhs, take k v\<^sub>1) \<in> iclosure P k (lrstate P k {init_item Sh St dm k} \<gamma>)\<close>
      using lr_reduce(4) by (simp add: Ss\<^sub>1 Kprod_iff)
    from items_okD[OF items_ok_closure_lrstate this]
    have QA: \<open>(A, rhs) \<in> insert (Sh, [Nt St]) P\<close> and mle: \<open>length rhs \<le> length \<gamma>\<close>
      and \<open>drop (length \<gamma> - length rhs) \<gamma> = rhs\<close>
      by auto
    hence \<gamma>: \<open>\<gamma> = ?\<gamma>\<^sub>0 @ rhs\<close> by (metis append_take_drop_id)

    have \<open>insert (Sh, [Nt St]) P \<turnstile> ?\<gamma>\<^sub>0 @ [Nt A] \<Rightarrow> \<gamma>\<close>
      using derive.intros[OF QA, of ?\<gamma>\<^sub>0 \<open>[]\<close>] by (simp add: \<gamma>[symmetric])
    hence \<open>insert (Sh, [Nt St]) P \<turnstile> ?\<gamma>\<^sub>0 @ [Nt A] \<Rightarrow>* map Tm c\<close>
      using d by (rule converse_rtranclp_into_rtranclp)
    moreover have \<open>Ss\<^sub>2 = lr_frames P k {init_item Sh St dm k} (?\<gamma>\<^sub>0 @ [Nt A])\<close>
      using lr_reduce(1) lr_frames_nth[OF mle] lr_frames_drop[OF mle] by (simp add: Ss\<^sub>1)
    ultimately show ?thesis using w\<^sub>0 lr_reduce(2) by blast
  qed
qed

theorem lr_sound:
  assumes fresh: \<open>fresh_start P Sh St\<close> and \<open>lr_accepts P k Sh St dm w\<close>
  shows \<open>P \<turnstile> [Nt St] \<Rightarrow>* map Tm w\<close>
proof -
  from assms(2) obtain Ss u where
    run: \<open>(lr_step P k)\<^sup>*\<^sup>* ([{init_item Sh St dm k}], w @ replicate k dm) (Ss, replicate k dm)\<close>
    and item: \<open>((Sh, [Nt St]), Suc 0, u) \<in> hd Ss\<close>
    unfolding lr_accepts_def by blast
  from lr_run_frames[OF run] obtain \<gamma> where
    Ss: \<open>Ss = lr_frames P k {init_item Sh St dm k} \<gamma>\<close> and d: \<open>insert (Sh, [Nt St]) P \<turnstile> \<gamma> \<Rightarrow>* map Tm w\<close>
    by auto
  from item have \<open>((Sh, [Nt St]), Suc 0, u) \<in> iclosure P k (lrstate P k {init_item Sh St dm k} \<gamma>)\<close>
    by (simp add: Ss iclosure_base)
  from lrstate_sh[OF fresh_startD(1)[OF fresh] this] have \<open>\<gamma> = [Nt St]\<close> by simp
  with d fresh_startD(3)[OF fresh] show ?thesis by (auto intro: derives_fresh_elim[OF _ _ fresh])
qed


text \<open>
  Completeness. Items travel along the canonical stack by dot advancement: an
  item in the closure of the state of \<^text>\<open>\<gamma>\<close> with
  \<^text>\<open>Z\<close> after the dot reappears, dot advanced, in the state of
  \<^text>\<open>\<gamma>Z\<close>.
\<close>

lemma lrstate_dot_advance:
  assumes \<open>((A, rhs), m, u) \<in> iclosure P k (lrstate P k I \<gamma>)\<close>
    and \<open>m < length rhs\<close>
  shows \<open>((A, rhs), Suc m, u) \<in> lrstate P k I (\<gamma> @ [rhs ! m])\<close>
  unfolding lrstate_snoc igoto_def using assms by blast

lemma lrstate_dot_advance_many:
  assumes \<open>((A, rhs), m, u) \<in> iclosure P k (lrstate P k I \<gamma>)\<close> and \<open>m + j \<le> length rhs\<close>
  shows \<open>((A, rhs), m + j, u) \<in> iclosure P k (lrstate P k I (\<gamma> @ take j (drop m rhs)))\<close>
  using assms
proof (induction j)
  case (Suc j)
  have lt: \<open>m + j < length rhs\<close> using Suc.prems(2) by simp
  from lrstate_dot_advance[OF Suc.IH[OF Suc.prems(1)] lt] Suc.prems(2)
  have \<open>((A, rhs), Suc (m + j), u) \<in> lrstate P k I ((\<gamma> @ take j (drop m rhs)) @ [rhs ! (m + j)])\<close> by simp
  moreover have \<open>take (Suc j) (drop m rhs) = take j (drop m rhs) @ [rhs ! (m + j)]\<close>
    using lt by (simp add: take_Suc_conv_app_nth)
  ultimately show ?case by (simp add: iclosure_base)
qed simp

text \<open>A reduce over the last \<open>\<xi>\<close> frames of a canonical stack lands on the
  canonical stack of the prefix extended by the reduced non-terminal.\<close>

lemma lr_frames_reduce:
  assumes \<open>take k w \<in> Kprod (iclosure P k (hd (lr_frames P k I (\<gamma> @ \<xi>)))) (C, \<xi>)\<close>
  shows \<open>lr_step P k (lr_frames P k I (\<gamma> @ \<xi>), w) (lr_frames P k I (\<gamma> @ [Nt C]), w)\<close>
  using lr_step.lr_reduce[OF lr_frames_ne assms] lr_frames_nth[of \<open>length \<xi>\<close> \<open>\<gamma> @ \<xi>\<close>]
    lr_frames_drop[of \<open>length \<xi>\<close> \<open>\<gamma> @ \<xi>\<close>]
  by simp

text \<open>
  The run-construction lemma behind completeness: if the part of an item's
  right-hand side behind the dot derives a terminal word \<^text>\<open>ys\<close>, and
  the item's lookahead is the padded input continuation after
  \<^text>\<open>ys\<close>, then the machine can consume \<^text>\<open>ys\<close>, building
  those symbols on the stack. All intermediate items arise by closure steps and
  dot advancement, so the non-deterministic machine needs no separate
  viable-prefix argument. The induction is on the derivation length, with an
  inner induction on the symbol list.
\<close>

lemma lr_run_build:
  assumes \<open>P \<turnstile> \<beta> \<Rightarrow>(n) map Tm ys\<close>
    and \<open>((A, rhs), m, u) \<in> iclosure P k (lrstate P k I \<gamma>)\<close>
    and \<open>drop m rhs = \<beta>\<close>
    and \<open>u = take k zs\<close> and \<open>k \<le> length zs\<close>
  shows \<open>(lr_step P k)\<^sup>*\<^sup>* (lr_frames P k I \<gamma>, ys @ zs) (lr_frames P k I (\<gamma> @ \<beta>), zs)\<close>
  using assms
proof (induction n arbitrary: \<beta> ys \<gamma> A rhs m u zs rule: less_induct)
  case (less n)
  have inner: \<open>(lr_step P k)\<^sup>*\<^sup>* (lr_frames P k I \<gamma>', ys' @ zs') (lr_frames P k I (\<gamma>' @ \<beta>'), zs')\<close>
    if \<open>n' \<le> n\<close> and \<open>P \<turnstile> \<beta>' \<Rightarrow>(n') map Tm ys'\<close>
      and \<open>((A', rhs'), m', u') \<in> iclosure P k (lrstate P k I \<gamma>')\<close>
      and \<open>drop m' rhs' = \<beta>'\<close> and \<open>u' = take k zs'\<close> and \<open>k \<le> length zs'\<close>
    for n' \<beta>' ys' \<gamma>' A' rhs' m' u' zs'
    using that
  proof (induction \<beta>' arbitrary: n' ys' \<gamma>' A' rhs' m' u' zs')
    case Nil
    thus ?case using deriven_from_empty by fastforce
  next
    case (Cons Z \<beta>\<^sub>2)
    have \<open>P \<turnstile> [Z] @ \<beta>\<^sub>2 \<Rightarrow>(n') map Tm ys'\<close> using Cons.prems(2) by simp
    then obtain n\<^sub>1 n\<^sub>2 ys\<^sub>1 ys\<^sub>2 where n: \<open>n' = n\<^sub>1 + n\<^sub>2\<close> and ys: \<open>ys' = ys\<^sub>1 @ ys\<^sub>2\<close>
      and d\<^sub>1: \<open>P \<turnstile> [Z] \<Rightarrow>(n\<^sub>1) map Tm ys\<^sub>1\<close> and d\<^sub>2: \<open>P \<turnstile> \<beta>\<^sub>2 \<Rightarrow>(n\<^sub>2) map Tm ys\<^sub>2\<close>
      unfolding deriven_appendD by (auto simp: map_eq_append_conv)
    note dZ = drop_eq_ConsD[OF Cons.prems(4)]
    have d2r: \<open>P \<turnstile> \<beta>\<^sub>2 \<Rightarrow>* map Tm ys\<^sub>2\<close> using d\<^sub>2 by (rule relpowp_imp_rtranclp)
    have n\<^sub>2: \<open>n\<^sub>2 \<le> n\<close> using n Cons.prems(1) by simp
    have kys: \<open>k \<le> length (ys\<^sub>2 @ zs')\<close> using Cons.prems(6) by simp
    show ?case
    proof (cases Z)
      case (Tm t)
      with d\<^sub>1 have ys\<^sub>1: \<open>ys\<^sub>1 = [t]\<close> by (auto simp: deriven_Tm_Cons map_eq_Cons_conv)
      have Xd: \<open>P \<turnstile> drop m' rhs' \<Rightarrow>* map Tm (t # ys\<^sub>2)\<close>
        using derives_prepend[OF d2r, of \<open>[Tm t]\<close>] Cons.prems(4) Tm by simp
      have \<open>take k ((t # ys\<^sub>2) @ zs') \<in> Hk P k (drop m' rhs' @ map Tm u')\<close>
        using Hk_take_appendI[OF Xd Cons.prems(6)] Cons.prems(5) by simp
      hence \<open>take k (t # ys\<^sub>2 @ zs') \<in> Kset P k (iclosure P k (hd (lr_frames P k I \<gamma>')))\<close>
        using Cons.prems(3) unfolding Kset_def by fastforce
      from lr_step.lr_shift[OF lr_frames_ne this]
      have \<open>lr_step P k (lr_frames P k I \<gamma>', t # (ys\<^sub>2 @ zs')) (lr_frames P k I (\<gamma>' @ [Tm t]), ys\<^sub>2 @ zs')\<close>
        by simp
      moreover have \<open>((A', rhs'), Suc m', u') \<in> iclosure P k (lrstate P k I (\<gamma>' @ [Tm t]))\<close>
        using lrstate_dot_advance[OF Cons.prems(3) dZ(1)] dZ(2) Tm by (simp add: iclosure_base)
      hence \<open>(lr_step P k)\<^sup>*\<^sup>* (lr_frames P k I (\<gamma>' @ [Tm t]), ys\<^sub>2 @ zs')
              (lr_frames P k I ((\<gamma>' @ [Tm t]) @ \<beta>\<^sub>2), zs')\<close>
        by (rule Cons.IH[OF n\<^sub>2 d\<^sub>2 _ dZ(3) Cons.prems(5,6)])
      ultimately show ?thesis unfolding ys ys\<^sub>1 Tm by (auto intro: converse_rtranclp_into_rtranclp)
    next
      case (Nt C)
      with d\<^sub>1 have d\<^sub>1': \<open>P \<turnstile> [Nt C] \<Rightarrow>(n\<^sub>1) map Tm ys\<^sub>1\<close> by simp
      obtain n\<^sub>1' \<xi> where n\<^sub>1: \<open>n\<^sub>1 = Suc n\<^sub>1'\<close> and C\<xi>: \<open>(C, \<xi>) \<in> P\<close> and d\<xi>: \<open>P \<turnstile> \<xi> \<Rightarrow>(n\<^sub>1') map Tm ys\<^sub>1\<close>
      proof (cases n\<^sub>1)
        case (Suc m)
        from relpowp_Suc_D2[OF d\<^sub>1'[unfolded Suc]] show ?thesis using that Suc by (auto simp: derive_singleton)
      qed (use d\<^sub>1' in auto)
      have \<open>take k (ys\<^sub>2 @ zs') \<in> Hk P k (drop (Suc m') rhs' @ map Tm u')\<close>
        using Hk_take_appendI[OF d2r Cons.prems(6)] Cons.prems(5) dZ(3) by simp
      with Cons.prems(3) dZ(1,2) Nt C\<xi>
      have Citem: \<open>((C, \<xi>), 0, take k (ys\<^sub>2 @ zs')) \<in> iclosure P k (lrstate P k I \<gamma>')\<close>
        by (auto intro: iclosure_step)
      have run\<xi>: \<open>(lr_step P k)\<^sup>*\<^sup>* (lr_frames P k I \<gamma>', ys\<^sub>1 @ (ys\<^sub>2 @ zs'))
                  (lr_frames P k I (\<gamma>' @ \<xi>), ys\<^sub>2 @ zs')\<close>
        using less.IH[OF _ d\<xi> Citem, where zs = \<open>ys\<^sub>2 @ zs'\<close>] n n\<^sub>1 Cons.prems(1) kys by simp
      have \<open>take k (ys\<^sub>2 @ zs') \<in> Kprod (iclosure P k (hd (lr_frames P k I (\<gamma>' @ \<xi>)))) (C, \<xi>)\<close>
        using lrstate_dot_advance_many[OF Citem, of \<open>length \<xi>\<close>] by (simp add: Kprod_iff)
      hence red: \<open>lr_step P k (lr_frames P k I (\<gamma>' @ \<xi>), ys\<^sub>2 @ zs') (lr_frames P k I (\<gamma>' @ [Nt C]), ys\<^sub>2 @ zs')\<close>
        by (rule lr_frames_reduce)
      have \<open>((A', rhs'), Suc m', u') \<in> iclosure P k (lrstate P k I (\<gamma>' @ [Nt C]))\<close>
        using lrstate_dot_advance[OF Cons.prems(3) dZ(1)] dZ(2) Nt by (simp add: iclosure_base)
      hence rest: \<open>(lr_step P k)\<^sup>*\<^sup>* (lr_frames P k I (\<gamma>' @ [Nt C]), ys\<^sub>2 @ zs')
                   (lr_frames P k I ((\<gamma>' @ [Nt C]) @ \<beta>\<^sub>2), zs')\<close>
        by (rule Cons.IH[OF n\<^sub>2 d\<^sub>2 _ dZ(3) Cons.prems(5,6)])
      show ?thesis
        using rtranclp_trans[OF run\<xi> converse_rtranclp_into_rtranclp[OF red rest]] unfolding ys Nt by simp
    qed
  qed
  show ?case by (rule inner[OF order.refl less.prems])
qed

theorem lr_complete:
  assumes \<open>P \<turnstile> [Nt St] \<Rightarrow>* map Tm w\<close>
  shows \<open>lr_accepts P k Sh St dm w\<close>
proof -
  from assms obtain n where \<open>P \<turnstile> [Nt St] \<Rightarrow>(n) map Tm w\<close> by (metis rtranclp_imp_relpowp)
  moreover have \<open>((Sh, [Nt St]), 0, replicate k dm) \<in> iclosure P k (lrstate P k {init_item Sh St dm k} [])\<close>
    by (simp add: iclosure_base init_item_def)
  ultimately have \<open>(lr_step P k)\<^sup>*\<^sup>* (lr_frames P k {init_item Sh St dm k} [], w @ replicate k dm)
      (lr_frames P k {init_item Sh St dm k} ([] @ [Nt St]), replicate k dm)\<close>
    by (rule lr_run_build) simp_all
  moreover have \<open>((Sh, [Nt St]), Suc 0, replicate k dm) \<in> hd (lr_frames P k {init_item Sh St dm k} [Nt St])\<close>
    by (force simp: lrstate_def igoto_def init_item_def intro: iclosure_base)
  ultimately show ?thesis unfolding lr_accepts_def by fastforce
qed

theorem lr_accepts_iff:
  assumes \<open>fresh_start P Sh St\<close>
  shows \<open>lr_accepts P k Sh St dm w \<longleftrightarrow> P \<turnstile> [Nt St] \<Rightarrow>* map Tm w\<close>
  by (auto intro: lr_sound[OF assms] lr_complete)


text \<open>
  Instantiation at the infinite II-CFG: a fresh non-terminal name yields fresh
  annotated start symbols, so Algorithm 8 over \<^term>\<open>infG G\<close> accepts the
  language of the IS-grammar \<^term>\<open>G\<close>, for every lookahead length
  \<^text>\<open>k\<close> and any end marker. This is the LR(k) correctness theorem for
  indentation-sensitive grammars that the paper cites to Knuth.
\<close>

definition fresh_name :: \<open>('n, 'tok) is_cfg \<Rightarrow> 'n \<Rightarrow> bool\<close> where
  \<open>fresh_name G Shn \<longleftrightarrow> Shn \<noteq> istart G \<and> Shn \<notin> fst ` set (iprods G) \<and>
     (\<forall>(A, rhs) \<in> set (iprods G). \<forall>(X, r) \<in> set rhs. X \<noteq> Nt Shn)\<close>

lemma fresh_start_infG:
  assumes \<open>fresh_name G Shn\<close>
  shows \<open>fresh_start (infG G) (Shn, i\<^sub>0) (istart G, istart_ind G)\<close>
proof -
  have \<open>(Shn, i\<^sub>0) \<notin> fst ` infG G\<close> using assms unfolding fresh_name_def infG_def by force
  moreover have \<open>Nt (Shn, i\<^sub>0) \<notin> set rhs\<^sub>B\<close> if \<open>(B, rhs\<^sub>B) \<in> infG G\<close> for B rhs\<^sub>B
  proof
    assume \<open>Nt (Shn, i\<^sub>0) \<in> set rhs\<^sub>B\<close>
    hence \<open>Nt Shn \<in> set (map unann rhs\<^sub>B)\<close> by force
    moreover from that obtain A rhs where \<open>(A, rhs) \<in> set (iprods G)\<close> \<open>map unann rhs\<^sub>B = map fst rhs\<close>
      by (cases B) (auto simp: infG_alt dest: annotates_unann)
    ultimately show False using assms unfolding fresh_name_def by fastforce
  qed
  moreover have \<open>(Shn, i\<^sub>0) \<noteq> (istart G, istart_ind G)\<close> using assms unfolding fresh_name_def by auto
  ultimately show ?thesis unfolding fresh_start_def Nts_def Nts_syms_def by force
qed

theorem lr_lang:
  assumes \<open>fresh_name G Shn\<close>
  shows \<open>lr_accepts (infG G) k (Shn, istart_ind G) (istart G, istart_ind G) dm (tcols w)
         \<longleftrightarrow> w \<in> ilang G\<close>
  using lr_accepts_iff[OF fresh_start_infG[OF assms]] by (simp add: ilang_derives)


subsection \<open>An executable GLR machine (k = 0)\<close>

text \<open>
  The GLR parser at the end of Sect. 5.5, made executable: an item is a triple
  of an original production, a dot, and an indentation set represented by
  \<^typ>\<open>indrep\<close>, the lookahead component being trivial at
  \<^text>\<open>k = 0\<close>. Two further executable operations on
  \<^typ>\<open>indrep\<close> are needed, non-emptiness and inclusion.
\<close>

fun irep_nonempty :: \<open>indrep \<Rightarrow> bool\<close> where
  \<open>irep_nonempty (FinRep xs) = (xs \<noteq> [])\<close>
| \<open>irep_nonempty (UpRep xs n) = True\<close>

lemma irep_nonempty_correct[simp]: \<open>irep_nonempty R \<longleftrightarrow> irep_set R \<noteq> {}\<close>
  by (cases R) auto

fun irep_subset :: \<open>indrep \<Rightarrow> indrep \<Rightarrow> bool\<close> where
  \<open>irep_subset (FinRep xs) R = list_all (\<lambda>i. irep_mem i R) xs\<close>
| \<open>irep_subset (UpRep xs n) (FinRep ys) = False\<close>
| \<open>irep_subset (UpRep xs n) (UpRep ys m) =
    (list_all (\<lambda>i. irep_mem i (UpRep ys m)) xs \<and> list_all (\<lambda>i. i \<in> set ys) [n..<m])\<close>

lemma irep_subset_correct[simp]:
  \<open>irep_subset R\<^sub>1 R\<^sub>2 \<longleftrightarrow> irep_set R\<^sub>1 \<subseteq> irep_set R\<^sub>2\<close>
proof (cases R\<^sub>1)
  case R\<^sub>1: (UpRep xs n)
  show ?thesis
  proof (cases R\<^sub>2)
    case (FinRep ys)
    have \<open>\<not> irep_set R\<^sub>1 \<subseteq> irep_set R\<^sub>2\<close>
      using infinite_Ici[of n] unfolding R\<^sub>1 FinRep
      by (auto simp: atLeast_def dest!: finite_subset[of \<open>{m. n \<le> m}\<close>])
    with R\<^sub>1 FinRep show ?thesis by simp
  next
    case (UpRep ys m)
    show ?thesis unfolding R\<^sub>1 UpRep by (auto simp: list_all_iff not_le)
  qed
qed (auto simp: list_all_iff)

type_synonym ('n, 'tok) xitem = \<open>('n \<times> ('n, 'tok) rhs) \<times> nat \<times> indrep\<close>

definition xconc :: \<open>('n, 'tok) xitem \<Rightarrow> ('n, 'tok) fitem\<close> where
  \<open>xconc xit = (case xit of (pr, m, R) \<Rightarrow> (pr, m, irep_set R \<times> {[]}))\<close>

definition xset :: \<open>('n, 'tok) xitem list \<Rightarrow> ('n, 'tok) fitem set\<close> where
  \<open>xset xs = xconc ` set xs\<close>

lemma xconc_triple: \<open>xconc (pr, m, R) = (pr, m, irep_set R \<times> {[]})\<close>
  unfolding xconc_def by simp

lemma xset_wf: \<open>list_all (\<lambda>(pr, m, R). m \<le> length (snd pr)) xs \<Longrightarrow> wf_fitems (xset xs)\<close>
  unfolding wf_fitems_def xset_def xconc_def
  by (fastforce simp: list_all_iff)

text \<open>Executable GOTO: advance the dot over \<^text>\<open>X\<close> shifted
  at indentation \<^text>\<open>l\<close>, filtering each indentation set. On
  concretizations this is \<^const>\<open>fgoto\<close>.\<close>

definition xgoto :: \<open>('n, 'tok) xitem list \<Rightarrow> ('n, 'tok) sym \<Rightarrow> nat \<Rightarrow> ('n, 'tok) xitem list\<close> where
  \<open>xgoto xs X l =
     map (\<lambda>(pr, m, R). (pr, Suc m, irep_filter (snd (snd pr ! m)) l R))
       (filter (\<lambda>(pr, m, R). m < length (snd pr) \<and> fst (snd pr ! m) = X) xs)\<close>

lemma xset_xgoto: \<open>xset (xgoto xs X l) = fgoto (xset xs) X l\<close>
proof (intro equalityI subsetI)
  fix fit assume \<open>fit \<in> xset (xgoto xs X l)\<close>
  then obtain A rhs m R where \<open>((A, rhs), m, R) \<in> set xs\<close> \<open>m < length rhs\<close> \<open>fst (rhs ! m) = X\<close>
    and fit: \<open>fit = ((A, rhs), Suc m, irep_set (irep_filter (snd (rhs ! m)) l R) \<times> {[]})\<close>
    unfolding xset_def xgoto_def xconc_def by fastforce
  moreover have \<open>irep_set (irep_filter (snd (rhs ! m)) l R) \<times> {[]} =
                 {(i, u) \<in> irep_set R \<times> {[]}. irel_sat (snd (rhs ! m)) l i}\<close>
    by auto
  moreover have \<open>((A, rhs), m, irep_set R \<times> {[]}) \<in> xset xs\<close>
    using \<open>_ \<in> set xs\<close> unfolding xset_def xconc_def by force
  ultimately show \<open>fit \<in> fgoto (xset xs) X l\<close> unfolding fgoto_def by blast
next
  fix fit assume \<open>fit \<in> fgoto (xset xs) X l\<close>
  then obtain A rhs m R where \<open>((A, rhs), m, R) \<in> set xs\<close> \<open>m < length rhs\<close> \<open>fst (rhs ! m) = X\<close>
    and fit: \<open>fit = ((A, rhs), Suc m, {(i, u) \<in> irep_set R \<times> {[]}. irel_sat (snd (rhs ! m)) l i})\<close>
    unfolding fgoto_def xset_def xconc_def by fastforce
  moreover have L: \<open>{(i, u) \<in> irep_set R \<times> {[]}. irel_sat (snd (rhs ! m)) l i} =
                    irep_set (irep_filter (snd (rhs ! m)) l R) \<times> {[]}\<close>
    by auto
  ultimately show \<open>fit \<in> xset (xgoto xs X l)\<close> unfolding xset_def xgoto_def fit L by (force simp: xconc_def)
qed


text \<open>
  Executable closure. The closure only adds dot-0 items, so one
  indentation set per production of \<^term>\<open>G\<close> suffices, a
  \<^emph>\<open>slot\<close>, ordered as \<^term>\<open>iprods G\<close>. One round adds, for
  every item present, kernel or slot, with \<^text>\<open>Nt B\<close> after the dot, the
  relational image of its indentation set to the slot of every
  \<^text>\<open>B\<close>-production. Instead of proving the fixpoint iteration
  terminating, the machine checks that its result is stable, a stable slot
  assignment concretizing to \<^const>\<open>fclosure\<close>. Sufficient fuel always
  exists because every slot's chain of values stabilizes after finitely many
  rounds.
\<close>

fun ximg :: \<open>'n \<times> ('n, 'tok) rhs \<Rightarrow> ('n, 'tok) xitem \<Rightarrow> nat set\<close> where
  \<open>ximg pr ((A, rhs), m, R) =
     (if m < length rhs \<and> fst (rhs ! m) = Nt (fst pr)
      then {j. \<exists>i \<in> irep_set R. irel_sat (snd (rhs ! m)) j i} else {})\<close>

fun xcontrib :: \<open>'n \<times> ('n, 'tok) rhs \<Rightarrow> ('n, 'tok) xitem \<Rightarrow> indrep \<Rightarrow> indrep\<close> where
  \<open>xcontrib pr ((A, rhs), m, R) acc =
     (if m < length rhs \<and> fst (rhs ! m) = Nt (fst pr)
      then irep_union (irep_img (snd (rhs ! m)) R) acc else acc)\<close>

lemma xcontrib_set: \<open>irep_set (xcontrib pr xit acc) = ximg pr xit \<union> irep_set acc\<close>
  by (induction pr xit acc rule: xcontrib.induct) simp

lemma fold_xcontrib_set:
  \<open>irep_set (fold (xcontrib pr) items acc) =
   irep_set acc \<union> (\<Union> (ximg pr ` set items))\<close>
  by (induction items arbitrary: acc) (auto simp: xcontrib_set)

definition xslots :: \<open>('n, 'tok) is_cfg \<Rightarrow> ('n, 'tok) xitem list \<Rightarrow> indrep list \<Rightarrow>
    ('n, 'tok) xitem list\<close> where
  \<open>xslots G xs cls = xs @ map (\<lambda>(pr, R). (pr, 0, R)) (zip (iprods G) cls)\<close>

lemma xslots_memE:
  assumes \<open>xit \<in> set (xslots G xs cls)\<close>
  obtains \<open>xit \<in> set xs\<close>
    | p where \<open>p < length (iprods G)\<close> and \<open>p < length cls\<close>
        and \<open>xit = (iprods G ! p, 0, cls ! p)\<close>
  using assms unfolding xslots_def
  by (auto simp: in_set_zip)

lemma xslots_kernel: \<open>xit \<in> set xs \<Longrightarrow> xit \<in> set (xslots G xs cls)\<close>
  unfolding xslots_def by simp

lemma xslots_slot:
  \<open>p < length (iprods G) \<Longrightarrow> p < length cls \<Longrightarrow>
   (iprods G ! p, 0, cls ! p) \<in> set (xslots G xs cls)\<close>
  unfolding xslots_def by (force simp: in_set_zip)

definition xround :: \<open>('n, 'tok) is_cfg \<Rightarrow> ('n, 'tok) xitem list \<Rightarrow> indrep list \<Rightarrow> indrep list\<close> where
  \<open>xround G xs cls =
     map (\<lambda>(pr, R). fold (xcontrib pr) (xslots G xs cls) R) (zip (iprods G) cls)\<close>

lemma xround_length:
  \<open>length cls = length (iprods G) \<Longrightarrow> length (xround G xs cls) = length (iprods G)\<close>
  unfolding xround_def by simp

lemma xround_nth:
  assumes \<open>length cls = length (iprods G)\<close> and \<open>p < length (iprods G)\<close>
  shows \<open>xround G xs cls ! p =
         fold (xcontrib (iprods G ! p)) (xslots G xs cls) (cls ! p)\<close>
  using assms unfolding xround_def by simp

fun xiter :: \<open>('n, 'tok) is_cfg \<Rightarrow> ('n, 'tok) xitem list \<Rightarrow> nat \<Rightarrow> indrep list\<close> where
  \<open>xiter G xs 0 = map (\<lambda>_. FinRep []) (iprods G)\<close>
| \<open>xiter G xs (Suc s) = xround G xs (xiter G xs s)\<close>

lemma xiter_length[simp]: \<open>length (xiter G xs s) = length (iprods G)\<close>
  by (induction s) (auto simp: xround_length)

definition xstable :: \<open>('n, 'tok) is_cfg \<Rightarrow> ('n, 'tok) xitem list \<Rightarrow> indrep list \<Rightarrow> bool\<close> where
  \<open>xstable G xs cls \<longleftrightarrow> list_all2 irep_subset (xround G xs cls) cls\<close>

definition xclosure :: \<open>('n, 'tok) is_cfg \<Rightarrow> nat \<Rightarrow> ('n, 'tok) xitem list \<Rightarrow> ('n, 'tok) xitem list\<close> where
  \<open>xclosure G fuel xs = xslots G xs (xiter G xs fuel)\<close>

lemma xstableD:
  assumes \<open>xstable G xs cls\<close> and \<open>length cls = length (iprods G)\<close> and \<open>p < length (iprods G)\<close>
  shows \<open>irep_set (xround G xs cls ! p) \<subseteq> irep_set (cls ! p)\<close>
  using assms unfolding xstable_def by (auto simp: list_all2_conv_all_nth xround_length)


text \<open>Every indentation reaching a slot is justified by an actual
  closure item.\<close>

lemma xiter_sound:
  assumes \<open>p < length (iprods G)\<close> and \<open>j \<in> irep_set (xiter G xs s ! p)\<close>
  shows \<open>\<exists>L. (iprods G ! p, 0, L) \<in> fclosure G 0 (xset xs) \<and> (j, []) \<in> L\<close>
  using assms
proof (induction s arbitrary: p j)
  case (Suc s)
  from Suc.prems have
    \<open>j \<in> irep_set (fold (xcontrib (iprods G ! p)) (xslots G xs (xiter G xs s)) (xiter G xs s ! p))\<close>
    by (simp add: xround_nth)
  then consider \<open>j \<in> irep_set (xiter G xs s ! p)\<close>
    | xit where \<open>xit \<in> set (xslots G xs (xiter G xs s))\<close> \<open>j \<in> ximg (iprods G ! p) xit\<close>
    by (auto simp: fold_xcontrib_set)
  then show ?case
  proof cases
    case 1
    with Suc.IH Suc.prems(1) show ?thesis by blast
  next
    case 2
    obtain A rhs m R where xit: \<open>xit = ((A, rhs), m, R)\<close> by (metis prod.collapse)
    with 2(2) obtain i where m: \<open>m < length rhs\<close> and B: \<open>fst (rhs ! m) = Nt (fst (iprods G ! p))\<close>
      and iR: \<open>i \<in> irep_set R\<close> and sat: \<open>irel_sat (snd (rhs ! m)) j i\<close>
      by (auto split: if_splits)
    have \<open>\<exists>Lp. ((A, rhs), m, Lp) \<in> fclosure G 0 (xset xs) \<and> (i, []) \<in> Lp\<close>
      using 2(1)
    proof (cases rule: xslots_memE)
      case 1
      hence \<open>((A, rhs), m, irep_set R \<times> {[]}) \<in> xset xs\<close> using xit unfolding xset_def xconc_def by force
      with iR show ?thesis by (blast intro: fclosure_base)
    next
      case (2 q)
      with xit have \<open>(A, rhs) = iprods G ! q\<close> \<open>m = 0\<close> \<open>R = xiter G xs s ! q\<close> by auto
      with Suc.IH[OF 2(1)] iR show ?thesis by auto
    qed
    then obtain Lp where Lp: \<open>((A, rhs), m, Lp) \<in> fclosure G 0 (xset xs)\<close> \<open>(i, []) \<in> Lp\<close> by blast
    obtain B rhs\<^sub>B where p: \<open>iprods G ! p = (B, rhs\<^sub>B)\<close> by (metis prod.collapse)
    from nth_mem[OF Suc.prems(1)] B have \<open>(B, rhs\<^sub>B) \<in> set (iprods G)\<close> \<open>fst (rhs ! m) = Nt B\<close>
      by (simp_all add: p)
    from fclosure_step[OF Lp(1) m this(2,1) refl] Lp(2) sat show ?thesis unfolding p by fastforce
  qed
qed simp

text \<open>Conversely, a stable slot assignment covers the whole closure.\<close>

lemma stable_covers:
  assumes st: \<open>xstable G xs cls\<close> and len: \<open>length cls = length (iprods G)\<close>
    and \<open>fit \<in> fclosure G 0 (xset xs)\<close> and \<open>(i, u) \<in> snd (snd fit)\<close>
  shows \<open>\<exists>R. (fst fit, fst (snd fit), R) \<in> set (xslots G xs cls) \<and> i \<in> irep_set R \<and> u = []\<close>
  using assms(3,4)
proof (induction arbitrary: i u rule: fclosure.induct)
  case (fclosure_base fit)
  then obtain xit where xit: \<open>xit \<in> set xs\<close> \<open>fit = xconc xit\<close> unfolding xset_def by blast
  obtain A rhs m R where \<open>xit = ((A, rhs), m, R)\<close> by (metis prod.collapse)
  with xit fclosure_base.prems show ?case by (auto simp: xconc_triple intro: xslots_kernel)
next
  case (fclosure_step A rhs m L B rhs\<^sub>B L')
  from fclosure_step.prems obtain i' u' where \<open>(i', u') \<in> L\<close> and sat: \<open>irel_sat (snd (rhs ! m)) i i'\<close>
    and u: \<open>u = []\<close>
    unfolding fclosure_step.hyps(5) by auto
  from fclosure_step.IH[of i' u'] this(1) obtain R\<^sub>p where
    \<open>((A, rhs), m, R\<^sub>p) \<in> set (xslots G xs cls)\<close> \<open>i' \<in> irep_set R\<^sub>p\<close> by auto
  moreover obtain p where p: \<open>p < length (iprods G)\<close> \<open>iprods G ! p = (B, rhs\<^sub>B)\<close>
    using fclosure_step.hyps(4) by (metis in_set_conv_nth)
  ultimately have \<open>i \<in> irep_set (fold (xcontrib (iprods G ! p)) (xslots G xs cls) (cls ! p))\<close>
    using fclosure_step.hyps(2,3) sat unfolding fold_xcontrib_set by fastforce
  hence \<open>i \<in> irep_set (cls ! p)\<close> using xstableD[OF st len p(1)] by (auto simp: xround_nth[OF len p(1)])
  with xslots_slot[OF p(1), of cls xs] len p u show ?case by auto
qed

theorem xclosure_correct:
  assumes st: \<open>xstable G xs (xiter G xs fuel)\<close>
  shows \<open>fconcs (xset (xclosure G fuel xs)) = fconcs (fclosure G 0 (xset xs))\<close>
proof (intro equalityI subsetI)
  fix it assume \<open>it \<in> fconcs (xset (xclosure G fuel xs))\<close>
  then obtain xit where xit: \<open>xit \<in> set (xclosure G fuel xs)\<close> and it: \<open>it \<in> fconc (xconc xit)\<close>
    unfolding xset_def by (blast elim: fconcsE)
  obtain A rhs m R where xit_eq: \<open>xit = ((A, rhs), m, R)\<close> by (metis prod.collapse)
  from xit[unfolded xclosure_def] show \<open>it \<in> fconcs (fclosure G 0 (xset xs))\<close>
  proof (cases rule: xslots_memE)
    case 1
    hence \<open>xconc xit \<in> fclosure G 0 (xset xs)\<close> unfolding xset_def by (blast intro: fclosure_base)
    with it show ?thesis by (rule fconcsI[rotated])
  next
    case (2 p)
    with xit_eq have preq: \<open>(A, rhs) = iprods G ! p\<close> \<open>m = 0\<close> \<open>R = xiter G xs fuel ! p\<close> by auto
    from it obtain i arhs where \<open>i \<in> irep_set R\<close> \<open>annotates i rhs arhs\<close> \<open>it = (((A, i), arhs), m, [])\<close>
      by (auto simp: xit_eq xconc_triple fconc_def)
    from xiter_sound[OF 2(1) this(1)[unfolded preq(3)]] obtain L where
      L: \<open>(iprods G ! p, 0, L) \<in> fclosure G 0 (xset xs)\<close> \<open>(i, []) \<in> L\<close> by blast
    have \<open>it \<in> fconc ((A, rhs), 0, L)\<close>
      using \<open>annotates i rhs arhs\<close> L(2) by (simp add: \<open>it = _\<close> preq(2) fconc_iff)
    with L(1) show ?thesis unfolding preq(1) by (rule fconcsI)
  qed
next
  fix it assume \<open>it \<in> fconcs (fclosure G 0 (xset xs))\<close>
  then obtain B rhs\<^sub>B m L i arhs u where fit: \<open>((B, rhs\<^sub>B), m, L) \<in> fclosure G 0 (xset xs)\<close>
    and iu: \<open>(i, u) \<in> L\<close> and ann: \<open>annotates i rhs\<^sub>B arhs\<close> and it: \<open>it = (((B, i), arhs), m, u)\<close>
    by (auto elim!: fconcsE simp: fconc_def split: prod.splits)
  from stable_covers[OF st xiter_length fit, of i u] iu obtain R where
    \<open>((B, rhs\<^sub>B), m, R) \<in> set (xslots G xs (xiter G xs fuel))\<close> \<open>i \<in> irep_set R\<close> \<open>u = []\<close> by auto
  from this(1) have \<open>xconc ((B, rhs\<^sub>B), m, R) \<in> xset (xclosure G fuel xs)\<close>
    unfolding xset_def xclosure_def by (rule imageI)
  moreover have \<open>it \<in> fconc (xconc ((B, rhs\<^sub>B), m, R))\<close>
    using \<open>i \<in> irep_set R\<close> \<open>u = []\<close> ann by (simp add: it xconc_triple fconc_iff)
  ultimately show \<open>it \<in> fconcs (xset (xclosure G fuel xs))\<close> by (rule fconcsI)
qed


text \<open>At \<^text>\<open>k = 0\<close> the acceptable-lookahead condition
  degenerates to non-emptiness of the closed item set, which is executable on
  the representation.\<close>

lemma Kset_zero: \<open>Kset P 0 S = (if S = {} then {} else {[]})\<close>
  unfolding Kset_def by (auto simp: ex_in_conv[symmetric])

lemma fconc_empty_iff: \<open>fconc (pr, m, L) = {} \<longleftrightarrow> L = {}\<close>
proof (cases pr)
  case (Pair A rhs)
  moreover have \<open>fconc ((A, rhs), m, L) \<noteq> {}\<close> if \<open>(i, u) \<in> L\<close> for i u
    using annotates_ex that by (fastforce simp: fconc_def)
  ultimately show ?thesis by (auto simp: fconc_def)
qed

lemma iequiv_empty_iff: \<open>S \<approx> T \<Longrightarrow> S = {} \<longleftrightarrow> T = {}\<close>
  unfolding iequiv_def by auto

lemma xset_nonempty_iff:
  fixes CL :: \<open>('n, 'tok) xitem list\<close>
  shows \<open>fconcs (xset CL) \<noteq> {} \<longleftrightarrow> (\<exists>(pr, m, R) \<in> set CL. irep_nonempty R)\<close>
  by (auto simp: fconcs_def xset_def xconc_def fconc_empty_iff split: prod.splits)

text \<open>
  The executable machine. The paper leaves the choice of reduction and its
  indentation to standard GLR stack splitting, orthogonal to this development.
  Here an explicit \<^emph>\<open>action trace\<close> drives the machine: a certificate
  recording for every step the fuel for the closure iteration and, for a
  reduction, the production and the indentation of the reduced non-terminal.
  Every side condition is checked, stability of the
  fuelled closure included, so a successful run is a verified parse: it maps
  step by step onto Algorithm 8 on the infinite II-CFG.
\<close>

datatype ('n, 'tok) gaction =
  GShift nat | GReduce nat nat \<open>'n \<times> ('n, 'tok) rhs\<close> nat

type_synonym ('n, 'tok) gconfig = \<open>('n, 'tok) xitem list list \<times> ('tok \<times> nat) list\<close>

definition xclosure_chk :: \<open>('n, 'tok) is_cfg \<Rightarrow> nat \<Rightarrow> ('n, 'tok) xitem list \<Rightarrow>
    ('n, 'tok) xitem list option\<close> where
  \<open>xclosure_chk G fuel xs =
     (if xstable G xs (xiter G xs fuel) then Some (xclosure G fuel xs) else None)\<close>

lemma xclosure_chk_correct:
  assumes \<open>xclosure_chk G fuel xs = Some CL\<close>
  shows \<open>fconcs (xset CL) = fconcs (fclosure G 0 (xset xs))\<close>
  using assms xclosure_correct
  unfolding xclosure_chk_def by (auto split: if_splits)

fun gstep :: \<open>('n, 'tok) is_cfg \<Rightarrow> ('n, 'tok) gconfig \<Rightarrow> ('n, 'tok) gaction \<Rightarrow>
    ('n, 'tok) gconfig option\<close> where
  \<open>gstep G (Xs, (t, l) # w) (GShift fuel) =
     (if Xs = [] then None
      else case xclosure_chk G fuel (hd Xs) of
        None \<Rightarrow> None
      | Some CL \<Rightarrow>
          if list_ex (\<lambda>(pr, m, R). irep_nonempty R) CL
          then Some (xgoto CL (Tm t) l # Xs, w) else None)\<close>
| \<open>gstep G (Xs, []) (GShift fuel) = None\<close>
| \<open>gstep G (Xs, w) (GReduce f\<^sub>1 f\<^sub>2 pr i) =
     (if Xs = [] \<or> \<not> length (snd pr) < length Xs then None
      else case xclosure_chk G f\<^sub>1 (hd Xs) of
        None \<Rightarrow> None
      | Some CL \<Rightarrow>
          if list_ex (\<lambda>(pr', m, R). pr' = pr \<and> m = length (snd pr) \<and>
                       irep_mem i R) CL
          then (case xclosure_chk G f\<^sub>2 (Xs ! length (snd pr)) of
              None \<Rightarrow> None
            | Some CL\<^sub>2 \<Rightarrow>
                Some (xgoto CL\<^sub>2 (Nt (fst pr)) i # drop (length (snd pr)) Xs, w))
          else None)\<close>

fun grun :: \<open>('n, 'tok) is_cfg \<Rightarrow> ('n, 'tok) gaction list \<Rightarrow> ('n, 'tok) gconfig \<Rightarrow>
    ('n, 'tok) gconfig option\<close> where
  \<open>grun G [] gc = Some gc\<close>
| \<open>grun G (act # acts) gc =
     (case gstep G gc act of None \<Rightarrow> None | Some gc' \<Rightarrow> grun G acts gc')\<close>

definition xinit :: \<open>('n, 'tok) is_cfg \<Rightarrow> 'n \<Rightarrow> ('n, 'tok) xitem list\<close> where
  \<open>xinit G Shn = [((Shn, [(Nt (istart G), Eq)]), 0, FinRep [istart_ind G])]\<close>

definition gaccepts ::
  \<open>('n, 'tok) is_cfg \<Rightarrow> 'n \<Rightarrow> ('n, 'tok) gaction list \<Rightarrow> ('tok \<times> nat) list \<Rightarrow> bool\<close> where
  \<open>gaccepts G Shn acts w \<longleftrightarrow>
     (case grun G acts ([xinit G Shn], w) of
        None \<Rightarrow> False
      | Some (Xs, v) \<Rightarrow> v = [] \<and> Xs \<noteq> [] \<and>
          list_ex (\<lambda>(pr, m, R). fst pr = Shn \<and> m = Suc 0 \<and>
                    irep_mem (istart_ind G) R) (hd Xs))\<close>

text \<open>The initial stacks are related: the executable initial item
  concretizes to the initial item of Algorithm 8.\<close>

lemma xinit_conc:
  fixes G :: \<open>('n, 'tok) is_cfg\<close> and dm :: \<open>'tok \<times> nat\<close>
  shows \<open>fconcs (xset (xinit G Shn)) =
   {init_item (Shn, istart_ind G) (istart G, istart_ind G) dm 0}\<close>
proof -
  have \<open>annotates (istart_ind G) [(Nt (istart G), Eq)] arhs \<longleftrightarrow> arhs = [Nt (istart G, istart_ind G)]\<close>
    for arhs :: \<open>('n \<times> nat, 'tok \<times> nat) syms\<close>
    by (cases arhs) (auto simp: annotates_def)
  thus ?thesis unfolding xinit_def xset_def init_item_def by (auto simp: xconc_triple fconcs_def fconc_def)
qed

lemma xinit_rel:
  \<open>stack_rel [{init_item (Shn, istart_ind G) (istart G, istart_ind G) dm 0}] (map xset [xinit G Shn])\<close>
  unfolding stack_rel_def
  by (simp add: xinit_conc[of G Shn dm] wf_iset_def init_item_def) (intro xset_wf, simp add: xinit_def)


text \<open>Transfer of the machine's primitives to the executable
  representation.\<close>

lemma xclosure_chk_transfer:
  assumes \<open>S \<approx> fconcs (xset xs)\<close> and \<open>xclosure_chk G fuel xs = Some CL\<close>
  shows \<open>iclosure (infG G) 0 S \<approx> fconcs (xset CL)\<close>
  using closure_transfer[OF assms(1)] xclosure_chk_correct[OF assms(2)] by simp

lemma xgoto_transfer:
  assumes \<open>iclosure (infG G) 0 S \<approx> fconcs (xset CL)\<close>
  shows \<open>igoto (iclosure (infG G) 0 S) (annsym (X, l)) \<approx> fconcs (xset (xgoto CL X l))\<close>
  using iequiv_trans[OF igoto_cong[OF assms] fconcs_igoto] by (simp add: xset_xgoto)

lemma wf_xgoto: \<open>wf_fitems (xset (xgoto CL X l))\<close>
  by (intro xset_wf) (auto simp: xgoto_def list_all_iff)

text \<open>Auxiliary destructors for the acceptance transfer.\<close>

lemma iequiv_memD:
  assumes \<open>S \<approx> T\<close> and \<open>((A\<^sub>i, arhs), m, u) \<in> T\<close>
  obtains arhs' m' where \<open>((A\<^sub>i, arhs'), m', u) \<in> S\<close>
    and \<open>map unann (take m' arhs') = map unann (take m arhs)\<close>
    and \<open>drop m' arhs' = drop m arhs\<close>
proof -
  have \<open>icore ((A\<^sub>i, arhs), m, u) \<in> icore ` S\<close> using assms unfolding iequiv_def by blast
  thus thesis by (rule icore_image_D) (rule that)
qed

lemma fconcs_xset_memD:
  assumes \<open>(((An, i), arhs), m, u) \<in> fconcs (xset CL)\<close>
  obtains rhs\<^sub>B R where \<open>((An, rhs\<^sub>B), m, R) \<in> set CL\<close> and \<open>i \<in> irep_set R\<close> and \<open>annotates i rhs\<^sub>B arhs\<close>
  using assms unfolding xset_def by (auto elim!: fconcsE simp: xconc_def fconc_def split: prod.splits)

text \<open>Pushing a goto frame on both stacks at depth \<open>k\<close>: the closures of the
  \<open>k\<close>-th frames correspond, and the stack relation extends.\<close>

lemma stack_rel_push:
  assumes rel: \<open>stack_rel Ss (map xset Xs)\<close> and k: \<open>k < length Xs\<close>
    and chk: \<open>xclosure_chk G fuel (Xs ! k) = Some CL\<close>
  shows \<open>iclosure (infG G) 0 (Ss ! k) \<approx> fconcs (xset CL)\<close>
    and \<open>stack_rel (igoto (iclosure (infG G) 0 (Ss ! k)) (annsym (X, l)) # drop k Ss)
                   (map xset (xgoto CL X l # drop k Xs))\<close>
proof -
  have \<open>k < length Ss\<close> using stack_rel_length[OF rel] k by simp
  from stack_rel_nth[OF rel this] k have nth: \<open>Ss ! k \<approx> fconcs (xset (Xs ! k))\<close> \<open>wf_iset (Ss ! k)\<close>
    by simp_all
  show cl: \<open>iclosure (infG G) 0 (Ss ! k) \<approx> fconcs (xset CL)\<close> by (rule xclosure_chk_transfer[OF nth(1) chk])
  show \<open>stack_rel (igoto (iclosure (infG G) 0 (Ss ! k)) (annsym (X, l)) # drop k Ss)
          (map xset (xgoto CL X l # drop k Xs))\<close>
    using stack_rel_drop[OF rel, of k]
    by (auto simp: drop_map intro!: stack_rel_Cons xgoto_transfer[OF cl] wf_xgoto wf_iset_igoto
          wf_iset_iclosure nth(2))
qed

lemma stack_rel_push_hd:
  assumes rel: \<open>stack_rel Ss (map xset Xs)\<close> and ne: \<open>Xs \<noteq> []\<close>
    and chk: \<open>xclosure_chk G fuel (hd Xs) = Some CL\<close>
  shows \<open>iclosure (infG G) 0 (hd Ss) \<approx> fconcs (xset CL)\<close>
    and \<open>stack_rel (igoto (iclosure (infG G) 0 (hd Ss)) (annsym (X, l)) # Ss)
                   (map xset (xgoto CL X l # Xs))\<close>
proof -
  have \<open>Ss \<noteq> []\<close> using stack_rel_length[OF rel] ne by fastforce
  with ne have hd: \<open>hd Xs = Xs ! 0\<close> \<open>hd Ss = Ss ! 0\<close> by (simp_all add: hd_conv_nth)
  from stack_rel_push(1)[OF rel _ chk[unfolded hd(1)]] ne
  show \<open>iclosure (infG G) 0 (hd Ss) \<approx> fconcs (xset CL)\<close> unfolding hd(2) by simp
  from stack_rel_push(2)[OF rel _ chk[unfolded hd(1)], of X l] ne
  show \<open>stack_rel (igoto (iclosure (infG G) 0 (hd Ss)) (annsym (X, l)) # Ss) (map xset (xgoto CL X l # Xs))\<close>
    unfolding hd(2) by simp
qed

text \<open>Every successful step of the executable machine is a step of
  Algorithm 8 on the infinite II-CFG and preserves the stack relation.\<close>

lemma gstep_to_lr:
  assumes rel: \<open>stack_rel Ss (map xset Xs)\<close>
    and st: \<open>gstep G (Xs, w) act = Some (Xs', w')\<close>
  obtains Ss' where \<open>lr_step (infG G) 0 (Ss, w) (Ss', w')\<close>
    and \<open>stack_rel Ss' (map xset Xs')\<close>
proof (cases act)
  case (GShift fuel)
  with st obtain al w\<^sub>2 where \<open>w = al # w\<^sub>2\<close> by (cases w) auto
  then obtain t l where w: \<open>w = (t, l) # w\<^sub>2\<close> by (cases al) auto
  from st obtain CL where ne: \<open>Xs \<noteq> []\<close> and chk: \<open>xclosure_chk G fuel (hd Xs) = Some CL\<close>
    unfolding GShift w by (auto split: if_splits option.splits)
  with st have nonempty: \<open>list_ex (\<lambda>(pr, m, R). irep_nonempty R) CL\<close>
    and Xs': \<open>Xs' = xgoto CL (Tm t) l # Xs\<close> and w': \<open>w' = w\<^sub>2\<close>
    unfolding GShift w by (fastforce simp: list_ex_iff split: if_splits)+
  note push = stack_rel_push_hd[OF rel ne chk]
  have \<open>fconcs (xset CL) \<noteq> {}\<close> using nonempty by (simp add: xset_nonempty_iff list_ex_iff)
  hence \<open>iclosure (infG G) 0 (hd Ss) \<noteq> {}\<close> using iequiv_empty_iff[OF push(1)] by blast
  hence kset: \<open>take 0 ((t, l) # w\<^sub>2) \<in> Kset (infG G) 0 (iclosure (infG G) 0 (hd Ss))\<close>
    by (simp add: Kset_zero)
  have \<open>Ss \<noteq> []\<close> using stack_rel_length[OF rel] ne by fastforce
  from lr_step.lr_shift[OF this kset] show thesis
    by (rule that[unfolded w w']) (use push(2)[of \<open>Tm t\<close> l] Xs' in simp)
next
  case (GReduce f\<^sub>1 f\<^sub>2 pr i)
  obtain A rhs where pr: \<open>pr = (A, rhs)\<close> by (cases pr)
  from st obtain CL CL\<^sub>2 where ne: \<open>Xs \<noteq> []\<close> and lt: \<open>length rhs < length Xs\<close>
    and chk\<^sub>1: \<open>xclosure_chk G f\<^sub>1 (hd Xs) = Some CL\<close>
    and found: \<open>list_ex (\<lambda>(pr', m, R). pr' = (A, rhs) \<and> m = length rhs \<and> irep_mem i R) CL\<close>
    and chk\<^sub>2: \<open>xclosure_chk G f\<^sub>2 (Xs ! length rhs) = Some CL\<^sub>2\<close>
    and Xs': \<open>Xs' = xgoto CL\<^sub>2 (Nt A) i # drop (length rhs) Xs\<close> and w': \<open>w' = w\<close>
    unfolding GReduce pr by (auto split: if_splits option.splits)
  from found obtain R where \<open>((A, rhs), length rhs, R) \<in> set CL\<close> \<open>i \<in> irep_set R\<close>
    by (auto simp: list_ex_iff)
  moreover obtain arhs where ann: \<open>annotates i rhs arhs\<close> using annotates_ex by blast
  ultimately have \<open>(((A, i), arhs), length arhs, []) \<in> fconcs (xset CL)\<close>
    unfolding xset_def annotates_length[OF ann]
    by (auto intro!: fconcsI[of \<open>xconc ((A, rhs), length rhs, R)\<close>] simp: xconc_triple fconc_iff)
  have \<open>Ss \<noteq> []\<close> using stack_rel_length[OF rel] ne by fastforce
  have \<open>icore ` fconcs (xset CL) \<subseteq> icore ` iclosure (infG G) 0 (hd Ss)\<close>
    using stack_rel_push_hd(1)[OF rel ne chk\<^sub>1] unfolding iequiv_def by simp
  from completed_core_transfer[OF this wf_iset_iclosure[OF stack_rel_hd(2)[OF rel \<open>Ss \<noteq> []\<close>]]
      \<open>_ \<in> fconcs (xset CL)\<close>]
  obtain arhs' where \<open>(((A, i), arhs'), length arhs', []) \<in> iclosure (infG G) 0 (hd Ss)\<close>
    and len': \<open>length arhs' = length rhs\<close>
    unfolding annotates_length[OF ann] by blast
  hence \<open>take 0 w \<in> Kprod (iclosure (infG G) 0 (hd Ss)) ((A, i), arhs')\<close> by (simp add: Kprod_iff)
  from lr_step.lr_reduce[OF \<open>Ss \<noteq> []\<close> this, unfolded len'] lt stack_rel_length[OF rel]
  have step: \<open>lr_step (infG G) 0 (Ss, w)
      (igoto (iclosure (infG G) 0 (Ss ! length rhs)) (Nt (A, i)) # drop (length rhs) Ss, w)\<close>
    by simp
  show thesis
    by (rule that[unfolded w', OF step])
       (use stack_rel_push(2)[OF rel lt chk\<^sub>2, of \<open>Nt A\<close> i] in \<open>simp add: Xs'\<close>)
qed


text \<open>
  Fuel sufficient for a stable closure always exists. Slot values grow
  monotonically, and a round that is not yet stable strictly decreases the
  lexicographic measure built from the number of slots without an upward-closed
  part, the sum of the minima of the upward parts, and the number of kernel
  finite-part elements not yet covered. The argument rests on two facts: finite
  parts of slot values only copy finite parts of kernel values, and the
  relational images for \<^const>\<open>Gt\<close>, \<^const>\<open>Ge\<close> and
  \<^const>\<open>Any\<close> are upward closed.
\<close>

fun irep_fin :: \<open>indrep \<Rightarrow> nat list\<close> where
  \<open>irep_fin (FinRep xs) = xs\<close>
| \<open>irep_fin (UpRep xs n) = xs\<close>

fun irep_hasup :: \<open>indrep \<Rightarrow> bool\<close> where
  \<open>irep_hasup (FinRep xs) = False\<close>
| \<open>irep_hasup (UpRep xs n) = True\<close>

fun irep_upmin :: \<open>indrep \<Rightarrow> nat\<close> where
  \<open>irep_upmin (FinRep xs) = 0\<close>
| \<open>irep_upmin (UpRep xs n) = n\<close>

lemma irep_set_split:
  \<open>irep_set R = set (irep_fin R) \<union> (if irep_hasup R then {m. irep_upmin R \<le> m} else {})\<close>
  by (cases R) auto

lemma irep_union_fin:
  \<open>set (irep_fin (irep_union R\<^sub>1 R\<^sub>2)) = set (irep_fin R\<^sub>1) \<union> set (irep_fin R\<^sub>2)\<close>
  by (cases R\<^sub>1; cases R\<^sub>2) auto

lemma irep_union_hasup:
  \<open>irep_hasup (irep_union R\<^sub>1 R\<^sub>2) \<longleftrightarrow> irep_hasup R\<^sub>1 \<or> irep_hasup R\<^sub>2\<close>
  by (cases R\<^sub>1; cases R\<^sub>2) auto

lemma irep_union_upmin:
  \<open>irep_hasup R\<^sub>2 \<Longrightarrow> irep_upmin (irep_union R\<^sub>1 R\<^sub>2) \<le> irep_upmin R\<^sub>2\<close>
  by (cases R\<^sub>1; cases R\<^sub>2) auto

lemma irep_img_fin: \<open>set (irep_fin (irep_img r R)) \<subseteq> set (irep_fin R)\<close>
  by (cases r; cases R) auto

lemma xcontrib_fin:
  \<open>set (irep_fin (xcontrib pr xit acc)) \<subseteq>
   set (irep_fin acc) \<union> set (irep_fin (snd (snd xit)))\<close>
  by (induction pr xit acc rule: xcontrib.induct)
     (auto simp: irep_union_fin dest: irep_img_fin[THEN subsetD])

lemma xcontrib_upmin:
  assumes \<open>irep_hasup acc\<close>
  shows \<open>irep_hasup (xcontrib pr xit acc) \<and>
         irep_upmin (xcontrib pr xit acc) \<le> irep_upmin acc\<close>
  using assms
  by (induction pr xit acc rule: xcontrib.induct)
     (auto simp: irep_union_hasup irep_union_upmin)

lemma fold_xcontrib_fin:
  \<open>set (irep_fin (fold (xcontrib pr) items acc)) \<subseteq>
   set (irep_fin acc) \<union> (\<Union> xit \<in> set items. set (irep_fin (snd (snd xit))))\<close>
proof (induction items arbitrary: acc)
  case (Cons x items)
  with xcontrib_fin[of pr x acc] show ?case by (fastforce simp: subset_iff)
qed simp

lemma fold_xcontrib_upmin:
  assumes \<open>irep_hasup acc\<close>
  shows \<open>irep_hasup (fold (xcontrib pr) items acc) \<and>
         irep_upmin (fold (xcontrib pr) items acc) \<le> irep_upmin acc\<close>
  using assms
proof (induction items arbitrary: acc)
  case (Cons x items)
  from xcontrib_upmin[OF Cons.prems, of pr x] Cons.IH[of \<open>xcontrib pr x acc\<close>] show ?case by auto
qed simp

lemma xiter_fin:
  assumes \<open>p < length (iprods G)\<close>
  shows \<open>set (irep_fin (xiter G xs s ! p)) \<subseteq> (\<Union> xit \<in> set xs. set (irep_fin (snd (snd xit))))\<close>
  using assms
proof (induction s arbitrary: p)
  case (Suc s)
  have \<open>set (irep_fin (xiter G xs (Suc s) ! p)) \<subseteq>
        set (irep_fin (xiter G xs s ! p)) \<union> (\<Union> xit \<in> set (xslots G xs (xiter G xs s)). set (irep_fin (snd (snd xit))))\<close>
    using fold_xcontrib_fin by (simp add: xround_nth[OF xiter_length Suc.prems])
  moreover have \<open>set (irep_fin (snd (snd xit))) \<subseteq> (\<Union> xit \<in> set xs. set (irep_fin (snd (snd xit))))\<close>
    if \<open>xit \<in> set (xslots G xs (xiter G xs s))\<close> for xit
    using that Suc.IH by (cases rule: xslots_memE) auto
  ultimately show ?case using Suc.IH[OF Suc.prems] by blast
qed simp

lemma xiter_set_mono:
  assumes \<open>p < length (iprods G)\<close>
  shows \<open>irep_set (xiter G xs s ! p) \<subseteq> irep_set (xiter G xs (Suc s) ! p)\<close>
  by (simp add: xround_nth[OF xiter_length assms] fold_xcontrib_set)

lemma xiter_upmin_mono:
  assumes \<open>p < length (iprods G)\<close> and \<open>irep_hasup (xiter G xs s ! p)\<close>
  shows \<open>irep_hasup (xiter G xs (Suc s) ! p) \<and>
         irep_upmin (xiter G xs (Suc s) ! p) \<le> irep_upmin (xiter G xs s ! p)\<close>
  using fold_xcontrib_upmin[OF assms(2)] by (simp add: xround_nth[OF xiter_length assms(1)])


text \<open>One round of \<^const>\<open>xiter\<close> that is not yet stable strictly decreases
  the lexicographic measure (frames without an up-set, sum of the up-set
  minima, sum of the finite complements).\<close>

lemma xiter_measure_dec:
  fixes G xs s len kf g
  assumes len_def: \<open>len = length (iprods G)\<close>
    and kf_def: \<open>kf = (\<Union> xit \<in> set xs. set (irep_fin (snd (snd xit))))\<close>
    and g_def: \<open>g = (\<lambda>s p. if irep_hasup (xiter G xs s ! p) then irep_upmin (xiter G xs s ! p) else 0)\<close>
  defines c\<^sub>1_def: \<open>c\<^sub>1 \<equiv> \<lambda>s. card {p. p < len \<and> \<not> irep_hasup (xiter G xs s ! p)}\<close>
    and c\<^sub>2_def: \<open>c\<^sub>2 \<equiv> \<lambda>s. \<Sum> p < len. g s p\<close>
    and c\<^sub>3_def: \<open>c\<^sub>3 \<equiv> \<lambda>s. \<Sum> p < len. card (kf - irep_set (xiter G xs s ! p))\<close>
  assumes notst: \<open>\<not> xstable G xs (xiter G xs s)\<close>
  shows \<open>c\<^sub>1 (Suc s) < c\<^sub>1 s \<or>
         (c\<^sub>1 (Suc s) = c\<^sub>1 s \<and> (c\<^sub>2 (Suc s) < c\<^sub>2 s \<or> (c\<^sub>2 (Suc s) = c\<^sub>2 s \<and> c\<^sub>3 (Suc s) < c\<^sub>3 s)))\<close>
proof -
  have finkf: \<open>finite kf\<close> unfolding kf_def by simp
  have hup: \<open>irep_hasup (xiter G xs (Suc s) ! p)\<close>
    and upm: \<open>irep_upmin (xiter G xs (Suc s) ! p) \<le> irep_upmin (xiter G xs s ! p)\<close>
    if \<open>p < len\<close> and \<open>irep_hasup (xiter G xs s ! p)\<close> for p
    using xiter_upmin_mono that unfolding len_def by blast+
  have smono: \<open>irep_set (xiter G xs s ! p) \<subseteq> irep_set (xiter G xs (Suc s) ! p)\<close> if \<open>p < len\<close> for p
    using xiter_set_mono that unfolding len_def by blast

  from notst obtain p\<^sub>0 where p\<^sub>0: \<open>p\<^sub>0 < len\<close>
    and \<open>\<not> irep_subset (xround G xs (xiter G xs s) ! p\<^sub>0) (xiter G xs s ! p\<^sub>0)\<close>
    using xround_length[of \<open>xiter G xs s\<close> G xs] unfolding xstable_def len_def
    by (fastforce simp: list_all2_conv_all_nth)
  then obtain x where xnew: \<open>x \<in> irep_set (xiter G xs (Suc s) ! p\<^sub>0)\<close>
    and xold: \<open>x \<notin> irep_set (xiter G xs s ! p\<^sub>0)\<close>
    by auto

  have c1le: \<open>c\<^sub>1 (Suc s) \<le> c\<^sub>1 s\<close> unfolding c\<^sub>1_def by (intro card_mono) (auto dest: hup)
  show ?thesis
  proof (cases \<open>c\<^sub>1 (Suc s) = c\<^sub>1 s\<close>)
    case False
    with c1le show ?thesis by simp
  next
    case c1eq: True
    have \<open>{p. p < len \<and> \<not> irep_hasup (xiter G xs (Suc s) ! p)} = {p. p < len \<and> \<not> irep_hasup (xiter G xs s ! p)}\<close>
      using c1eq unfolding c\<^sub>1_def by (intro card_subset_eq) (auto dest: hup)
    hence huppt: \<open>irep_hasup (xiter G xs (Suc s) ! p) = irep_hasup (xiter G xs s ! p)\<close> if \<open>p < len\<close> for p
      using that by blast
    have c2ptle: \<open>g (Suc s) p \<le> g s p\<close> if \<open>p < len\<close> for p
      unfolding g_def using huppt[OF that] upm[OF that] by auto
    have c2le: \<open>c\<^sub>2 (Suc s) \<le> c\<^sub>2 s\<close> unfolding c\<^sub>2_def by (intro sum_mono) (use c2ptle in auto)
    show ?thesis
    proof (cases \<open>c\<^sub>2 (Suc s) = c\<^sub>2 s\<close>)
      case False
      with c2le c1eq show ?thesis by simp
    next
      case c2eq: True
      have c2pteq: \<open>g (Suc s) p = g s p\<close> if p: \<open>p < len\<close> for p
      proof (rule ccontr)
        assume \<open>g (Suc s) p \<noteq> g s p\<close>
        with c2ptle[OF p] have \<open>g (Suc s) p < g s p\<close> by simp
        hence \<open>(\<Sum> p < len. g (Suc s) p) < (\<Sum> p < len. g s p)\<close>
          by (intro sum_strict_mono_ex1) (use c2ptle p in auto)
        with c2eq show False unfolding c\<^sub>2_def by simp
      qed
      have xkf: \<open>x \<in> kf\<close>
      proof (cases \<open>irep_hasup (xiter G xs (Suc s) ! p\<^sub>0)\<close>)
        case False
        with xnew have \<open>x \<in> set (irep_fin (xiter G xs (Suc s) ! p\<^sub>0))\<close>
          using irep_set_split[of \<open>xiter G xs (Suc s) ! p\<^sub>0\<close>] by auto
        with xiter_fin[of p\<^sub>0 G xs \<open>Suc s\<close>] p\<^sub>0 show ?thesis unfolding kf_def len_def by blast
      next
        case hup\<^sub>1: True
        with huppt[OF p\<^sub>0] have hup\<^sub>0: \<open>irep_hasup (xiter G xs s ! p\<^sub>0)\<close> by simp
        with c2pteq[OF p\<^sub>0] hup\<^sub>1
        have \<open>irep_upmin (xiter G xs (Suc s) ! p\<^sub>0) = irep_upmin (xiter G xs s ! p\<^sub>0)\<close>
          unfolding g_def by auto
        with xold hup\<^sub>0 have \<open>x \<notin> {m. irep_upmin (xiter G xs (Suc s) ! p\<^sub>0) \<le> m}\<close>
          using irep_set_split[of \<open>xiter G xs s ! p\<^sub>0\<close>] by auto
        with xnew hup\<^sub>1 have \<open>x \<in> set (irep_fin (xiter G xs (Suc s) ! p\<^sub>0))\<close>
          using irep_set_split[of \<open>xiter G xs (Suc s) ! p\<^sub>0\<close>] by auto
        with xiter_fin[of p\<^sub>0 G xs \<open>Suc s\<close>] p\<^sub>0 show ?thesis unfolding kf_def len_def by blast
      qed
      have c3pt: \<open>card (kf - irep_set (xiter G xs (Suc s) ! p)) \<le> card (kf - irep_set (xiter G xs s ! p))\<close>
        if \<open>p < len\<close> for p
        by (intro card_mono) (use finkf smono[OF that] in auto)
      have c3strict: \<open>card (kf - irep_set (xiter G xs (Suc s) ! p\<^sub>0)) < card (kf - irep_set (xiter G xs s ! p\<^sub>0))\<close>
        by (intro psubset_card_mono) (use finkf smono[OF p\<^sub>0] xnew xold xkf in auto)
      have \<open>c\<^sub>3 (Suc s) < c\<^sub>3 s\<close>
        unfolding c\<^sub>3_def by (intro sum_strict_mono_ex1) (use c3pt c3strict p\<^sub>0 in auto)
      with c1eq c2eq show ?thesis by simp
    qed
  qed
qed

theorem xcls_stable_ex: \<open>\<exists>fuel. xstable G xs (xiter G xs fuel)\<close>
proof (rule ccontr)
  assume \<open>\<not> ?thesis\<close>
  then have notst: \<open>\<And>s. \<not> xstable G xs (xiter G xs s)\<close> by blast
  define len where \<open>len = length (iprods G)\<close>
  define kf where \<open>kf = (\<Union> xit \<in> set xs. set (irep_fin (snd (snd xit))))\<close>
  define g where \<open>g s p = (if irep_hasup (xiter G xs s ! p)
                           then irep_upmin (xiter G xs s ! p) else 0)\<close> for s p
  define c\<^sub>1 where \<open>c\<^sub>1 s = card {p. p < len \<and> \<not> irep_hasup (xiter G xs s ! p)}\<close> for s
  define c\<^sub>2 where \<open>c\<^sub>2 s = (\<Sum> p < len. g s p)\<close> for s
  define c\<^sub>3 where \<open>c\<^sub>3 s = (\<Sum> p < len. card (kf - irep_set (xiter G xs s ! p)))\<close> for s
  define \<mu> where \<open>\<mu> s = (c\<^sub>1 s, c\<^sub>2 s, c\<^sub>3 s)\<close> for s
  have dec: \<open>c\<^sub>1 (Suc s) < c\<^sub>1 s \<or>
             (c\<^sub>1 (Suc s) = c\<^sub>1 s \<and> (c\<^sub>2 (Suc s) < c\<^sub>2 s \<or>
               (c\<^sub>2 (Suc s) = c\<^sub>2 s \<and> c\<^sub>3 (Suc s) < c\<^sub>3 s)))\<close> for s
    unfolding c\<^sub>1_def c\<^sub>2_def c\<^sub>3_def g_def kf_def len_def
    by (rule xiter_measure_dec[OF refl refl refl notst])
  have step: \<open>(\<mu> (Suc s), \<mu> s) \<in> measures [fst, fst \<circ> snd, snd \<circ> snd]\<close> for s
    using dec[of s] unfolding \<mu>_def
    by (auto intro: measures_less measures_lesseq)
  have \<open>\<not> wf (measures [fst, fst \<circ> snd, snd \<circ> snd] ::
              ((nat \<times> nat \<times> nat) \<times> nat \<times> nat \<times> nat) set)\<close>
    unfolding wf_iff_no_infinite_down_chain using step by blast
  then show False using wf_measures by blast
qed


lemma wf_xclosure:
  assumes \<open>wf_fitems (xset xs)\<close>
  shows \<open>wf_fitems (xset (xclosure G fuel xs))\<close>
  unfolding wf_fitems_def
proof (intro allI impI)
  fix B rhs m L assume \<open>((B, rhs), m, L) \<in> xset (xclosure G fuel xs)\<close>
  then obtain xit where eq: \<open>xconc xit = ((B, rhs), m, L)\<close> and \<open>xit \<in> set (xclosure G fuel xs)\<close>
    unfolding xset_def by auto
  from this(2)[unfolded xclosure_def] show \<open>m \<le> length rhs\<close>
  proof (cases rule: xslots_memE)
    case 1
    with assms eq show ?thesis unfolding wf_fitems_def xset_def by force
  qed (use eq in \<open>auto simp: xconc_triple\<close>)
qed

text \<open>Conversely, every step of Algorithm 8 is matched by the
  executable machine under a suitable action, with the fuel supplied by
  \<^text>\<open>xcls_stable_ex\<close>, preserving the stack relation.\<close>

lemma lr_to_gstep:
  assumes rel: \<open>stack_rel Ss (map xset Xs)\<close>
    and step: \<open>lr_step (infG G) 0 (Ss, w) (Ss', w')\<close>
  obtains act Ys where \<open>gstep G (Xs, w) act = Some (Ys, w')\<close>
    and \<open>stack_rel Ss' (map xset Ys)\<close>
  using step
proof (cases rule: lr_step.cases)
  case (lr_shift t)
  obtain t\<^sub>0 l where t: \<open>t = (t\<^sub>0, l)\<close> by (cases t)
  have ne: \<open>Xs \<noteq> []\<close> using stack_rel_length[OF rel] lr_shift(3) by fastforce
  obtain fuel where \<open>xstable G (hd Xs) (xiter G (hd Xs) fuel)\<close> using xcls_stable_ex by blast
  hence chk: \<open>xclosure_chk G fuel (hd Xs) = Some (xclosure G fuel (hd Xs))\<close> by (simp add: xclosure_chk_def)
  note push = stack_rel_push_hd[OF rel ne chk]
  have \<open>iclosure (infG G) 0 (hd Ss) \<noteq> {}\<close> using lr_shift(4) unfolding Kset_zero by (auto split: if_splits)
  hence \<open>fconcs (xset (xclosure G fuel (hd Xs))) \<noteq> {}\<close> using iequiv_empty_iff[OF push(1)] by blast
  hence \<open>list_ex (\<lambda>(pr, m, R). irep_nonempty R) (xclosure G fuel (hd Xs))\<close>
    by (simp add: xset_nonempty_iff list_ex_iff)
  hence \<open>gstep G (Xs, w) (GShift fuel) = Some (xgoto (xclosure G fuel (hd Xs)) (Tm t\<^sub>0) l # Xs, w')\<close>
    unfolding lr_shift(1) t using ne chk by (fastforce simp: list_ex_iff)
  moreover have \<open>stack_rel Ss' (map xset (xgoto (xclosure G fuel (hd Xs)) (Tm t\<^sub>0) l # Xs))\<close>
    unfolding lr_shift(2) t using push(2)[of \<open>Tm t\<^sub>0\<close> l] by simp
  ultimately show thesis by (rule that)
next
  case (lr_reduce A\<^sub>i arhs)
  obtain A i where A\<^sub>i: \<open>A\<^sub>i = (A, i)\<close> by (cases A\<^sub>i)
  have ne: \<open>Xs \<noteq> []\<close> using stack_rel_length[OF rel] lr_reduce(3) by fastforce
  obtain fuel\<^sub>1 where \<open>xstable G (hd Xs) (xiter G (hd Xs) fuel\<^sub>1)\<close> using xcls_stable_ex by blast
  hence chk\<^sub>1: \<open>xclosure_chk G fuel\<^sub>1 (hd Xs) = Some (xclosure G fuel\<^sub>1 (hd Xs))\<close>
    by (simp add: xclosure_chk_def)
  let ?CL = \<open>xclosure G fuel\<^sub>1 (hd Xs)\<close>

  have \<open>icore ` iclosure (infG G) 0 (hd Ss) \<subseteq> icore ` fconcs (xset ?CL)\<close>
    using stack_rel_push_hd(1)[OF rel ne chk\<^sub>1] unfolding iequiv_def by simp
  moreover have \<open>wf_iset (fconcs (xset ?CL))\<close>
    using stack_rel_hd(3)[OF rel lr_reduce(3)] ne by (intro wf_iset_fconcs wf_xclosure) (simp add: hd_map)
  moreover have \<open>((A\<^sub>i, arhs), length arhs, []) \<in> iclosure (infG G) 0 (hd Ss)\<close>
    using lr_reduce(4) by (simp add: Kprod_iff)
  ultimately obtain arhs\<^sub>2 where \<open>((A\<^sub>i, arhs\<^sub>2), length arhs\<^sub>2, []) \<in> fconcs (xset ?CL)\<close>
    and len\<^sub>2: \<open>length arhs\<^sub>2 = length arhs\<close>
    by (rule completed_core_transfer)
  from this(1)[unfolded A\<^sub>i] obtain rhs\<^sub>B R where
    xit: \<open>((A, rhs\<^sub>B), length arhs\<^sub>2, R) \<in> set ?CL\<close> and iR: \<open>i \<in> irep_set R\<close>
    and ann: \<open>annotates i rhs\<^sub>B arhs\<^sub>2\<close>
    by (rule fconcs_xset_memD)
  have lenb: \<open>length rhs\<^sub>B = length arhs\<close> using annotates_length[OF ann] len\<^sub>2 by simp
  have lenXs: \<open>length rhs\<^sub>B < length Xs\<close> using lenb lr_reduce(5) stack_rel_length[OF rel] by simp

  obtain fuel\<^sub>2 where \<open>xstable G (Xs ! length rhs\<^sub>B) (xiter G (Xs ! length rhs\<^sub>B) fuel\<^sub>2)\<close>
    using xcls_stable_ex by blast
  hence chk\<^sub>2: \<open>xclosure_chk G fuel\<^sub>2 (Xs ! length rhs\<^sub>B) = Some (xclosure G fuel\<^sub>2 (Xs ! length rhs\<^sub>B))\<close>
    by (simp add: xclosure_chk_def)
  have \<open>list_ex (\<lambda>(pr', m, R). pr' = (A, rhs\<^sub>B) \<and> m = length rhs\<^sub>B \<and> irep_mem i R) ?CL\<close>
    using xit iR lenb len\<^sub>2 by (auto simp: list_ex_iff)
  hence \<open>gstep G (Xs, w) (GReduce fuel\<^sub>1 fuel\<^sub>2 (A, rhs\<^sub>B) i) =
         Some (xgoto (xclosure G fuel\<^sub>2 (Xs ! length rhs\<^sub>B)) (Nt A) i # drop (length rhs\<^sub>B) Xs, w)\<close>
    using ne lenXs chk\<^sub>1 chk\<^sub>2 by simp
  moreover have \<open>stack_rel Ss' (map xset (xgoto (xclosure G fuel\<^sub>2 (Xs ! length rhs\<^sub>B)) (Nt A) i # drop (length rhs\<^sub>B) Xs))\<close>
    unfolding lr_reduce(1) A\<^sub>i lenb[symmetric] using stack_rel_push(2)[OF rel lenXs chk\<^sub>2, of \<open>Nt A\<close> i] by simp
  ultimately show thesis by (rule that[unfolded lr_reduce(2)])
qed


lemma grun_append:
  \<open>grun G (as\<^sub>1 @ as\<^sub>2) gc =
   (case grun G as\<^sub>1 gc of None \<Rightarrow> None | Some gc' \<Rightarrow> grun G as\<^sub>2 gc')\<close>
  by (induction as\<^sub>1 arbitrary: gc) (auto split: option.splits)

text \<open>Run-level simulation, in both directions.\<close>

lemma grun_to_lr:
  assumes \<open>grun G acts (Xs, w) = Some (Ys, v)\<close> and \<open>stack_rel Ss (map xset Xs)\<close>
  shows \<open>\<exists>Ss'. (lr_step (infG G) 0)\<^sup>*\<^sup>* (Ss, w) (Ss', v) \<and> stack_rel Ss' (map xset Ys)\<close>
  using assms
proof (induction acts arbitrary: Xs w Ss)
  case (Cons act acts)
  from Cons.prems(1) obtain Xs\<^sub>1 w\<^sub>1 where
    \<open>gstep G (Xs, w) act = Some (Xs\<^sub>1, w\<^sub>1)\<close> \<open>grun G acts (Xs\<^sub>1, w\<^sub>1) = Some (Ys, v)\<close>
    by (auto split: option.splits)
  from gstep_to_lr[OF Cons.prems(2) this(1)] obtain Ss\<^sub>1 where
    st: \<open>lr_step (infG G) 0 (Ss, w) (Ss\<^sub>1, w\<^sub>1)\<close> \<open>stack_rel Ss\<^sub>1 (map xset Xs\<^sub>1)\<close> .
  from Cons.IH[OF \<open>grun G acts (Xs\<^sub>1, w\<^sub>1) = _\<close> st(2)] obtain Ss' where
    \<open>(lr_step (infG G) 0)\<^sup>*\<^sup>* (Ss\<^sub>1, w\<^sub>1) (Ss', v)\<close> \<open>stack_rel Ss' (map xset Ys)\<close> by blast
  with st(1) show ?case by (blast intro: converse_rtranclp_into_rtranclp)
qed auto

lemma lr_to_grun:
  assumes \<open>(lr_step (infG G) 0)\<^sup>*\<^sup>* (Ss, w) (Ss', w')\<close> and \<open>stack_rel Ss (map xset Xs)\<close>
  shows \<open>\<exists>acts Ys. grun G acts (Xs, w) = Some (Ys, w') \<and> stack_rel Ss' (map xset Ys)\<close>
  using assms
proof (induction rule: rtranclp_induct2)
  case refl
  thus ?case by (intro exI[of _ \<open>[]\<close>] exI[of _ Xs]) auto
next
  case (step Ss\<^sub>1 v\<^sub>1 Ss\<^sub>2 v\<^sub>2)
  from step.IH[OF step.prems] obtain acts Ys\<^sub>1 where
    \<open>grun G acts (Xs, w) = Some (Ys\<^sub>1, v\<^sub>1)\<close> \<open>stack_rel Ss\<^sub>1 (map xset Ys\<^sub>1)\<close> by blast
  from lr_to_gstep[OF this(2) step.hyps(2)] obtain act Ys\<^sub>2 where
    \<open>gstep G (Ys\<^sub>1, v\<^sub>1) act = Some (Ys\<^sub>2, v\<^sub>2)\<close> \<open>stack_rel Ss\<^sub>2 (map xset Ys\<^sub>2)\<close> .
  thus ?case using \<open>grun G acts (Xs, w) = _\<close>
    by (auto simp: grun_append intro!: exI[of _ \<open>acts @ [act]\<close>])
qed

text \<open>
  Correctness of the executable GLR machine: a word is accepted under some
  action trace iff it lies in the language of the IS-grammar. Soundness holds
  for every trace, so a successful run is a verified parse, and for a word in
  the language a suitable trace exists, the parse certificate a GLR search
  would produce.
\<close>

theorem gaccepts_sound:
  fixes G :: \<open>('n, 'tok) is_cfg\<close>
  assumes fn: \<open>fresh_name G Shn\<close> and \<open>gaccepts G Shn acts (tcols w)\<close>
  shows \<open>w \<in> ilang G\<close>
proof -
  define dm where \<open>dm = (undefined :: 'tok \<times> nat)\<close>
  define Sh where \<open>Sh = (Shn, istart_ind G)\<close>
  define St' where \<open>St' = (istart G, istart_ind G)\<close>
  from assms(2) obtain Ys where run\<^sub>0: \<open>grun G acts ([xinit G Shn], tcols w) = Some (Ys, [])\<close>
    and Ysne: \<open>Ys \<noteq> []\<close>
    and item: \<open>list_ex (\<lambda>(pr, m, R). fst pr = Shn \<and> m = Suc 0 \<and> irep_mem (istart_ind G) R) (hd Ys)\<close>
    unfolding gaccepts_def by (cases \<open>grun G acts ([xinit G Shn], tcols w)\<close>) auto
  from grun_to_lr[OF run\<^sub>0 xinit_rel] obtain Ss' where
    run: \<open>(lr_step (infG G) 0)\<^sup>*\<^sup>* ([{init_item Sh St' dm 0}], tcols w) (Ss', [])\<close>
    and rel: \<open>stack_rel Ss' (map xset Ys)\<close>
    unfolding Sh_def St'_def by blast
  have Ssne: \<open>Ss' \<noteq> []\<close> using stack_rel_length[OF rel] Ysne by fastforce

  from item obtain rhs\<^sub>B R where xit: \<open>((Shn, rhs\<^sub>B), Suc 0, R) \<in> set (hd Ys)\<close>
    and inR: \<open>istart_ind G \<in> irep_set R\<close>
    by (auto simp: list_ex_iff split: prod.splits)
  have \<open>wf_fitems (xset (hd Ys))\<close> using stack_rel_hd(3)[OF rel Ssne] Ysne by (simp add: hd_map)
  with xit have \<open>Suc 0 \<le> length rhs\<^sub>B\<close> unfolding wf_fitems_def xset_def by (force simp: xconc_triple)
  obtain arhs where ann: \<open>annotates (istart_ind G) rhs\<^sub>B arhs\<close> using annotates_ex by blast
  with \<open>Suc 0 \<le> length rhs\<^sub>B\<close> have lenarhs: \<open>Suc 0 \<le> length arhs\<close> by (simp add: annotates_length)
  have \<open>((Sh, arhs), Suc 0, []) \<in> fconcs (xset (hd Ys))\<close>
    using xit inR ann unfolding Sh_def xset_def
    by (auto intro!: fconcsI[of \<open>xconc ((Shn, rhs\<^sub>B), Suc 0, R)\<close>] simp: xconc_triple fconc_iff)
  then obtain arhs' m' where mem': \<open>((Sh, arhs'), m', []) \<in> hd Ss'\<close>
    and pre': \<open>map unann (take m' arhs') = map unann (take (Suc 0) arhs)\<close>
    by (rule iequiv_memD[OF stack_rel_hd(1)[OF rel Ssne, unfolded hd_map[OF Ysne]]])

  from lr_run_frames[OF run] obtain \<gamma> where \<open>Ss' = lr_frames (infG G) 0 {init_item Sh St' dm 0} \<gamma>\<close> by blast
  with mem' have memcl: \<open>((Sh, arhs'), m', []) \<in> iclosure (infG G) 0 (lrstate (infG G) 0 {init_item Sh St' dm 0} \<gamma>)\<close>
    by (simp add: iclosure_base)
  have \<open>Sh \<notin> fst ` infG G\<close> unfolding Sh_def by (rule fresh_startD(1)[OF fresh_start_infG[OF fn]])
  from lrstate_sh[OF this memcl] have \<open>arhs' = [Nt St']\<close> and disj: \<open>m' = 0 \<and> \<gamma> = [] \<or> m' = 1 \<and> \<gamma> = [Nt St']\<close>
    by auto
  have \<open>m' \<noteq> 0\<close> using pre' lenarhs by (cases m'; cases arhs) auto
  with disj have \<open>m' = Suc 0\<close> by simp
  with run Ssne mem' \<open>arhs' = _\<close> have \<open>lr_accepts (infG G) 0 Sh St' dm (tcols w)\<close>
    unfolding lr_accepts_def by auto
  thus ?thesis using lr_lang[OF fn, of 0 dm w] unfolding Sh_def St'_def by simp
qed

theorem gaccepts_complete:
  fixes G :: \<open>('n, 'tok) is_cfg\<close>
  assumes fn: \<open>fresh_name G Shn\<close> and \<open>w \<in> ilang G\<close>
  shows \<open>\<exists>acts. gaccepts G Shn acts (tcols w)\<close>
proof -
  define dm where \<open>dm = (undefined :: 'tok \<times> nat)\<close>
  define Sh where \<open>Sh = (Shn, istart_ind G)\<close>
  define St' where \<open>St' = (istart G, istart_ind G)\<close>
  have \<open>lr_accepts (infG G) 0 Sh St' dm (tcols w)\<close>
    using lr_lang[OF fn, of 0 dm w] assms(2) unfolding Sh_def St'_def by simp
  then obtain Ss' u where run: \<open>(lr_step (infG G) 0)\<^sup>*\<^sup>* ([{init_item Sh St' dm 0}], tcols w) (Ss', [])\<close>
    and Ssne: \<open>Ss' \<noteq> []\<close> and item: \<open>((Sh, [Nt St']), Suc 0, u) \<in> hd Ss'\<close>
    unfolding lr_accepts_def by auto
  from lr_to_grun[OF run[unfolded Sh_def St'_def] xinit_rel] obtain acts Ys where
    grun: \<open>grun G acts ([xinit G Shn], tcols w) = Some (Ys, [])\<close> and rel: \<open>stack_rel Ss' (map xset Ys)\<close>
    unfolding Sh_def St'_def by blast
  have Ysne: \<open>Ys \<noteq> []\<close> using stack_rel_length[OF rel] Ssne by fastforce

  from item obtain arhs\<^sub>2 m\<^sub>2 where mem\<^sub>2: \<open>((Sh, arhs\<^sub>2), m\<^sub>2, u) \<in> fconcs (xset (hd Ys))\<close>
    and pre\<^sub>2: \<open>map unann (take m\<^sub>2 arhs\<^sub>2) = map unann (take (Suc 0) [Nt St'])\<close>
    and drop\<^sub>2: \<open>drop m\<^sub>2 arhs\<^sub>2 = drop (Suc 0) [Nt St']\<close>
    by (rule iequiv_memD[OF iequiv_sym[OF stack_rel_hd(1)[OF rel Ssne, unfolded hd_map[OF Ysne]]]])
  from mem\<^sub>2[unfolded Sh_def] obtain rhs\<^sub>B R where
    xit: \<open>((Shn, rhs\<^sub>B), m\<^sub>2, R) \<in> set (hd Ys)\<close> and inR: \<open>istart_ind G \<in> irep_set R\<close>
    and ann\<^sub>2: \<open>annotates (istart_ind G) rhs\<^sub>B arhs\<^sub>2\<close>
    by (rule fconcs_xset_memD)
  have \<open>wf_fitems (xset (hd Ys))\<close> using stack_rel_hd(3)[OF rel Ssne] Ysne by (simp add: hd_map)
  with xit have \<open>m\<^sub>2 \<le> length rhs\<^sub>B\<close> unfolding wf_fitems_def xset_def by (force simp: xconc_triple)
  moreover have \<open>length (map unann (take m\<^sub>2 arhs\<^sub>2)) = Suc 0\<close> using pre\<^sub>2 by simp
  moreover have \<open>length arhs\<^sub>2 \<le> m\<^sub>2\<close> using drop\<^sub>2 by simp
  ultimately have \<open>m\<^sub>2 = Suc 0\<close> using annotates_length[OF ann\<^sub>2] by (simp add: min_def)
  with xit inR have \<open>list_ex (\<lambda>(pr, m, R). fst pr = Shn \<and> m = Suc 0 \<and> irep_mem (istart_ind G) R) (hd Ys)\<close>
    by (fastforce simp: list_ex_iff)
  thus ?thesis using grun Ysne unfolding gaccepts_def by (intro exI[of _ acts]) simp
qed

text \<open>
  What this section provides, and what it does not.  Three machines exist.
  Algorithm 8 (\<^const>\<open>lr_step\<close>, \<^const>\<open>lr_accepts\<close>) is the paper's LR(k)
  machine for every \<open>k\<close>, with the lookahead sets \<^const>\<open>Hk\<close> as sets;
  \<^text>\<open>lr_lang\<close> proves it accepts exactly \<^const>\<open>ilang\<close>, but nothing
  computes \<^const>\<open>Hk\<close>, so it is a specification.  The factored machine
  (\<^const>\<open>flr_step\<close>) is bisimilar to it, and at the level formalized here
  the factoring loses nothing: the correspondences for lookahead sets,
  closure and GOTO are equalities.  The executable machine
  (\<^const>\<open>gstep\<close>, \<^const>\<open>gaccepts\<close>) is the factored machine at
  \<open>k = 0\<close> with the finite \<^typ>\<open>indrep\<close> representation; it is a GLR
  acceptor, i.e. it asks whether \<^emph>\<open>some\<close> action sequence accepts rather
  than choosing one.

  Lookahead is not computed in this theory.  The paper's Sect. 5.6 compresses
  the lookahead components into finite tuples, over-approximating them
  (the conflicts Sect. 5.7 discusses), and omits the \<open>k \<ge> 1\<close> lookahead
  computation as intricate.  This development takes a different route to the
  same effect: theory \<^text>\<open>LR\<close> propagates one token of LALR-style
  lookahead, with the layout relation attached, over the LR(0) automaton of
  the \<open>k = 0\<close> frames, and \<^text>\<open>LR_Driver\<close> runs a deterministic
  parser licensed by those cells.  That parser is an LALR(1)-style parser with
  layout constraints, not the canonical LR(1) instance of Algorithm 8: its
  static conflict check is stronger than the LR(1) condition of Sect. 5.6,
  and no theorem yet relates the cells to \<^const>\<open>Hk\<close> at \<open>k = 1\<close>.
  Sect. 5.8 is an efficiency discussion with no formal content.
\<close>

end
