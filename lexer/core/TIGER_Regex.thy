(* Author: Basil Fürer *)

theory TIGER_Regex
  imports "Regular-Sets.Derivatives"
begin

section \<open>Symbolic regular expressions\<close>

text \<open>A symbolic regular expression is a \<^typ>\<open>'p rexp\<close> of \<^session>\<open>Regular-Sets\<close> whose
  atoms are syntactic predicates. A denotation \<open>sem :: 'p \<Rightarrow> 'ch \<Rightarrow> bool\<close> says which
  characters a predicate holds for \<^cite>\<open>\<open>Sect.~2\<close> in
  "dantoni2014-minimization-symbolic-automata"\<close>. We reuse the datatype rather than copy it
  (its \<^const>\<open>nullable\<close>, \<^const>\<open>atoms\<close> and partial derivatives then apply unchanged).

  Predicates are syntax, not functions (the generator compares regexes and decides
  satisfiability of predicates, and functions allow neither). The locale \<open>symbolic\<close> fixes
  \<open>sem\<close>, and \<open>'ch\<close> carries no type class. Definitions that need no denotation stay
  outside it.

  The language \<^const>\<open>lang\<close> reads an atom as the characters its denotation holds for.

  This theory defines the derivative \<^cite>\<open>"brzozowski1964-derivatives-regular-expressions"\<close>,
  the partial derivative \<^cite>\<open>"antimirov1996-partial-derivatives"\<close> by a character and by a
  predicate class, proves both language-correct and proves that the partial derivatives
  of a regex are finitely many.\<close>

abbreviation Pred :: \<open>'p \<Rightarrow> 'p rexp\<close> where
  \<open>Pred \<equiv> Atom\<close>

locale symbolic =
  fixes sem :: \<open>'p \<Rightarrow> 'ch \<Rightarrow> bool\<close>
begin

primrec lang :: \<open>'p rexp \<Rightarrow> 'ch lang\<close> where
  \<open>lang Zero = {}\<close>
| \<open>lang One = {[]}\<close>
| \<open>lang (Pred p) = {[c] | c. sem p c}\<close>
| \<open>lang (Plus r s) = lang r \<union> lang s\<close>
| \<open>lang (Times r s) = lang r @@ lang s\<close>
| \<open>lang (Star r) = star (lang r)\<close>

text \<open>\<^const>\<open>Regular_Exp.lang\<close> would read \<^term>\<open>Pred p\<close> as the one-letter word \<open>[p]\<close>
  over the alphabet of predicates. \<^const>\<open>lang\<close> is the symbolic reading.\<close>

lemma nullable_iff: \<open>nullable r \<longleftrightarrow> [] \<in> lang r\<close>
  by (induct r) (auto simp: conc_def)

subsection \<open>Derivative\<close>

primrec deriv :: \<open>'ch \<Rightarrow> 'p rexp \<Rightarrow> 'p rexp\<close> where
  \<open>deriv c Zero = Zero\<close>
| \<open>deriv c One = Zero\<close>
| \<open>deriv c (Pred p) = (if sem p c then One else Zero)\<close>
| \<open>deriv c (Plus r s) = Plus (deriv c r) (deriv c s)\<close>
| \<open>deriv c (Times r s) =
    (if nullable r then Plus (Times (deriv c r) s) (deriv c s)
     else Times (deriv c r) s)\<close>
| \<open>deriv c (Star r) = Times (deriv c r) (Star r)\<close>

text \<open>The derivative of \<open>r\<close> by \<open>c\<close> denotes the words \<open>w\<close> with \<open>c # w \<in> lang r\<close>
  \<^cite>\<open>\<open>Thm.~3.1\<close> in "brzozowski1964-derivatives-regular-expressions"\<close>:\<close>

lemma Deriv_Pred[simp]: \<open>Deriv c {[d] | d. P d} = (if P c then {[]} else {})\<close>
  by (auto simp: Deriv_def)

lemma lang_deriv: \<open>lang (deriv c r) = Deriv c (lang r)\<close>
  by (induct r) (simp_all add: nullable_iff)

subsection \<open>Partial derivatives\<close>

primrec pderiv :: \<open>'ch \<Rightarrow> 'p rexp \<Rightarrow> 'p rexp set\<close> where
  \<open>pderiv c Zero = {}\<close>
| \<open>pderiv c One = {}\<close>
| \<open>pderiv c (Pred p) = (if sem p c then {One} else {})\<close>
| \<open>pderiv c (Plus r s) = pderiv c r \<union> pderiv c s\<close>
| \<open>pderiv c (Times r s) =
    (if nullable r then Timess (pderiv c r) s \<union> pderiv c s
     else Timess (pderiv c r) s)\<close>
| \<open>pderiv c (Star r) = Timess (pderiv c r) (Star r)\<close>

primrec pderivs :: \<open>'ch list \<Rightarrow> 'p rexp \<Rightarrow> 'p rexp set\<close> where
  \<open>pderivs [] r = {r}\<close>
| \<open>pderivs (c # w) r = \<Union> (pderivs w ` pderiv c r)\<close>

text \<open>The partial derivatives of \<open>r\<close> by \<open>c\<close> are a set of regexes whose union denotes
  the derivative \<^cite>\<open>\<open>Def.~2.8, Prop.~2.10\<close> in "antimirov1996-partial-derivatives"\<close>.
  The proofs follow \<^session>\<open>Regular-Sets\<close> (\<open>Derivatives\<close>, @{thm [source]
  Derivatives.Deriv_pderiv} and @{thm [source] Derivatives.Derivs_pderivs}):\<close>

lemma Deriv_pderiv: \<open>Deriv c (lang r) = \<Union> (lang ` pderiv c r)\<close>
  by (induct r) (auto simp: nullable_iff conc_UNION_distrib)

lemma Derivs_pderivs: \<open>Derivs w (lang r) = \<Union> (lang ` pderivs w r)\<close>
proof (induct w arbitrary: r)
  case (Cons c w)
  have \<open>Derivs w (\<Union> (lang ` pderiv c r)) =
    (\<Union>r' \<in> pderiv c r. Derivs w (lang r'))\<close>
    by (auto simp: Derivs_def)
  then show ?case
    by (simp add: Deriv_pderiv Cons)
qed simp

end

subsection \<open>Partial derivatives by a predicate class\<close>

text \<open>A class is a set \<open>S\<close> of predicates, read as the characters for which exactly the
  predicates in \<open>S\<close> hold (so it needs no denotation). The partial derivative by a class
  treats every atom in \<open>S\<close> as true \<^cite>\<open>\<open>Sect.~5.2, Thm.~12\<close> in "keil2014-symbolic-regex-inequalities"\<close>:\<close>

primrec pderiv_cls :: \<open>'p set \<Rightarrow> 'p rexp \<Rightarrow> 'p rexp set\<close> where
  \<open>pderiv_cls S Zero = {}\<close>
| \<open>pderiv_cls S One = {}\<close>
| \<open>pderiv_cls S (Pred p) = (if p \<in> S then {One} else {})\<close>
| \<open>pderiv_cls S (Plus r s) = pderiv_cls S r \<union> pderiv_cls S s\<close>
| \<open>pderiv_cls S (Times r s) =
    (if nullable r then Timess (pderiv_cls S r) s \<union> pderiv_cls S s
     else Timess (pderiv_cls S r) s)\<close>
| \<open>pderiv_cls S (Star r) = Timess (pderiv_cls S r) (Star r)\<close>

primrec pderivs_cls :: \<open>'p set list \<Rightarrow> 'p rexp \<Rightarrow> 'p rexp set\<close> where
  \<open>pderivs_cls [] r = {r}\<close>
| \<open>pderivs_cls (S # Ss) r = \<Union> (pderivs_cls Ss ` pderiv_cls S r)\<close>

text \<open>The partial derivative by a class is a union of \<^session>\<open>Regular-Sets\<close> partial
  derivatives over the alphabet of predicates. This lifting lemma is the bridge to its
  finiteness theorem:\<close>

lemma pderiv_cls_eq_UN: \<open>pderiv_cls S r = (\<Union>p \<in> S. Derivatives.pderiv p r)\<close>
  by (induct r) auto

lemma pderiv_empty_if_notin_atoms: \<open>p \<notin> atoms r \<Longrightarrow> Derivatives.pderiv p r = {}\<close>
  by (induct r) simp_all

lemma atoms_if_pderiv: \<open>x \<in> Derivatives.pderiv p r \<Longrightarrow> p \<in> atoms r\<close>
  by (metis empty_iff pderiv_empty_if_notin_atoms)

lemma pderiv_cls_Int_atoms: \<open>pderiv_cls (S \<inter> atoms r) r = pderiv_cls S r\<close>
  unfolding pderiv_cls_eq_UN by (auto dest: atoms_if_pderiv)

context symbolic
begin

definition sig :: \<open>'p rexp \<Rightarrow> 'ch \<Rightarrow> 'p set\<close> where
  \<open>sig r c = {p \<in> atoms r. sem p c}\<close>

text \<open>The signature of \<open>c\<close> in \<open>r\<close> is the set of atoms of \<open>r\<close> that hold for \<open>c\<close>:\<close>

lemma pderiv_eq_pderiv_cls: \<open>pderiv c r = pderiv_cls {p. sem p c} r\<close>
  by (induct r) simp_all

text \<open>Characters with the same signature have the same partial derivatives
  \<^cite>\<open>\<open>Thm.~4.2\<close> in "owens2009-regex-derivatives-reexamined"\<close>, so the partial
  derivative by a class is the partial derivative by any of its characters:\<close>

lemma pderiv_eq_pderiv_cls_sig: \<open>pderiv c r = pderiv_cls (sig r c) r\<close>
proof -
  have \<open>sig r c = {p. sem p c} \<inter> atoms r\<close>
    by (auto simp: sig_def)
  then show ?thesis
    by (simp add: pderiv_eq_pderiv_cls pderiv_cls_Int_atoms)
qed

lemma pderiv_eq_if_sig_eq: \<open>sig r c = sig r d \<Longrightarrow> pderiv c r = pderiv d r\<close>
  by (simp add: pderiv_eq_pderiv_cls_sig)

lemma Deriv_pderiv_cls:
  \<open>sig r c = S \<inter> atoms r \<Longrightarrow> Deriv c (lang r) = \<Union> (lang ` pderiv_cls S r)\<close>
  by (simp add: Deriv_pderiv pderiv_eq_pderiv_cls_sig pderiv_cls_Int_atoms)

lemma pderivs_eq_pderivs_cls: \<open>pderivs w r = pderivs_cls (map (\<lambda>c. {p. sem p c}) w) r\<close>
  by (induct w arbitrary: r) (simp_all add: pderiv_eq_pderiv_cls)

end

subsection \<open>Finiteness\<close>

definition pderiv_closure :: \<open>'p rexp \<Rightarrow> 'p rexp set\<close> where
  \<open>pderiv_closure r = (\<Union>Ss. pderivs_cls Ss r)\<close>

text \<open>The closure of \<open>r\<close> under partial derivatives by classes contains the partial
  derivatives by all words. It is a subset of the \<^session>\<open>Regular-Sets\<close> partial
  derivatives of \<open>r\<close> over the alphabet of predicates, so @{thm [source]
  finite_pderivs_lang} and @{thm [source] card_pderivs_lang_UNIV_le_awidth} apply
  unchanged and no proof is copied \<^cite>\<open>\<open>Thm.~3.4\<close> in "antimirov1996-partial-derivatives"\<close>:\<close>

lemma pderivs_cls_subset_pderivs_lang: \<open>pderivs_cls Ss r \<subseteq> pderivs_lang UNIV r\<close>
proof (induct Ss arbitrary: r)
  case (Cons S Ss)
  show ?case
  proof
    fix x
    assume \<open>x \<in> pderivs_cls (S # Ss) r\<close>
    then obtain p r' where \<open>r' \<in> Derivatives.pderiv p r\<close> \<open>x \<in> pderivs_cls Ss r'\<close>
      by (auto simp: pderiv_cls_eq_UN)
    with Cons obtain u where \<open>r' \<in> Derivatives.pderiv p r\<close> \<open>x \<in> Derivatives.pderivs u r'\<close>
      by (auto simp: pderivs_lang_def)
    then have \<open>x \<in> Derivatives.pderivs (p # u) r\<close>
      by auto
    then show \<open>x \<in> pderivs_lang UNIV r\<close>
      unfolding pderivs_lang_def by blast
  qed
qed (simp add: pderivs_lang_UNIV)

lemma pderiv_closure_subset_pderivs_lang: \<open>pderiv_closure r \<subseteq> pderivs_lang UNIV r\<close>
  using pderivs_cls_subset_pderivs_lang by (fastforce simp: pderiv_closure_def)

lemma finite_pderiv_closure: \<open>finite (pderiv_closure r)\<close>
  using pderiv_closure_subset_pderivs_lang finite_pderivs_lang by (rule finite_subset)

lemma card_pderiv_closure_le_awidth: \<open>card (pderiv_closure r) \<le> awidth r + 1\<close>
  using card_mono[OF finite_pderivs_lang pderiv_closure_subset_pderivs_lang]
    card_pderivs_lang_UNIV_le_awidth by (rule le_trans)

context symbolic
begin

lemma pderivs_subset_pderiv_closure: \<open>pderivs w r \<subseteq> pderiv_closure r\<close>
  by (auto simp: pderiv_closure_def pderivs_eq_pderivs_cls)

lemma finite_pderivs_UNIV: \<open>finite (\<Union>w. pderivs w r)\<close>
  by (rule finite_subset[OF UN_least finite_pderiv_closure]) (rule pderivs_subset_pderiv_closure)

end

end
