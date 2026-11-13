(* Author: Basil Fürer *)

theory TIGER_Driver
  imports TIGER_Lexer
begin

section \<open>The driver\<close>

text \<open>The driver lexes a whole input. It steps the runner of the mode on top of the
  stack, applies the action of the winning rule and stops when no step applies: the
  stack is empty, no rule matches, or the action returns the empty stack. It returns
  the lexed source, the residue and the stack it stops in
  \<^cite>\<open>\<open>Sect.~10\<close> in "paxson2026-flex-manual"\<close>
  \<^cite>\<open>\<open>Fig.~4, Tokens\<close> in "egolf2021-verbatim-verified-lexer"\<close>. Trivia go into the
  header or the trailing trivia of the token before them, spans come from
  \<^const>\<open>span_at\<close> and \<^const>\<open>advance_list\<close>.

  The driver is generic in the runner \<open>R\<close>, which maps a mode and an input to the winning
  rule, the lexeme and the rest. It takes the rest as \<^term>\<open>drop (length p) s\<close>, which
  makes the termination argument independent of \<open>R\<close>, and it stops on an empty lexeme,
  which a correct runner never returns.\<close>

fun drive ::
  \<open>('m \<Rightarrow> 'ch list \<Rightarrow> (nat \<times> 'ch list \<times> 'ch list) option) \<Rightarrow> ('k, 'p, 'ch, 'm) lexer_spec \<Rightarrow>
    ('ch \<Rightarrow> bool) \<Rightarrow> 'm list \<Rightarrow> pos \<Rightarrow> 'ch list \<Rightarrow> ('k, 'ch) lexed \<times> 'ch list \<times> 'm list\<close>
where
  \<open>drive R sp is_newline [] q s = (Lexed [] [], s, [])\<close>
| \<open>drive R sp is_newline (m # st) q [] = (Lexed [] [], [], m # st)\<close>
| \<open>drive R sp is_newline (m # st) q (c # v) =
    (case R m (c # v) of
      None \<Rightarrow> (Lexed [] [], c # v, m # st)
    | Some (i, p, _) \<Rightarrow>
        (case act (sp m ! i) p (m # st) of
          (k, st') \<Rightarrow>
            if p = [] \<or> st' = [] then (Lexed [] [], c # v, m # st)
            else
              (case drive R sp is_newline st' (advance_list is_newline p q)
                  (drop (length p) (c # v)) of
                (Lexed h ts, r, st\<^sub>f) \<Rightarrow>
                  (case k of
                    None \<Rightarrow> (Lexed (p @ h) ts, r, st\<^sub>f)
                  | Some k \<Rightarrow>
                      (Lexed [] (\<lparr>tok = k, span = span_at q p, trivia = h\<rparr> # ts), r, st\<^sub>f)))))\<close>

text \<open>A spec whose modes are the numbers below the length of a list, with no rules in
  the other modes. Tables for such a spec are an array indexed by the mode, so the
  driver never compares modes:\<close>

definition list_spec :: \<open>'a list list \<Rightarrow> nat \<Rightarrow> 'a list\<close> where
  \<open>list_spec sps m = (if m < length sps then sps ! m else [])\<close>

context symbolic
begin

subsection \<open>The invariant\<close>

text \<open>\<open>R\<close> runs the modes of \<open>sp\<close> if it returns exactly the winning rule and lexeme of
  \<^const>\<open>first_token\<close> in each mode:\<close>

definition mode_runner ::
  \<open>('k, 'p, 'ch, 'm) lexer_spec \<Rightarrow> ('m \<Rightarrow> 'ch list \<Rightarrow> (nat \<times> 'ch list \<times> 'ch list) option) \<Rightarrow>
    bool\<close>
where
  \<open>mode_runner sp R \<longleftrightarrow>
    (\<forall>m s i p rest. R m s = Some (i, p, rest) \<longleftrightarrow> first_token (sp m) i p s \<and> s = p @ rest)\<close>

lemma step_iff_mode_runner:
  assumes \<open>mode_runner sp R\<close>
  shows \<open>step sp (m # st) s (k, p, st', s') \<longleftrightarrow>
    (\<exists>i. R m s = Some (i, p, s') \<and> act (sp m ! i) p (m # st) = (k, st') \<and> st' \<noteq> [])\<close>
  using assms by (auto simp: mode_runner_def step.simps)

lemma lexes_drive:
  assumes \<open>mode_runner sp R\<close>
  shows \<open>case drive R sp is_newline st q s of
    (l, r, st\<^sub>f) \<Rightarrow> lexes sp is_newline st q s l r st\<^sub>f\<close>
  using assms
proof (induction R sp is_newline st q s rule: drive.induct)
  case (1 R sp is_newline q s)
  then show ?case
    by (auto intro: lexes_stop elim: step.cases)
next
  case (2 R sp is_newline m st q)
  have \<open>\<not> step sp (m # st) [] x\<close> for x
    by (auto elim!: step.cases first_token.cases match_rule.cases)
  then show ?case
    by (auto intro: lexes_stop)
next
  case (3 R sp is_newline m st q c v)
  note runner = step_iff_mode_runner[OF \<open>mode_runner sp R\<close>]
  show ?case
  proof (cases \<open>R m (c # v)\<close>)
    case None
    then have \<open>\<not> step sp (m # st) (c # v) x\<close> for x
      using runner by (cases x) auto
    with None show ?thesis
      by (auto intro: lexes_stop)
  next
    case (Some x)
    then obtain i p rest where R: \<open>R m (c # v) = Some (i, p, rest)\<close>
      by (cases x) auto
    with \<open>mode_runner sp R\<close> have \<open>first_token (sp m) i p (c # v)\<close> \<open>c # v = p @ rest\<close>
      by (auto simp: mode_runner_def)
    then have \<open>p \<noteq> []\<close> and rest: \<open>drop (length p) (c # v) = rest\<close>
      by (auto dest!: first_token_match elim: match_rule.cases)
    obtain k st' where act: \<open>act (sp m ! i) p (m # st) = (k, st')\<close>
      by (cases \<open>act (sp m ! i) p (m # st)\<close>)
    show ?thesis
    proof (cases \<open>st' = []\<close>)
      case True
      then have \<open>\<not> step sp (m # st) (c # v) y\<close> for y
        using runner R act by (cases y) auto
      with R act True show ?thesis
        by (auto intro: lexes_stop)
    next
      case False
      with R act have step: \<open>step sp (m # st) (c # v) (k, p, st', rest)\<close>
        using runner by auto
      let ?d = \<open>drive R sp is_newline st' (advance_list is_newline p q) rest\<close>
      from "3.IH"[OF R refl refl act[symmetric]] False \<open>p \<noteq> []\<close> \<open>mode_runner sp R\<close> rest
      have IH: \<open>case ?d of (l, r, st\<^sub>f) \<Rightarrow>
        lexes sp is_newline st' (advance_list is_newline p q) rest l r st\<^sub>f\<close>
        by simp
      obtain h ts r st\<^sub>f where d: \<open>?d = (Lexed h ts, r, st\<^sub>f)\<close>
        by (metis lexed.exhaust prod.exhaust)
      from IH d step R act False \<open>p \<noteq> []\<close> rest show ?thesis
        by (cases k) (auto intro: lexes_token lexes_trivia)
    qed
  qed
qed

text \<open>The driver returns a run of the spec (\<open>lexes_drive\<close>), and by determinism of the spec
  that run is the only one. This is how Verbatim gets Completeness from Soundness and
  Uniqueness \<^cite>\<open>\<open>Sects.~V-A--V-C\<close> in "egolf2021-verbatim-verified-lexer"\<close>. Verbatim
  assumes unambiguous rules (each label has one regex); this driver needs only a correct
  runner.\<close>

theorem drive_iff_lexes:
  assumes \<open>mode_runner sp R\<close>
  shows \<open>drive R sp is_newline st q s = (l, r, st\<^sub>f) \<longleftrightarrow> lexes sp is_newline st q s l r st\<^sub>f\<close>
proof
  assume \<open>drive R sp is_newline st q s = (l, r, st\<^sub>f)\<close>
  with lexes_drive[OF assms, of is_newline st q s] show \<open>lexes sp is_newline st q s l r st\<^sub>f\<close>
    by simp
next
  assume \<open>lexes sp is_newline st q s l r st\<^sub>f\<close>
  with lexes_drive[OF assms, of is_newline st q s]
  show \<open>drive R sp is_newline st q s = (l, r, st\<^sub>f)\<close>
    by (auto split: prod.splits dest: lexes_deterministic)
qed

end

context eba
begin

text \<open>The driver over the DFA runner of each mode, with a classifier for each mode:\<close>

definition run_lexer ::
  \<open>('k, 'p, 'ch, 'm) lexer_spec \<Rightarrow> ('m \<Rightarrow> 'ch \<Rightarrow> nat) \<Rightarrow> ('ch \<Rightarrow> bool) \<Rightarrow> 'm list \<Rightarrow> pos \<Rightarrow>
    'ch list \<Rightarrow> ('k, 'ch) lexed \<times> 'ch list \<times> 'm list\<close>
where
  \<open>run_lexer sp cls = drive (\<lambda>m. run_dfa (sp m) (cls m)) sp\<close>

lemma mode_runner_run_dfa:
  assumes \<open>\<And>m. minterm_classifier (sp m) (cls m)\<close>
  shows \<open>mode_runner sp (\<lambda>m. run_dfa (sp m) (cls m))\<close>
  using run_dfa_Some_iff[OF assms] by (simp add: mode_runner_def)

section \<open>Surface theorems\<close>

text \<open>With a classifier into the minterms of each mode, the driver returns exactly the
  lexed source, the residue and the final stack of \<^const>\<open>lexes\<close>:\<close>

theorem run_lexer_iff_lexes:
  assumes \<open>\<And>m. minterm_classifier (sp m) (cls m)\<close>
  shows \<open>run_lexer sp cls is_newline st q s = (l, r, st\<^sub>f) \<longleftrightarrow>
    lexes sp is_newline st q s l r st\<^sub>f\<close>
  unfolding run_lexer_def by (rule drive_iff_lexes[OF mode_runner_run_dfa[OF assms]])

end

end
