(* Author: Basil Fürer, Dmitriy Traytel *)

theory Grammar_Command
  imports TIGER_Grammar_Model.Grammar_Base
  keywords "grammar" :: thy_decl
    and "tokens" "terminals" "productions"
    and "^=" "^>=" "^>" "*"
    and "\<Rightarrow>" "=>"
    and "parser" :: thy_decl
    and "for"
begin

section \<open>The grammar and parser commands\<close>

text \<open>The commands are described in the manual, the theory \<open>TIGER\<close> of the session
  \<open>TIGER\<close> (\<^verbatim>\<open>TIGER.thy\<close>).\<close>

subsection \<open>The span of a yield\<close>

text \<open>An alternative that writes \<open>@span\<close> passes its action the span of its yield,
  from the first token to the last (\<open>word_span\<close>): line, column and offset of
  the first token, the length up to the end of the last, and the concatenated texts of
  the tokens. The decoders compute it on the children of a node
  (\<open>yield_span\<close>), the relation on the word; \<open>ast_yield_erase\<close> makes the two
  agree.\<close>

fun ast_yield :: \<open>('m, 'ch, 'n, 'tok) ast \<Rightarrow> ('m, 'ch, 'tok) tword\<close> where
  \<open>ast_yield (Leaf t) = [t]\<close>
| \<open>ast_yield (Node n ts) = concat (map ast_yield ts)\<close>

definition word_span :: \<open>('m, 'ch, 'tok) tword \<Rightarrow> 'ch span\<close> where
  \<open>word_span w =
    (case w of
      [] \<Rightarrow> \<lparr>s_line = 0, s_col = 0, s_off = 0, s_len = 0, s_txt = []\<rparr>
    | t # _ \<Rightarrow>
        \<lparr>s_line = s_line (span t), s_col = s_col (span t), s_off = s_off (span t),
         s_len = s_off (span (last w)) + s_len (span (last w)) - s_off (span t),
         s_txt = concat (map (s_txt \<circ> span) w)\<rparr>)\<close>

definition yield_span :: \<open>('m, 'ch, 'n, 'tok) ast list \<Rightarrow> 'ch span\<close> where
  \<open>yield_span xs = word_span (concat (map ast_yield xs))\<close>

lemma ast_yield_erase [simp]: \<open>ast_yield (erase pt) = pyield pt\<close>
  by (induction pt) (simp_all cong: map_cong)

(*<*)
fun ast_first :: \<open>('m, 'ch, 'n, 'tok) ast list \<Rightarrow> ('tok, 'ch, 'm) token_scheme option\<close> where
  \<open>ast_first [] = None\<close>
| \<open>ast_first (Leaf t # _) = Some t\<close>
| \<open>ast_first (Node _ ts # xs) = (case ast_first ts of None \<Rightarrow> ast_first xs | r \<Rightarrow> r)\<close>

fun ast_last :: \<open>('m, 'ch, 'n, 'tok) ast list \<Rightarrow> ('tok, 'ch, 'm) token_scheme option\<close> where
  \<open>ast_last [] = None\<close>
| \<open>ast_last (x # xs) =
    (case ast_last xs of
      None \<Rightarrow> (case x of Leaf t \<Rightarrow> Some t | Node _ ts \<Rightarrow> ast_last ts)
    | r \<Rightarrow> r)\<close>

fun hd_opt :: \<open>'a list \<Rightarrow> 'a option\<close> where
  \<open>hd_opt [] = None\<close>
| \<open>hd_opt (x # _) = Some x\<close>

lemma hd_opt_append: \<open>hd_opt (a @ b) = (case hd_opt a of None \<Rightarrow> hd_opt b | r \<Rightarrow> r)\<close>
  by (cases a) auto

lemma hd_opt_rev: \<open>hd_opt (rev c) = (if c = [] then None else Some (last c))\<close>
  by (induction c) (auto simp: hd_opt_append split: option.split)

lemma ast_first_yield: \<open>ast_first xs = hd_opt (concat (map ast_yield xs))\<close>
  by (induction xs rule: ast_first.induct) (auto simp: hd_opt_append split: option.split)

lemma ast_last_yield: \<open>ast_last xs = hd_opt (rev (concat (map ast_yield xs)))\<close>
  by (induction xs rule: ast_last.induct) (auto simp: hd_opt_append split: option.split ast.split)

text \<open>The texts by an accumulator: on a left-recursive spine, \<open>concat (map ast_yield xs)\<close>
  would rebuild the left-nested appends at every node.\<close>

fun ast_txts :: \<open>('m, 'ch, 'n, 'tok) ast list \<Rightarrow> 'ch list \<Rightarrow> 'ch list\<close> where
  \<open>ast_txts [] acc = acc\<close>
| \<open>ast_txts (Leaf t # xs) acc = s_txt (span t) @ ast_txts xs acc\<close>
| \<open>ast_txts (Node _ ts # xs) acc = ast_txts ts (ast_txts xs acc)\<close>

lemma ast_txts_yield:
  \<open>ast_txts xs acc = concat (map (s_txt \<circ> span) (concat (map ast_yield xs))) @ acc\<close>
  by (induction xs acc rule: ast_txts.induct) simp_all

lemma yield_span_code [code]:
  \<open>yield_span xs =
    (case ast_first xs of
      None \<Rightarrow> \<lparr>s_line = 0, s_col = 0, s_off = 0, s_len = 0, s_txt = []\<rparr>
    | Some t \<Rightarrow>
        (case ast_last xs of
          None \<Rightarrow> undefined
        | Some z \<Rightarrow>
            \<lparr>s_line = s_line (span t), s_col = s_col (span t), s_off = s_off (span t),
             s_len = s_off (span z) + s_len (span z) - s_off (span t),
             s_txt = ast_txts xs []\<rparr>))\<close>
proof -
  obtain c where c: \<open>concat (map ast_yield xs) = c\<close> by blast
  show ?thesis
    unfolding yield_span_def word_span_def ast_first_yield ast_last_yield ast_txts_yield c
    by (cases c) (simp_all add: hd_opt_rev del: rev.simps)
qed
(*>*)

(*<*)
ML_file \<open>grammar_common.ML\<close>
ML_file \<open>grammar_ptree_induct.ML\<close>
ML_file \<open>grammar_defs.ML\<close>
ML_file \<open>grammar_rel.ML\<close>
ML_file \<open>grammar_expand.ML\<close>
ML_file \<open>grammar_elab.ML\<close>
ML_file \<open>grammar_syntax.ML\<close>

ML_file \<open>parser_dec_total.ML\<close>
ML_file \<open>parser_rel_bridge.ML\<close>
ML_file \<open>parser_generators.ML\<close>

hide_fact
  lang_of_complete
  wf_ptree_Tm_leaf
  erase_Nt_E2
  proot_Tm_E
  case_ast_Nt_None
(*>*)

subsection \<open>The prelude\<close>

text \<open>Generic templates, used as \<open>List(X)\<close>, \<open>Sep1(X, S)\<close> and so on.\<close>

grammar Grammar_Prelude =
  productions
    List(X) :: \<open>'x list\<close> = \<Rightarrow> \<open>[]\<close> | List(X) X \<Rightarrow> \<open>\<lambda>xs x. xs @ [x]\<close>
  and
    List1(X) :: \<open>'x list\<close> = X \<Rightarrow> \<open>\<lambda>x. [x]\<close> | List1(X) X \<Rightarrow> \<open>\<lambda>xs x. xs @ [x]\<close>
  and
    Opt(X) :: \<open>'x option\<close> = \<Rightarrow> \<open>None\<close> | X \<Rightarrow> \<open>Some\<close>
  and
    Sep1(X, S) :: \<open>'x list\<close> = X \<Rightarrow> \<open>\<lambda>x. [x]\<close> | Sep1(X, S) S X \<Rightarrow> \<open>\<lambda>xs x. xs @ [x]\<close>
  and
    Sep(X, S) :: \<open>'x list\<close> = \<Rightarrow> \<open>[]\<close> | Sep1(X, S)

end
