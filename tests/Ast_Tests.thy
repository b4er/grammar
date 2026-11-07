theory Ast_Tests
  imports LR_Parser.LR_Prec_Parse Parser_Check
begin

section \<open>\<^theory_text>\<open>parser (ast)\<close>: the tree, no decoder\<close>

text \<open>\<^theory_text>\<open>parser (ast) p for G\<close> returns the tree of \<^const>\<open>dparse\<close> and ignores the
  actions: \<open>p.sound\<close> says the tree is the erasure of a parse tree of the word,
  \<open>p.complete\<close> that the erasure of every parse tree is returned for its yield.\<close>

fun toks :: \<open>nat \<Rightarrow> 'tok list \<Rightarrow> ('tok, unit) token list\<close> where
  \<open>toks i [] = []\<close>
| \<open>toks i (x # xs) = \<lparr>tok = x, span = span.make 0 i i 1 []\<rparr> # toks (Suc (Suc i)) xs\<close>

text \<open>A token at a line and a column.\<close>

definition tk :: \<open>nat \<Rightarrow> nat \<Rightarrow> 'tok \<Rightarrow> ('tok, unit) token\<close> where
  \<open>tk l c x = \<lparr>tok = x, span = span.make l c c 1 []\<rparr>\<close>

datatype a_tok = AId | APlus | AStar | ANum | AKw | AErr

text \<open>The tree without the token records, for the checks.\<close>

datatype ('n, 't) tr = TL 't | TN 'n \<open>('n, 't) tr list\<close>

fun shape :: \<open>('m, 'ch, 'n, 't) ast \<Rightarrow> ('n, 't) tr\<close> where
  \<open>shape (Leaf x) = TL (tok x)\<close>
| \<open>shape (Node n ts) = TN n (map shape ts)\<close>

ML \<open>
  (* the premises of a theorem, but for the ones of the grammar *)
  fun nprems ctxt name = Thm.nprems_of (Proof_Context.get_thm ctxt name);
\<close>


subsection \<open>Layout-free\<close>

text \<open>With a relation, which \<open>(ast)\<close> does not read, and an entry.\<close>

grammar (relation) ae =
  tokens \<open>a_tok\<close>
  terminals "+" = \<open>APlus\<close>
  productions
    E :: \<open>nat\<close> = E "+" T \<Rightarrow> \<open>(+)\<close> | T
  and
    T :: \<open>nat\<close> = AId \<Rightarrow> \<open>\<lambda>_. 1\<close> | AErr \<Rightarrow> \<open>\<lambda>_. 0\<close>

parser (ast) ae_parse for ae recover AErr and ae_t for ae (T)

thm ae_parse.sound ae_parse.complete ae_parse.sound_lang ae_parse.complete_lang
  ae_parse_recover.no_error

ML_val \<open>
  \<^assert> (nprems \<^context> "ae_parse.sound" = 1);
  \<^assert> (nprems \<^context> "ae_parse.complete" = 2);
  \<^assert> (nprems \<^context> "ae_parse.complete_lang" = 1);
  \<^assert> (nprems \<^context> "ae_parse_recover.no_error" = 2);
\<close>

parser_check \<open>map_option shape (ae_parse (toks 0 [AId, APlus, AId])) =
  Some (TN ''E'' [TN ''E'' [TN ''T'' [TL AId]], TL APlus, TN ''T'' [TL AId]])\<close>
parser_check \<open>ae_parse (toks 0 [AId, AId]) = None\<close>
parser_check \<open>isl (ae_parse_diag (toks 0 [AId, AId]))\<close>
parser_check \<open>map_option shape (snd (ae_parse_recover (toks 0 [AId, APlus, APlus, AId]))) =
  Some (TN ''E'' [TN ''E'' [TN ''E'' [TN ''T'' [TL AId]], TL APlus, TN ''T'' [TL AErr]],
    TL APlus, TN ''T'' [TL AId]])\<close>

text \<open>The decoding parser of the same grammar is unchanged.\<close>

parser ae_value for ae

parser_check \<open>ae_value (toks 0 [AId, APlus, AId]) = Some 2\<close>
thm ae_value.sound

parser_check \<open>map_option shape (ae_t (toks 0 [AId])) = Some (TN ''T'' [TL AId])\<close>
thm ae_t.sound ae_t.complete


subsection \<open>Layout\<close>

grammar ab =
  tokens \<open>a_tok\<close>
  productions
    Ds :: \<open>nat list\<close> = Decl\<^sup>= \<Rightarrow> \<open>\<lambda>x. [x]\<close> | Ds\<^sup>= Decl\<^sup>= \<Rightarrow> \<open>\<lambda>xs x. xs @ [x]\<close>
  and
    Decl :: \<open>nat\<close> = AId\<^sup>= \<Rightarrow> \<open>\<lambda>_. 1\<close> | AKw\<^sup>= Ds\<^sup>> \<Rightarrow> \<open>\<lambda>_ ds. sum_list ds\<close>

parser (ast, no_diagnostics) ab_parse for ab

ML_val \<open>
  \<^assert> (nprems \<^context> "ab_parse.sound" = 1);
  \<^assert> (nprems \<^context> "ab_parse.complete" = 2);
\<close>

text \<open>The column decides the tree: the second \<open>AId\<close> in column 0 is a declaration of
  its own, in column 2 one of the block.\<close>

parser_check \<open>map_option shape (ab_parse [tk 0 0 AKw, tk 1 2 AId, tk 2 0 AId]) =
  Some (TN ''Ds'' [TN ''Ds'' [TN ''Decl'' [TL AKw, TN ''Ds'' [TN ''Decl'' [TL AId]]]],
    TN ''Decl'' [TL AId]])\<close>
parser_check \<open>map_option shape (ab_parse [tk 0 0 AKw, tk 1 2 AId, tk 2 2 AId]) =
  Some (TN ''Ds'' [TN ''Decl'' [TL AKw,
    TN ''Ds'' [TN ''Ds'' [TN ''Decl'' [TL AId]], TN ''Decl'' [TL AId]]]])\<close>
parser_check \<open>ab_parse [tk 0 0 AKw, tk 1 0 AId] = None\<close>


subsection \<open>Precedence declarations\<close>

text \<open>The tree speaks of the grammar as written, not of the restricted one.\<close>

grammar ap =
  tokens \<open>a_tok\<close>
  terminals "+" = \<open>APlus\<close> and "*" = \<open>AStar\<close>
  precedence left "*" > left "+"
  productions
    E :: \<open>nat\<close> = E "+" E \<Rightarrow> \<open>(+)\<close> | E "*" E \<Rightarrow> \<open>(*)\<close> | ANum \<Rightarrow> \<open>\<lambda>_. 1\<close>

parser (ast) ap_parse for ap

thm ap_parse.sound ap_parse.complete

ML_val \<open>
  \<^assert> (nprems \<^context> "ap_parse.sound" = 1);
  \<^assert> (nprems \<^context> "ap_parse.complete" = 3);
\<close>

parser_check \<open>map_option shape (ap_parse (toks 0 [ANum, APlus, ANum, AStar, ANum])) =
  Some (TN ''E'' [TN ''E'' [TL ANum], TL APlus,
    TN ''E'' [TN ''E'' [TL ANum], TL AStar, TN ''E'' [TL ANum]]])\<close>

end
