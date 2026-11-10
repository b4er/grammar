theory Prec_Tests
  imports LR_Parser.LR_Prec_Parse Parser_Check
begin

text \<open>The theorems of \<^theory>\<open>LR_Parser.LR_Prec_Parse\<close> relate \<^const>\<open>restrict\<close> to
  \<^const>\<open>prec_ok\<close>. What they cannot say is that \<^const>\<open>prec_ok\<close> of a level table means what
  a reader expects, and that \<^const>\<open>restrict\<close> computes. Both are checked here on small
  grammars by enumerating every tree of every short word.\<close>

section \<open>Enumeration\<close>

datatype tk = TA | TP | TM | TI | TB

type_synonym tree = \<open>(unit, unit, string, tk) ptree\<close>
type_synonym word = \<open>(unit, unit, tk) tword\<close>

definition tk_at :: \<open>nat \<Rightarrow> tk \<Rightarrow> (tk, unit) token\<close> where
  \<open>tk_at c x = \<lparr>tok = x, span = span.make 0 c 0 1 []\<rparr>\<close>

fun cart :: \<open>'a list list \<Rightarrow> 'a list list\<close> where
  \<open>cart [] = [[]]\<close>
| \<open>cart (xs # xss) = concat (map (\<lambda>x. map (Cons x) (cart xss)) xs)\<close>

fun splits :: \<open>nat \<Rightarrow> 'a list \<Rightarrow> 'a list list list\<close> where
  \<open>splits 0 w = (if w = [] then [[]] else [])\<close>
| \<open>splits (Suc n) w = concat (map (\<lambda>i. map (Cons (take i w)) (splits n (drop i w))) [0..<Suc (length w)])\<close>

definition kids_ok :: \<open>(string, tk) rhs \<Rightarrow> nat \<Rightarrow> tree list \<Rightarrow> bool\<close> where
  \<open>kids_ok r i ts \<longleftrightarrow> list_all2 (\<lambda>a t. fst (proot t) = fst a \<and> irel_sat (snd a) (snd (proot t)) i) r ts\<close>

definition fits :: \<open>string list \<Rightarrow> (string, tk) rhs \<Rightarrow> word list \<Rightarrow> bool\<close> where
  \<open>fits ns r ws \<longleftrightarrow> list_all2 (\<lambda>a u. u \<noteq> [] \<or> sym_null ns (fst a)) r ws\<close>

text \<open>All trees of a word, with node indentations from \<open>ixs\<close>; \<open>f\<close> bounds the depth, \<open>ns\<close> are
  the nullable names, which keeps empty parts from branching.\<close>

fun gen :: \<open>(string, tk) is_cfg \<Rightarrow> string list \<Rightarrow> nat list \<Rightarrow> nat \<Rightarrow> (string, tk) sym \<Rightarrow> word \<Rightarrow> tree list\<close> where
  \<open>gen G ns ixs 0 X w = []\<close>
| \<open>gen G ns ixs (Suc f) (Tm t) w = (case w of [x] \<Rightarrow> if tok x = t then [PLeaf x] else [] | _ \<Rightarrow> [])\<close>
| \<open>gen G ns ixs (Suc f) (Nt n) w = concat (map (\<lambda>r. concat (map (\<lambda>ws.
       let kids = cart (map2 (\<lambda>a u. gen G ns ixs f (fst a) u) r ws) in
       concat (map (\<lambda>i. map (PNode n i) (filter (kids_ok r i) kids)) ixs))
       (filter (fits ns r) (splits (length r) w)))) (map snd (filter (\<lambda>p. fst p = n) (iprods G))))\<close>

text \<open>\<^const>\<open>pk\<close>, run on a tree.\<close>

fun chk :: \<open>nat \<Rightarrow> (string, tk) is_cfg \<Rightarrow> string list \<Rightarrow> (string, tk) forbid list \<Rightarrow>
    (string, tk) alt list \<Rightarrow> (string, tk) alt list \<Rightarrow> (string, tk) alt list \<Rightarrow> tree \<Rightarrow> bool\<close> where
  \<open>chk f G ns F Ds Rs Ls (PLeaf t) = True\<close>
| \<open>chk 0 G ns F Ds Rs Ls (PNode n i ts) = False\<close>
| \<open>chk (Suc f) G ns F Ds Rs Ls (PNode n i ts) = list_ex (\<lambda>p. fst p = n \<and> p \<notin> set Ds \<and> p \<notin> set Rs \<and>
     p \<notin> set Ls \<and> kids_ok (snd p) i ts \<and> list_all (\<lambda>k. chk f G ns F (fb F FDirect p k)
       (fb F FRight p k @ (if rpos ns (snd p) k then Rs else []))
       (fb F FLeft p k @ (if lpos ns (snd p) k then Ls else [])) (ts ! k)) [0..<length ts]) (iprods G)\<close>

definition words :: \<open>tk list \<Rightarrow> nat \<Rightarrow> word list\<close> where
  \<open>words ts n = concat (map (\<lambda>m. map (map (tk_at 0)) (cart (replicate m ts))) [0..<Suc n])\<close>

text \<open>The trees of \<open>G\<close> accepted by \<^const>\<open>prec_ok\<close> and those read back from \<open>G'\<close> agree
  on each word.\<close>

definition same_on :: \<open>(string, tk) is_cfg \<Rightarrow> (string, tk) prec_decl \<Rightarrow> nat list \<Rightarrow> nat \<Rightarrow> word list \<Rightarrow> bool\<close> where
  \<open>same_on G d ixs f ws = (let G' = restrict G d; ns = nulls G; ns' = nulls G'; F = forbids G d in
     list_all (\<lambda>w.
       set (filter (chk 12 G ns F [] [] []) (gen G ns ixs f (Nt (istart G)) w)) =
       set (map (plain orig_name) (gen G' ns' ixs (3 * f) (Nt (istart G')) w))) ws)\<close>

definition unique_on :: \<open>(string, tk) is_cfg \<Rightarrow> (string, tk) prec_decl \<Rightarrow> nat list \<Rightarrow> nat \<Rightarrow> word list \<Rightarrow> bool\<close> where
  \<open>unique_on G d ixs f ws = (let ns = nulls G; F = forbids G d in list_all (\<lambda>w.
     let ts = gen G ns ixs f (Nt (istart G)) w
     in ts = [] \<or> length (filter (chk 12 G ns F [] [] []) ts) = 1) ws)\<close>

section \<open>Infix, and \<open>if\<close> in an operand\<close>

definition p_add where \<open>p_add = (''E'', [(Nt ''E'', Any), (Tm TP, Any), (Nt ''E'', Any)])\<close>
definition p_mul where \<open>p_mul = (''E'', [(Nt ''E'', Any), (Tm TM, Any), (Nt ''E'', Any)])\<close>
definition p_if  where \<open>p_if  = (''E'', [(Tm TI, Any), (Nt ''E'', Any)])\<close>
definition p_a   where \<open>p_a   = (''E'', [(Tm TA, Any)])\<close>

definition ge :: \<open>(string, tk) is_cfg\<close> where
  \<open>ge = \<lparr>iprods = [p_add, p_mul, p_if, p_a], istart = ''E'', istart_ind = 0\<rparr>\<close>

definition de :: \<open>(string, tk) prec_decl\<close> where
  \<open>de = \<lparr>dlevels = [[(AOpen, [(p_if, False)]), (ALeft, [(p_add, False)]), (ALeft, [(p_mul, False)])]],
         dforbids = []\<rparr>\<close>

definition w :: \<open>tk list \<Rightarrow> word\<close> where \<open>w = map (tk_at 0)\<close>

text \<open>Every word has one tree, and none lost its language.\<close>

parser_check \<open>unique_on ge de [0] 7 (words [TA, TP, TM, TI] 4)\<close>
parser_check \<open>same_on ge de [0] 7 (words [TA, TP, TM, TI] 4)\<close>

text \<open>Without a declaration nothing changes, and the grammar stays ambiguous.\<close>

parser_check \<open>same_on ge \<lparr>dlevels = [], dforbids = []\<rparr> [0] 7 (words [TA, TP, TI] 4)\<close>

parser_check \<open>\<not> unique_on ge \<lparr>dlevels = [], dforbids = []\<rparr> [0] 7 (words [TA, TP] 5)\<close>

definition tr where \<open>tr G f ws = (let ns = nulls G in map erase
  (filter (chk 12 G ns (forbids G de) [] [] []) (gen G ns [0] f (Nt ''E'') (w ws))))\<close>

abbreviation \<open>la \<equiv> Node ''E'' [Leaf (tk_at 0 TA)] :: (unit, unit, string, tk) ast\<close>
abbreviation \<open>bin x a b \<equiv> Node ''E'' [a, Leaf (tk_at 0 x), b] :: (unit, unit, string, tk) ast\<close>
abbreviation \<open>ifn a \<equiv> Node ''E'' [Leaf (tk_at 0 TI), a] :: (unit, unit, string, tk) ast\<close>

parser_check \<open>tr ge 7 [TA, TP, TA, TM, TA] = [bin TP la (bin TM la la)]\<close>
parser_check \<open>tr ge 7 [TA, TP, TA, TP, TA] = [bin TP (bin TP la la) la]\<close>
parser_check \<open>tr ge 7 [TA, TP, TI, TA, TP, TA] = [bin TP la (ifn (bin TP la la))]\<close>
parser_check \<open>tr ge 7 [TA, TM, TI, TA, TP, TA] = [bin TM la (ifn (bin TP la la))]\<close>
parser_check \<open>tr ge 7 [TI, TA, TP, TA] = [ifn (bin TP la la)]\<close>

text \<open>The driver on the restricted grammar, unit nodes dropped by \<^const>\<open>plain_ast\<close>.\<close>

definition Sh where \<open>Sh = ''S''\<close>

parser_check \<open>rlalr_conflicts (restrict ge de) Sh = []\<close>

definition pa where \<open>pa ws = map_option (plain_ast orig_name) (dparse (restrict ge de) Sh (w ws))\<close>

parser_check \<open>pa [TA, TP, TI, TA, TP, TA] = Some (bin TP la (ifn (bin TP la la)))\<close>
parser_check \<open>pa [TA, TM, TA, TP, TA] = Some (bin TP (bin TM la la) la)\<close>
parser_check \<open>pa [TA, TP] = None\<close>

section \<open>A layout grammar\<close>

text \<open>A block keyword whose body is indented; the left operand keeps its own column.\<close>

definition q_add where \<open>q_add = (''E'', [(Nt ''E'', Eq), (Tm TP, Any), (Nt ''E'', Ge)])\<close>
definition q_blk where \<open>q_blk = (''E'', [(Tm TB, Eq), (Nt ''E'', Gt)])\<close>
definition q_a   where \<open>q_a   = (''E'', [(Tm TA, Eq)])\<close>

definition gl :: \<open>(string, tk) is_cfg\<close> where
  \<open>gl = \<lparr>iprods = [q_add, q_blk, q_a], istart = ''E'', istart_ind = 0\<rparr>\<close>

definition dl :: \<open>(string, tk) prec_decl\<close> where
  \<open>dl = \<lparr>dlevels = [[(AOpen, [(q_blk, False)]), (ALeft, [(q_add, False)])]], dforbids = []\<rparr>\<close>

definition lwords :: \<open>word list\<close> where
  \<open>lwords = concat (map (\<lambda>n. concat (map (\<lambda>ts. map (\<lambda>cs. map2 tk_at cs ts)
       (cart (replicate n [0, 1, 2]))) (cart (replicate n [TA, TP, TB])))) [0..<4])\<close>

parser_check \<open>same_on gl dl [0, 1, 2] 6 lwords\<close>
parser_check \<open>unique_on gl dl [0, 1, 2] 6 lwords\<close>

text \<open>A unit step of the chains relates the child to its parent by \<open>=\<close>, so it adds no
  indentation constraint.\<close>

definition unit_eq :: \<open>(string, tk) is_cfg \<Rightarrow> bool\<close> where
  \<open>unit_eq H \<longleftrightarrow> list_all (\<lambda>(m, r). case r of
     [(Nt c, i)] \<Rightarrow> orig_name c \<noteq> orig_name m \<or> i = Eq | _ \<Rightarrow> True) (iprods H)\<close>

parser_check \<open>unit_eq (restrict gl dl)\<close>
parser_check \<open>unit_eq (restrict ge de)\<close>

section \<open>Spines through nullable tails\<close>

text \<open>The right spine runs through \<open>n_app\<close>, whose last symbol \<open>O\<close> can derive nothing.\<close>

definition n_app where \<open>n_app = (''E'', [(Tm TI, Any), (Nt ''E'', Any), (Nt ''O'', Any)])\<close>
definition n_add where \<open>n_add = (''E'', [(Nt ''E'', Any), (Tm TP, Any), (Nt ''E'', Any)])\<close>
definition n_a   where \<open>n_a   = (''E'', [(Tm TA, Any)])\<close>
definition n_e   where \<open>n_e   = (''O'', [])\<close>
definition n_b   where \<open>n_b   = (''O'', [(Tm TB, Any)])\<close>

definition gn :: \<open>(string, tk) is_cfg\<close> where
  \<open>gn = \<lparr>iprods = [n_app, n_add, n_a, n_e, n_b], istart = ''E'', istart_ind = 0\<rparr>\<close>

definition dn :: \<open>(string, tk) prec_decl\<close> where
  \<open>dn = \<lparr>dlevels = [], dforbids = [(n_add, 0, FRight, n_add)]\<rparr>\<close>

parser_check \<open>nulls gn = [''O'']\<close>
parser_check \<open>same_on gn dn [0] 7 (words [TA, TP, TI, TB] 4)\<close>

end
