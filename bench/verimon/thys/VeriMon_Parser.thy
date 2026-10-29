theory VeriMon_Parser
  imports LR_Parser.LR_Parser
begin

section \<open>MonPoly's formula grammar (VeriMon, 2020)\<close>

text \<open>A transcription of \<^file>\<open>../vendor/formula_parser.mly\<close>, MonPoly's ocamlyacc
  grammar, with the same parses and the same rejections, but without
  regular expressions (\<open>MATCHF\<close>, \<open>MATCHP\<close>).

  The \<open>grammar\<close> command has no \<open>%left\<close>/\<open>%prec\<close>, so the precedences
  become levels, loosest first:
  \<^item> \<open>SINCE\<close> and \<open>UNTIL\<close> (right-associative);
  \<^item> the prefix temporal operators, \<open>EXISTS\<close> and \<open>FORALL\<close>;
  \<^item> \<open>EQUIV\<close> (left), then \<open>IMPLIES\<close> (right), then \<open>OR\<close> (left), then \<open>AND\<close> (left);
  \<^item> \<open>NOT\<close>.

  A prefix operator's body extends as far right as it can. An operand that
  ends in one is open, so it can only be the last operand of its chain:
  \<^item> suffix \<open>_s\<close>: a temporal operator, \<open>EXISTS\<close> or \<open>FORALL\<close>, whose body stops
    before \<open>SINCE\<close>/\<open>UNTIL\<close>;
  \<^item> suffix \<open>_l\<close>: \<open>LET\<close> or an aggregation, whose body takes everything.

  The other resolutions ocamlyacc makes:
  \<^item> \<open>/\<close> and \<open>MOD\<close> have no precedence, so they always shift. They take a
    primary on the left and the whole rest of the term on the right
    (\<open>a / b + c\<close> is \<open>a / (b + c)\<close>); a term ending in one (\<open>t_o\<close>) is open.
  \<^item> After the \<open>;\<close> of an aggregation, an identifier is always a group-by
    variable. With no variables, the formula cannot start with an
    identifier or \<open>_\<close>: suffix \<open>_n\<close> repeats the left spine without those.

  A prototype of these levels as an ocamlyacc file had no conflicts. It parsed
  1.2 M random formulas and token-level mutations of them as the original does.

  Regular expressions are left out because the original's resolutions there
  are not a grammar one would write. Inside \<open>MATCHF\<close>, for example,
  \<open>(p AND q)\<close> is a syntax error.\<close>

subsection \<open>Tokens\<close>

text \<open>The constructors are the ocamlyacc token names, with a \<open>T_\<close> prefix. The
  harness puts a token's payload in its text:
  \<^item> identifiers and string constants as lexed;
  \<^item> numbers in OCaml's \<open>%h\<close> notation;
  \<^item> time units as digits and a letter;
  \<^item> for \<open>_\<close>, \<open>_\<close> and the token's index. That orders the variables as the
    original's counter does.\<close>

datatype mtok =
    T_FALSE | T_TRUE | T_LPA | T_RPA | T_LSB | T_RSB | T_COM | T_SC | T_DOT | T_QM | T_LD
  | T_LESSEQ | T_EQ | T_LESS | T_GTR | T_GTREQ | T_STAR | T_LARROW
  | T_PLUS | T_MINUS | T_SLASH | T_MOD | T_F2I | T_I2F
  | T_STR | T_STR_CST | T_INT | T_RAT | T_TU
  | T_LET | T_IN | T_NOT | T_AND | T_OR | T_IMPL | T_EQUIV | T_EX | T_FA
  | T_PREV | T_NEXT | T_EVENTUALLY | T_ONCE | T_ALWAYS | T_PAST_ALWAYS | T_SINCE | T_UNTIL
  | T_BAR | T_FREX | T_PREX
  | T_CNT | T_MIN | T_MAX | T_SUM | T_AVG | T_MED
  | T_END

type_synonym mtoken = \<open>(mtok, char) token\<close>

definition ttxt :: \<open>mtoken \<Rightarrow> string\<close> where
  \<open>ttxt t = s_txt (span t)\<close>

subsection \<open>Formulas\<close>

text \<open>MonPoly's \<open>MFOTL.formula\<close>, without regular expressions. Numbers stay
  token text: the harness converts them as the original's actions do,
  including their \<open>assert\<close>s. A string constant keeps its quotes, which the
  original's \<open>strip\<close> asserts are double quotes.\<close>

datatype mcst = CInt string | CRat string | CStr string

datatype mterm =
    TVar string | TCst mcst | TF2i mterm | TI2f mterm
  | TPlus mterm mterm | TMinus mterm mterm | TUMinus mterm
  | TMult mterm mterm | TDiv mterm mterm | TMod mterm mterm

datatype munits = UNum string | UTime string

datatype mbound = OBnd munits | CBnd munits | BInf

type_synonym mintv = \<open>mbound \<times> mbound\<close>

datatype magg = ACnt | AMin | AMax | ASum | AAvg | AMed

datatype mformula =
    FEqual mterm mterm | FLess mterm mterm | FLessEq mterm mterm
  | FPred string \<open>mterm list\<close>
  | FLet string \<open>mterm list\<close> mformula mformula
  | FNeg mformula | FAnd mformula mformula | FOr mformula mformula
  | FImplies mformula mformula | FEquiv mformula mformula
  | FExists \<open>string list\<close> mformula | FForAll \<open>string list\<close> mformula
  | FAggreg string magg string \<open>string list\<close> mformula
  | FPrev mintv mformula | FNext mintv mformula | FEventually mintv mformula
  | FOnce mintv mformula | FAlways mintv mformula | FPastAlways mintv mformula
  | FSince mintv mformula mformula | FUntil mintv mformula mformula

definition dfintv :: mintv where
  \<open>dfintv = (CBnd (UNum ''0''), BInf)\<close>

fun tvars :: \<open>mterm \<Rightarrow> string list\<close> where
  \<open>tvars (TVar v) = [v]\<close>
| \<open>tvars (TCst _) = []\<close>
| \<open>tvars (TF2i t) = tvars t\<close>
| \<open>tvars (TI2f t) = tvars t\<close>
| \<open>tvars (TUMinus t) = tvars t\<close>
| \<open>tvars (TPlus a b) = tvars a @ tvars b\<close>
| \<open>tvars (TMinus a b) = tvars a @ tvars b\<close>
| \<open>tvars (TMult a b) = tvars a @ tvars b\<close>
| \<open>tvars (TDiv a b) = tvars a @ tvars b\<close>
| \<open>tvars (TMod a b) = tvars a @ tvars b\<close>

text \<open>\<open>MFOTL.free_vars\<close>, up to order and duplicates: the parser only asks for
  membership.\<close>

fun fv :: \<open>mformula \<Rightarrow> string list\<close> where
  \<open>fv (FEqual a b) = tvars a @ tvars b\<close>
| \<open>fv (FLess a b) = tvars a @ tvars b\<close>
| \<open>fv (FLessEq a b) = tvars a @ tvars b\<close>
| \<open>fv (FPred _ ts) = concat (map tvars ts)\<close>
| \<open>fv (FLet _ _ _ f) = fv f\<close>
| \<open>fv (FNeg f) = fv f\<close>
| \<open>fv (FAnd a b) = fv a @ fv b\<close>
| \<open>fv (FOr a b) = fv a @ fv b\<close>
| \<open>fv (FImplies a b) = fv a @ fv b\<close>
| \<open>fv (FEquiv a b) = fv a @ fv b\<close>
| \<open>fv (FExists vs f) = filter (\<lambda>x. x \<notin> set vs) (fv f)\<close>
| \<open>fv (FForAll vs f) = filter (\<lambda>x. x \<notin> set vs) (fv f)\<close>
| \<open>fv (FAggreg y _ _ g _) = y # g\<close>
| \<open>fv (FPrev _ f) = fv f\<close>
| \<open>fv (FNext _ f) = fv f\<close>
| \<open>fv (FEventually _ f) = fv f\<close>
| \<open>fv (FOnce _ f) = fv f\<close>
| \<open>fv (FAlways _ f) = fv f\<close>
| \<open>fv (FPastAlways _ f) = fv f\<close>
| \<open>fv (FSince _ a b) = fv a @ fv b\<close>
| \<open>fv (FUntil _ a b) = fv a @ fv b\<close>

subsection \<open>Semantic actions\<close>

text \<open>A value \<^const>\<open>None\<close> is a parse whose action fails in the original, which
  then rejects the formula.\<close>

definition o2 :: \<open>('a \<Rightarrow> 'b \<Rightarrow> 'c) \<Rightarrow> 'a option \<Rightarrow> 'b option \<Rightarrow> 'c option\<close> where
  \<open>o2 f a b = (case a of None \<Rightarrow> None | Some x \<Rightarrow> map_option (f x) b)\<close>

text \<open>\<open>check\<close>: no comparison between an integer and a string constant.\<close>

fun check :: \<open>mterm \<Rightarrow> mterm \<Rightarrow> bool\<close> where
  \<open>check (TCst (CInt _)) (TCst (CStr _)) = False\<close>
| \<open>check (TCst (CStr _)) (TCst (CInt _)) = False\<close>
| \<open>check _ _ = True\<close>

definition cmp :: \<open>(mterm \<Rightarrow> mterm \<Rightarrow> mformula) \<Rightarrow> mterm \<Rightarrow> mterm \<Rightarrow> mformula option\<close> where
  \<open>cmp c a b = (if check a b then Some (c a b) else None)\<close>

definition anon :: \<open>string \<Rightarrow> bool\<close> where
  \<open>anon v = (case v of c # _ \<Rightarrow> c = CHR ''_'' | [] \<Rightarrow> False)\<close>

text \<open>\<open>add_ex\<close>: a predicate's \<open>_\<close>-variable arguments are bound by an \<open>EXISTS\<close>.\<close>

definition anon_args :: \<open>mterm list \<Rightarrow> string list\<close> where
  \<open>anon_args ts = concat (map (\<lambda>t. case t of TVar v \<Rightarrow> if anon v then [v] else [] | _ \<Rightarrow> []) ts)\<close>

definition add_ex :: \<open>string \<times> mterm list \<Rightarrow> mformula\<close> where
  \<open>add_ex p = (case p of (n, ts) \<Rightarrow>
     (case anon_args ts of [] \<Rightarrow> FPred n ts | vs \<Rightarrow> FExists vs (FPred n ts)))\<close>

text \<open>\<open>LET\<close> needs a predicate that \<open>add_ex\<close> left alone.\<close>

definition mk_let :: \<open>string \<times> mterm list \<Rightarrow> mformula option \<Rightarrow> mformula option \<Rightarrow> mformula option\<close> where
  \<open>mk_let p a b = (case p of (n, ts) \<Rightarrow>
     if anon_args ts = [] then o2 (FLet n ts) a b else None)\<close>

definition mk_quant ::
  \<open>(string list \<Rightarrow> mformula \<Rightarrow> mformula) \<Rightarrow> string list \<Rightarrow> mformula option \<Rightarrow> mformula option\<close> where
  \<open>mk_quant q vs f = (if vs = [] then None else map_option (q vs) f)\<close>

text \<open>\<open>aggreg\<close>: the aggregated and the group-by variables are free in the body.\<close>

definition mk_aggreg ::
  \<open>string \<Rightarrow> magg \<Rightarrow> string \<Rightarrow> string list \<Rightarrow> mformula option \<Rightarrow> mformula option\<close> where
  \<open>mk_aggreg y op x g f = Option.bind f (\<lambda>b.
     if x \<in> set (fv b) \<and> (\<forall>v \<in> set g. v \<in> set (fv b)) then Some (FAggreg y op x g b) else None)\<close>

definition ff :: mformula where
  \<open>ff = FLess (TCst (CInt ''0'')) (TCst (CInt ''0''))\<close>

definition tt :: mformula where
  \<open>tt = FEqual (TCst (CInt ''0'')) (TCst (CInt ''0''))\<close>

subsection \<open>The grammar\<close>

text \<open>The nonterminals are those of the ocamlyacc prototype, see the section
  header for the levels.\<close>

grammar verimon =
  tokens \<open>mtoken\<close>
  terminals
    "FALSE" = T_FALSE and "TRUE" = T_TRUE and "(" = T_LPA and ")" = T_RPA and
    "[" = T_LSB and "]" = T_RSB and "," = T_COM and ";" = T_SC and "." = T_DOT and
    "<=" = T_LESSEQ and "=" = T_EQ and "<" = T_LESS and ">" = T_GTR and ">=" = T_GTREQ and
    "*" = T_STAR and "<-" = T_LARROW and "+" = T_PLUS and "-" = T_MINUS and "/" = T_SLASH and
    "MOD" = T_MOD and "f2i" = T_F2I and "i2f" = T_I2F and
    "LET" = T_LET and "IN" = T_IN and "NOT" = T_NOT and "AND" = T_AND and "OR" = T_OR and
    "IMPLIES" = T_IMPL and "EQUIV" = T_EQUIV and "EXISTS" = T_EX and "FORALL" = T_FA and
    "PREVIOUS" = T_PREV and "NEXT" = T_NEXT and "EVENTUALLY" = T_EVENTUALLY and
    "ONCE" = T_ONCE and "ALWAYS" = T_ALWAYS and "PAST_ALWAYS" = T_PAST_ALWAYS and
    "SINCE" = T_SINCE and "UNTIL" = T_UNTIL and
    "CNT" = T_CNT and "MIN" = T_MIN and "MAX" = T_MAX and "SUM" = T_SUM and
    "AVG" = T_AVG and "MED" = T_MED
  productions
      f0 :: \<open>mformula option\<close>
        = f1s "SINCE" interval f0               \<Rightarrow> \<open>\<lambda>a i b. o2 (FSince i) a b\<close>
        | f1s "SINCE" f0                        \<Rightarrow> \<open>o2 (FSince dfintv)\<close>
        | f1s "UNTIL" interval f0               \<Rightarrow> \<open>\<lambda>a i b. o2 (FUntil i) a b\<close>
        | f1s "UNTIL" f0                        \<Rightarrow> \<open>o2 (FUntil dfintv)\<close>
        | f1s                                   \<Rightarrow> \<open>\<lambda>a. a\<close>
        | eo_l                                  \<Rightarrow> \<open>\<lambda>a. a\<close>
    and
      f1s :: \<open>mformula option\<close>
        = ec                                    \<Rightarrow> \<open>\<lambda>a. a\<close>
        | eo_s                                  \<Rightarrow> \<open>\<lambda>a. a\<close>
    and
      ec :: \<open>mformula option\<close>
        = ec "EQUIV" ic                         \<Rightarrow> \<open>o2 FEquiv\<close>
        | ic                                    \<Rightarrow> \<open>\<lambda>a. a\<close>
    and
      ic :: \<open>mformula option\<close>
        = oc "IMPLIES" ic                       \<Rightarrow> \<open>o2 FImplies\<close>
        | oc                                    \<Rightarrow> \<open>\<lambda>a. a\<close>
    and
      oc :: \<open>mformula option\<close>
        = oc "OR" ac                            \<Rightarrow> \<open>o2 FOr\<close>
        | ac                                    \<Rightarrow> \<open>\<lambda>a. a\<close>
    and
      ac :: \<open>mformula option\<close>
        = ac "AND" nc                           \<Rightarrow> \<open>o2 FAnd\<close>
        | nc                                    \<Rightarrow> \<open>\<lambda>a. a\<close>
    and
      nc :: \<open>mformula option\<close>
        = "NOT" nc                              \<Rightarrow> \<open>map_option FNeg\<close>
        | atom                                  \<Rightarrow> \<open>\<lambda>a. a\<close>
    and
      eo_s :: \<open>mformula option\<close>
        = ec "EQUIV" io_s                       \<Rightarrow> \<open>o2 FEquiv\<close>
        | io_s                                  \<Rightarrow> \<open>\<lambda>a. a\<close>
    and
      io_s :: \<open>mformula option\<close>
        = oc "IMPLIES" io_s                     \<Rightarrow> \<open>o2 FImplies\<close>
        | oo_s                                  \<Rightarrow> \<open>\<lambda>a. a\<close>
    and
      oo_s :: \<open>mformula option\<close>
        = oc "OR" ao_s                          \<Rightarrow> \<open>o2 FOr\<close>
        | ao_s                                  \<Rightarrow> \<open>\<lambda>a. a\<close>
    and
      ao_s :: \<open>mformula option\<close>
        = ac "AND" no_s                         \<Rightarrow> \<open>o2 FAnd\<close>
        | no_s                                  \<Rightarrow> \<open>\<lambda>a. a\<close>
    and
      no_s :: \<open>mformula option\<close>
        = "NOT" no_s                            \<Rightarrow> \<open>map_option FNeg\<close>
        | tp interval f1s                       \<Rightarrow> \<open>\<lambda>t i. map_option (t i)\<close>
        | tp f1s                                \<Rightarrow> \<open>\<lambda>t. map_option (t dfintv)\<close>
        | "EXISTS" varlist "." f1s              \<Rightarrow> \<open>mk_quant FExists\<close>
        | "FORALL" varlist "." f1s              \<Rightarrow> \<open>mk_quant FForAll\<close>
    and
      eo_l :: \<open>mformula option\<close>
        = ec "EQUIV" io_l                       \<Rightarrow> \<open>o2 FEquiv\<close>
        | io_l                                  \<Rightarrow> \<open>\<lambda>a. a\<close>
    and
      io_l :: \<open>mformula option\<close>
        = oc "IMPLIES" io_l                     \<Rightarrow> \<open>o2 FImplies\<close>
        | oo_l                                  \<Rightarrow> \<open>\<lambda>a. a\<close>
    and
      oo_l :: \<open>mformula option\<close>
        = oc "OR" ao_l                          \<Rightarrow> \<open>o2 FOr\<close>
        | ao_l                                  \<Rightarrow> \<open>\<lambda>a. a\<close>
    and
      ao_l :: \<open>mformula option\<close>
        = ac "AND" no_l                         \<Rightarrow> \<open>o2 FAnd\<close>
        | no_l                                  \<Rightarrow> \<open>\<lambda>a. a\<close>
    and
      no_l :: \<open>mformula option\<close>
        = "NOT" no_l                            \<Rightarrow> \<open>map_option FNeg\<close>
        | tp interval eo_l                      \<Rightarrow> \<open>\<lambda>t i. map_option (t i)\<close>
        | tp eo_l                               \<Rightarrow> \<open>\<lambda>t. map_option (t dfintv)\<close>
        | "EXISTS" varlist "." eo_l             \<Rightarrow> \<open>mk_quant FExists\<close>
        | "FORALL" varlist "." eo_l             \<Rightarrow> \<open>mk_quant FForAll\<close>
        | "LET" predicate "=" f0 "IN" f0        \<Rightarrow> \<open>mk_let\<close>
        | var "<-" aggreg var f0                \<Rightarrow> \<open>\<lambda>y op x. mk_aggreg y op x []\<close>
        | var "<-" aggreg var ";" vl1 f0        \<Rightarrow> \<open>mk_aggreg\<close>
        | var "<-" aggreg var ";" f0_n          \<Rightarrow> \<open>\<lambda>y op x. mk_aggreg y op x []\<close>
    and
      tp :: \<open>mintv \<Rightarrow> mformula \<Rightarrow> mformula\<close>
        = "PREVIOUS"                            \<Rightarrow> \<open>FPrev\<close>
        | "NEXT"                                \<Rightarrow> \<open>FNext\<close>
        | "EVENTUALLY"                          \<Rightarrow> \<open>FEventually\<close>
        | "ONCE"                                \<Rightarrow> \<open>FOnce\<close>
        | "ALWAYS"                              \<Rightarrow> \<open>FAlways\<close>
        | "PAST_ALWAYS"                         \<Rightarrow> \<open>FPastAlways\<close>
    and
      atom :: \<open>mformula option\<close>
        = "(" f0 ")"                            \<Rightarrow> \<open>\<lambda>a. a\<close>
        | "FALSE"                               \<Rightarrow> \<open>Some ff\<close>
        | "TRUE"                                \<Rightarrow> \<open>Some tt\<close>
        | predicate                             \<Rightarrow> \<open>\<lambda>p. Some (add_ex p)\<close>
        | trm relop trm                         \<Rightarrow> \<open>\<lambda>a c b. c a b\<close>
    and
      relop :: \<open>mterm \<Rightarrow> mterm \<Rightarrow> mformula option\<close>
        = "="                                   \<Rightarrow> \<open>cmp FEqual\<close>
        | "<="                                  \<Rightarrow> \<open>cmp FLessEq\<close>
        | "<"                                   \<Rightarrow> \<open>cmp FLess\<close>
        | ">"                                   \<Rightarrow> \<open>\<lambda>a b. cmp FLess b a\<close>
        | ">="                                  \<Rightarrow> \<open>\<lambda>a b. cmp FLessEq b a\<close>
    and
      f0_n :: \<open>mformula option\<close>
        = f1s_n "SINCE" interval f0             \<Rightarrow> \<open>\<lambda>a i b. o2 (FSince i) a b\<close>
        | f1s_n "SINCE" f0                      \<Rightarrow> \<open>o2 (FSince dfintv)\<close>
        | f1s_n "UNTIL" interval f0             \<Rightarrow> \<open>\<lambda>a i b. o2 (FUntil i) a b\<close>
        | f1s_n "UNTIL" f0                      \<Rightarrow> \<open>o2 (FUntil dfintv)\<close>
        | f1s_n                                 \<Rightarrow> \<open>\<lambda>a. a\<close>
        | eo_l_n                                \<Rightarrow> \<open>\<lambda>a. a\<close>
    and
      f1s_n :: \<open>mformula option\<close>
        = ec_n                                  \<Rightarrow> \<open>\<lambda>a. a\<close>
        | eo_s_n                                \<Rightarrow> \<open>\<lambda>a. a\<close>
    and
      ec_n :: \<open>mformula option\<close>
        = ec_n "EQUIV" ic                       \<Rightarrow> \<open>o2 FEquiv\<close>
        | ic_n                                  \<Rightarrow> \<open>\<lambda>a. a\<close>
    and
      ic_n :: \<open>mformula option\<close>
        = oc_n "IMPLIES" ic                     \<Rightarrow> \<open>o2 FImplies\<close>
        | oc_n                                  \<Rightarrow> \<open>\<lambda>a. a\<close>
    and
      oc_n :: \<open>mformula option\<close>
        = oc_n "OR" ac                          \<Rightarrow> \<open>o2 FOr\<close>
        | ac_n                                  \<Rightarrow> \<open>\<lambda>a. a\<close>
    and
      ac_n :: \<open>mformula option\<close>
        = ac_n "AND" nc                         \<Rightarrow> \<open>o2 FAnd\<close>
        | nc_n                                  \<Rightarrow> \<open>\<lambda>a. a\<close>
    and
      nc_n :: \<open>mformula option\<close>
        = "NOT" nc                              \<Rightarrow> \<open>map_option FNeg\<close>
        | atom_n                                \<Rightarrow> \<open>\<lambda>a. a\<close>
    and
      eo_s_n :: \<open>mformula option\<close>
        = ec_n "EQUIV" io_s                     \<Rightarrow> \<open>o2 FEquiv\<close>
        | io_s_n                                \<Rightarrow> \<open>\<lambda>a. a\<close>
    and
      io_s_n :: \<open>mformula option\<close>
        = oc_n "IMPLIES" io_s                   \<Rightarrow> \<open>o2 FImplies\<close>
        | oo_s_n                                \<Rightarrow> \<open>\<lambda>a. a\<close>
    and
      oo_s_n :: \<open>mformula option\<close>
        = oc_n "OR" ao_s                        \<Rightarrow> \<open>o2 FOr\<close>
        | ao_s_n                                \<Rightarrow> \<open>\<lambda>a. a\<close>
    and
      ao_s_n :: \<open>mformula option\<close>
        = ac_n "AND" no_s                       \<Rightarrow> \<open>o2 FAnd\<close>
        | no_s                                  \<Rightarrow> \<open>\<lambda>a. a\<close>
    and
      eo_l_n :: \<open>mformula option\<close>
        = ec_n "EQUIV" io_l                     \<Rightarrow> \<open>o2 FEquiv\<close>
        | io_l_n                                \<Rightarrow> \<open>\<lambda>a. a\<close>
    and
      io_l_n :: \<open>mformula option\<close>
        = oc_n "IMPLIES" io_l                   \<Rightarrow> \<open>o2 FImplies\<close>
        | oo_l_n                                \<Rightarrow> \<open>\<lambda>a. a\<close>
    and
      oo_l_n :: \<open>mformula option\<close>
        = oc_n "OR" ao_l                        \<Rightarrow> \<open>o2 FOr\<close>
        | ao_l_n                                \<Rightarrow> \<open>\<lambda>a. a\<close>
    and
      ao_l_n :: \<open>mformula option\<close>
        = ac_n "AND" no_l                       \<Rightarrow> \<open>o2 FAnd\<close>
        | no_l_n                                \<Rightarrow> \<open>\<lambda>a. a\<close>
    and
      no_l_n :: \<open>mformula option\<close>
        = "NOT" no_l                            \<Rightarrow> \<open>map_option FNeg\<close>
        | tp interval eo_l                      \<Rightarrow> \<open>\<lambda>t i. map_option (t i)\<close>
        | tp eo_l                               \<Rightarrow> \<open>\<lambda>t. map_option (t dfintv)\<close>
        | "EXISTS" varlist "." eo_l             \<Rightarrow> \<open>mk_quant FExists\<close>
        | "FORALL" varlist "." eo_l             \<Rightarrow> \<open>mk_quant FForAll\<close>
        | "LET" predicate "=" f0 "IN" f0        \<Rightarrow> \<open>mk_let\<close>
    and
      atom_n :: \<open>mformula option\<close>
        = "(" f0 ")"                            \<Rightarrow> \<open>\<lambda>a. a\<close>
        | "FALSE"                               \<Rightarrow> \<open>Some ff\<close>
        | "TRUE"                                \<Rightarrow> \<open>Some tt\<close>
        | trm_n relop trm                       \<Rightarrow> \<open>\<lambda>a c b. c a b\<close>
    and
      aggreg :: \<open>magg\<close>
        = "CNT"                                 \<Rightarrow> \<open>ACnt\<close>
        | "MIN"                                 \<Rightarrow> \<open>AMin\<close>
        | "MAX"                                 \<Rightarrow> \<open>AMax\<close>
        | "SUM"                                 \<Rightarrow> \<open>ASum\<close>
        | "AVG"                                 \<Rightarrow> \<open>AAvg\<close>
        | "MED"                                 \<Rightarrow> \<open>AMed\<close>
    and
      interval :: \<open>mintv\<close>
        = lbound "," rbound                     \<Rightarrow> \<open>Pair\<close>
    and
      lbound :: \<open>mbound\<close>
        = "(" units                             \<Rightarrow> \<open>OBnd\<close>
        | "[" units                             \<Rightarrow> \<open>CBnd\<close>
    and
      rbound :: \<open>mbound\<close>
        = units ")"                             \<Rightarrow> \<open>OBnd\<close>
        | units "]"                             \<Rightarrow> \<open>CBnd\<close>
        | "*" ")"                               \<Rightarrow> \<open>BInf\<close>
        | "*" "]"                               \<Rightarrow> \<open>BInf\<close>
    and
      units :: \<open>munits\<close>
        = T_TU                                  \<Rightarrow> \<open>\<lambda>t. UTime (ttxt t)\<close>
        | T_INT                                 \<Rightarrow> \<open>\<lambda>t. UNum (ttxt t)\<close>
    and
      predicate :: \<open>string \<times> mterm list\<close>
        = T_STR "(" termlist ")"                \<Rightarrow> \<open>\<lambda>n ts. (ttxt n, ts)\<close>
    and
      trm :: \<open>mterm\<close>
        = t_c                                   \<Rightarrow> \<open>\<lambda>t. t\<close>
        | t_o                                   \<Rightarrow> \<open>\<lambda>t. t\<close>
    and
      t_c :: \<open>mterm\<close>
        = t_c "+" m_c                           \<Rightarrow> \<open>TPlus\<close>
        | t_c "-" m_c                           \<Rightarrow> \<open>TMinus\<close>
        | m_c                                   \<Rightarrow> \<open>\<lambda>t. t\<close>
    and
      t_o :: \<open>mterm\<close>
        = t_c "+" m_o                           \<Rightarrow> \<open>TPlus\<close>
        | t_c "-" m_o                           \<Rightarrow> \<open>TMinus\<close>
        | m_o                                   \<Rightarrow> \<open>\<lambda>t. t\<close>
    and
      m_c :: \<open>mterm\<close>
        = m_c "*" u_c                           \<Rightarrow> \<open>TMult\<close>
        | u_c                                   \<Rightarrow> \<open>\<lambda>t. t\<close>
    and
      m_o :: \<open>mterm\<close>
        = m_c "*" u_o                           \<Rightarrow> \<open>TMult\<close>
        | u_o                                   \<Rightarrow> \<open>\<lambda>t. t\<close>
    and
      u_c :: \<open>mterm\<close>
        = "-" u_c                               \<Rightarrow> \<open>TUMinus\<close>
        | prim                                  \<Rightarrow> \<open>\<lambda>t. t\<close>
    and
      u_o :: \<open>mterm\<close>
        = "-" u_o                               \<Rightarrow> \<open>TUMinus\<close>
        | prim "/" trm                          \<Rightarrow> \<open>TDiv\<close>
        | prim "MOD" trm                        \<Rightarrow> \<open>TMod\<close>
    and
      prim :: \<open>mterm\<close>
        = var                                   \<Rightarrow> \<open>TVar\<close>
        | prim_n                                \<Rightarrow> \<open>\<lambda>t. t\<close>
    and
      trm_n :: \<open>mterm\<close>
        = t_c_n                                 \<Rightarrow> \<open>\<lambda>t. t\<close>
        | t_o_n                                 \<Rightarrow> \<open>\<lambda>t. t\<close>
    and
      t_c_n :: \<open>mterm\<close>
        = t_c_n "+" m_c                         \<Rightarrow> \<open>TPlus\<close>
        | t_c_n "-" m_c                         \<Rightarrow> \<open>TMinus\<close>
        | m_c_n                                 \<Rightarrow> \<open>\<lambda>t. t\<close>
    and
      t_o_n :: \<open>mterm\<close>
        = t_c_n "+" m_o                         \<Rightarrow> \<open>TPlus\<close>
        | t_c_n "-" m_o                         \<Rightarrow> \<open>TMinus\<close>
        | m_o_n                                 \<Rightarrow> \<open>\<lambda>t. t\<close>
    and
      m_c_n :: \<open>mterm\<close>
        = m_c_n "*" u_c                         \<Rightarrow> \<open>TMult\<close>
        | u_c_n                                 \<Rightarrow> \<open>\<lambda>t. t\<close>
    and
      m_o_n :: \<open>mterm\<close>
        = m_c_n "*" u_o                         \<Rightarrow> \<open>TMult\<close>
        | u_o_n                                 \<Rightarrow> \<open>\<lambda>t. t\<close>
    and
      u_c_n :: \<open>mterm\<close>
        = "-" u_c                               \<Rightarrow> \<open>TUMinus\<close>
        | prim_n                                \<Rightarrow> \<open>\<lambda>t. t\<close>
    and
      u_o_n :: \<open>mterm\<close>
        = "-" u_o                               \<Rightarrow> \<open>TUMinus\<close>
        | prim_n "/" trm                        \<Rightarrow> \<open>TDiv\<close>
        | prim_n "MOD" trm                      \<Rightarrow> \<open>TMod\<close>
    and
      prim_n :: \<open>mterm\<close>
        = "(" trm ")"                           \<Rightarrow> \<open>\<lambda>t. t\<close>
        | "f2i" "(" trm ")"                     \<Rightarrow> \<open>TF2i\<close>
        | "i2f" "(" trm ")"                     \<Rightarrow> \<open>TI2f\<close>
        | cst                                   \<Rightarrow> \<open>TCst\<close>
    and
      cst :: \<open>mcst\<close>
        = T_INT                                 \<Rightarrow> \<open>\<lambda>t. CInt (ttxt t)\<close>
        | T_RAT                                 \<Rightarrow> \<open>\<lambda>t. CRat (ttxt t)\<close>
        | T_STR_CST                             \<Rightarrow> \<open>\<lambda>t. CStr (ttxt t)\<close>
    and
      termlist :: \<open>mterm list\<close>
        = trm "," termlist                      \<Rightarrow> \<open>Cons\<close>
        | trm                                   \<Rightarrow> \<open>\<lambda>t. [t]\<close>
        |                                       \<Rightarrow> \<open>[]\<close>
    and
      varlist :: \<open>string list\<close>
        = vl1                                   \<Rightarrow> \<open>\<lambda>vs. vs\<close>
        |                                       \<Rightarrow> \<open>[]\<close>
    and
      vl1 :: \<open>string list\<close>
        = vl1 "," var                           \<Rightarrow> \<open>\<lambda>vs v. vs @ [v]\<close>
        | var                                   \<Rightarrow> \<open>\<lambda>v. [v]\<close>
        | "," var                               \<Rightarrow> \<open>\<lambda>v. [v]\<close>
    and
      var :: \<open>string\<close>
        = T_LD                                  \<Rightarrow> \<open>ttxt\<close>
        | T_STR                                 \<Rightarrow> \<open>ttxt\<close>

parser verimon_parse for verimon

subsection \<open>Code\<close>

text \<open>The OCaml harness (\<^verbatim>\<open>bench/verimon/src\<close>) builds the tokens with
  \<open>mk_token\<close> from MonPoly's lexer, and converts the formula to MonPoly's
  \<open>MFOTL.formula\<close>. The code needs Zarith.\<close>

definition mk_token :: \<open>mtok \<Rightarrow> String.literal \<Rightarrow> mtoken\<close> where
  \<open>mk_token x s = \<lparr>tok = x, span = span.make 0 0 0 0 (String.explode s)\<rparr>\<close>

export_code verimon_parse mk_token String.implode String.explode
  T_FALSE FEqual TVar CInt UNum OBnd ACnt
  in OCaml module_name VeriMon_Parser file_prefix verimon_parser

end
