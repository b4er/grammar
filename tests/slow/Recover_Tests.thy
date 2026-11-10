theory Recover_Tests
  imports Grammar_Tests.Diag_Tests Grammar_Tests.Parser_Check
begin

section \<open>Recovery from rejected words\<close>

text \<open>Tokens with their offsets, as a lexer gives them: the span of an error token
  is computed from them.\<close>

definition tr :: \<open>nat \<Rightarrow> nat \<Rightarrow> 'tok \<Rightarrow> ('tok, unit) token\<close> where
  \<open>tr l c x = \<lparr>tok = x, span = span.make l c (100 * l + c) 1 []\<rparr>\<close>

fun toks :: \<open>nat \<Rightarrow> 'tok list \<Rightarrow> ('tok, unit) token list\<close> where
  \<open>toks i [] = []\<close>
| \<open>toks i (x # xs) = tr 0 i x # toks (Suc (Suc i)) xs\<close>

definition rtoks :: \<open>('n, 't, unit, unit) perr list \<times> ('t, unit) token list \<Rightarrow>
    nat list \<times> ('t \<times> nat \<times> nat) list\<close> where
  \<open>rtoks r = (map pe_index (fst r), map (\<lambda>x. (tok x, s_col (span x), s_len (span x))) (snd r))\<close>

subsection \<open>Layout-free: the simple driver\<close>

datatype r_tok = RX | RNum | RPlus | RSemi | RLP | RRP | REq | RErr

datatype r_exp = ENum | EAdd r_exp r_exp | EBad
datatype r_stmt = SLet r_exp | SBad

grammar (relation) rc =
  tokens \<open>r_tok\<close>
  productions
    P :: \<open>r_stmt list\<close> = St RSemi P \<Rightarrow> \<open>\<lambda>s _ p. s # p\<close> | St \<Rightarrow> \<open>\<lambda>s. [s]\<close>
  and
    St :: \<open>r_stmt\<close> = RX REq E \<Rightarrow> \<open>\<lambda>_ _ e. SLet e\<close> | RErr \<Rightarrow> \<open>\<lambda>_. SBad\<close>
  and
    E :: \<open>r_exp\<close> = E RPlus T \<Rightarrow> \<open>\<lambda>a _ b. EAdd a b\<close> | T
  and
    T :: \<open>r_exp\<close> = RNum \<Rightarrow> \<open>\<lambda>_. ENum\<close> | RLP E RRP \<Rightarrow> \<open>\<lambda>_ e _. e\<close> | RErr \<Rightarrow> \<open>\<lambda>_. EBad\<close>

parser (no_diagnostics) rc_plain for rc

parser (diagnostics) rc_parse for rc recover RErr

ML_val \<open>same_code \<^context> "rc_plain" "rc_parse" ["_coverage", "_diag", "_info", "_probe", "_recover", "_render", "_repair", "_terminals"]\<close>

thm rc_parse_recover.clean rc_parse_recover.no_error

text \<open>A good word goes through untouched.\<close>

parser_check \<open>rc_parse_recover (toks 0 [RX, REq, RNum]) = ([], Some [SLet ENum])\<close>

text \<open>The offending token is replaced where an expression may stand, and the
  error token is not offered as expected.\<close>

parser_check \<open>(case rc_parse_recover (toks 0 [RX, REq, RNum, RPlus, RRP, RSemi, RX, REq, RNum]) of
    ([e], Some x) \<Rightarrow> pe_index e = 4 \<and> pe_expected e = [RNum, RLP] \<and>
      x = [SLet (EAdd ENum EBad), SLet ENum]
  | _ \<Rightarrow> False)\<close>

text \<open>Nothing skipped: the error token is inserted, with an empty span.\<close>

parser_check \<open>rtoks (rc_parse_repair (toks 0 [RX, REq, RSemi, RX, REq, RNum])) =
    ([2], [(RX, 0, 1), (REq, 2, 1), (RErr, 4, 0), (RSemi, 4, 1), (RX, 6, 1), (REq, 8, 1), (RNum, 10, 1)])\<close>

text \<open>At the end of the input.\<close>

parser_check \<open>rtoks (rc_parse_repair (toks 0 [RX, REq, RNum, RPlus])) =
    ([4], [(RX, 0, 1), (REq, 2, 1), (RNum, 4, 1), (RPlus, 6, 1), (RErr, 7, 0)])\<close>

text \<open>The stack is popped to where the error token can be shifted, and the tokens
  up to the continuation are skipped: the span runs from the first to the last.\<close>

parser_check \<open>rtoks (rc_parse_repair (toks 0 [RX, REq, RNum, RNum, RNum, RSemi, RX, REq, RNum])) =
    ([3], [(RX, 0, 1), (REq, 2, 1), (RErr, 4, 5), (RSemi, 10, 1), (RX, 12, 1), (REq, 14, 1), (RNum, 16, 1)])\<close>

text \<open>A statement that does not start right, with no expression on the stack.\<close>

parser_check \<open>rc_parse_recover (toks 0 [RRP, RSemi, RX, REq, RNum]) \<noteq> ([], None) \<and>
    snd (rc_parse_recover (toks 0 [RRP, RSemi, RX, REq, RNum])) = Some [SBad, SLet ENum]\<close>

text \<open>Several errors in one word, each index one of the original word.\<close>

parser_check \<open>(case rc_parse_recover (toks 0 [RX, REq, RRP, RSemi, RX, REq, RNum, RSemi, RX, RSemi,
      RX, REq, RPlus, RSemi, RX, REq, RNum]) of (es, x) \<Rightarrow> (map pe_index es, x)) =
    ([2, 9, 12], Some [SLet EBad, SLet ENum, SBad, SLet (EAdd EBad EBad), SLet ENum])\<close>

text \<open>A second error right after a recovery is taken for a consequence of it: it is
  recovered from, not reported.\<close>

parser_check \<open>(case rc_parse_recover (toks 0 [RX, REq, RRP, RRP, RPlus, RRP, RSemi, RX, REq, RNum]) of
    (es, x) \<Rightarrow> (map pe_index es, x)) = ([2], Some [SLet (EAdd EBad EBad), SLet ENum])\<close>

text \<open>The empty word has no token to make an error token from.\<close>

parser_check \<open>(case rc_parse_recover [] of ([e], None) \<Rightarrow> pe_index e = 0 | _ \<Rightarrow> False)\<close>

text \<open>A word with no place for the error token: \<open>None\<close>, with the report.\<close>

datatype np_tok = NA | NB | NErr

grammar (relation) np =
  tokens \<open>np_tok\<close>
  productions S :: \<open>nat\<close> = NA X \<Rightarrow> \<open>\<lambda>_ x. x\<close>
    and X :: \<open>nat\<close> = NB \<Rightarrow> \<open>\<lambda>_. 1\<close> | NErr \<Rightarrow> \<open>\<lambda>_. 0\<close>

parser (diagnostics) np_parse for np recover NErr

parser_check \<open>(case np_parse_recover (toks 0 [NB]) of ([e], None) \<Rightarrow> pe_index e = 0 | _ \<Rightarrow> False)\<close>

parser_check \<open>snd (np_parse_recover (toks 0 [NA, NA])) = Some 0\<close>

text \<open>An entry: the facts are about the grammar of the entry.\<close>

parser (diagnostics) rc_exp for rc (E) recover RErr

thm rc_exp_recover.no_error

parser_check \<open>snd (rc_exp_recover (toks 0 [RNum, RPlus, RRP])) = Some (EAdd ENum EBad)\<close>

text \<open>A name that is not a terminal of the grammar is ignored (expected warning).\<close>

parser (diagnostics) np_none for np recover RX

subsection \<open>A conflict\<close>

text \<open>The error token is an ordinary terminal: the normal check reports a conflict
  it takes part in (expected warnings), and the vector driver restarts on the sparse
  one, which is the sparse adapter here.\<close>

datatype cf_tok = CA | CB | CErr

grammar (relation) cf =
  tokens \<open>cf_tok\<close>
  productions S :: \<open>nat\<close> = X CB \<Rightarrow> \<open>\<lambda>x _. x\<close> | Y CB \<Rightarrow> \<open>\<lambda>y _. y\<close>
    and X :: \<open>nat\<close> = CA \<Rightarrow> \<open>\<lambda>_. 0\<close> | CErr \<Rightarrow> \<open>\<lambda>_. 1\<close>
    and Y :: \<open>nat\<close> = CErr \<Rightarrow> \<open>\<lambda>_. 2\<close>

parser (diagnostics) cf_parse for cf recover CErr

parser_check \<open>(case cf_parse_recover (toks 0 [CB, CB]) of (es, x) \<Rightarrow> (map pe_index es, x)) =
    ([0], Some 1)\<close>

subsection \<open>The set-anchored driver\<close>

text \<open>A cycle keeps the parser on the dense tables with the history (expected warning).\<close>

datatype dc_tok = DA | DB | DC | DErr

grammar (relation) dc =
  tokens \<open>dc_tok\<close>
  productions S :: \<open>nat\<close> = X DB \<Rightarrow> \<open>\<lambda>x _. x\<close> | DC D \<Rightarrow> \<open>\<lambda>_ d. d\<close>
    and X :: \<open>nat\<close> = DA \<Rightarrow> \<open>\<lambda>_. 0\<close> | DErr \<Rightarrow> \<open>\<lambda>_. 1\<close>
    and D :: \<open>nat\<close> = D \<Rightarrow> \<open>\<lambda>d. d\<close> | DB \<Rightarrow> \<open>\<lambda>_. 2\<close>

parser (diagnostics) dc_parse for dc recover DErr

parser_check \<open>dc_parse_recover (toks 0 [DA, DB]) = ([], Some 0)\<close>

parser_check \<open>(case dc_parse_recover (toks 0 [DB, DB]) of (es, x) \<Rightarrow> (map pe_index es, x)) =
    ([0], Some 1)\<close>

subsection \<open>Layout: the vector driver\<close>

datatype l_tok = LWhile | LColon | LId | LErr

datatype l_stm = LS | LBad

grammar (relation) ly =
  tokens \<open>l_tok\<close>
  terminals "while" = \<open>LWhile\<close> and ":" = \<open>LColon\<close>
  productions
      WhileStmt :: \<open>l_stm list\<close> = "while"\<^sup>> Test\<^sup>= ":"\<^sup>> Suite\<^sup>= \<Rightarrow> \<open>\<lambda>_ s. s\<close>
    and
      Test = LId\<^sup>\<ge> \<Rightarrow> \<open>\<lambda>_. ()\<close>
    and
      Suite :: \<open>l_stm list\<close> = Block\<^sup>>
    and
      Block :: \<open>l_stm list\<close>
        = St\<^sup>=        \<Rightarrow> \<open>\<lambda>s. [s]\<close>
        | Block\<^sup>= St\<^sup>= \<Rightarrow> \<open>\<lambda>b s. b @ [s]\<close>
    and
      St :: \<open>l_stm\<close> = LId\<^sup>= \<Rightarrow> \<open>\<lambda>_. LS\<close> | LErr\<^sup>= \<Rightarrow> \<open>\<lambda>_. LBad\<close>

parser (no_diagnostics) ly_plain for ly

parser (diagnostics) ly_parse for ly recover LErr

ML_val \<open>same_code \<^context> "ly_plain" "ly_parse" ["_coverage", "_diag", "_info", "_probe", "_recover", "_render", "_repair", "_terminals"]\<close>

definition lw where \<open>lw xs = map (\<lambda>(l, c, x). tr l c x) xs\<close>

parser_check \<open>ly_parse_recover (lw [(0, 1, LWhile), (0, 7, LId), (0, 8, LColon), (1, 3, LId), (2, 3, LId)]) =
    ([], Some [LS, LS])\<close>

text \<open>A misaligned statement: the error token gets the column that fits, and the
  word stays good from there on.\<close>

parser_check \<open>(case ly_parse_recover (lw [(0, 1, LWhile), (0, 7, LId), (0, 8, LColon), (1, 3, LId), (2, 4, LId), (3, 3, LId)])
    of (es, x) \<Rightarrow> (map (\<lambda>e. (pe_index e, pe_kind e)) es, x)) =
    ([(4, Misaligned [(3, Some 3)])], Some [LS, LBad, LS])\<close>

parser_check \<open>rtoks (ly_parse_repair (lw [(0, 1, LWhile), (0, 7, LId), (0, 8, LColon), (1, 3, LId), (2, 4, LId), (3, 3, LId)])) =
    ([4], [(LWhile, 1, 1), (LId, 7, 1), (LColon, 8, 1), (LId, 3, 1), (LErr, 3, 1), (LId, 3, 1)])\<close>

text \<open>An offside suite: its token is replaced at a column the state accepts.\<close>

parser_check \<open>(case ly_parse_recover (lw [(0, 1, LWhile), (0, 7, LId), (0, 8, LColon), (1, 0, LId)])
    of (es, x) \<Rightarrow> (map (\<lambda>e. (pe_index e, pe_kind e)) es, x)) =
    ([(3, Offside [(1, None)])], Some [LBad])\<close>

parser_check \<open>rtoks (ly_parse_repair (lw [(0, 1, LWhile), (0, 7, LId), (0, 8, LColon), (1, 0, LId)])) =
    ([3], [(LWhile, 1, 1), (LId, 7, 1), (LColon, 8, 1), (LErr, 1, 1)])\<close>

text \<open>Two errors, far apart.\<close>

parser_check \<open>(case ly_parse_recover (lw [(0, 1, LWhile), (0, 7, LId), (0, 8, LColon), (1, 3, LId), (2, 4, LId),
   (3, 3, LId), (4, 3, LId), (5, 3, LId), (6, 3, LId), (7, 5, LId), (8, 3, LId)])
  of (es, x) \<Rightarrow> (map (\<lambda>e. (pe_index e, pe_kind e)) es, x)) =
    ([(4, Misaligned [(3, Some 3)]), (9, Misaligned [(3, Some 3)])],
     Some [LS, LBad, LS, LS, LS, LS, LBad, LS])\<close>

subsection \<open>Reports and target languages\<close>

text \<open>The report of a stop is the one of \<open>p_diag\<close>, on the original word.\<close>

parser_check \<open>(case rc_parse_diag (toks 0 [RX, RNum]) of
    Inl e \<Rightarrow> fst (rc_parse_recover (toks 0 [RX, RNum])) = [e] | Inr _ \<Rightarrow> False)\<close>

export_code rc_parse_recover ly_parse_recover cf_parse_recover dc_parse_recover
  checking SML Scala

export_code rc_parse_recover ly_parse_recover cf_parse_recover dc_parse_recover in Haskell

export_code rc_parse_recover ly_parse_recover cf_parse_recover dc_parse_recover in OCaml

end
