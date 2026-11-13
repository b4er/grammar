(* Author: Basil Fürer *)

theory Repair_Tests
  imports Recover_Tests
begin

section \<open>Repair sequences\<close>

datatype p_tok = PLP | PRP | PNum | PPlus | PSemi

datatype p_exp = PN | PAdd p_exp p_exp

grammar (relation) rp =
  tokens \<open>p_tok\<close>
  productions
    Pr :: \<open>p_exp list\<close> = E PSemi Pr \<Rightarrow> \<open>\<lambda>e _ p. e # p\<close> | E \<Rightarrow> \<open>\<lambda>e. [e]\<close>
  and
    E :: \<open>p_exp\<close> = E PPlus T \<Rightarrow> \<open>\<lambda>a _ b. PAdd a b\<close> | T
  and
    T :: \<open>p_exp\<close> = PNum \<Rightarrow> \<open>\<lambda>_. PN\<close> | PLP E PRP \<Rightarrow> \<open>\<lambda>_ e _. e\<close>

parser (no_diagnostics) rp_plain for rp

parser (diagnostics) rp_parse for rp repair


ML \<open>same_code \<^context> "rp_plain" "rp_parse" ["_coverage", "_diag", "_info", "_probe", "_recover", "_render", "_repair", "_terminals"]\<close>

definition rrep :: \<open>('n, 't, unit, unit) perr list \<times> 'x \<Rightarrow> (nat \<times> 't rop list) list \<times> 'x\<close> where
  \<open>rrep r = (map (\<lambda>e. (pe_index e, pe_repair e)) (fst r), snd r)\<close>

subsection \<open>The simple driver\<close>

text \<open>A good word, a missing operand, a missing separator, an unclosed bracket, the
  end of the input, two errors apart, and the empty word, which has no neighbour.\<close>

parser_check \<open>rrep (rp_parse_recover (toks 0 [PNum, PPlus, PNum])) =
    ([], Some [PAdd PN PN])\<close>

parser_check \<open>rrep (rp_parse_recover (toks 0 [PNum, PPlus, PPlus, PNum])) =
    ([(2, [RIns PNum 4])], Some [PAdd (PAdd PN PN) PN])\<close>

parser_check \<open>rrep (rp_parse_recover (toks 0 [PNum, PNum, PPlus, PNum])) =
    ([(1, [RIns PSemi 2])], Some [PN, PAdd PN PN])\<close>

parser_check \<open>rrep (rp_parse_recover (toks 0 [PLP, PNum, PSemi, PNum, PSemi, PNum, PPlus, PNum])) =
    ([(2, [RIns PRP 4])], Some [PN, PN, PAdd PN PN])\<close>

parser_check \<open>rrep (rp_parse_recover (toks 0 [PNum, PPlus])) =
    ([(2, [RIns PNum 3])], Some [PAdd PN PN])\<close>

parser_check \<open>rrep (rp_parse_recover (toks 0 [PNum, PPlus, PPlus, PNum, PSemi, PNum, PSemi, PNum, PNum, PPlus, PNum, PSemi, PNum])) =
    ([(2, [RIns PNum 4]), (8, [RIns PSemi 16])], Some [PAdd (PAdd PN PN) PN, PN, PN, PAdd PN PN, PN])\<close>

parser_check \<open>rrep (rp_parse_recover ([] :: (p_tok, unit) token list)) =
    ([(0, [])], None)\<close>


subsection \<open>The other drivers, and error productions first\<close>

text \<open>The vector driver with its sparse fallback, the dense one with a history, and
  layout: \<open>LId\<close> takes the column of the next token. \<open>rc_both\<close> repairs first, and
  takes the error token only when the search finds nothing.\<close>

parser (diagnostics) cf_fix for cf repair
parser (diagnostics) dc_fix for dc repair
parser (diagnostics) ly_fix for ly repair avoid LErr
parser (diagnostics) rc_both for rc recover RErr repair

parser_check \<open>rrep (cf_fix_recover (toks 0 [CA])) =
    ([(1, [RIns CB 1])], Some 0)\<close>

parser_check \<open>rrep (cf_fix_recover (toks 0 [CB, CB])) =
    ([(0, [RIns CA 0, RDel CB])], Some 0)\<close>

parser_check \<open>rrep (dc_fix_recover (toks 0 [DA])) =
    ([(1, [RIns DB 1])], Some 0)\<close>

parser_check \<open>rrep (dc_fix_recover (toks 0 [DB, DB])) =
    ([(0, [RIns DC 0, RDel DB])], Some 2)\<close>

parser_check \<open>rrep (ly_fix_recover (lw [(0, 1, LWhile), (0, 7, LId), (0, 8, LColon)])) =
    ([(3, [RIns LId 9])], Some [LS])\<close>

parser_check \<open>rrep (ly_fix_recover (lw [(0, 1, LWhile), (0, 8, LColon), (1, 3, LId)])) =
    ([(1, [RIns LId 8])], Some [LS])\<close>

parser_check \<open>rrep (ly_fix_recover (lw [(0, 1, LWhile), (0, 7, LId), (0, 8, LColon), (1, 3, LId), (2, 4, LId), (3, 3, LId)])) =
    ([(4, [RDel LId])], Some [LS, LS])\<close>

text \<open>The report of \<open>on_error_reduce\<close> keeps the repair.\<close>

parser (diagnostics) ly_oer for ly repair avoid LErr on_error_reduce St

parser_check \<open>map snd (fst (rrep (ly_oer_recover (lw [(0, 1, LWhile), (0, 8, LColon), (1, 3, LId)])))) =
    [[RIns LId 8]]\<close>

parser_check \<open>rtoks (ly_fix_repair (lw [(0, 1, LWhile), (0, 8, LColon), (1, 3, LId)])) =
    ([1], [(LWhile, 1, 1), (LId, 8, 0), (LColon, 8, 1), (LId, 3, 1)])\<close>

parser_check \<open>rrep (rc_both_recover (toks 0 [RX, REq, RRP, RSemi, RX, REq, RNum])) =
    ([(2, [RIns RNum 4, RDel RRP])], Some [SLet ENum, SLet ENum])\<close>

parser_check \<open>rrep (rc_both_recover (toks 0 [RSemi])) =
    ([(0, [RIns RX 0, RIns REq 0, RIns RNum 0, RDel RSemi])], Some [SLet ENum])\<close>

text \<open>Past the budget the error token still gives a tree.\<close>

parser_check \<open>(case rrep (rc_both_recover (toks 0 ([RX, REq] @ replicate 12 RLP @
      [RNum, RSemi, RX, REq, RNum, RSemi, RX, REq, RNum]))) of
    (es, t) \<Rightarrow> es \<noteq> [] \<and> (\<forall>e \<in> set es. snd e = []) \<and> t \<noteq> None)\<close>


subsection \<open>A token function, and terminals to avoid\<close>

definition mk_tok :: \<open>p_tok \<Rightarrow> unit span \<Rightarrow> (p_tok, unit) token\<close> where
  \<open>mk_tok t s = \<lparr>tok = t, span = s\<lparr>s_txt := [()]\<rparr>\<rparr>\<close>

parser (diagnostics) rp_tok for rp repair token mk_tok
parser (diagnostics) rp_av for rp repair avoid PNum

parser_check \<open>map (\<lambda>x. (tok x, length (s_txt (span x)))) (snd (rp_tok_repair (toks 0 [PNum, PPlus]))) =
    [(PNum, 0), (PPlus, 0), (PNum, 1)]\<close>

parser_check \<open>rrep (rp_av_recover (toks 0 [PNum, PPlus, PPlus, PNum])) =
    ([(2, [RDel PPlus])], Some [PAdd PN PN])\<close>


subsection \<open>The message\<close>

parser_check \<open>map rp_parse_render (fst (rp_parse_recover (toks 0 [PNum, PPlus, PPlus, PNum]))) =
    [''0:4: syntax error at '' @ squote ''PPlus'' @ [CHR 0x0A] @
     ''  expected: '' @ squote ''PNum'' @ '' or '' @ squote ''PLP'' @ [CHR 0x0A] @
     ''  repaired by: insert '' @ squote ''PNum'']\<close>

subsection \<open>Unmatched brackets\<close>

text \<open>The nodes the search takes on a word with \<open>n\<close> unmatched brackets, in a budget
  \<open>b\<close>, and how many repairs it finds: about 1.7 times as many nodes per bracket with
  merging, 2.4 without it, the exponential of \<^cite>\<open>\<open>Sect.~5.4\<close> in "diekmann2020-dont-panic"\<close>. \<^const>\<open>rnodes\<close> stops it at
  6 brackets, with no repair and the report standing.\<close>

definition brackets :: \<open>nat \<Rightarrow> p_tok list\<close> where
  \<open>brackets n = replicate n PLP @ [PNum, PSemi, PNum, PSemi, PNum]\<close>

definition bnodes :: \<open>nat \<Rightarrow> nat \<Rightarrow> (nat \<times> nat) option\<close> where
  \<open>bnodes b n = (let w = toks 0 (brackets n); P = rp_parse_ptabs; f = rp_parse_tnum in
     case pdiag_run P rp_parse_i0 f w of
       Some (DStuck NoAction _ sh) \<Rightarrow>
         let i = length w - length (snd (fst sh));
             r = rcost (Suc b) (pops P f) (map fst rp_parse_terminals) [] 0 b
                   [(fst (fst sh), tcols (drop i w), 0, [])] []
         in Some (b - fst r, length (snd r))
     | _ \<Rightarrow> None)\<close>

parser_check \<open>map (bnodes 30000) [1, 2, 3, 4, 5, 6, 7, 8] =
    map Some [(7, 1), (15, 1), (33, 1), (69, 1), (135, 1), (247, 1), (427, 1), (709, 1)]\<close>

parser_check \<open>map (bnodes rnodes) [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12] =
    map Some ([(7, 1), (15, 1), (33, 1), (69, 1), (135, 1)] @ replicate 7 (240, 0))\<close>

parser_check \<open>map (\<lambda>n. rrep (rp_parse_recover (toks 0 (brackets n)))) [4, 5, 6, 12] =
    [([(5, replicate 4 (RIns PRP 10))], Some [PN, PN, PN]), ([(6, replicate 5 (RIns PRP 12))], Some [PN, PN, PN]),
     ([(7, [])], None), ([(13, [])], None)]\<close>

subsection \<open>The budget of a word\<close>

text \<open>The stops of a word share one budget.\<close>

definition rword :: \<open>nat \<Rightarrow> (p_tok, unit) token list \<Rightarrow> _\<close> where
  \<open>rword b w = rloop (prstop rp_parse_ptabs rp_parse_i0 rp_parse_tnum (map fst rp_parse_terminals)
     \<lparr>rm_err = None, rm_repair = Some ([], rtoken)\<rparr>)
     (Suc (length w)) (Suc (length w)) 0 (length w) b w []\<close>

definition two_errs :: \<open>(p_tok, unit) token list\<close> where
  \<open>two_errs = toks 0 [PNum, PPlus, PPlus, PNum, PSemi, PNum, PSemi, PNum, PNum, PPlus, PNum, PSemi, PNum]\<close>

text \<open>Too little for the first stop, enough for the first but not what is left for the
  second, and enough for both.\<close>

parser_check \<open>map (\<lambda>b. map (length \<circ> pe_repair) (fst (rword b two_errs))) [4, 14, 16] = [[0], [1, 0], [1, 1]]\<close>


subsection \<open>Target languages\<close>

export_code rp_parse_recover rc_both_recover ly_fix_recover cf_fix_recover dc_fix_recover
  rp_tok_recover
  checking SML

export_code rp_parse_recover ly_fix_recover in Haskell

end
