(* Author: Basil Fürer, Claude *)

theory Repair_Code_Tests
  imports Repair_Tests "HOL-Library.Code_Target_Numeral"
begin

section \<open>Repairs and messages under target numerals\<close>

text \<open>The message path too: \<open>lay_parse_render\<close> renders through \<^const>\<open>perr_message\<close>,
  whose summary of the expected terminals reaches \<^const>\<open>lreach\<close>, and \<open>m_br_lines\<close>
  through the hand-written messages. A Haskell or OCaml export typically imports
  \<open>Code_Target_Numeral\<close>.\<close>

export_code rp_parse_recover ly_fix_recover lay_parse_render m_br_lines checking SML

end
