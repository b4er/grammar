theory Intervals_Tests
  imports Lexer.Tables
begin

section \<open>Tests of character classes\<close>

text \<open>The class operations and minterms of \<^theory>\<open>Lexer.Intervals\<close> on two
  instances: natural numbers below a bound and bytes.\<close>

subsection \<open>Natural numbers below a bound\<close>

text \<open>Natural numbers up to a bound are a discrete order:\<close>

global_interpretation nat_cls: discrete_order \<open>0::nat\<close> \<open>100\<close> Suc \<open>\<lambda>n. n - 1\<close>
  defines nat_clip = nat_cls.clip
    and nat_merge = nat_cls.merge
    and nat_norm = nat_cls.cls_norm
    and nat_compl_from = nat_cls.compl_from
    and nat_disj = nat_cls.cls_disj
    and nat_neg = nat_cls.cls_neg
    and nat_conj = nat_cls.cls_conj
  by unfold_locales (auto simp: le_diff_conv2)

value \<open>nat_disj [(4, 6), (10, 12)] [(1, 3), (11, 20)]\<close>
value \<open>nat_neg [(0, 9), (20, 200), (15, 16)]\<close>
value \<open>nat_conj [(1, 10), (30, 40)] [(5, 35)]\<close>
value \<open>sat_cls (nat_conj [(1, 4)] [(5, 9)])\<close>

subsection \<open>Bytes\<close>

value \<open>char_disj [(CHR ''a'', CHR ''z'')] [(CHR ''A'', CHR ''Z''), (CHR ''_'', CHR ''_'')]\<close>
value \<open>char_neg [(CHR ''a'', CHR ''z'')]\<close>
value \<open>char_conj (char_neg [(CHR ''0'', CHR ''9'')]) [(CHR ''+'', CHR ''@'')]\<close>
value \<open>sat_cls (char_conj [(CHR ''a'', CHR ''z'')] (char_neg char_top))\<close>

text \<open>The minterms of \<open>\w\<close> and \<open>\d\<close> are \<open>\d\<close>, \<open>\w \<and> \<not> \d\<close> and \<open>\<not> \w\<close>
  \<^cite>\<open>\<open>Ex. 1\<close> in "dantoni2014-minimization-symbolic-automata"\<close>. Each character
  lies in exactly one minterm, whose signature is its own:\<close>

definition char_w where
  \<open>char_w = [(CHR ''0'', CHR ''9''), (CHR ''A'', CHR ''Z''), (CHR ''_'', CHR ''_''),
    (CHR ''a'', CHR ''z'')]\<close>

definition char_d where
  \<open>char_d = [(CHR ''0'', CHR ''9'')]\<close>

value \<open>char_minterms [char_w, char_d]\<close>

definition minterms_ok :: \<open>char cls list \<Rightarrow> bool\<close> where
  \<open>minterms_ok P = list_all (\<lambda>c.
    (case filter (\<lambda>(S, \<mu>). in_cls \<mu> c) (char_minterms P) of
      [(S, \<mu>)] \<Rightarrow> S = Set.filter (\<lambda>p. in_cls p c) (set P)
    | _ \<Rightarrow> False)) Enum.enum\<close>

value \<open>minterms_ok [char_w, char_d]\<close>

text \<open>The bit predicates of \<^cite>\<open>\<open>Ex. 2\<close> in "dantoni2014-minimization-symbolic-automata"\<close>
  on bytes give one minterm per byte value below \<open>2\<^sup>k\<close>:\<close>

definition char_bit :: \<open>nat \<Rightarrow> char cls\<close> where
  \<open>char_bit i = map (\<lambda>n. (char_of (n * 2 ^ Suc i + 2 ^ i),
    char_of (n * 2 ^ Suc i + 2 ^ Suc i - 1))) [0 ..< 2 ^ (7 - i)]\<close>

value \<open>length (char_minterms (map char_bit [0 ..< 4]))\<close>
value \<open>minterms_ok (map char_bit [0 ..< 4])\<close>

(* ~7s: 256 minterms. The check minterms_ok on 8 bits does not finish in 10 min. *)
value \<open>length (char_minterms (map char_bit [0 ..< 8]))\<close>

end
