(* Author: Basil Fürer *)

theory Lexer_Table_Tests
  imports Lexer_Command_Tests TIGER_Lexer.Lexer_Check
begin

section \<open>Tests of the generated lexers\<close>

text \<open>The lexers that @{command lexer} builds for the specs of \<open>Lexer_Command_Tests\<close>,
  checked with @{command lexer_check} where no theorem is needed.\<close>

subsection \<open>Identifiers and operators\<close>

text \<open>\<open>\<alpha>\<beta> \<rightarrow>\<Rightarrow>\<close>, a newline and \<open>A\<close>. The final stack is the start stack:\<close>

lexer_check \<open>cp_lex [0x3B1, 0x3B2, 0x20, 0x2192, 0x21D2, 0x0A, 0x41] =
  (Lexed []
    [\<lparr>tok = LIDENT, span = \<lparr>s_line = 0, s_col = 0, s_off = 0, s_len = 2, s_txt = [0x3B1, 0x3B2]\<rparr>,
      trivia = [0x20]\<rparr>,
     \<lparr>tok = OP, span = \<lparr>s_line = 0, s_col = 3, s_off = 3, s_len = 2, s_txt = [0x2192, 0x21D2]\<rparr>,
      trivia = [0x0A]\<rparr>,
     \<lparr>tok = UIDENT, span = \<lparr>s_line = 1, s_col = 0, s_off = 6, s_len = 1, s_txt = [0x41]\<rparr>,
      trivia = []\<rparr>],
   [], [()])\<close>

subsection \<open>Nested comments\<close>

text \<open>\<open>a(*(**)*)1\<close>: the nested comment is the trailing trivia of \<open>a\<close>:\<close>

lexer_check \<open>cmt_lex [0x61, 0x28, 0x2A, 0x28, 0x2A, 0x2A, 0x29, 0x2A, 0x29, 0x31] =
  (Lexed []
    [\<lparr>tok = Word, span = \<lparr>s_line = 0, s_col = 0, s_off = 0, s_len = 1, s_txt = [0x61]\<rparr>,
      trivia = [0x28, 0x2A, 0x28, 0x2A, 0x2A, 0x29, 0x2A, 0x29]\<rparr>,
     \<lparr>tok = Num, span = \<lparr>s_line = 0, s_col = 9, s_off = 9, s_len = 1, s_txt = [0x31]\<rparr>,
      trivia = []\<rparr>],
   [], [Code])\<close>

text \<open>An unterminated comment consumes the input but ends in \<open>Comment\<close>, which is not
  final, so the scan fails:\<close>

lexer_check \<open>cmt_lex [0x61, 0x28, 0x2A, 0x62] =
  (Lexed []
    [\<lparr>tok = Word, span = \<lparr>s_line = 0, s_col = 0, s_off = 0, s_len = 1, s_txt = [0x61]\<rparr>,
      trivia = [0x28, 0x2A, 0x62]\<rparr>],
   [], [Comment, Code])\<close>

lexer_check \<open>cmt_lex.ok [0x61, 0x62]\<close> \<open>\<not> cmt_lex.ok [0x61, 0x28, 0x2A, 0x62]\<close>
  \<open>\<not> cmt_lex.ok [0x61, 0x2B]\<close>

text \<open>The correctness theorem on a concrete input: the result of the lexer is a
  derivation of \<^const>\<open>symbolic.lexes\<close> from the start mode:\<close>

lemma cmt_lex_ab:
  \<open>cmt_lex [0x61, 0x62] =
    (Lexed [] [\<lparr>tok = Word, span = \<lparr>s_line = 0, s_col = 0, s_off = 0, s_len = 2,
      s_txt = [0x61, 0x62]\<rparr>, trivia = []\<rparr>], [], [Code])\<close>
  by eval

lemma
  \<open>symbolic.lexes in_cls cmt.spec cmt.is_newline [cmt.start] \<lparr>line = 0, col = 0, off = 0\<rparr>
    [0x61, 0x62]
    (Lexed [] [\<lparr>tok = Word, span = \<lparr>s_line = 0, s_col = 0, s_off = 0, s_len = 2,
      s_txt = [0x61, 0x62]\<rparr>, trivia = []\<rparr>]) [] [Code]\<close>
  by (rule cmt_lex.correct[THEN iffD1]) (simp_all add: cmt_lex_ab)

subsection \<open>Bytes\<close>

text \<open>The same spec on bytes. Its classes stay below \<open>0x100\<close>, apart from the
  complement in the comment rule, which reaches the end of the codepoints:\<close>

lexer (char) cmt_bytes :: \<open>ctok\<close> (* ~6 s *)
  modes Code Comment
  exclusive Comment
  where letter = \<open>[a-z]\<close>
  rules
    \<open>letter+\<close> \<Rightarrow> Word
  | \<open>[0-9]+\<close> \<Rightarrow> Num
  | \<open>[ \n]+\<close> \<Rightarrow> skip
  | "(*" \<Rightarrow> skip, push Comment
  | <Comment> (
      "(*" \<Rightarrow> skip, push Comment
    | "*)" \<Rightarrow> skip, pop
    | \<open>[^*(]+ | [*(]\<close> \<Rightarrow> skip
  )

lexer_check \<open>cmt_bytes_lex ''ab (* (* c *) *) 12'' =
  (Lexed []
    [\<lparr>tok = Word, span = \<lparr>s_line = 0, s_col = 0, s_off = 0, s_len = 2, s_txt = ''ab''\<rparr>,
      trivia = '' (* (* c *) *) ''\<rparr>,
     \<lparr>tok = Num, span = \<lparr>s_line = 0, s_col = 17, s_off = 17, s_len = 2, s_txt = ''12''\<rparr>,
      trivia = []\<rparr>],
   [], [cmt_bytes_mode.Code])\<close>

subsection \<open>The hook\<close>

text \<open>\<open>a--b\<close>: subtraction after the operand, negation after the operator:\<close>

lexer_check \<open>map tok (toks (fst (ops_lex [0x61, 0x2D, 0x2D, 0x62]))) = [Id, Minus, Neg, Id]\<close>

subsection \<open>Shared tables\<close>

text \<open>Modes with the same active rules share their tables: \<open>A\<close> and \<open>B\<close> have the
  untagged rules, the exclusive \<open>C\<close> has its own:\<close>

lexer sh :: \<open>ctok\<close>
  modes A B C
  exclusive C
  rules
    \<open>[a-z]+\<close> \<Rightarrow> Word
  | "{" \<Rightarrow> skip, push C
  | <C> ("}" \<Rightarrow> skip, pop | \<open>[0-9]+\<close> \<Rightarrow> Num)

lemma \<open>sh_lex.index A = 0\<close> \<open>sh_lex.index B = 0\<close> \<open>sh_lex.index C = 1\<close>
  \<open>IArray.length sh_lex.tables = 2\<close>
  by (simp_all add: sh_lex.index_def sh_lex.tables_def)

lexer_check \<open>map tok (toks (fst (sh_lex [0x61, 0x7B, 0x31, 0x7D, 0x62]))) = [Word, Num, Word]\<close>

subsection \<open>Unreachable rules\<close>

text \<open>The second rule matches only \<open>a\<close>, which the first matches with higher priority.
  The command warns that the second rule cannot be matched in mode \<open>()\<close>:\<close>

lexer dup :: \<open>ctok\<close>
  rules "a" \<Rightarrow> Word | "a" \<Rightarrow> Num

ML_command \<open>
  let
    val th = Proof_Context.get_thm \<^context> \<^unchecked_name>\<open>dup_lex.tables_0_code\<close>;
    val lit = snd (HOLogic.dest_eq (HOLogic.dest_Trueprop (Thm.prop_of th)));
  in \<^assert> (Lexer_Tables.accepted lit = [0]) end
\<close>

text \<open>With \<open>(no_check)\<close>, the command does not warn:\<close>

lexer (no_check) dup' :: \<open>ctok\<close>
  rules "a" \<Rightarrow> Word | "a" \<Rightarrow> Num

subsection \<open>The lexing diagnostic\<close>

text \<open>@{command lex} prints the tokens of a text with their trivia, the residue and the
  final stack:\<close>

lex cmt_lex \<open>ab (* c *) 12\<close>

lex cmt_bytes_lex \<open>ab (* c\<close>

ML_command \<open>
  let
    val out = Lexer_Check.lex \<^context> \<^term>\<open>cmt_lex\<close> \<open>a (* *) 1+\<close>
      |> Pretty.string_of |> Protocol_Message.clean_output;
  in
    \<^assert> (String.isSubstring "Word  0:0     \"a\"  trivia \" (* *) \"" out);
    \<^assert> (String.isSubstring "residue \"+\"" out);
    \<^assert> (String.isSubstring "(the top is final)" out)
  end
\<close>

subsection \<open>A failing check\<close>

text \<open>A false check shows the left-hand side:\<close>

ML_command \<open>
  (case Exn.capture (Lexer_Check.verify \<^context>)
      \<^term>\<open>map tok (toks (fst (sh_lex [0x61]))) = []\<close> of
    Exn.Res _ => error "No error"
  | Exn.Exn exn =>
      \<^assert> (String.isSubstring "the left-hand side is [Word]"
        (Protocol_Message.clean_output (Runtime.exn_message exn))))
\<close>

subsection \<open>Errors\<close>

text \<open>The byte instance rejects a class that reaches above \<open>0xFF\<close>, at the definition of
  a named class or at the lexer for a class written in a rule:\<close>

ML_command \<open>
  lexer_fails \<^context>
    "(char) greek :: \<open>ctok\<close> where alpha = \<open>[\<alpha>-\<omega>]\<close> rules \<open>alpha+\<close> \<Rightarrow> Word"
    "the class \"alpha\" = [0x3B1-0x3C9] reaches above";
  lexer_fails \<^context> "(char) lambda :: \<open>ctok\<close> rules \"\<lambda>\" \<Rightarrow> Word"
    "= [0x3BB] reaches above 0xFF";
  lexer_fails \<^context> "(utf8) e :: \<open>ctok\<close> rules \"x\" \<Rightarrow> Word"
    "unknown option \"utf8\""
\<close>

text \<open>With \<open>(sketch)\<close>, the command defines the spec only:\<close>

lexer (sketch) sk :: \<open>ctok\<close>
  rules \<open>[a-z]+\<close> \<Rightarrow> Word

ML_command \<open>
  \<^assert> (can (Proof_Context.get_thms \<^context>) \<^unchecked_name>\<open>sk.spec.simps\<close>);
  \<^assert> (not (can (Proof_Context.read_const {proper = true, strict = true} \<^context>) "sk_lex"))
\<close>

end
