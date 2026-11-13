(* Author: Basil Fürer, Claude *)

theory Lexer_Command_Tests
  imports Codepoint_Tests TIGER_Lexer.Lexer_Command
begin

section \<open>Tests of the lexer command\<close>

subsection \<open>Identifiers and operators\<close>

text \<open>The rules of \<open>Codepoint_Tests\<close> as a @{command lexer}. Without \<open>modes\<close> the mode
  type is \<^typ>\<open>unit\<close>:\<close>

lexer cp :: \<open>tok\<close>
  where
    lower = \<open>[a-z\<alpha>-\<kappa>\<mu>-\<omega>]\<close> | upper = \<open>[A-ZΑ-Ρ\<Sigma>-\<Omega>]\<close>
  | idchar = \<open>lower | upper | [0-9_']\<close>
  | many(p) = \<open>p p*\<close>
  rules
    \<open>lower idchar*\<close> \<Rightarrow> LIDENT
  | \<open>upper idchar*\<close> \<Rightarrow> UIDENT
  | \<open>many([\u{2190}-\u{22FF}])\<close> \<Rightarrow> OP
  | \<open>many([ \n])\<close> \<Rightarrow> skip

lemma \<open>cp.spec () =
  [\<lparr>match = Times (Pred cp.lower) (Star (Pred cp.idchar)),
     act = mk_act (\<lambda>k m. m) (\<lambda>u. Some LIDENT) (\<lambda>u. True) Keep\<rparr>,
   \<lparr>match = Times (Pred cp.upper) (Star (Pred cp.idchar)),
     act = mk_act (\<lambda>k m. m) (\<lambda>u. Some UIDENT) (\<lambda>u. True) Keep\<rparr>,
   \<lparr>match = Times (Pred [(0x2190, 0x22FF)]) (Star (Pred [(0x2190, 0x22FF)])),
     act = mk_act (\<lambda>k m. m) (\<lambda>u. Some OP) (\<lambda>u. True) Keep\<rparr>,
   \<lparr>match = Times (Pred [(0x0A, 0x0A), (0x20, 0x20)]) (Star (Pred [(0x0A, 0x0A), (0x20, 0x20)])),
     act = mk_act (\<lambda>k m. m) (\<lambda>u. None) (\<lambda>u. True) Keep\<rparr>]\<close>
  by simp

text \<open>The regexes are those of \<^const>\<open>cp_rules\<close> up to the normal form of classes, and
  the actions agree:\<close>

lemma \<open>map (map_rexp cp_norm \<circ> match) (cp.spec ()) = map (map_rexp cp_norm \<circ> match) (hd cp_rules)\<close>
  by eval

lemma \<open>map (\<lambda>r. fst (act r u [()])) (cp.spec ()) = [Some LIDENT, Some UIDENT, Some OP, None]\<close>
  by (simp add: mk_act_def)

lemma \<open>cp.start = ()\<close> \<open>cp.final ()\<close> \<open>cp.is_newline 0x0A\<close> \<open>\<not> cp.is_newline 0x20\<close>
  by (simp_all add: cp.start_def cp.final_def cp.is_newline_def)

subsection \<open>Nested comments\<close>

text \<open>A mode for comments, entered by \<open>push\<close> and left by \<open>pop\<close>. \<open>Comment\<close> is exclusive,
  so the untagged rules are not active there:\<close>

datatype ctok = Word | Num

lexer cmt :: \<open>ctok\<close>
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

lemma \<open>cmt.spec Comment =
  [\<lparr>match = Times (Pred [(0x28, 0x28)]) (Pred [(0x2A, 0x2A)]),
     act = mk_act (\<lambda>k m. m) (\<lambda>u. None) (\<lambda>u. True) (Push Comment)\<rparr>,
   \<lparr>match = Times (Pred [(0x2A, 0x2A)]) (Pred [(0x29, 0x29)]),
     act = mk_act (\<lambda>k m. m) (\<lambda>u. None) (\<lambda>u. True) Pop\<rparr>,
   \<lparr>match =
      Plus (Times (Pred (cp_neg [(0x28, 0x28), (0x2A, 0x2A)]))
          (Star (Pred (cp_neg [(0x28, 0x28), (0x2A, 0x2A)]))))
        (Pred [(0x28, 0x28), (0x2A, 0x2A)]),
     act = mk_act (\<lambda>k m. m) (\<lambda>u. None) (\<lambda>u. True) Keep\<rparr>]\<close>
  by simp

lemma \<open>length (cmt.spec Code) = 4\<close> \<open>cmt.start = Code\<close> \<open>cmt.final Code\<close> \<open>\<not> cmt.final Comment\<close>
  by (simp_all add: cmt.start_def cmt.final_def)

text \<open>A comment opens and closes, and a pop of the last mode is the empty stack:\<close>

lemma
  \<open>act (cmt.spec Code ! 3) u [Code] = (None, [Comment, Code])\<close>
  \<open>act (cmt.spec Comment ! 0) u [Comment, Code] = (None, [Comment, Comment, Code])\<close>
  \<open>act (cmt.spec Comment ! 1) u [Comment, Code] = (None, [Code])\<close>
  \<open>act (cmt.spec Comment ! 1) u [Comment] = (None, [])\<close>
  by (simp_all add: mk_act_def)

subsection \<open>The hook\<close>

text \<open>A minus is negation at the start of an operand and subtraction after one. The hook
  computes the mode from the token, trivia included, and a tag selects the rule:\<close>

datatype otok = Id | Minus | Neg | LParen | RParen

datatype omode = Start | AfterOperand

fun after_tok :: \<open>otok option \<Rightarrow> omode \<Rightarrow> omode\<close> where
  \<open>after_tok (Some Id) _ = AfterOperand\<close>
| \<open>after_tok (Some RParen) _ = AfterOperand\<close>
| \<open>after_tok _ _ = Start\<close>

lexer ops :: \<open>otok\<close>
  modes \<open>omode\<close>
  after after_tok
  rules
    \<open>[a-z]+\<close> \<Rightarrow> Id | "(" \<Rightarrow> LParen | ")" \<Rightarrow> RParen | \<open>[ ]+\<close> \<Rightarrow> skip
  | <Start> "-" \<Rightarrow> Neg
  | <AfterOperand> "-" \<Rightarrow> Minus

lemma \<open>map (\<lambda>r. act r u [Start]) (ops.spec Start) =
  [(Some Id, [AfterOperand]), (Some LParen, [Start]), (Some RParen, [AfterOperand]),
   (None, [Start]), (Some Neg, [Start])]\<close>
  by (simp add: mk_act_def)

lemma \<open>map (\<lambda>r. act r u [AfterOperand]) (ops.spec AfterOperand) =
  [(Some Id, [AfterOperand]), (Some LParen, [Start]), (Some RParen, [AfterOperand]),
   (None, [Start]), (Some Minus, [Start])]\<close>
  by (simp add: mk_act_def)

subsection \<open>Errors\<close>

text \<open>Each spec below fails with the given message. A spec is parsed from a string and
  elaborated in the theory:\<close>

definition \<open>dflt = Start\<close>

ML \<open>
fun lexer_fails ctxt text msg =
  let
    val toks =
      Token.explode (Thy_Header.get_keywords' ctxt) Position.none text
      |> filter Token.is_proper;
    val (opts, spec) =
      #1 (Scan.finite Token.stopper (Lexer_Syntax.options -- Lexer_Syntax.spec) toks);
    val thy = Proof_Context.theory_of ctxt;
  in
    (case Exn.capture (fn () => Named_Target.theory_map (Lexer_Syntax.lexer opts spec) thy) () of
      Exn.Res _ => error ("No error, expected " ^ quote msg)
    | Exn.Exn exn =>
        let val msg' = Runtime.exn_message exn in
          if String.isSubstring msg msg' then ()
          else error ("Expected " ^ quote msg ^ ", got " ^ quote msg')
        end)
  end;
\<close>

ML_command \<open>
  lexer_fails \<^context> "e :: \<open>otok\<close> rules \"x\" \<Rightarrow> Foo"
    "unknown token constructor \"Foo\"";
  lexer_fails \<^context> "e :: \<open>otok\<close> rules \"x\" \<Rightarrow> \<open>1 :: nat\<close>"
    "the action must be";
  lexer_fails \<^context> "e :: \<open>otok\<close> modes A B exclusive A B rules \"x\" \<Rightarrow> Id"
    "active in no mode";
  lexer_fails \<^context> "e :: \<open>otok\<close> modes \<open>omode\<close> rules <Foo> \"x\" \<Rightarrow> Id"
    "unknown mode constructor \"Foo\"";
  lexer_fails \<^context> "e :: \<open>otok\<close> modes \<open>omode\<close> rules <dflt> \"x\" \<Rightarrow> Id"
    "matches no mode";
  lexer_fails \<^context>
    "e :: \<open>otok\<close> where a = \<open>b\<close> | b = \<open>[x]\<close> rules \<open>a\<close> \<Rightarrow> Id"
    "\"b\" is used before its definition";
  lexer_fails \<^context> "e :: \<open>otok\<close> modes \<open>omode\<close> rules \"x\" \<Rightarrow> Id, push dflt"
    "is no mode";
  lexer_fails \<^context> "e :: \<open>otok\<close> modes \<open>nat\<close> rules \"x\" \<Rightarrow> Id"
    "is recursive";
  lexer_fails \<^context> "e :: \<open>otok\<close> rules \"x\" \<Rightarrow> error, pop"
    "error takes no guard and no mode operation"
\<close>

end
