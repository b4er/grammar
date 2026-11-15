(* Author: Basil Fürer *)

theory Bridge_Tests
  imports TIGER_Bridge.TIGER_Bridge TIGER_Grammar_Tests.Parser_Check
begin

section \<open>A grammar on the tokens of a lexer\<close>

text \<open>A toy expression language: the keywords and operators are literal rules of the
  lexer, and the grammar writes them as spellings without a terminals block.\<close>

datatype b_tok = BLet | BIn | BEq | BPlus | BTimes | BLP | BRP | BId | BNum

datatype b_ex = BVar string | BLit nat | BAdd b_ex b_ex | BMul b_ex b_ex | BBind string b_ex b_ex

lexer toy :: \<open>b_tok\<close>
  where letter = \<open>[a-z]\<close> | digit = \<open>[0-9]\<close>
  rules
    "let" \<Rightarrow> BLet | "in" \<Rightarrow> BIn | "=" \<Rightarrow> BEq | "+" \<Rightarrow> BPlus | "*" \<Rightarrow> BTimes
  | "(" \<Rightarrow> BLP | ")" \<Rightarrow> BRP
  | \<open>letter (letter | digit)*\<close> \<Rightarrow> BId
  | \<open>digit+\<close> \<Rightarrow> BNum
  | \<open>[ \n]+\<close> \<Rightarrow> skip

definition b_text :: \<open>(b_tok, nat) lex_token \<Rightarrow> string\<close> where
  \<open>b_text t = map char_of (s_txt (span t))\<close>

definition b_num :: \<open>string \<Rightarrow> nat\<close> where
  \<open>b_num s = foldl (\<lambda>n c. 10 * n + (of_char c - 48)) 0 s\<close>

grammar toy_g = tokens of toy
  precedence left "*" > left "+"
  productions
    E :: \<open>b_ex\<close> = "let" BId "=" E "in" E \<Rightarrow> \<open>\<lambda>x a b. BBind (b_text x) a b\<close> | A
  and
    A :: \<open>b_ex\<close> = A "+" A \<Rightarrow> \<open>BAdd\<close>
      | A "*" A \<Rightarrow> \<open>BMul\<close>
      | "(" E ")"
      | BId \<Rightarrow> \<open>\<lambda>x. BVar (b_text x)\<close>
      | BNum \<Rightarrow> \<open>\<lambda>x. BLit (b_num (b_text x))\<close>

parser toy_parse for toy_g

text \<open>Lexing then parsing: a text that the lexer consumes up to a final mode, parsed.\<close>

definition toy_run :: \<open>string \<Rightarrow> b_ex option\<close> where
  \<open>toy_run s = (case toy_lex (map of_char s) of
    (l, [], _) \<Rightarrow> toy_parse (toks l) | _ \<Rightarrow> None)\<close>

parser_check
  \<open>toy_run ''let x = 1 + 2 * 3 in (x + y1) * 20'' =
    Some (BBind ''x'' (BAdd (BLit 1) (BMul (BLit 2) (BLit 3)))
      (BMul (BAdd (BVar ''x'') (BVar ''y1'')) (BLit 20)))\<close>
  \<open>toy_run ''1 + + 2'' = None\<close>
  \<open>toy_run ''1 ; 2'' = None\<close>

subsection \<open>The example of the manual\<close>

datatype tok = Let | In | Eq | Plus | Id | Num

lexer toy2 :: \<open>tok\<close>
  rules
    "let" \<Rightarrow> Let | "in" \<Rightarrow> In | "=" \<Rightarrow> Eq | "+" \<Rightarrow> Plus
  | \<open>[a-z]+\<close> \<Rightarrow> Id | \<open>[0-9]+\<close> \<Rightarrow> Num | \<open>[ \n]+\<close> \<Rightarrow> skip

grammar toy2_g = tokens of toy2
  productions
    E :: \<open>nat\<close> = "let" Id "=" E "in" E \<Rightarrow> \<open>\<lambda>_ a b. a + b\<close> | S
  and
    S :: \<open>nat\<close> = S "+" Num \<Rightarrow> \<open>\<lambda>a _. a + 1\<close> | Num \<Rightarrow> \<open>\<lambda>_. 1\<close>

parser toy2_parse for toy2_g

definition toy2_run :: \<open>string \<Rightarrow> nat option\<close> where
  \<open>toy2_run s = (case toy2_lex (map of_char s) of
    (l, [], _) \<Rightarrow> toy2_parse (toks l) | _ \<Rightarrow> None)\<close>

parser_check \<open>toy2_run ''let x = 1 + 2 in 3 + 4 + 5'' = Some 5\<close>

subsection \<open>Errors\<close>

text \<open>A terminals block next to \<^theory_text>\<open>tokens of\<close>, and a spelling without a
  literal rule in the lexer:\<close>

ML \<open>
local
  fun spec name terminals lit : Grammar_Common.spec =
    {name = Binding.name name, tok_typ = NONE, lexer = SOME ("toy", Position.none),
     terminals = terminals, prec = NONE,
     productions =
      [((Binding.name "S", SOME (Input.string "unit")),
        [([(Grammar_Common.Lit (lit, Position.none), NONE)], SOME (Input.string "()"))])]};
  fun expect_error prefix sp =
    (Named_Target.theory_map (Grammar_Command.grammar_cmd [] sp) \<^theory>;
     error ("accepted: " ^ Binding.name_of (#name sp)))
    handle ERROR msg =>
      if String.isPrefix prefix msg then () else error ("unexpected: " ^ msg);
in
val _ =
  expect_error "grammar \"both\" takes its terminals from \"toy\""
    (spec "both" [Grammar_Common.Fixed ("let", Input.string "BLet")] "let");
val _ =
  expect_error "Fixed spelling \"if\": the lexer \"toy\" has no literal rule"
    (spec "unspelled" [] "if");
end
\<close>

end
