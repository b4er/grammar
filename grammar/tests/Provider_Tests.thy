(* Author: Basil Fürer *)

theory Provider_Tests
  imports TIGER_Grammar.LR_Prec_Parse Parser_Check
begin

section \<open>Terminals from a provider: \<^theory_text>\<open>tokens of L\<close>\<close>

text \<open>A terminal provider gives a grammar its token type and the token of each fixed
  spelling. In the session \<^verbatim>\<open>TIGER_Bridge\<close> every lexer is one; here a
  provider is registered by hand.\<close>

datatype p_tok = PLet | PIn | PEq | PPlus | PId | PNum

datatype p_ex = PVar \<open>char list\<close> | PLit nat | PSum p_ex p_ex | PBind \<open>char list\<close> p_ex p_ex

type_synonym p_token = \<open>(p_tok, char) token\<close>

local_setup \<open>
  Terminal_Provider.register \<^binding>\<open>toy\<close>
    {tokenT = \<^typ>\<open>p_token\<close>,
     spellings = [("let", \<^term>\<open>PLet\<close>), ("in", \<^term>\<open>PIn\<close>), ("=", \<^term>\<open>PEq\<close>),
       ("+", \<^term>\<open>PPlus\<close>)]}
\<close>

grammar toy_g = tokens of toy
  productions
    E :: \<open>p_ex\<close> = "let" PId "=" E "in" E \<Rightarrow> \<open>\<lambda>x a b. PBind (s_txt (span x)) a b\<close>
      | T "+" E \<Rightarrow> \<open>PSum\<close>
      | T
  and
    T :: \<open>p_ex\<close> = PId \<Rightarrow> \<open>\<lambda>x. PVar (s_txt (span x))\<close> | PNum \<Rightarrow> \<open>\<lambda>x. PLit (length (s_txt (span x)))\<close>

text \<open>The literals are the provider's tokens:\<close>

lemma \<open>toy_g =
  is_cfg.make
   [(''E'', [(Tm PLet, Any), (Tm PId, Any), (Tm PEq, Any), (Nt ''E'', Any), (Tm PIn, Any),
      (Nt ''E'', Any)]),
    (''E'', [(Nt ''T'', Any), (Tm PPlus, Any), (Nt ''E'', Any)]),
    (''E'', [(Nt ''T'', Any)]),
    (''T'', [(Tm PId, Any)]),
    (''T'', [(Tm PNum, Any)])]
   ''E'' 0\<close>
  by (simp only: toy_g_def)

parser toy_parse for toy_g

fun ptoks :: \<open>nat \<Rightarrow> (p_tok \<times> string) list \<Rightarrow> p_token list\<close> where
  \<open>ptoks i [] = []\<close>
| \<open>ptoks i ((t, s) # xs) =
    \<lparr>tok = t, span = span.make 1 i i (length s) s\<rparr> # ptoks (i + length s + 1) xs\<close>

parser_check \<open>toy_parse (ptoks 0 [(PLet, ''let''), (PId, ''x''), (PEq, ''=''), (PNum, ''12''),
    (PIn, ''in''), (PId, ''x''), (PPlus, ''+''), (PId, ''y'')]) =
  Some (PBind ''x'' (PLit 2) (PSum (PVar ''x'') (PVar ''y'')))\<close>

subsection \<open>Errors\<close>

text \<open>A terminals block next to \<^theory_text>\<open>tokens of\<close>, a spelling the provider does
  not have, and an unknown provider are errors.\<close>

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
    (spec "both" [Grammar_Common.Fixed ("let", Input.string "PLet")] "let");
val _ =
  expect_error "Fixed spelling \"if\": the lexer \"toy\" has no literal rule"
    (spec "unspelled" [] "if");
val _ =
  expect_error "Undefined terminal provider"
    {name = Binding.name "unknown", tok_typ = NONE, lexer = SOME ("nope", Position.none),
     terminals = [], prec = NONE, productions = #productions (spec "u" [] "let")};
end
\<close>

end
