(* Author: Basil Fürer *)

theory Stress_Lexer_Tests
  imports TIGER_Lexer.Lexer_Check
begin

section \<open>A stress lexer\<close>

text \<open>A toy ML-like language whose lexer uses the features of @{command lexer} together:
  keywords as literal rules before the identifier rule, nested block comments in an
  exclusive mode with one stack entry per opener, strings with interpolation holes,
  braces that nest in a hole, a negative literal that the hook allows only after an
  operator, error rules, and final modes.

  A string without holes is one token \<open>Str\<close>. A string with holes lexes as \<open>StrStart\<close>
  (\<open>"\<dots>${\<close>), \<open>StrMid\<close> (\<open>}\<dots>${\<close>) and \<open>StrEnd\<close> (\<open>}\<dots>"\<close>), with the tokens of each hole
  between them, as in Swift, Kotlin and Scala lexers. \<open>StrStart\<close> pushes a hole mode,
  \<open>StrMid\<close> replaces it and \<open>StrEnd\<close> pops it; \<open>{\<close> pushes an outer mode and \<open>}\<close> pops it,
  so a \<open>}\<close> in a hole closes a brace opened in that hole, and otherwise ends a string
  piece. A \<open>$\<close> in a string is written \<open>\$\<close>.\<close>

datatype stok =
  KwLet | KwIn | KwFun | Ident | Num | NegNum | Op | LParen | RParen | LBrace | RBrace
| Str | StrStart | StrMid | StrEnd

datatype sctx = Outer | Hole

text \<open>Whether the last token ends an operand: a minus after an operand is an operator,
  after an operator it starts a negative literal.\<close>

datatype sside = AfterOp | AfterVal

datatype smode = Tok sctx sside | Cmt

fun ends_value :: \<open>stok \<Rightarrow> bool\<close> where
  \<open>ends_value t \<longleftrightarrow> t \<in> {Ident, Num, NegNum, RParen, RBrace, Str, StrEnd}\<close>

text \<open>The hook sets the side of a token mode and keeps everything else, trivia included,
  so a comment between an operand and a minus does not make the minus a sign. After a
  \<^const>\<open>Pop\<close> it applies to the revealed mode, so the mode under a hole or a brace
  learns that the string or the block ended an operand.\<close>

fun stress_after :: \<open>stok option \<Rightarrow> smode \<Rightarrow> smode\<close> where
  \<open>stress_after (Some t) (Tok c _) = Tok c (if ends_value t then AfterVal else AfterOp)\<close>
| \<open>stress_after _ m = m\<close>

lexer stress :: \<open>stok\<close>
  modes \<open>smode\<close>
  start \<open>Tok Outer AfterOp\<close>
  exclusive Cmt
  final \<open>Tok Outer AfterOp\<close> \<open>Tok Outer AfterVal\<close>
  after stress_after
  where
    letter = \<open>[a-zA-Z_]\<close> | digit = \<open>[0-9]\<close> | idchar = \<open>letter | digit | [']\<close>
  | strchar = \<open>[^"$\\\n] | "\\" [^\n]\<close>
  rules
    "let" \<Rightarrow> KwLet | "in" \<Rightarrow> KwIn | "fun" \<Rightarrow> KwFun
  | \<open>letter idchar*\<close> \<Rightarrow> Ident
  | \<open>digit+\<close> \<Rightarrow> Num
  | \<open>digit+ letter+\<close> \<Rightarrow> error
  | <Tok _ AfterOp> (
      \<open>"-" digit+\<close> \<Rightarrow> NegNum
    | \<open>"-" digit+ letter+\<close> \<Rightarrow> error
  )
  | \<open>[-+*/<>=]+\<close> \<Rightarrow> Op
  | "(" \<Rightarrow> LParen | ")" \<Rightarrow> RParen
  | "{" \<Rightarrow> LBrace, push \<open>Tok Outer AfterOp\<close>
  | <Tok Outer _> "}" \<Rightarrow> RBrace, pop
  | \<open>"\"" strchar* "\""\<close> \<Rightarrow> Str
  | \<open>"\"" strchar* "${"\<close> \<Rightarrow> StrStart, push \<open>Tok Hole AfterOp\<close>
  | <Tok Hole _> (
      \<open>"}" strchar* "${"\<close> \<Rightarrow> StrMid, begin \<open>Tok Hole AfterOp\<close>
    | \<open>"}" strchar* "\""\<close> \<Rightarrow> StrEnd, pop
  )
  | \<open>[ \n]+\<close> \<Rightarrow> skip
  | "(*" \<Rightarrow> skip, push Cmt
  | <Cmt> (
      "(*" \<Rightarrow> skip, push Cmt
    | "*)" \<Rightarrow> skip, pop
    | \<open>[^*(]+ | [*(]\<close> \<Rightarrow> skip
  )

text \<open>Size and cost (PIDE, 2026-11-13): five tables, one per token mode and one for
  \<open>Cmt\<close>, as no two modes have the same active rules. A token table has 45 class
  intervals, 22 or 23 minterms and 26 to 34 states (the hole modes have the most), the
  comment table 7 states. The command takes about 5 s, 1 s per table; the first
  @{command lexer_check} compiles the tables in about 1 s, the others take milliseconds.\<close>

text \<open>The tokens of a text, its residue and the final stack:\<close>

definition stress_run :: \<open>string \<Rightarrow> stok list \<times> nat \<times> smode list\<close> where
  \<open>stress_run s = (case stress_lex (map (of_char :: char \<Rightarrow> nat) s) of
    (l, r, st) \<Rightarrow> (map tok (toks l), length r, st))\<close>

subsection \<open>Keywords and identifiers\<close>

text \<open>A keyword is a literal rule before the identifier rule: it wins on its own text,
  and a longer identifier wins by length.\<close>

lexer_check
  \<open>stress_run ''let x = fun y in lets'' =
    ([KwLet, Ident, Op, KwFun, Ident, KwIn, Ident], 0, [Tok Outer AfterVal])\<close>
  \<open>stress_run ''in_ fun' f2'' = ([Ident, Ident, Ident], 0, [Tok Outer AfterVal])\<close>
  \<open>stress_run (''x'' @ [CHR 0x0A] @ ''y'') = ([Ident, Ident], 0, [Tok Outer AfterVal])\<close>

text \<open>Spans count lines and columns from 0:\<close>

lexer_check
  \<open>map (\<lambda>t. (s_line (span t), s_col (span t), s_len (span t)))
     (toks (fst (stress_lex (map of_char (''let'' @ [CHR 0x0A] @ ''  xy''))))) =
     [(0, 0, 3), (1, 2, 2)]\<close>

subsection \<open>The negative literal\<close>

text \<open>A minus right after an operand is an operator, after an operator or at the start a
  sign. The side survives trivia and comments, and \<open>)\<close>, \<open>}\<close> and the end of a string
  are operands.\<close>

lexer_check
  \<open>stress_run ''-1'' = ([NegNum], 0, [Tok Outer AfterVal])\<close>
  \<open>stress_run ''x-1'' = ([Ident, Op, Num], 0, [Tok Outer AfterVal])\<close>
  \<open>stress_run ''x - 1'' = ([Ident, Op, Num], 0, [Tok Outer AfterVal])\<close>
  \<open>stress_run ''x = -1'' = ([Ident, Op, NegNum], 0, [Tok Outer AfterVal])\<close>
  \<open>stress_run ''x (* c *) -1'' = ([Ident, Op, Num], 0, [Tok Outer AfterVal])\<close>
  \<open>stress_run ''(-1)-2'' = ([LParen, NegNum, RParen, Op, Num], 0, [Tok Outer AfterVal])\<close>
  \<open>stress_run ''{x}-2'' = ([LBrace, Ident, RBrace, Op, Num], 0, [Tok Outer AfterVal])\<close>
  \<open>stress_run ''"a"-2'' = ([Str, Op, Num], 0, [Tok Outer AfterVal])\<close>
  \<open>stress_run ''"${x}"-2'' = ([StrStart, Ident, StrEnd, Op, Num], 0, [Tok Outer AfterVal])\<close>
  \<open>stress_run ''x--1'' = ([Ident, Op, Num], 0, [Tok Outer AfterVal])\<close>

subsection \<open>Nested comments\<close>

text \<open>One stack entry per opener; the comment is trivia of the token before it:\<close>

lexer_check
  \<open>stress_run ''a (* b (* c *) d *) e'' = ([Ident, Ident], 0, [Tok Outer AfterVal])\<close>
  \<open>stress_run ''(* ( * ) *)'' = ([], 0, [Tok Outer AfterOp])\<close>
  \<open>trivia (hd (toks (fst (stress_lex (map of_char ''a(*(**)*)b''))))) =
     map of_char ''(*(**)*)''\<close>

subsection \<open>Strings and holes\<close>

lexer_check
  \<open>stress_run (''"q'' @ [CHR 0x5C, CHR 0x22] @ '' '' @ [CHR 0x5C] @ ''$x"'') =
    ([Str], 0, [Tok Outer AfterVal])\<close>
  \<open>stress_run ''"a${x}b${y + 1}c"'' =
    ([StrStart, Ident, StrMid, Ident, Op, Num, StrEnd], 0, [Tok Outer AfterVal])\<close>
  \<open>stress_run ''"${ {x} }"'' =
    ([StrStart, LBrace, Ident, RBrace, StrEnd], 0, [Tok Outer AfterVal])\<close>
  \<open>stress_run ''"a${ "b${c}" }d"'' =
    ([StrStart, StrStart, Ident, StrEnd, StrEnd], 0, [Tok Outer AfterVal])\<close>
  \<open>stress_run ''"${-1}"'' = ([StrStart, NegNum, StrEnd], 0, [Tok Outer AfterVal])\<close>
  \<open>stress_run ''"${(* } *) x}"'' = ([StrStart, Ident, StrEnd], 0, [Tok Outer AfterVal])\<close>

text \<open>Inside a hole the stack holds the hole mode over the outer mode, and a brace in the
  hole one more:\<close>

lexer_check
  \<open>stress_run ''"a${x'' = ([StrStart, Ident], 0, [Tok Hole AfterVal, Tok Outer AfterOp])\<close>
  \<open>stress_run ''"${{x'' =
    ([StrStart, LBrace, Ident], 0, [Tok Outer AfterVal, Tok Hole AfterOp, Tok Outer AfterOp])\<close>

subsection \<open>Errors\<close>

text \<open>An error rule \<open>R P\<^sup>+\<close> after the token rule \<open>R\<close> rejects a numeral directly
  followed by a letter: it matches a longer lexeme than \<open>R\<close>, and its action stops the
  lexer. The tokens before it are kept, and the rest of the input is the residue.\<close>

lexer_check
  \<open>stress_run ''x 12ab'' = ([Ident], 4, [Tok Outer AfterVal])\<close>
  \<open>stress_run ''x = -3e'' = ([Ident, Op], 3, [Tok Outer AfterOp])\<close>
  \<open>stress_run ''x-3e'' = ([Ident, Op], 2, [Tok Outer AfterOp])\<close>
  \<open>\<not> stress_lex.ok (map of_char ''12ab'')\<close> \<open>\<not> stress_lex.ok (map of_char ''-3e'')\<close>

text \<open>A character no rule matches is a residue, and so is a \<open>}\<close> in a hole with no
  string piece after it:\<close>

lexer_check
  \<open>stress_run ''x # y'' = ([Ident], 3, [Tok Outer AfterVal])\<close>
  \<open>fst (snd (stress_run ''"${x} '')) = 2\<close>
  \<open>\<not> stress_lex.ok (map of_char ''"${x} '')\<close>

text \<open>A \<open>}\<close> at the top level would pop the last mode. As with \<^theory_text>\<open>error\<close>, the
  step that would leave the empty stack is not taken: lexing stops before the \<open>}\<close>, in
  the stack it had.\<close>

lexer_check
  \<open>stress_run ''x } y'' = ([Ident], 3, [Tok Outer AfterVal])\<close>
  \<open>\<not> stress_lex.ok (map of_char ''x }'')\<close>

subsection \<open>Final modes\<close>

text \<open>An unterminated comment or hole consumes the input but stops in a mode that is
  not final:\<close>

lexer_check
  \<open>stress_lex.ok (map of_char ''let s = "a${f (-1)}b" in {s} (* (* *) *)'')\<close>
  \<open>\<not> stress_lex.ok (map of_char ''x (* (* *)'')\<close>
  \<open>snd (snd (stress_run ''x (* (* *)'')) = [Cmt, Tok Outer AfterVal]\<close>
  \<open>\<not> stress_lex.ok (map of_char ''"a${x'')\<close>
  \<open>\<not> stress_lex.ok (map of_char ''"a${x}b'')\<close>

end
