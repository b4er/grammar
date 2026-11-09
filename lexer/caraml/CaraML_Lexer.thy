theory CaraML_Lexer
  imports CaraML_Spec Lexer_Command.Lexer_Command
begin

section \<open>CaraML's lexer in the surface of the lexer command\<close>

text \<open>The prototype \<open>CaraML_Spec\<close> written with @{command lexer}. HOL remains where the
  judgment is about values: the mode type and its hook \<open>next_mode\<close>,
  \<^const>\<open>operand_end\<close>, \<^const>\<open>int_ok\<close> and the keyword test of backticked operators.

  A token mode has a context (outside any hole, directly in a hole, or in a hole before
  its first token) and a kind (after trivia, after an operand, after any other token).
  The hook computes the kind from the token, and a fresh hole becomes a hole at its
  first token.\<close>

datatype kind = Spaced | AfterOp | AfterNonop

datatype ctx = Outer | Hole | Fresh

datatype cmode = Tok ctx kind | Comment

fun next_mode :: \<open>tok option \<Rightarrow> cmode \<Rightarrow> cmode\<close> where
  \<open>next_mode None (Tok c _) = Tok c Spaced\<close>
| \<open>next_mode (Some t) (Tok c _) =
    Tok (if c = Fresh then Hole else c) (if operand_end t then AfterOp else AfterNonop)\<close>
| \<open>next_mode _ Comment = Comment\<close>

definition is_keyword :: \<open>nat list \<Rightarrow> bool\<close> where
  \<open>is_keyword u \<longleftrightarrow> u \<in> fst ` set keyword_table\<close>

lexer caraml :: \<open>tok\<close>
  modes \<open>cmode\<close> start \<open>Tok Outer Spaced\<close> exclusive Comment final \<open>Tok Outer _\<close>
  after next_mode
  newline newline
  where
    lower = \<open>[a-z \<alpha>-\<kappa> \<mu>-\<omega>]\<close> | upper = \<open>[A-Z Α-Ρ \<Sigma>-\<Omega>]\<close>
  | digit = \<open>[0-9]\<close> | hex = \<open>[0-9 a-f A-F]\<close> | bin = \<open>[01]\<close>
  | idchar = \<open>lower | upper | digit | [_']\<close>
  | symchar = \<open>[! # $ % & * + \- / : < = > ? @ \\ ^ | ~ \u{2190}-\u{22FF}]\<close>
  | space = \<open>[\n-\r \  \u{85} \u{200E}-\u{200F} \u{2028}-\u{2029}]\<close>
  | newline = \<open>[\n-\r \u{85} \u{2028}-\u{2029}]\<close>
  | bidi = \<open>[\u{202A}-\u{202E} \u{2066}-\u{2069}]\<close>
  | line_char = \<open>_ # (newline | bidi)\<close> | line_start = \<open>line_char # symchar\<close>
  | cmt_char = \<open>_ # ([{\-] | bidi)\<close>
  | run(d) = \<open>d ("_"? d)*\<close>
  | suffix = \<open>"i8" | "i16" | "i32" | "i64" | "u8" | "u16" | "u32" | "u64"\<close>
  | int = \<open>(run(digit) | "0x" run(hex) | "0b" run(bin)) suffix?\<close>
  | exp = \<open>[eE] "-"? run(digit)\<close>
  | float = \<open>run(digit) ("." run(digit) exp? | exp)\<close>
  | hex_cp4 = \<open>[0-9 a-c e-f A-C E-F] hex hex hex | [dD] [0-7] hex hex\<close>
  | hex_cp5 = \<open>[1-9 a-f A-F] hex hex hex hex | "0" hex_cp4\<close>
  | hex_cp6 = \<open>"0" hex_cp5 | "10" hex hex hex hex\<close>
  | escape =
      \<open>"\\" ([0tnr"'\\$] | "u{" (hex | hex hex | hex hex hex | hex_cp4 | hex_cp5 | hex_cp6) "}")\<close>
  | str_char = \<open>_ # ([" \\ $] | newline | bidi)\<close>
  | str_text = \<open>(str_char | escape | "$"+ (str_char # [{] | escape))*\<close>
  | str_open = \<open>str_text "$"* "${"\<close> | str_close = \<open>str_text "$"* "\""\<close>
  | char = \<open>"'" ((_ # (['\\] | newline | bidi)) | escape) "'"\<close>
  rules
    \<open>space+\<close> \<Rightarrow> skip
  | \<open>"--" "-"* (line_start line_char*)?\<close> \<Rightarrow> skip
  | "{-" \<Rightarrow> skip, push Comment
  | "let" \<Rightarrow> KLet | "with" \<Rightarrow> KWith | "if" \<Rightarrow> KIf | "then" \<Rightarrow> KThen | "else" \<Rightarrow> KElse
  | "match" \<Rightarrow> KMatch | "handler" \<Rightarrow> KHandler | "mask" \<Rightarrow> KMask | "return" \<Rightarrow> KReturn
  | "finally" \<Rightarrow> KFinally | "as" \<Rightarrow> KAs | "type" \<Rightarrow> KType | "extern" \<Rightarrow> KExtern
  | "infixl" \<Rightarrow> KInfixl | "infixr" \<Rightarrow> KInfixr | "infix" \<Rightarrow> KInfix | "effect" \<Rightarrow> KEffect
  | "module" \<Rightarrow> KModule | "signature" \<Rightarrow> KSignature | "instance" \<Rightarrow> KInstance
  | "open" \<Rightarrow> KOpen | "include" \<Rightarrow> KInclude
  | \<open>lower idchar*\<close> \<Rightarrow> LId | \<open>upper idchar*\<close> \<Rightarrow> UId
  | \<open>"`" lower idchar* "`"\<close> \<Rightarrow> Op when \<open>\<lambda>u. \<not> is_keyword (butlast (tl u))\<close>
  | "=" \<Rightarrow> Assign | ":" \<Rightarrow> Colon | \<open>"->" | "\<rightarrow>"\<close> \<Rightarrow> Arrow | "|" \<Rightarrow> Bar
  | \<open>"\\" | "\<lambda>"\<close> \<Rightarrow> KLambda
  | \<open>symchar+\<close> \<Rightarrow> Op
  | "(" \<Rightarrow> LP | ")" \<Rightarrow> RP | "[" \<Rightarrow> LB | "]" \<Rightarrow> RB | "," \<Rightarrow> Comma | ";" \<Rightarrow> Semi
  | "{" \<Rightarrow> LC, push \<open>Tok Outer AfterNonop\<close>
  | <Tok Outer _> "}" \<Rightarrow> RC, pop
  | "_" \<Rightarrow> KWild | \<open>"_" idchar+\<close> \<Rightarrow> error
  | <Tok _ Spaced> (
      \<open>"." lower idchar*\<close> \<Rightarrow> LSelL | \<open>"." upper idchar*\<close> \<Rightarrow> LSelU | \<open>"." digit+\<close> \<Rightarrow> LSelN)
  | <Tok _ AfterOp, Tok _ AfterNonop> (
      \<open>"." lower idchar*\<close> \<Rightarrow> TSelL | \<open>"." upper idchar*\<close> \<Rightarrow> TSelU | \<open>"." digit+\<close> \<Rightarrow> TSelN)
  | \<open>"." digit+ idchar+\<close> \<Rightarrow> error
  | \<open>"\"" str_close\<close> \<Rightarrow> StrL
  | \<open>"\"" str_open\<close> \<Rightarrow> StrStart, push \<open>Tok Fresh AfterNonop\<close>
  | <Tok Hole _> \<open>"}" str_open\<close> \<Rightarrow> StrMid, begin \<open>Tok Fresh AfterNonop\<close>
  | <Tok Hole _> \<open>"}" str_close\<close> \<Rightarrow> StrEnd, pop
  | \<open>char\<close> \<Rightarrow> CharL
  | <Tok _ Spaced, Tok _ AfterNonop> (
      \<open>"-"? int\<close> \<Rightarrow> IntL when int_ok | \<open>"-"? float\<close> \<Rightarrow> FloatL
    | \<open>"-"? (int | float) idchar+\<close> \<Rightarrow> error)
  | <Tok _ AfterOp> (
      \<open>int\<close> \<Rightarrow> IntL when int_ok | \<open>float\<close> \<Rightarrow> FloatL | \<open>(int | float) idchar+\<close> \<Rightarrow> error)
  | <Comment> (
      "{-" \<Rightarrow> skip, push Comment | "-}" \<Rightarrow> skip, pop | \<open>cmt_char+ | [{\-]\<close> \<Rightarrow> skip)


end
