theory CaraML_Lexer
  imports Lexer_Command.Lexer_Check
begin

section \<open>CaraML's lexer in the surface of the lexer command\<close>

text \<open>caraml's token relation (\<open>match_token\<close> in caraml's \<open>parser/Lexer.thy\<close>) and its
  trivia (\<open>match_trivia\<close> in \<open>parser/Trivia.thy\<close>) as a lexer over codepoints, written
  with @{command lexer}. The classes are those of caraml's \<open>UnicodeLexer\<close>. HOL remains
  where the judgment is about values: the token type, the mode type and its hook
  \<open>next_mode\<close>, \<open>operand_end\<close>, \<open>int_ok\<close> and the keyword test of
  backticked operators.

  String interpolation departs from caraml. caraml's \<open>StrI\<close> is one token whose holes
  hold value paths only. Here a hole holds any tokens, braces and strings nested, so a
  string with holes is a start \<open>StrStart\<close>, middles \<open>StrMid\<close> and an end
  \<open>StrEnd\<close> with the tokens of the holes between them.

  A token mode has a context (outside any hole, directly in a hole, or in a hole before
  its first token) and a kind (after trivia, after an operand, after any other token).
  The hook computes the kind from the token, and a fresh hole becomes a hole at its
  first token.\<close>

abbreviation cp :: \<open>string \<Rightarrow> nat list\<close> where
  \<open>cp s \<equiv> map of_char s\<close>

text \<open>caraml's tokens, without its unused \<open>Err\<close> and with the three pieces of a string
  with holes:\<close>

datatype tok
  = KLet | KWith | KIf | KThen | KElse | KMatch | KHandler | KMask | KReturn | KFinally
  | KAs | KType | KExtern | KInfixl | KInfixr | KInfix | KEffect | KModule | KSignature
  | KInstance | KOpen | KInclude
  | Assign | Colon | Arrow | Bar | Comma | Semi | LP | RP | LB | RB | LC | RC | KWild | KLambda
  | LId | UId | Op
  | TSelL | TSelU | TSelN | LSelL | LSelU | LSelN
  | IntL | FloatL | StrL | StrStart | StrMid | StrEnd | CharL

text \<open>The tokens that end an operand (caraml's \<open>operand_end\<close>). A minus right after one is
  an operator, and a dot right after one starts a trailing selector:\<close>

definition operand_end :: \<open>tok \<Rightarrow> bool\<close> where
  \<open>operand_end t \<longleftrightarrow>
     t \<in> {LId, UId, KWild, IntL, FloatL, StrL, StrEnd, CharL, RP, RB, RC,
           TSelL, TSelU, TSelN, LSelL, LSelU, LSelN}\<close>

text \<open>The keywords, which a backticked operator must not be (caraml's \<open>is_keyword\<close>):\<close>

definition is_keyword :: \<open>nat list \<Rightarrow> bool\<close> where
  \<open>is_keyword u \<longleftrightarrow> u \<in> cp ` set
     [''let'', ''with'', ''if'', ''then'', ''else'', ''match'', ''handler'', ''mask'',
      ''return'', ''finally'', ''as'', ''type'', ''extern'', ''infixl'', ''infixr'', ''infix'',
      ''effect'', ''module'', ''signature'', ''instance'', ''open'', ''include'']\<close>

subsection \<open>Integer ranges\<close>

text \<open>A suffixed integer must lie in its type's range (caraml's \<open>in_range\<close>). The
  guard checks it on the lexeme. A range is regular, but a regex for it (leading zeros
  and underscores included) would blow up the tables, and it is a judgment about the
  value, not the form.\<close>

definition digit_val :: \<open>nat \<Rightarrow> nat\<close> where
  \<open>digit_val c =
     (if 0x61 \<le> c \<and> c \<le> 0x66 then c - 0x61 + 10
      else if 0x41 \<le> c \<and> c \<le> 0x46 then c - 0x41 + 10
      else c - 0x30)\<close>

definition digits_value :: \<open>nat \<Rightarrow> nat list \<Rightarrow> int\<close> where
  \<open>digits_value b ds =
     foldl (\<lambda>v c. if c = 0x5F then v else v * int b + int (digit_val c)) 0 ds\<close>

definition suffix_bounds :: \<open>(nat list \<times> int \<times> int) list\<close> where
  \<open>suffix_bounds =
     [(cp ''i8'', - 128, 127),
      (cp ''i16'', - 32768, 32767),
      (cp ''i32'', - 2147483648, 2147483647),
      (cp ''i64'', - 9223372036854775808, 9223372036854775807),
      (cp ''u8'', 0, 255),
      (cp ''u16'', 0, 65535),
      (cp ''u32'', 0, 4294967295),
      (cp ''u64'', 0, 18446744073709551615)]\<close>

definition int_ok :: \<open>nat list \<Rightarrow> bool\<close> where
  \<open>int_ok u =
     (let neg = (take 1 u = [0x2D]);
          v = (if neg then tl u else u);
          (b, w) = (if take 2 v = [0x30, 0x78] then (16, drop 2 v)
                    else if take 2 v = [0x30, 0x62] then (2, drop 2 v) else (10, v));
          is_sfx = (\<lambda>c. c = 0x69 \<or> c = 0x75);
          n = digits_value b (takeWhile (Not \<circ> is_sfx) w);
          x = (if neg then - n else n)
      in case map_of suffix_bounds (dropWhile (Not \<circ> is_sfx) w) of
           None \<Rightarrow> True
         | Some (lo, hi) \<Rightarrow> lo \<le> x \<and> x \<le> hi)\<close>

subsection \<open>The lexer\<close>

datatype kind = Spaced | AfterOp | AfterNonop

datatype ctx = Outer | Hole | Fresh

datatype cmode = Tok ctx kind | Comment

fun next_mode :: \<open>tok option \<Rightarrow> cmode \<Rightarrow> cmode\<close> where
  \<open>next_mode None (Tok c _) = Tok c Spaced\<close>
| \<open>next_mode (Some t) (Tok c _) =
    Tok (if c = Fresh then Hole else c) (if operand_end t then AfterOp else AfterNonop)\<close>
| \<open>next_mode _ Comment = Comment\<close>

lexer caraml :: \<open>tok\<close> (* ~90 s *)
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

text \<open>@{command lexer} evaluates ten tables: one for each token mode and one for
  \<open>Comment\<close>. No two token modes share a table (the selector rules tell the kinds apart,
  the string pieces the contexts). A token table has 96 intervals in its class table, 63
  minterms and 195 to 216 states. The keywords as literal rules cost about 100 of them (a
  trie of the keywords): with one identifier rule and a keyword lookup in its action, a
  token table has 82 intervals, 44 minterms and 98 states, 124 in a hole. Each token table takes 7 to 9 s, the first
  20 s with the setup of the code generator, and the command about 90 s. An evaluation
  of \<^const>\<open>caraml_lex\<close> takes about 40 s, nearly all of it compiling the table
  literals (about 3.5 s each), so its tests use @{command lexer_check}, which compiles
  them once (\<open>CaraML_Lexer_Tests\<close>). Every rule wins in some state of each of its modes
  (the command warns of none).\<close>

text \<open>What caraml has to change to adopt this lexer, in its own repository:

  \<^item> \<open>Tok.thy\<close> loses \<open>Err\<close> and gains \<^const>\<open>StrStart\<close>, \<^const>\<open>StrMid\<close> and
    \<^const>\<open>StrEnd\<close> (in place of \<open>StrI\<close>).
  \<^item> \<open>parser/Lexing.thy\<close> imports the session \<open>Token\<close> for the token record.
  \<^item> The grammar's string productions take a string with holes as a start, the hole's
    tokens, middles and an end, so a hole holds any expression.\<close>

end
