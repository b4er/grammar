theory CaraML_Spec
  imports Lexer.Codepoints
begin

section \<open>A prototype of CaraML's lexer as a spec\<close>

text \<open>CaraML's token relation (\<open>match_token\<close> in caraml's \<open>parser/Lexer.thy\<close>) and its
  trivia (\<open>match_trivia\<close> in \<open>parser/Trivia.thy\<close>) written as a lexer spec over
  codepoints, to find out whether our format expresses them and what the tables cost.
  The classes are those of caraml's \<open>UnicodeLexer\<close>, the token type is caraml's
  \<open>tok\<close> without the unused \<open>Err\<close>.

  String interpolation departs from caraml. caraml's \<open>StrI\<close> is one token whose holes
  hold value paths only. Here a hole holds any tokens, braces and strings nested, so a
  string with holes is a sequence of tokens (see the modes below).\<close>

subsection \<open>Character classes\<close>

abbreviation cp :: \<open>string \<Rightarrow> nat list\<close> where
  \<open>cp s \<equiv> map of_char s\<close>

definition ch :: \<open>nat \<Rightarrow> nat cls\<close> where
  \<open>ch c = [(c, c)]\<close>

definition chs :: \<open>nat list \<Rightarrow> nat cls\<close> where
  \<open>chs cs = map (\<lambda>c. (c, c)) cs\<close>

definition \<open>lower = [(0x61, 0x7A), (0x3B1, 0x3BA), (0x3BC, 0x3C9)]\<close>
definition \<open>upper = [(0x41, 0x5A), (0x391, 0x3A1), (0x3A3, 0x3A9)]\<close>
definition \<open>digit = [(0x30, 0x39)]\<close>
definition \<open>hexdigit = [(0x30, 0x39), (0x41, 0x46), (0x61, 0x66)]\<close>
definition \<open>bindigit = [(0x30, 0x31)]\<close>

definition \<open>idstart = lower @ upper\<close>
definition \<open>idchar = lower @ upper @ digit @ chs [0x5F, 0x27]\<close>

definition \<open>symchar = chs
  [0x21, 0x23, 0x24, 0x25, 0x26, 0x2A, 0x2B, 0x2D, 0x2F, 0x3A,
   0x3C, 0x3D, 0x3E, 0x3F, 0x40, 0x5C, 0x5E, 0x7C, 0x7E] @
  [(0x2190, 0x22FF)]\<close>

definition \<open>whitespace = [(0x0A, 0x0D), (0x20, 0x20), (0x85, 0x85), (0x200E, 0x200F), (0x2028, 0x2029)]\<close>
definition \<open>newline = [(0x0A, 0x0D), (0x85, 0x85), (0x2028, 0x2029)]\<close>

definition \<open>bidi = [(0x202A, 0x202E), (0x2066, 0x2069)]\<close>

text \<open>The classes of text exclude the bidirectional controls:\<close>

definition \<open>special = bidi\<close>

definition \<open>line_char = cp_neg (newline @ special)\<close>
definition \<open>line_start = cp_neg (symchar @ newline @ special)\<close>
definition \<open>cmt_char = cp_neg (chs [0x7B, 0x2D] @ special)\<close>
definition \<open>str_char = cp_neg (chs [0x22, 0x5C, 0x24] @ newline @ special)\<close>
definition \<open>str_char_nobrace = cp_neg (chs [0x22, 0x5C, 0x24, 0x7B] @ newline @ special)\<close>
definition \<open>char_char = cp_neg (chs [0x27, 0x5C] @ newline @ special)\<close>

subsection \<open>Tokens and tables\<close>

datatype tok
  = KLet | KWith | KIf | KThen | KElse | KMatch | KHandler | KMask | KReturn | KFinally
  | KAs | KType | KExtern | KInfixl | KInfixr | KInfix | KEffect | KModule | KSignature
  | KInstance | KOpen | KInclude
  | Assign | Colon | Arrow | Bar | Comma | Semi | LP | RP | LB | RB | LC | RC | KWild | KLambda
  | LId | UId | Op
  | TSelL | TSelU | TSelN | LSelL | LSelU | LSelN
  | IntL | FloatL | StrL | StrStart | StrMid | StrEnd | CharL

definition keyword_table :: \<open>(nat list \<times> tok) list\<close> where
  \<open>keyword_table =
     [(cp ''let'', KLet), (cp ''with'', KWith), (cp ''if'', KIf), (cp ''then'', KThen),
      (cp ''else'', KElse), (cp ''match'', KMatch), (cp ''handler'', KHandler),
      (cp ''mask'', KMask), (cp ''return'', KReturn), (cp ''finally'', KFinally),
      (cp ''as'', KAs), (cp ''type'', KType), (cp ''extern'', KExtern),
      (cp ''infixl'', KInfixl), (cp ''infixr'', KInfixr), (cp ''infix'', KInfix),
      (cp ''effect'', KEffect), (cp ''module'', KModule), (cp ''signature'', KSignature),
      (cp ''instance'', KInstance), (cp ''open'', KOpen), (cp ''include'', KInclude)]\<close>

definition symbol_table :: \<open>(nat list \<times> tok) list\<close> where
  \<open>symbol_table =
     [(cp ''='', Assign), (cp '':'', Colon), (cp ''->'', Arrow), ([0x2192], Arrow),
      (cp ''|'', Bar), ([0x5C], KLambda)]\<close>

definition delim_table :: \<open>(nat \<times> tok) list\<close> where
  \<open>delim_table =
     [(0x28, LP), (0x29, RP), (0x5B, LB), (0x5D, RB), (0x2C, Comma), (0x3B, Semi),
      (0x3BB, KLambda)]\<close>

definition classify_id :: \<open>nat list \<Rightarrow> tok\<close> where
  \<open>classify_id u =
     (case map_of keyword_table u of
        Some t \<Rightarrow> t
      | None \<Rightarrow> if in_cls upper (hd u) then UId else LId)\<close>

definition classify_sym :: \<open>nat list \<Rightarrow> tok\<close> where
  \<open>classify_sym u = (case map_of symbol_table u of Some t \<Rightarrow> t | None \<Rightarrow> Op)\<close>

definition operand_end :: \<open>tok \<Rightarrow> bool\<close> where
  \<open>operand_end t \<longleftrightarrow>
     t \<in> {LId, UId, KWild, IntL, FloatL, StrL, StrEnd, CharL, RP, RB, RC,
           TSelL, TSelU, TSelN, LSelL, LSelU, LSelN}\<close>

subsection \<open>Modes\<close>

text \<open>caraml's lexer state \<open>lstate\<close> has two flags: \<open>operand\<close> (the previous token ends
  an operand) and \<open>adjacent\<close> (no trivia since). Only three combinations are
  distinguished, the three kinds of a token mode:

  \<^item> \<open>spaced\<close> (0): at the start or after trivia (\<open>adjacent\<close> false). A dash directly
    before a digit starts a numeral, a selector is loose.
  \<^item> \<open>after_op\<close> (1): directly after an operand-ending token (caraml's
    \<open>after_operand\<close>). There is no negative numeral rule, so \<open>-\<close> is an operator; a
    selector is tight.
  \<^item> \<open>after_nonop\<close> (2): directly after any other token. The rules of \<open>spaced\<close>, and a
    selector is tight.

  A token mode also has a context: \<open>outer\<close> (0) outside any hole or inside braces,
  \<open>hole\<close> (1) directly inside a hole \<open>${\<dots>}\<close>, and \<open>fresh\<close> (2) in a hole before its first
  token. A hole has the rules of the other contexts and two more, which read the \<open>}\<close> that
  closes it. The token mode of context \<open>c\<close> and kind \<open>k\<close> is \<open>3 * c + k\<close>. The mode
  \<open>comment\<close> (9) is inside a block comment, the stack holding one entry per open \<open>{-\<close>.

  A token action replaces the top by the kind \<open>after_op\<close> or \<open>after_nonop\<close> by caraml's
  \<open>operand_end\<close>, a trivia action by \<open>spaced\<close>. Both keep the context, except that a fresh
  hole stays fresh only through trivia. \<open>{-\<close> in a token mode replaces the top by
  \<open>spaced\<close> and pushes \<open>comment\<close> (the comment is trivia, so the mode after it is
  \<open>spaced\<close>), \<open>{-\<close> in \<open>comment\<close> pushes, \<open>-}\<close> pops.

  \<open>{\<close> pushes an outer mode and \<open>}\<close> pops it (an unmatched \<open>}\<close> outside a hole keeps the
  stack), so the \<open>}\<close> that closes a hole is the first one at the hole's own level. The
  start \<open>"\<dots>${\<close> of a string with holes pushes a fresh hole above the mode after the
  string, a middle \<open>}\<dots>${\<close> replaces the hole by a fresh one, and the end \<open>}\<dots>"\<close> pops it.

  An action that rejects the lexeme returns the empty stack, which stops the driver: the
  error rules, a suffixed integer out of range, a backticked keyword, a \<open>}\<close> in a hole
  that no string piece follows and an empty hole.

  The input must end in outer modes. An input that ends inside a comment or a hole
  leaves the mode \<open>comment\<close> or a hole on the final stack.\<close>

definition \<open>spaced      \<equiv> 0 :: nat\<close>
definition \<open>after_op    \<equiv> 1 :: nat\<close>
definition \<open>after_nonop \<equiv> 2 :: nat\<close>

definition \<open>outer \<equiv> 0 :: nat\<close>
definition \<open>hole  \<equiv> 1 :: nat\<close>
definition \<open>fresh \<equiv> 2 :: nat\<close>

definition \<open>comment \<equiv> 9 :: nat\<close>

definition tmode :: \<open>nat \<Rightarrow> nat \<Rightarrow> nat\<close> where
  \<open>tmode c k = 3 * c + k\<close>

definition mode_kind :: \<open>nat \<Rightarrow> nat\<close> where
  \<open>mode_kind m = m mod 3\<close>

definition mode_ctx :: \<open>nat \<Rightarrow> nat\<close> where
  \<open>mode_ctx m = m div 3\<close>

definition set_top :: \<open>nat \<Rightarrow> nat list \<Rightarrow> nat list\<close> where
  \<open>set_top k st =
     (let c = mode_ctx (hd st) in tmode (if c = fresh \<and> k \<noteq> spaced then hole else c) k # tl st)\<close>

definition mode_after :: \<open>tok \<Rightarrow> nat\<close> where
  \<open>mode_after t = (if operand_end t then after_op else after_nonop)\<close>

definition emit :: \<open>tok \<Rightarrow> nat list \<Rightarrow> tok option \<times> nat list\<close> where
  \<open>emit t st = (Some t, set_top (mode_after t) st)\<close>

definition \<open>trivia_act = (\<lambda>_ st. (None, set_top spaced st))\<close>
definition \<open>reject_act = (\<lambda>_ _. (None, []))\<close>

text \<open>The actions of braces and string pieces:\<close>

definition open_brace_act :: \<open>nat list \<Rightarrow> nat list \<Rightarrow> tok option \<times> nat list\<close> where
  \<open>open_brace_act _ st = (Some LC, tmode outer after_nonop # set_top after_nonop st)\<close>

definition close_brace_act :: \<open>nat list \<Rightarrow> nat list \<Rightarrow> tok option \<times> nat list\<close> where
  \<open>close_brace_act _ st =
     (if mode_ctx (hd st) \<noteq> outer then (None, [])
      else (Some RC, set_top after_op (if tl st = [] then st else tl st)))\<close>

definition str_start_act :: \<open>nat list \<Rightarrow> nat list \<Rightarrow> tok option \<times> nat list\<close> where
  \<open>str_start_act _ st = (Some StrStart, tmode fresh after_nonop # set_top after_op st)\<close>

definition str_mid_act :: \<open>nat list \<Rightarrow> nat list \<Rightarrow> tok option \<times> nat list\<close> where
  \<open>str_mid_act _ st =
     (if mode_ctx (hd st) = fresh then (None, [])
      else (Some StrMid, tmode fresh after_nonop # tl st))\<close>

definition str_end_act :: \<open>nat list \<Rightarrow> nat list \<Rightarrow> tok option \<times> nat list\<close> where
  \<open>str_end_act _ st = (if mode_ctx (hd st) = fresh then (None, []) else (Some StrEnd, tl st))\<close>

definition sel_tok :: \<open>nat \<Rightarrow> nat \<Rightarrow> tok\<close> where
  \<open>sel_tok m c =
     (if in_cls digit c then (if mode_kind m = spaced then LSelN else TSelN)
      else if in_cls upper c then (if mode_kind m = spaced then LSelU else TSelU)
      else (if mode_kind m = spaced then LSelL else TSelL))\<close>

subsection \<open>Integer ranges\<close>

text \<open>A suffixed integer must lie in its type's range (caraml's \<open>in_range\<close>). The
  action checks it on the lexeme. A range is regular, but a regex for it (leading zeros
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

subsection \<open>Regexes\<close>

definition many :: \<open>'p \<Rightarrow> 'p rexp\<close> where
  \<open>many p = Times (Pred p) (Star (Pred p))\<close>

definition opt :: \<open>'p rexp \<Rightarrow> 'p rexp\<close> where
  \<open>opt r = Plus One r\<close>

definition alts :: \<open>'p rexp list \<Rightarrow> 'p rexp\<close> where
  \<open>alts rs = foldr Plus (butlast rs) (last rs)\<close>

definition seq :: \<open>'p rexp list \<Rightarrow> 'p rexp\<close> where
  \<open>seq rs = foldr Times (butlast rs) (last rs)\<close>

definition word :: \<open>nat list \<Rightarrow> nat cls rexp\<close> where
  \<open>word cs = seq (map (Pred \<circ> ch) cs)\<close>

text \<open>Digit runs \<open>D ("_"? D)*\<close>, the integers and floats of \<open>grammar.md\<close> \<section>1:\<close>

definition run :: \<open>nat cls \<Rightarrow> nat cls rexp\<close> where
  \<open>run d = Times (Pred d) (Star (Times (opt (Pred (ch 0x5F))) (Pred d)))\<close>

definition \<open>suffix_re = alts (map (word \<circ> fst) suffix_bounds)\<close>

definition \<open>int_re = Times
  (alts [run digit,
         Times (word (cp ''0x'')) (run hexdigit),
         Times (word (cp ''0b'')) (run bindigit)])
  (opt suffix_re)\<close>

definition \<open>frac_re = Times (Pred (ch 0x2E)) (run digit)\<close>
definition \<open>exp_re = seq [Pred (chs [0x65, 0x45]), opt (Pred (ch 0x2D)), run digit]\<close>
definition \<open>float_re = Times (run digit) (Plus (Times frac_re (opt exp_re)) exp_re)\<close>

text \<open>An escape \<open>\u{h\<dots>}\<close> takes one to six hexadecimal digits denoting a Unicode scalar
  value: at most \<open>10FFFF\<close> and no surrogate \<open>D800 .. DFFF\<close>. By number of digits:\<close>

definition \<open>hex = Pred hexdigit\<close>

definition \<open>hex_cp4 = Plus
  (seq [Pred (cp_neg ([(0, 0x2F), (0x3A, 0x40), (0x47, 0x60)] @ chs [0x44, 0x64])), hex, hex, hex])
  (seq [Pred (chs [0x44, 0x64]), Pred [(0x30, 0x37)], hex, hex])\<close>

definition \<open>hex_cp5 = Plus
  (seq [Pred [(0x31, 0x39), (0x41, 0x46), (0x61, 0x66)], hex, hex, hex, hex])
  (Times (Pred (ch 0x30)) hex_cp4)\<close>

definition \<open>hex_cp6 = Plus
  (Times (Pred (ch 0x30)) hex_cp5)
  (seq [Pred (ch 0x31), Pred (ch 0x30), hex, hex, hex, hex])\<close>

definition \<open>escape_re = Times (Pred (ch 0x5C)) (Plus
  (Pred (chs [0x30, 0x74, 0x6E, 0x72, 0x22, 0x27, 0x5C, 0x24]))
  (seq [word (cp ''u{''), alts [hex, seq [hex, hex], seq [hex, hex, hex], hex_cp4, hex_cp5,
    hex_cp6], Pred (ch 0x7D)]))\<close>

text \<open>The text of a string: characters, escapes, and runs of \<open>$\<close> before a character
  other than \<open>{\<close> or before an escape. A string without holes is text between quotes. A
  string with holes is a start \<open>"\<dots>${\<close>, middles \<open>}\<dots>${\<close> and an end \<open>}\<dots>"\<close>, with the tokens
  of the holes between them. A run of \<open>$\<close> may stand before \<open>${\<close> and the closing quote:\<close>

definition \<open>dollars = many (ch 0x24)\<close>

definition \<open>str_text = Star (alts [Pred str_char, escape_re,
  Times dollars (alts [Pred str_char_nobrace, escape_re])])\<close>

definition \<open>str_open = Times str_text (Times (Star (Pred (ch 0x24))) (word (cp ''${'')))\<close>
definition \<open>str_close = Times str_text (Times (opt dollars) (Pred (ch 0x22)))\<close>

definition \<open>str_re = Times (Pred (ch 0x22)) str_close\<close>
definition \<open>str_start_re = Times (Pred (ch 0x22)) str_open\<close>
definition \<open>str_mid_re = Times (Pred (ch 0x7D)) str_open\<close>
definition \<open>str_end_re = Times (Pred (ch 0x7D)) str_close\<close>

definition \<open>char_re = seq [Pred (ch 0x27), Plus (Pred char_char) escape_re, Pred (ch 0x27)]\<close>

text \<open>A line comment is a run of at least two dashes that no symbol character extends,
  then the rest of the line:\<close>

definition \<open>line_comment_re = seq [word (cp ''--''), Star (Pred (ch 0x2D)),
  opt (Times (Pred line_start) (Star (Pred line_char)))]\<close>

subsection \<open>The rules\<close>

type_synonym crule = \<open>(tok, nat cls, nat, nat) rule\<close>

definition tok_rule :: \<open>nat cls rexp \<Rightarrow> tok \<Rightarrow> crule\<close> where
  \<open>tok_rule r t = \<lparr>match = r, act = \<lambda>_. emit t\<rparr>\<close>

text \<open>The error rules: a lexeme that a character of a class would extend is an
  error. With \<open>R\<close> the form of the token and \<open>P\<close> the class, the error rule
  \<open>R P\<^sup>+\<close> after the token rule gives caraml's tail condition \<open>\<not> starts P tail\<close>
  (see the classification below):\<close>

definition err_rule :: \<open>nat cls rexp \<Rightarrow> crule\<close> where
  \<open>err_rule r = \<lparr>match = Times r (many idchar), act = reject_act\<rparr>\<close>

definition \<open>num_re neg = (if neg then Times (opt (Pred (ch 0x2D))) else id)\<close>

text \<open>The rules of a token mode, by whether it reads negative numerals and whether it
  is a hole:\<close>

definition token_rules :: \<open>bool \<Rightarrow> bool \<Rightarrow> crule list\<close> where
  \<open>token_rules neg h =
    [\<lparr>match = many whitespace, act = trivia_act\<rparr>,
     \<lparr>match = line_comment_re, act = trivia_act\<rparr>,
     \<lparr>match = word (cp ''{-''), act = \<lambda>_ st. (None, comment # set_top spaced st)\<rparr>,
     \<lparr>match = Times (Pred idstart) (Star (Pred idchar)), act = \<lambda>u. emit (classify_id u)\<rparr>,
     \<lparr>match = seq [Pred (ch 0x60), Pred lower, Star (Pred idchar), Pred (ch 0x60)],
      act = \<lambda>u st. if map_of keyword_table (butlast (tl u)) = None then emit Op st
                    else (None, [])\<rparr>,
     \<lparr>match = many symchar, act = \<lambda>u. emit (classify_sym u)\<rparr>,
     \<lparr>match = Pred (chs (map fst delim_table)), act = \<lambda>u. emit (the (map_of delim_table (hd u)))\<rparr>,
     \<lparr>match = Pred (ch 0x7B), act = open_brace_act\<rparr>,
     \<lparr>match = Pred (ch 0x7D), act = close_brace_act\<rparr>,
     tok_rule (Pred (ch 0x5F)) KWild,
     err_rule (Pred (ch 0x5F)),
     \<lparr>match = seq [Pred (ch 0x2E), Pred idstart, Star (Pred idchar)],
      act = \<lambda>u st. emit (sel_tok (hd st) (u ! 1)) st\<rparr>,
     \<lparr>match = Times (Pred (ch 0x2E)) (many digit),
      act = \<lambda>u st. emit (sel_tok (hd st) (u ! 1)) st\<rparr>,
     err_rule (Times (Pred (ch 0x2E)) (many digit)),
     tok_rule str_re StrL,
     \<lparr>match = str_start_re, act = str_start_act\<rparr>,
     tok_rule char_re CharL,
     \<lparr>match = num_re neg int_re, act = \<lambda>u st. if int_ok u then emit IntL st else (None, [])\<rparr>,
     tok_rule (num_re neg float_re) FloatL,
     err_rule (num_re neg (Plus int_re float_re))] @
    (if h then [\<lparr>match = str_mid_re, act = str_mid_act\<rparr>, \<lparr>match = str_end_re, act = str_end_act\<rparr>]
     else [])\<close>

definition comment_rules :: \<open>crule list\<close> where
  \<open>comment_rules =
    [\<lparr>match = word (cp ''{-''), act = \<lambda>_ st. (None, comment # st)\<rparr>,
     \<lparr>match = word (cp ''-}''), act = \<lambda>_ st. (None, tl st)\<rparr>,
     \<lparr>match = many cmt_char, act = \<lambda>_ st. (None, st)\<rparr>,
     \<lparr>match = Pred (chs [0x7B, 0x2D]), act = \<lambda>_ st. (None, st)\<rparr>]\<close>

definition caraml_rules :: \<open>crule list list\<close> where
  \<open>caraml_rules =
     [token_rules True False, token_rules False False, token_rules True False,
      token_rules True True, token_rules False True, token_rules True True,
      token_rules True True, token_rules False True, token_rules True True, comment_rules]\<close>

subsection \<open>Tables\<close>

text \<open>The kinds \<open>spaced\<close> and \<open>after_nonop\<close> share their rules, and so do the contexts
  \<open>hole\<close> and \<open>fresh\<close>, so four token tables are generated. \<open>timed_eval_table\<close> is
  \<open>eval_table\<close> printing the time it takes:\<close>

ML \<open>
fun timed_eval_table bt lthy =
  let val (time, lthy') = Timing.timing (eval_table bt) lthy
  in writeln (Timing.message time); lthy' end
\<close>

definition \<open>comment_tables = cp_tables comment_rules\<close>

local_setup \<open>timed_eval_table (\<^binding>\<open>comment_tables_code\<close>, \<^term>\<open>comment_tables\<close>)\<close>

declare comment_tables_code[code]

text \<open>Generation takes about 2.5 s for \<open>comment\<close> and 5 s for each token mode (the
  first of these includes setting up the code generator).\<close>

definition \<open>after_op_tables = cp_tables (token_rules False False)\<close>

local_setup \<open>timed_eval_table (\<^binding>\<open>after_op_tables_code\<close>, \<^term>\<open>after_op_tables\<close>)\<close>

declare after_op_tables_code[code]

definition \<open>spaced_tables = cp_tables (token_rules True False)\<close>

local_setup \<open>timed_eval_table (\<^binding>\<open>spaced_tables_code\<close>, \<^term>\<open>spaced_tables\<close>)\<close>

declare spaced_tables_code[code]

definition \<open>hole_after_op_tables = cp_tables (token_rules False True)\<close>

local_setup \<open>timed_eval_table (\<^binding>\<open>hole_after_op_tables_code\<close>, \<^term>\<open>hole_after_op_tables\<close>)\<close>

declare hole_after_op_tables_code[code]

definition \<open>hole_spaced_tables = cp_tables (token_rules True True)\<close>

local_setup \<open>timed_eval_table (\<^binding>\<open>hole_spaced_tables_code\<close>, \<^term>\<open>hole_spaced_tables\<close>)\<close>

declare hole_spaced_tables_code[code]

text \<open>The sizes: minterm intervals of the class table, minterms (DFA columns) and
  states of each mode.\<close>

lemma \<open>map table_size
         [spaced_tables, after_op_tables, hole_spaced_tables, hole_after_op_tables,
          comment_tables]
       = [(82, 44, 98), (82, 44, 98), (82, 44, 124), (82, 44, 124), (11, 5, 7)]\<close>
  by eval (* ~9 s *)

text \<open>The two token modes of a context have as many states: they differ in the state
  after \<open>-\<close>, from which the negative numeral rules lead into the states of the unsigned
  numerals. A hole has more states for the string pieces after \<open>}\<close>.\<close>

subsection \<open>The lexer\<close>

definition caraml_tables :: \<open>cp_tables iarray\<close> where
  \<open>caraml_tables = IArray
     [spaced_tables, after_op_tables, spaced_tables,
      hole_spaced_tables, hole_after_op_tables, hole_spaced_tables,
      hole_spaced_tables, hole_after_op_tables, hole_spaced_tables, comment_tables]\<close>

lemma caraml_tables_eq: \<open>caraml_tables = cp_lexer_tables caraml_rules\<close>
  by (simp add: caraml_tables_def cp_lexer_tables_def caraml_rules_def spaced_tables_def
      after_op_tables_def hole_spaced_tables_def hole_after_op_tables_def comment_tables_def)

definition is_nl :: \<open>nat \<Rightarrow> bool\<close> where
  \<open>is_nl c \<longleftrightarrow> in_cls newline c\<close>

definition start :: pos where
  \<open>start = \<lparr>line = 0, col = 0, off = 0\<rparr>\<close>

definition caraml_lex :: \<open>nat list \<Rightarrow> (tok, nat) lexed \<times> nat list \<times> nat list\<close> where
  \<open>caraml_lex s = cp_lexer caraml_tables id (list_spec caraml_rules) is_nl [spaced] start s\<close>

text \<open>On an input in range, the prototype is the driver of the spec:\<close>

theorem caraml_lex_iff_lexes:
  assumes \<open>\<forall>c \<in> set s. c \<le> 0x10FFFF\<close>
  shows \<open>caraml_lex s = (l, r, st\<^sub>f) \<longleftrightarrow>
    symbolic.lexes in_cls (list_spec caraml_rules) is_nl [spaced] start s l r st\<^sub>f\<close>
  unfolding caraml_lex_def caraml_tables_eq
  by (rule cp_lexer_list_iff_lexes_in_range) (use assms in auto)

subsection \<open>How caraml's rules map\<close>

text \<open>Each premise of caraml's \<open>match_token\<close> and \<open>match_trivia\<close> that looks at the
  input after the lexeme (\<open>starts P tail\<close>), and each use of the lexer state, falls in
  one of four classes. None needs trailing context (flex's \<open>r/s\<close>).

  \<^bold>\<open>Longest match.\<close> A condition \<open>\<not> starts P tail\<close> on a token whose form ends in
  \<open>P\<^sup>*\<close> only says that the run is maximal: \<open>Key\<close>, \<open>LId\<close>, \<open>UId\<close> (\<open>P\<close> =
  \<open>is_idchar\<close>), \<open>Sym\<close>, \<open>Op\<close> (\<open>is_symchar\<close>), \<open>Sel\<close>. Keywords and reserved symbols
  are one rule each with a lookup in the action (\<^const>\<open>classify_id\<close>,
  \<^const>\<open>classify_sym\<close>), as in caraml's executable lexer. \<open>Delim\<close>'s exclusion of
  \<open>{\<close> before \<open>-\<close> is the longer rule \<open>{-\<close>. The line comment (\<open>Line\<close>: a dash run that
  no symbol character extends) is the rule \<open>--\<close>\<open>-\<^sup>*\<close> followed by a character that is
  no symbol character, then the rest of the line, placed before the symbol rule: on
  \<open>-->\<close> the operator is longer, on \<open>--\<close> alone both have the same length and the
  comment wins by priority. Strings (\<open>Str\<close>, and \<open>$\<close> not before \<open>{\<close> is text) and
  characters (\<open>Char\<close>) have no tail condition; the escape \<open>\u{h\<dots>}\<close> with its
  scalar-value range is a regex by number of digits (@{const hex_cp4} to
  @{const hex_cp6}). Bidirectional controls are in no class a rule reads, so the
  driver stops at one wherever it is, as caraml's \<open>no_bidi\<close> rejects the source.

  \<^bold>\<open>Error rules.\<close> A condition \<open>\<not> starts P tail\<close> on a token whose form does not end
  in \<open>P\<^sup>*\<close>: \<open>Int\<close>, \<open>Float\<close> and \<open>SelN\<close> (a numeral or selector numeral followed by a
  letter, \<open>_\<close> or \<open>'\<close>) and \<open>Wild\<close> (\<open>_x\<close>, \<open>_1\<close>). With \<open>R\<close> the token's form, the
  rule \<open>R P\<^sup>+\<close> after the token rule rejects (@{const err_rule}). This is the same:
  let \<open>L\<close> be the longest prefix in \<open>R\<close>. If the tail after \<open>L\<close> starts with \<open>c \<in> P\<close>,
  then \<open>L c\<close> matches the error rule and is longer. If not, a match \<open>p w\<close> of the error
  rule with \<open>p \<in> R\<close>, \<open>w \<in> P\<^sup>+\<close> and \<open>|p w| > |L|\<close> has \<open>|p| \<le> |L|\<close>, so position
  \<open>|L|\<close> lies in \<open>w\<close> and the tail starts with \<open>P\<close>: no such match exists. On equal
  length the token rule comes first. It needs that no other rule matches longer from
  the same start, which holds: a digit, \<open>.\<close> and \<open>_\<close> start no other rule, and of a
  negative numeral the symbol rule matches only the dash. caraml's
  readers (\<open>read_num\<close>) are greedy, and on these deterministic forms greedy is
  longest.

  \<^bold>\<open>Actions.\<close> The range of a suffixed integer (\<open>in_range\<close>, @{const int_ok}) and a
  backticked keyword (\<open>Tick\<close>'s \<open>\<not> is_keyword\<close>) are decided on the lexeme. A
  rejecting action stops the driver as caraml's lexer stops: a lexeme it rejects is not
  lexed shorter.

  \<^bold>\<open>Modes.\<close> The lexer state (see the modes above): \<open>neg_ok\<close> and \<open>Op\<close>'s
  exclusion of a lone dash before a digit are the negative numeral rules, present in
  \<open>spaced\<close> and \<open>after_nonop\<close> and absent in \<open>after_op\<close> (where longest match would
  otherwise read \<open>x-1\<close> as \<open>x\<close>, \<open>-1\<close>); \<open>sel_tok\<close>'s tight against loose reads the mode
  in the selector action. Nested block comments (\<open>comment_body\<close>, \<open>Nest\<close>) are the
  \<open>comment\<close> mode: caraml's scanner \<open>lex_block_cmt\<close> also takes \<open>{-\<close> and \<open>-}\<close> at the
  first position they occur, so a body ending in \<open>{\<close> fails in both.

  \<^bold>\<open>End of input.\<close> An unterminated block comment or hole consumes the input, and
  the final stack of \<^const>\<open>symbolic.lexes\<close> holds a mode that is not outer. That is
  the error, without a sentinel at the end of the input.

  \<^bold>\<open>Does not fit.\<close> (1) A CRLF is one line end for caraml, two for
  \<^const>\<open>advance\<close>, which reads one character (test below). (2) caraml keeps the
  trivia of a token as a list
  of classified, spanned trivia; \<^type>\<open>lex_token\<close> keeps their text, so its
  \<open>comments_of\<close> is not available without a second pass.\<close>

section \<open>Tests against caraml\<close>

text \<open>The snippets and expected results of caraml's \<open>parser/test/Lexer_Test.thy\<close>, where
  each is checked against \<open>caraml_lex\<close> by \<open>eval\<close>. Both lexers cannot be loaded
  together (the two \<open>Token\<close> theories clash, see "Decisions" in \<open>README.md\<close>), so the
  expected token lists are copied from there; the token constructors have the same
  names. \<open>toks_of s\<close> is the token classes if \<open>s\<close> lexes completely (an empty residue
  and only outer modes on the final stack), \<open>lexs s\<close> the lexemes, \<open>err s\<close> says that
  \<open>s\<close> has a lexical error.

  Timing: each \<open>eval\<close> below takes about 3 s alone and up to 30 s with all of them
  running in parallel, nearly all of it generating and compiling the code of the table
  constants, not lexing; the theory takes about 10 min of CPU time. The checks of a
  subsection therefore share one \<open>eval\<close>.\<close>

definition toks_of :: \<open>nat list \<Rightarrow> tok list option\<close> where
  \<open>toks_of s = (case caraml_lex s of (l, r, st\<^sub>f) \<Rightarrow>
     if r = [] \<and> list_all (\<lambda>m. mode_ctx m = outer) st\<^sub>f then Some (map tok (toks l))
     else None)\<close>

abbreviation \<open>lexs s \<equiv> map (s_txt \<circ> span) (toks (fst (caraml_lex s)))\<close>
abbreviation \<open>err s \<equiv> toks_of s = None\<close>

abbreviation \<open>nl \<equiv> 0x0A :: nat\<close>
abbreviation \<open>sp \<equiv> 0x20 :: nat\<close>
abbreviation \<open>qt \<equiv> 0x22 :: nat\<close>
abbreviation \<open>cq \<equiv> 0x27 :: nat\<close>
abbreviation \<open>bslash \<equiv> 0x5C :: nat\<close>
abbreviation \<open>dot \<equiv> 0x2E :: nat\<close>
abbreviation \<open>lrm \<equiv> 0x202E :: nat\<close>

subsection \<open>Keywords, symbols and delimiters\<close>

lemma \<open>toks_of (cp ''let with if then else match handler mask return finally as type'')
       = Some [KLet, KWith, KIf, KThen, KElse, KMatch, KHandler, KMask, KReturn, KFinally, KAs,
          KType]\<close>
  by eval

lemma \<open>toks_of (cp ''extern infixl infixr infix effect module signature instance open include'')
       = Some [KExtern, KInfixl, KInfixr, KInfix, KEffect, KModule, KSignature, KInstance, KOpen,
          KInclude]\<close>
  by eval

lemma \<open>toks_of (cp ''in fn handle where literal'') = Some [LId, LId, LId, LId, LId] \<and>
       toks_of (cp ''lets if' then_'') = Some [LId, LId, LId]\<close>
  by eval

lemma \<open>toks_of (cp ''= : -> | '' @ [bslash, sp, 0x2192, sp, 0x3BB])
       = Some [Assign, Colon, Arrow, Bar, KLambda, Arrow, KLambda] \<and>
       toks_of ([bslash, bslash, sp, bslash] @ cp ''-> <- --> == :: |> ->>'')
       = Some [Op, Op, Op, Op, Op, Op, Op, Op] \<and>
       toks_of (cp ''( ) [ ] { } , ;'') = Some [LP, RP, LB, RB, LC, RC, Comma, Semi] \<and>
       toks_of ([0x3BB] @ cp ''x'') = Some [KLambda, LId]\<close>
  by eval

subsection \<open>Identifiers, the wildcard and backticked names\<close>

lemma \<open>toks_of (cp ''x x' x_1 M M' M_1 _'') = Some [LId, LId, LId, UId, UId, UId, KWild] \<and>
       lexs (cp ''f'' @ [cq] @ cp ''a'' @ [cq] @ cp '' x'')
       = [cp ''f'' @ [cq] @ cp ''a'' @ [cq], cp ''x''] \<and>
       err (cp ''_1'') \<and> err (cp ''_x'') \<and> toks_of (cp ''_ 1'') = Some [KWild, IntL] \<and>
       toks_of (cp ''x `f` y'') = Some [LId, Op, LId] \<and>
       err (cp ''`let`'') \<and> err (cp ''`F`'') \<and> err (cp ''`f'') \<and> err (cp ''``'')\<close>
  by eval

subsection \<open>Selectors\<close>

lemma \<open>toks_of (cp ''p.1.2'') = Some [LId, TSelN, TSelN] \<and>
       lexs (cp ''p.1.2'') = [cp ''p'', cp ''.1'', cp ''.2''] \<and>
       toks_of (cp ''1.2.3'') = Some [FloatL, TSelN] \<and>
       lexs (cp ''1.2.3'') = [cp ''1.2'', cp ''.3''] \<and>
       toks_of (cp ''.5'') = Some [LSelN] \<and> toks_of (cp ''x .5'') = Some [LId, LSelN]\<close>
  by eval

lemma \<open>toks_of (cp ''M.x M.N.y p.q x .y M .N'')
       = Some [UId, TSelL, UId, TSelU, TSelL, LId, TSelL, LId, LSelL, UId, LSelU] \<and>
       toks_of (cp ''x{- -}.y x'' @ [nl] @ cp ''.y (x).y'')
       = Some [LId, LSelL, LId, LSelL, LP, LId, RP, TSelL] \<and>
       err (cp ''x.'') \<and> err (cp ''x . y'') \<and> err (cp ''x.(y)'') \<and> err (cp ''.1x'') \<and>
       err (cp ''x.let'' @ [sp, dot]) \<and>
       toks_of (cp ''x.let'') = Some [LId, TSelL]\<close>
  by eval

subsection \<open>Numerals\<close>

lemma \<open>toks_of (cp ''0 42 1_000 0xFF 0xf_f 0b1010 0b1_0'')
       = Some [IntL, IntL, IntL, IntL, IntL, IntL, IntL] \<and>
       err (cp ''1_'') \<and> err (cp ''1__0'') \<and> err (cp ''0x_F'') \<and> err (cp ''0x'') \<and>
       toks_of (cp ''1i8 1i16 1i32 1i64 1u8 1u16 1u32 1u64'')
       = Some [IntL, IntL, IntL, IntL, IntL, IntL, IntL, IntL]\<close>
  by eval

lemma \<open>err (cp ''256u8'') \<and> err (cp ''-1u8'') \<and> err (cp ''128i8'') \<and>
       err (cp ''0xFFi8'') \<and>
       toks_of (cp ''-0x80i8 -128i8 127i8 255u8 0xFFu8 18446744073709551615u64'')
       = Some [IntL, IntL, IntL, IntL, IntL, IntL] \<and>
       err (cp ''18446744073709551616u64'')\<close>
  by eval

lemma \<open>toks_of (cp ''1.0 1.5e3 1.5E-3 1e3 1e-3 1_0.0_1e1_0'')
       = Some [FloatL, FloatL, FloatL, FloatL, FloatL, FloatL] \<and>
       err (cp ''1.'') \<and> err (cp ''1.5e'') \<and> err (cp ''1.5u8'') \<and>
       err (cp ''1e'') \<and> err (cp ''1e+3'') \<and>
       toks_of (cp ''1.e3'') = Some [IntL, TSelL] \<and> toks_of (cp ''0x1.5'') = Some [IntL, TSelN] \<and>
       err (cp ''1x'') \<and> err (cp ''1i9'') \<and> err (cp ''0xFFg'') \<and> err (cp ''1.5f'')\<close>
  by eval

subsection \<open>Negative literals\<close>

lemma \<open>toks_of (cp ''x-1'') = Some [LId, Op, IntL] \<and>
       toks_of (cp ''x - 1'') = Some [LId, Op, IntL] \<and>
       toks_of (cp ''f -1'') = Some [LId, IntL] \<and>
       toks_of (cp ''(-1)'') = Some [LP, IntL, RP] \<and>
       toks_of (cp ''(- 1)'') = Some [LP, Op, IntL, RP] \<and>
       toks_of (cp ''-1'') = Some [IntL] \<and>
       toks_of (cp ''-1.5'') = Some [FloatL] \<and>
       toks_of (cp ''x = -1'') = Some [LId, Assign, IntL] \<and>
       lexs (cp ''f -1'') = [cp ''f'', cp ''-1''] \<and>
       lexs (cp ''x-1'') = [cp ''x'', cp ''-'', cp ''1'']\<close>
  by eval

lemma \<open>toks_of (cp ''1-1 x.y-1 (x)-1 [x]-1 {x}-1 _-1'')
       = Some [IntL, Op, IntL, LId, TSelL, Op, IntL, LP, LId, RP, Op, IntL, LB, LId, RB, Op, IntL,
          LC, LId, RC, Op, IntL, KWild, Op, IntL] \<and>
       err (cp ''- 1u8'' @ [sp] @ cp ''-1u8'') \<and> toks_of (cp ''- 1u8'') = Some [Op, IntL]\<close>
  by eval

subsection \<open>Comments\<close>

lemma \<open>toks_of (cp ''x --> y'') = Some [LId, Op, LId] \<and>
       toks_of (cp ''x -- y'') = Some [LId] \<and>
       toks_of (cp ''x --- y'' @ [nl] @ cp ''z'') = Some [LId, LId] \<and>
       toks_of (cp ''x --| y'') = Some [LId, Op, LId] \<and>
       toks_of (cp ''x {- {- -} -} y'') = Some [LId, LId] \<and>
       err (cp ''x {- {- -} y'') \<and>
       toks_of (cp ''x {--} y'') = Some [LId, LId]\<close>
  by eval

text \<open>A comment is trivia of the token before it, read in pieces (caraml reads one
  trivium per comment):\<close>

lemma \<open>map (trivia) (toks (fst (caraml_lex (cp ''x {- {- -} -} y -- z''))))
       = [cp '' {- {- -} -} '', cp '' -- z'']\<close>
  by eval

subsection \<open>Bidirectional controls\<close>

lemma \<open>err (cp ''x -- '' @ [lrm]) \<and>
       err (cp ''x {- '' @ [lrm] @ cp '' -} y'') \<and>
       err ([qt] @ cp ''a'' @ [lrm] @ cp ''b'' @ [qt]) \<and>
       err ([cq, lrm, cq]) \<and>
       err (cp ''x '' @ [0x2066] @ cp '' y'') \<and>
       toks_of ([qt, bslash] @ cp ''u{202E}'' @ [qt]) = Some [StrL]\<close>
  by eval

subsection \<open>Strings and characters\<close>

lemma \<open>toks_of ([qt, bslash] @ cp ''$'' @ [qt]) = Some [StrL] \<and>
       toks_of ([qt] @ cp ''$x $'' @ [qt]) = Some [StrL] \<and>
       toks_of ([qt] @ cp ''a'' @ [bslash] @ cp ''tb'' @ [bslash] @ cp ''nc'' @ [bslash]
                   @ cp ''rd'' @ [bslash] @ cp ''0'' @ [bslash, qt, bslash, cq, bslash, bslash, qt])
       = Some [StrL] \<and>
       toks_of ([qt, bslash] @ cp ''u{41}'' @ [bslash] @ cp ''u{1F642}'' @ [qt]) = Some [StrL] \<and>
       toks_of [qt, qt] = Some [StrL]\<close>
  by eval

lemma \<open>err ([qt, bslash] @ cp ''q'' @ [qt]) \<and>
       err ([qt, bslash] @ cp ''u{110000}'' @ [qt]) \<and>
       err ([qt, bslash] @ cp ''u{}'' @ [qt]) \<and>
       err ([qt, bslash] @ cp ''u{1234567}'' @ [qt]) \<and>
       err ([qt, bslash] @ cp ''u{D800}'' @ [qt]) \<and>
       err ([qt] @ cp ''a'') \<and>
       err ([qt] @ cp ''a'' @ [nl] @ cp ''b'' @ [qt])\<close>
  by eval

lemma \<open>toks_of (cp ''x '' @ [qt] @ cp ''ab'' @ [qt] @ cp ''y'') = Some [LId, StrL, LId] \<and>
       toks_of ([cq, 0x61, cq, sp, cq, bslash] @ cp ''n'' @ [cq, sp, cq, bslash] @ cp ''u{1F642}''
             @ [cq, sp, cq, bslash, cq, cq]) = Some [CharL, CharL, CharL, CharL] \<and>
       err ([cq, bslash] @ cp ''u{110000}'' @ [cq]) \<and> err [cq, cq] \<and>
       err ([cq] @ cp ''ab'' @ [cq]) \<and> err [cq, 0x61] \<and> err [cq, nl, cq]\<close>
  by eval

subsection \<open>Interpolation\<close>

text \<open>These depart from caraml, whose \<open>StrI\<close> is one token and whose holes hold value
  paths only (see the header). A hole holds any tokens:\<close>

lemma \<open>toks_of ([qt] @ cp ''a${M.x}b'' @ [qt]) = Some [StrStart, UId, TSelL, StrEnd] \<and>
       toks_of ([qt] @ cp ''${A.B.c}${d}'' @ [qt])
       = Some [StrStart, UId, TSelU, TSelL, StrMid, LId, StrEnd] \<and>
       toks_of (cp ''"foo: ${foo} bar: ${bar}"'') = Some [StrStart, LId, StrMid, LId, StrEnd] \<and>
       toks_of (cp ''"foo: ${foo} bar: ${bar+1}"'')
       = Some [StrStart, LId, StrMid, LId, Op, IntL, StrEnd] \<and>
       lexs (cp ''"a${x}b${y}c"'') = [cp ''"a${'', cp ''x'', cp ''}b${'', cp ''y'', cp ''}c"''] \<and>
       toks_of (cp ''"${f x}"'') = Some [StrStart, LId, LId, StrEnd] \<and>
       toks_of (cp ''"${x.y}"'') = Some [StrStart, LId, TSelL, StrEnd] \<and>
       toks_of (cp ''"${M}"'') = Some [StrStart, UId, StrEnd] \<and>
       toks_of (cp ''"$${x}$"'') = Some [StrStart, LId, StrEnd] \<and>
       toks_of ([qt, bslash] @ cp ''${x}"'') = Some [StrL]\<close>
  by eval

text \<open>Braces, strings and comments nest in a hole, and the kinds work as outside:\<close>

lemma \<open>toks_of (cp ''"${ {a} }"'') = Some [StrStart, LC, LId, RC, StrEnd] \<and>
       toks_of (cp ''"${ {"}"} }"'') = Some [StrStart, LC, StrL, RC, StrEnd] \<and>
       toks_of (cp ''"a${ "b${c}d" }e"'') = Some [StrStart, StrStart, LId, StrEnd, StrEnd] \<and>
       toks_of (cp ''"${ {- } -} x }"'') = Some [StrStart, LId, StrEnd] \<and>
       toks_of (cp ''{ "${x}" }'') = Some [LC, StrStart, LId, StrEnd, RC] \<and>
       toks_of (cp ''"${-1}" "${x-1}" "${x}"-1'')
       = Some [StrStart, IntL, StrEnd, StrStart, LId, Op, IntL, StrEnd,
          StrStart, LId, StrEnd, Op, IntL] \<and>
       toks_of (cp ''} x'') = Some [RC, LId]\<close>
  by eval

text \<open>An empty hole, a hole or string left open, and a \<open>}\<close> that closes a hole without a
  string piece after it are errors:\<close>

lemma \<open>err (cp ''"${}"'') \<and> err (cp ''"${ }"'') \<and> err (cp ''"${ {- c -} }"'') \<and>
       err (cp ''"a${x}${}"'') \<and>
       err ([qt] @ cp ''${x'' @ [qt]) \<and> err (cp ''"${x'') \<and> err (cp ''"${x}'') \<and>
       err (cp ''"${x}b'') \<and> err (cp ''"${ {x"'') \<and> err (cp ''"${ {x}"'') \<and>
       err (cp ''"${bar+1'')\<close>
  by eval

text \<open>Escapes at the edges of the scalar values, which caraml's tests do not cover:\<close>

lemma \<open>toks_of ([qt, bslash] @ cp ''u{D7FF}'' @ [bslash] @ cp ''u{E000}'' @ [bslash]
          @ cp ''u{0D800}'' @ [bslash] @ cp ''u{10FFFF}'' @ [bslash] @ cp ''u{000041}'' @ [qt])
       = None \<and>
       toks_of ([qt, bslash] @ cp ''u{D7FF}'' @ [bslash] @ cp ''u{E000}'' @ [bslash]
          @ cp ''u{10FFFF}'' @ [bslash] @ cp ''u{000041}'' @ [bslash] @ cp ''u{d80}'' @ [qt])
       = Some [StrL] \<and>
       err ([qt, bslash] @ cp ''u{00dfff}'' @ [qt]) \<and>
       err ([qt, bslash] @ cp ''u{110000}'' @ [qt]) \<and>
       err ([qt, bslash] @ cp ''u{200000}'' @ [qt])\<close>
  by eval

subsection \<open>A small program and positions\<close>

lemma \<open>toks_of (cp ''module M = {'' @ [nl] @ cp ''  let f = '' @ [bslash] @ cp ''x -> x.1 + -1''
             @ [nl] @ cp ''}'')
       = Some [KModule, UId, Assign, LC, KLet, LId, Assign, KLambda, LId, Arrow, LId, TSelN, Op,
          IntL, RC]\<close>
  by eval

lemma \<open>map (\<lambda>t. (s_line (span t), s_col (span t), s_off (span t)))
         (toks (fst (caraml_lex (cp ''ab'' @ [nl] @ cp '' c''))))
       = [(0, 0, 0), (1, 1, 4)]\<close>
  by eval

text \<open>caraml counts a carriage return before a line feed as one line end and gets
  \<open>[(0, 0, 0), (1, 0, 3), (2, 0, 5), (4, 0, 8), (5, 0, 16)]\<close> here.
  \<^const>\<open>advance\<close> reads one character at a time, so a CRLF counts twice:\<close>

lemma \<open>map (\<lambda>t. (s_line (span t), s_col (span t), s_off (span t)))
         (toks (fst (caraml_lex (cp ''a'' @ [0x0D, nl] @ cp ''b'' @ [0x0D] @ cp ''c'' @ [nl, nl]
                                 @ cp ''d -- e'' @ [0x0D, nl] @ cp ''f''))))
       = [(0, 0, 0), (2, 0, 3), (3, 0, 5), (5, 0, 8), (7, 0, 16)]\<close>
  by eval

lemma \<open>err (cp ''x'' @ [0x09] @ cp ''y'') \<and> err [0x09] \<and>
       toks_of ([qt] @ cp ''a'' @ [0x09] @ cp ''b'' @ [qt]) = Some [StrL] \<and>
       toks_of (cp ''x -- a'' @ [0x09] @ cp ''b'') = Some [LId] \<and>
       toks_of (cp ''x {-'' @ [0x09] @ cp ''-}'') = Some [LId]\<close>
  by eval

value \<open>caraml_lex (cp ''"foo: ${foo}"'')\<close>
value \<open>caraml_lex (cp ''"foo: ${foo} bar: ${bar+12}"'')\<close>

end
