theory Pattern_Tests
  imports Lexer_Command.Pattern "Regular-Sets.Equivalence_Checking"
begin

section \<open>Tests of the pattern sublanguage\<close>

text \<open>Every class and regex of a hand-written lexer spec of caraml (the prototype of
  \<open>CaraML_Lexer\<close>), written as a pattern over the prototype's names, elaborates to the
  prototype's definition. Classes agree in normal form. Regexes agree as regexes over
  their normalized classes, read as letters, by the equivalence checker of
  \<open>Regular-Sets\<close> (two regexes with the same letter language have the same symbolic
  language). Associativity and units are not compared, as the prototype nests
  concatenations differently.\<close>

subsection \<open>The prototype's classes and regexes\<close>

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

definition \<open>whitespace =
  [(0x0A, 0x0D), (0x20, 0x20), (0x85, 0x85), (0x200E, 0x200F), (0x2028, 0x2029)]\<close>
definition \<open>newline = [(0x0A, 0x0D), (0x85, 0x85), (0x2028, 0x2029)]\<close>

definition \<open>bidi = [(0x202A, 0x202E), (0x2066, 0x2069)]\<close>

definition \<open>line_char = cp_neg (newline @ bidi)\<close>
definition \<open>line_start = cp_neg (symchar @ newline @ bidi)\<close>
definition \<open>cmt_char = cp_neg (chs [0x7B, 0x2D] @ bidi)\<close>
definition \<open>str_char = cp_neg (chs [0x22, 0x5C, 0x24] @ newline @ bidi)\<close>
definition \<open>str_char_nobrace = cp_neg (chs [0x22, 0x5C, 0x24, 0x7B] @ newline @ bidi)\<close>
definition \<open>char_char = cp_neg (chs [0x27, 0x5C] @ newline @ bidi)\<close>

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

definition \<open>suffix_re = alts (map (word \<circ> cp)
  [''i8'', ''i16'', ''i32'', ''i64'', ''u8'', ''u16'', ''u32'', ''u64''])\<close>

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

subsection \<open>Comparison\<close>

fun atom_list :: \<open>'a rexp \<Rightarrow> 'a list\<close> where
  \<open>atom_list (Atom a) = [a]\<close>
| \<open>atom_list (Plus r s) = atom_list r @ atom_list s\<close>
| \<open>atom_list (Times r s) = atom_list r @ atom_list s\<close>
| \<open>atom_list (Star r) = atom_list r\<close>
| \<open>atom_list _ = []\<close>

definition same_lang :: \<open>nat cls rexp \<Rightarrow> nat cls rexp \<Rightarrow> bool\<close> where
  \<open>same_lang r s =
    (let r' = map_rexp cp_norm r; s' = map_rexp cp_norm s;
         as = remdups (atom_list r' @ atom_list s');
         ix = (\<lambda>a. the (map_of (zip as [0..<length as]) a))
     in check_eqv (map_rexp ix r') (map_rexp ix s'))\<close>

subsection \<open>Classes\<close>

lemma \<open>cp_norm PAT\<open>[a-z \<alpha>-\<kappa> \<mu>-\<omega>]\<close> = cp_norm lower\<close> by eval
lemma \<open>cp_norm PAT\<open>[A-Z Α-Ρ \<Sigma>-\<Omega>]\<close> = cp_norm upper\<close> by eval
lemma \<open>cp_norm PAT\<open>[0-9]\<close> = cp_norm digit\<close> by eval
lemma \<open>cp_norm PAT\<open>[0-9 a-f A-F]\<close> = cp_norm hexdigit\<close> by eval
lemma \<open>cp_norm PAT\<open>[01]\<close> = cp_norm bindigit\<close> by eval
lemma \<open>cp_norm PAT\<open>lower | upper\<close> = cp_norm idstart\<close> by eval
lemma \<open>cp_norm PAT\<open>lower | upper | digit | [_']\<close> = cp_norm idchar\<close> by eval

lemma \<open>cp_norm PAT\<open>[! # $ % & * + \- / : < = > ? @ \\ ^ | ~ \u{2190}-\u{22FF}]\<close> =
  cp_norm symchar\<close>
  by eval

lemma \<open>cp_norm PAT\<open>[\n-\r \  \u{85} \u{200E}-\u{200F} \u{2028}-\u{2029}]\<close> = cp_norm whitespace\<close>
  by eval

lemma \<open>cp_norm PAT\<open>[\n-\r \u{85} \u{2028}-\u{2029}]\<close> = cp_norm newline\<close> by eval
lemma \<open>cp_norm PAT\<open>[\u{202A}-\u{202E} \u{2066}-\u{2069}]\<close> = cp_norm bidi\<close> by eval
lemma \<open>cp_norm PAT\<open>_ # (newline | bidi)\<close> = cp_norm line_char\<close> by eval
lemma \<open>cp_norm PAT\<open>line_char # symchar\<close> = cp_norm line_start\<close> by eval
lemma \<open>cp_norm PAT\<open>_ # ([{\-] | bidi)\<close> = cp_norm cmt_char\<close> by eval
lemma \<open>cp_norm PAT\<open>_ # ([" \\ $] | newline | bidi)\<close> = cp_norm str_char\<close> by eval
lemma \<open>cp_norm PAT\<open>str_char # [{]\<close> = cp_norm str_char_nobrace\<close> by eval
lemma \<open>cp_norm PAT\<open>_ # ([' \\] | newline | bidi)\<close> = cp_norm char_char\<close> by eval

subsection \<open>Regexes\<close>

lemma \<open>same_lang PAT\<open>digit ("_"? digit)*\<close> (run digit)\<close> by eval
lemma \<open>same_lang PAT\<open>"i8" | "i16" | "i32" | "i64" | "u8" | "u16" | "u32" | "u64"\<close> suffix_re\<close>
  by eval

lemma \<open>same_lang PAT\<open>(run(digit) | "0x" run(hexdigit) | "0b" run(bindigit)) suffix_re?\<close> int_re\<close>
  by eval

lemma \<open>same_lang PAT\<open>"." run(digit)\<close> frac_re\<close> by eval
lemma \<open>same_lang PAT\<open>[eE] "-"? run(digit)\<close> exp_re\<close> by eval
lemma \<open>same_lang PAT\<open>run(digit) (frac_re exp_re? | exp_re)\<close> float_re\<close> by eval
lemma \<open>same_lang (Pred PAT\<open>[0-9 a-f A-F]\<close>) hex\<close> by eval
text \<open>The first class of the prototype's \<^const>\<open>hex_cp4\<close> is the complement of the
  non-digits below \<open>g\<close> and of \<open>d\<close>, \<open>D\<close>, so it also holds every codepoint from \<open>g\<close>
  on (\<open>\u{z123}\<close> is an escape). The pattern of the design differs from it, and agrees
  with it once those codepoints are added:\<close>

lemma \<open>\<not> same_lang PAT\<open>[0-9 a-c e-f A-C E-F] hex hex hex | [dD] [0-7] hex hex\<close> hex_cp4\<close>
  by eval

lemma \<open>same_lang
  PAT\<open>[0-9 a-c e-f A-C E-F \u{67}-\u{10FFFF}] hex hex hex | [dD] [0-7] hex hex\<close> hex_cp4\<close>
  by eval

lemma \<open>same_lang PAT\<open>[1-9 a-f A-F] hex hex hex hex | "0" hex_cp4\<close> hex_cp5\<close> by eval
lemma \<open>same_lang PAT\<open>"0" hex_cp5 | "10" hex hex hex hex\<close> hex_cp6\<close> by eval

lemma \<open>same_lang
  PAT\<open>"\\" ([0tnr"'\\$] | "u{" (hex | hex hex | hex hex hex | hex_cp4 | hex_cp5 | hex_cp6) "}")\<close>
  escape_re\<close>
  by eval

lemma \<open>same_lang PAT\<open>"$"+\<close> dollars\<close> by eval
lemma \<open>same_lang PAT\<open>(str_char | escape_re | "$"+ (str_char # [{] | escape_re))*\<close> str_text\<close>
  by eval

lemma \<open>same_lang PAT\<open>str_text "$"* "${"\<close> str_open\<close> by eval
lemma \<open>same_lang PAT\<open>str_text "$"* "\""\<close> str_close\<close> by eval
lemma \<open>same_lang PAT\<open>"\"" str_close\<close> str_re\<close> by eval
lemma \<open>same_lang PAT\<open>"\"" str_open\<close> str_start_re\<close> by eval
lemma \<open>same_lang PAT\<open>"}" str_open\<close> str_mid_re\<close> by eval
lemma \<open>same_lang PAT\<open>"}" str_close\<close> str_end_re\<close> by eval
lemma \<open>same_lang PAT\<open>"'" (char_char | escape_re) "'"\<close> char_re\<close> by eval
lemma \<open>same_lang PAT\<open>"--" "-"* (line_start line_char*)?\<close> line_comment_re\<close> by eval

text \<open>The equivalence checker tells regexes apart:\<close>

lemma \<open>\<not> same_lang PAT\<open>"--" "-"+\<close> line_comment_re\<close> by eval

subsection \<open>Templates and errors\<close>

text \<open>The diagnostic command elaborates in the environment of its \<open>where\<close> block. A
  parameter used as a class is a class:\<close>

pattern \<open>run(digit) | sep([a], [b])\<close>
  where digit = \<open>[0-9]\<close> | run(d) = \<open>d ("_"? d)*\<close> | sep(c, d) = \<open>(c # d) d\<close>

ML \<open>
fun expect_error msg src =
  (case Exn.capture (Pattern.read \<^context> (Pattern.const_env \<^context>)) (Input.string src) of
    Exn.Res _ => error ("No error for " ^ quote src)
  | Exn.Exn (ERROR m) =>
      if String.isSubstring msg m then () else error ("Wrong error for " ^ quote src ^ ": " ^ m)
  | Exn.Exn e => Exn.reraise e);

expect_error "Undefined constant: \"nowhere\"" "[a] nowhere";
expect_error "left side of # is not a class" "\"ab\" # [a]";
expect_error "right side of # is not a class" "_ # [a]*";
expect_error "empty range" "[z-a]";
expect_error "codepoint above U+10FFFF" "\"\\u{110000}\"";
expect_error "unknown escape" "\"\\q\"";
expect_error "unterminated class" "[a-z";
expect_error "takes 1 argument" "run";
expect_error "is neither a class nor a regex" "cp";
expect_error "expected \")\"" "(lower";
\<close>

end
