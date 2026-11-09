theory Pattern_Tests
  imports Lexer_Command.Pattern CaraML_Lexer.CaraML_Spec "Regular-Sets.Equivalence_Checking"
begin

section \<open>Tests of the pattern sublanguage\<close>

text \<open>Every class and regex of the CaraML prototype, written as a pattern over the
  prototype's names, elaborates to the prototype's definition. Classes agree in normal
  form. Regexes agree as regexes over their normalized classes, read as letters, by the
  equivalence checker of \<open>Regular-Sets\<close> (two regexes with the same letter language have
  the same symbolic language). Associativity and units are not compared, as the
  prototype nests concatenations differently.\<close>

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
