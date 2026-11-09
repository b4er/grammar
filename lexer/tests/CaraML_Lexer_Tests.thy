theory CaraML_Lexer_Tests
  imports CaraML_Lexer.CaraML_Lexer
begin

section \<open>Tests of CaraML's lexer spec\<close>

text \<open>Every token mode has the 47 untagged rules and its tagged ones: the closing brace
  outside holes, the three selectors of its kind, the two string pieces in a hole and the
  three numerals of its kind. \<open>Comment\<close> is exclusive and has its own three rules:\<close>

lemma
  \<open>length (caraml.spec (Tok Outer Spaced)) = 54\<close>
  \<open>length (caraml.spec (Tok Outer AfterOp)) = 54\<close>
  \<open>length (caraml.spec (Tok Hole AfterNonop)) = 55\<close>
  \<open>length (caraml.spec (Tok Fresh Spaced)) = 53\<close>
  \<open>length (caraml.spec Comment) = 3\<close>
  by simp_all

text \<open>The end of a comment pops, and the hook makes the outer mode spaced. The end of a
  string pops a hole, and the hook makes the outer mode one after an operand:\<close>

lemma
  \<open>act (caraml.spec Comment ! 1) u [Comment, Tok Outer AfterOp] = (None, [Tok Outer Spaced])\<close>
  \<open>act (caraml.spec (Tok Hole Spaced) ! 50) u [Tok Hole Spaced, Tok Outer Spaced] =
    (Some StrEnd, [Tok Outer AfterOp])\<close>
  by (simp_all add: mk_act_def operand_end_def)

lemma \<open>caraml.start = Tok Outer Spaced\<close> \<open>caraml.final (Tok Outer AfterOp)\<close>
  \<open>\<not> caraml.final (Tok Hole Spaced)\<close> \<open>\<not> caraml.final Comment\<close>
  by (simp_all add: caraml.start_def caraml.final_def)

subsection \<open>The generated lexer\<close>

text \<open>The first check compiles \<^const>\<open>caraml_lex\<close> and \<^const>\<open>caraml_lex.ok\<close>
  with the table literals (about 40 s), the others reuse them. A minus is a sign after
  trivia and an operator after an operand. A dot after trivia starts a leading selector
  and one after an operand a trailing selector:\<close>

lexer_check (* ~40 s *)
  \<open>map tok (toks (fst (caraml_lex (cp ''let x = f -1 in a-1'')))) =
    [KLet, LId, Assign, LId, IntL, LId, LId, Op, IntL]\<close>
  \<open>map tok (toks (fst (caraml_lex (cp ''r.x .y M.N.0'')))) =
    [LId, TSelL, LSelL, UId, TSelU, TSelN]\<close>
  \<open>caraml_lex.ok (cp ''r.x'')\<close>

text \<open>An interpolated string is a start, the tokens of its hole and an end. A comment
  nests, and an unterminated one ends in \<^const>\<open>Comment\<close>, which is not final:\<close>

lexer_check
  \<open>map tok (toks (fst (caraml_lex ([0x22] @ cp ''a${x}b'' @ [0x22])))) =
    [StrStart, LId, StrEnd]\<close>
  \<open>map tok (toks (fst (caraml_lex (cp ''a {- {- b -} -} c'')))) = [LId, LId]\<close>
  \<open>caraml_lex.ok (cp ''a {- {- b -} -} c'')\<close>
  \<open>\<not> caraml_lex.ok (cp ''a {- b'')\<close>

text \<open>A backticked name is an operator unless it is a keyword, where the guard stops the
  lexer:\<close>

lexer_check
  \<open>map tok (toks (fst (caraml_lex (cp ''a `mod` b'')))) = [LId, Op, LId]\<close>
  \<open>\<not> caraml_lex.ok (cp ''a `let` b'')\<close>

lex caraml_lex \<open>let s = "n = ${n + 1}" -- done\<close>

section \<open>Tests against caraml\<close>

text \<open>The snippets and expected results of caraml's \<open>parser/test/Lexer_Test.thy\<close>, where
  each is checked against caraml's lexer by \<open>eval\<close>. Both lexers cannot be loaded
  together (the two \<open>Token\<close> theories clash, see "Decisions" in \<open>README.md\<close>), so the
  expected token lists are copied from there. The token constructors have the same
  names. \<open>toks_of s\<close> is the token kinds if \<open>s\<close> lexes completely (an empty residue
  and only final modes on a non-empty final stack), \<open>lexs s\<close> the lexemes, \<open>err s\<close> says
  that \<open>s\<close> has a lexical error. They are abbreviations, so each check mentions only the
  compiled \<^const>\<open>caraml_lex\<close>.

  One test departs from caraml. An unmatched \<open>}\<close> at the top level is an error (the pop
  of the only mode empties the stack, as flex's \<open>yy_pop_state\<close> on a stack of one fails),
  where caraml reads it as \<^const>\<open>RC\<close> and keeps the stack. The parser rejects it
  anyway.\<close>

abbreviation toks_of :: \<open>nat list \<Rightarrow> tok list option\<close> where
  \<open>toks_of s \<equiv> (case caraml_lex s of (l, r, st\<^sub>f) \<Rightarrow>
     if r = [] \<and> st\<^sub>f \<noteq> [] \<and> list_all caraml.final st\<^sub>f then Some (map tok (toks l))
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

lexer_check
  \<open>toks_of (cp ''let with if then else match handler mask return finally as type'')
    = Some [KLet, KWith, KIf, KThen, KElse, KMatch, KHandler, KMask, KReturn, KFinally, KAs, KType]\<close>
  \<open>toks_of (cp ''extern infixl infixr infix effect module signature instance open include'')
    = Some [KExtern, KInfixl, KInfixr, KInfix, KEffect, KModule, KSignature, KInstance, KOpen,
       KInclude]\<close>
  \<open>toks_of (cp ''in fn handle where literal'') = Some [LId, LId, LId, LId, LId]\<close>
  \<open>toks_of (cp ''lets if' then_'') = Some [LId, LId, LId]\<close>
  \<open>toks_of (cp ''= : -> | '' @ [bslash, sp, 0x2192, sp, 0x3BB])
    = Some [Assign, Colon, Arrow, Bar, KLambda, Arrow, KLambda]\<close>
  \<open>toks_of ([bslash, bslash, sp, bslash] @ cp ''-> <- --> == :: |> ->>'')
    = Some [Op, Op, Op, Op, Op, Op, Op, Op]\<close>
  \<open>toks_of (cp ''( ) [ ] { } , ;'') = Some [LP, RP, LB, RB, LC, RC, Comma, Semi]\<close>
  \<open>toks_of ([0x3BB] @ cp ''x'') = Some [KLambda, LId]\<close>

subsection \<open>Identifiers, the wildcard and backticked names\<close>

lexer_check
  \<open>toks_of (cp ''x x' x_1 M M' M_1 _'') = Some [LId, LId, LId, UId, UId, UId, KWild]\<close>
  \<open>lexs (cp ''f'' @ [cq] @ cp ''a'' @ [cq] @ cp '' x'')
    = [cp ''f'' @ [cq] @ cp ''a'' @ [cq], cp ''x'']\<close>
  \<open>err (cp ''_1'')\<close>
  \<open>err (cp ''_x'')\<close>
  \<open>toks_of (cp ''_ 1'') = Some [KWild, IntL]\<close>
  \<open>toks_of (cp ''x `f` y'') = Some [LId, Op, LId]\<close>
  \<open>err (cp ''`let`'')\<close>
  \<open>err (cp ''`F`'')\<close>
  \<open>err (cp ''`f'')\<close>
  \<open>err (cp ''``'')\<close>

subsection \<open>Selectors\<close>

lexer_check
  \<open>toks_of (cp ''p.1.2'') = Some [LId, TSelN, TSelN]\<close>
  \<open>lexs (cp ''p.1.2'') = [cp ''p'', cp ''.1'', cp ''.2'']\<close>
  \<open>toks_of (cp ''1.2.3'') = Some [FloatL, TSelN]\<close>
  \<open>lexs (cp ''1.2.3'') = [cp ''1.2'', cp ''.3'']\<close>
  \<open>toks_of (cp ''.5'') = Some [LSelN]\<close>
  \<open>toks_of (cp ''x .5'') = Some [LId, LSelN]\<close>
  \<open>toks_of (cp ''M.x M.N.y p.q x .y M .N'')
    = Some [UId, TSelL, UId, TSelU, TSelL, LId, TSelL, LId, LSelL, UId, LSelU]\<close>
  \<open>toks_of (cp ''x{- -}.y x'' @ [nl] @ cp ''.y (x).y'')
    = Some [LId, LSelL, LId, LSelL, LP, LId, RP, TSelL]\<close>
  \<open>err (cp ''x.'')\<close>
  \<open>err (cp ''x . y'')\<close>
  \<open>err (cp ''x.(y)'')\<close>
  \<open>err (cp ''.1x'')\<close>
  \<open>err (cp ''x.let'' @ [sp, dot])\<close>
  \<open>toks_of (cp ''x.let'') = Some [LId, TSelL]\<close>

subsection \<open>Numerals\<close>

lexer_check
  \<open>toks_of (cp ''0 42 1_000 0xFF 0xf_f 0b1010 0b1_0'')
    = Some [IntL, IntL, IntL, IntL, IntL, IntL, IntL]\<close>
  \<open>err (cp ''1_'')\<close>
  \<open>err (cp ''1__0'')\<close>
  \<open>err (cp ''0x_F'')\<close>
  \<open>err (cp ''0x'')\<close>
  \<open>toks_of (cp ''1i8 1i16 1i32 1i64 1u8 1u16 1u32 1u64'')
    = Some [IntL, IntL, IntL, IntL, IntL, IntL, IntL, IntL]\<close>
  \<open>err (cp ''256u8'')\<close>
  \<open>err (cp ''-1u8'')\<close>
  \<open>err (cp ''128i8'')\<close>
  \<open>err (cp ''0xFFi8'')\<close>
  \<open>toks_of (cp ''-0x80i8 -128i8 127i8 255u8 0xFFu8 18446744073709551615u64'')
    = Some [IntL, IntL, IntL, IntL, IntL, IntL]\<close>
  \<open>err (cp ''18446744073709551616u64'')\<close>
  \<open>toks_of (cp ''1.0 1.5e3 1.5E-3 1e3 1e-3 1_0.0_1e1_0'')
    = Some [FloatL, FloatL, FloatL, FloatL, FloatL, FloatL]\<close>
  \<open>err (cp ''1.'')\<close>
  \<open>err (cp ''1.5e'')\<close>
  \<open>err (cp ''1.5u8'')\<close>
  \<open>err (cp ''1e'')\<close>
  \<open>err (cp ''1e+3'')\<close>
  \<open>toks_of (cp ''1.e3'') = Some [IntL, TSelL]\<close>
  \<open>toks_of (cp ''0x1.5'') = Some [IntL, TSelN]\<close>
  \<open>err (cp ''1x'')\<close>
  \<open>err (cp ''1i9'')\<close>
  \<open>err (cp ''0xFFg'')\<close>
  \<open>err (cp ''1.5f'')\<close>

subsection \<open>Negative literals\<close>

lexer_check
  \<open>toks_of (cp ''x-1'') = Some [LId, Op, IntL]\<close>
  \<open>toks_of (cp ''x - 1'') = Some [LId, Op, IntL]\<close>
  \<open>toks_of (cp ''f -1'') = Some [LId, IntL]\<close>
  \<open>toks_of (cp ''(-1)'') = Some [LP, IntL, RP]\<close>
  \<open>toks_of (cp ''(- 1)'') = Some [LP, Op, IntL, RP]\<close>
  \<open>toks_of (cp ''-1'') = Some [IntL]\<close>
  \<open>toks_of (cp ''-1.5'') = Some [FloatL]\<close>
  \<open>toks_of (cp ''x = -1'') = Some [LId, Assign, IntL]\<close>
  \<open>lexs (cp ''f -1'') = [cp ''f'', cp ''-1'']\<close>
  \<open>lexs (cp ''x-1'') = [cp ''x'', cp ''-'', cp ''1'']\<close>
  \<open>toks_of (cp ''1-1 x.y-1 (x)-1 [x]-1 {x}-1 _-1'')
    = Some [IntL, Op, IntL, LId, TSelL, Op, IntL, LP, LId, RP, Op, IntL, LB, LId, RB, Op, IntL, LC,
       LId, RC, Op, IntL, KWild, Op, IntL]\<close>
  \<open>err (cp ''- 1u8'' @ [sp] @ cp ''-1u8'')\<close>
  \<open>toks_of (cp ''- 1u8'') = Some [Op, IntL]\<close>

subsection \<open>Comments\<close>

lexer_check
  \<open>toks_of (cp ''x --> y'') = Some [LId, Op, LId]\<close>
  \<open>toks_of (cp ''x -- y'') = Some [LId]\<close>
  \<open>toks_of (cp ''x --- y'' @ [nl] @ cp ''z'') = Some [LId, LId]\<close>
  \<open>toks_of (cp ''x --| y'') = Some [LId, Op, LId]\<close>
  \<open>toks_of (cp ''x {- {- -} -} y'') = Some [LId, LId]\<close>
  \<open>err (cp ''x {- {- -} y'')\<close>
  \<open>toks_of (cp ''x {--} y'') = Some [LId, LId]\<close>

text \<open>A comment is trivia of the token before it, read in pieces (caraml reads one
  trivium per comment):\<close>

lexer_check
  \<open>map trivia (toks (fst (caraml_lex (cp ''x {- {- -} -} y -- z''))))
    = [cp '' {- {- -} -} '', cp '' -- z'']\<close>

subsection \<open>Bidirectional controls\<close>

lexer_check
  \<open>err (cp ''x -- '' @ [lrm])\<close>
  \<open>err (cp ''x {- '' @ [lrm] @ cp '' -} y'')\<close>
  \<open>err ([qt] @ cp ''a'' @ [lrm] @ cp ''b'' @ [qt])\<close>
  \<open>err ([cq, lrm, cq])\<close>
  \<open>err (cp ''x '' @ [0x2066] @ cp '' y'')\<close>
  \<open>toks_of ([qt, bslash] @ cp ''u{202E}'' @ [qt]) = Some [StrL]\<close>

subsection \<open>Strings and characters\<close>

lexer_check
  \<open>toks_of ([qt, bslash] @ cp ''$'' @ [qt]) = Some [StrL]\<close>
  \<open>toks_of ([qt] @ cp ''$x $'' @ [qt]) = Some [StrL]\<close>
  \<open>toks_of ([qt] @ cp ''a'' @ [bslash] @ cp ''tb'' @ [bslash] @ cp ''nc'' @ [bslash]
      @ cp ''rd'' @ [bslash] @ cp ''0'' @ [bslash, qt, bslash, cq, bslash, bslash, qt])
    = Some [StrL]\<close>
  \<open>toks_of ([qt, bslash] @ cp ''u{41}'' @ [bslash] @ cp ''u{1F642}'' @ [qt]) = Some [StrL]\<close>
  \<open>toks_of [qt, qt] = Some [StrL]\<close>
  \<open>err ([qt, bslash] @ cp ''q'' @ [qt])\<close>
  \<open>err ([qt, bslash] @ cp ''u{110000}'' @ [qt])\<close>
  \<open>err ([qt, bslash] @ cp ''u{}'' @ [qt])\<close>
  \<open>err ([qt, bslash] @ cp ''u{1234567}'' @ [qt])\<close>
  \<open>err ([qt, bslash] @ cp ''u{D800}'' @ [qt])\<close>
  \<open>err ([qt] @ cp ''a'')\<close>
  \<open>err ([qt] @ cp ''a'' @ [nl] @ cp ''b'' @ [qt])\<close>
  \<open>toks_of (cp ''x '' @ [qt] @ cp ''ab'' @ [qt] @ cp ''y'') = Some [LId, StrL, LId]\<close>
  \<open>toks_of ([cq, 0x61, cq, sp, cq, bslash] @ cp ''n'' @ [cq, sp, cq, bslash] @ cp ''u{1F642}''
      @ [cq, sp, cq, bslash, cq, cq])
    = Some [CharL, CharL, CharL, CharL]\<close>
  \<open>err ([cq, bslash] @ cp ''u{110000}'' @ [cq])\<close>
  \<open>err [cq, cq]\<close>
  \<open>err ([cq] @ cp ''ab'' @ [cq])\<close>
  \<open>err [cq, 0x61]\<close>
  \<open>err [cq, nl, cq]\<close>

subsection \<open>Interpolation\<close>

text \<open>These depart from caraml, whose \<open>StrI\<close> is one token and whose holes hold value
  paths only (see \<open>CaraML_Lexer\<close>). A hole holds any tokens:\<close>

lexer_check
  \<open>toks_of ([qt] @ cp ''a${M.x}b'' @ [qt]) = Some [StrStart, UId, TSelL, StrEnd]\<close>
  \<open>toks_of ([qt] @ cp ''${A.B.c}${d}'' @ [qt])
    = Some [StrStart, UId, TSelU, TSelL, StrMid, LId, StrEnd]\<close>
  \<open>toks_of (cp ''"foo: ${foo} bar: ${bar}"'') = Some [StrStart, LId, StrMid, LId, StrEnd]\<close>
  \<open>toks_of (cp ''"foo: ${foo} bar: ${bar+1}"'')
    = Some [StrStart, LId, StrMid, LId, Op, IntL, StrEnd]\<close>
  \<open>lexs (cp ''"a${x}b${y}c"'') = [cp ''"a${'', cp ''x'', cp ''}b${'', cp ''y'', cp ''}c"'']\<close>
  \<open>toks_of (cp ''"${f x}"'') = Some [StrStart, LId, LId, StrEnd]\<close>
  \<open>toks_of (cp ''"${x.y}"'') = Some [StrStart, LId, TSelL, StrEnd]\<close>
  \<open>toks_of (cp ''"${M}"'') = Some [StrStart, UId, StrEnd]\<close>
  \<open>toks_of (cp ''"$${x}$"'') = Some [StrStart, LId, StrEnd]\<close>
  \<open>toks_of ([qt, bslash] @ cp ''${x}"'') = Some [StrL]\<close>

text \<open>Braces, strings and comments nest in a hole, and the kinds work as outside:\<close>

lexer_check
  \<open>toks_of (cp ''"${ {a} }"'') = Some [StrStart, LC, LId, RC, StrEnd]\<close>
  \<open>toks_of (cp ''"${ {"}"} }"'') = Some [StrStart, LC, StrL, RC, StrEnd]\<close>
  \<open>toks_of (cp ''"a${ "b${c}d" }e"'') = Some [StrStart, StrStart, LId, StrEnd, StrEnd]\<close>
  \<open>toks_of (cp ''"${ {- } -} x }"'') = Some [StrStart, LId, StrEnd]\<close>
  \<open>toks_of (cp ''{ "${x}" }'') = Some [LC, StrStart, LId, StrEnd, RC]\<close>
  \<open>toks_of (cp ''"${-1}" "${x-1}" "${x}"-1'')
    = Some [StrStart, IntL, StrEnd, StrStart, LId, Op, IntL, StrEnd, StrStart, LId, StrEnd, Op,
       IntL]\<close>

text \<open>An empty hole, a hole or string left open, and a \<open>}\<close> that closes a hole without a
  string piece after it are errors. So is a \<open>}\<close> at the top level, whose pop empties the
  stack (see the header of this section):\<close>

lexer_check
  \<open>err (cp ''} x'')\<close>
  \<open>err (cp ''"${}"'')\<close>
  \<open>err (cp ''"${ }"'')\<close>
  \<open>err (cp ''"${ {- c -} }"'')\<close>
  \<open>err (cp ''"a${x}${}"'')\<close>
  \<open>err ([qt] @ cp ''${x'' @ [qt])\<close>
  \<open>err (cp ''"${x'')\<close>
  \<open>err (cp ''"${x}'')\<close>
  \<open>err (cp ''"${x}b'')\<close>
  \<open>err (cp ''"${ {x"'')\<close>
  \<open>err (cp ''"${ {x}"'')\<close>
  \<open>err (cp ''"${bar+1'')\<close>

text \<open>Escapes at the edges of the scalar values, which caraml's tests do not cover:\<close>

lexer_check
  \<open>toks_of ([qt, bslash] @ cp ''u{D7FF}'' @ [bslash] @ cp ''u{E000}'' @ [bslash]
      @ cp ''u{0D800}'' @ [bslash] @ cp ''u{10FFFF}'' @ [bslash] @ cp ''u{000041}'' @ [qt])
    = None\<close>
  \<open>toks_of ([qt, bslash] @ cp ''u{D7FF}'' @ [bslash] @ cp ''u{E000}'' @ [bslash]
      @ cp ''u{10FFFF}'' @ [bslash] @ cp ''u{000041}'' @ [bslash] @ cp ''u{d80}'' @ [qt])
    = Some [StrL]\<close>
  \<open>err ([qt, bslash] @ cp ''u{00dfff}'' @ [qt])\<close>
  \<open>err ([qt, bslash] @ cp ''u{110000}'' @ [qt])\<close>
  \<open>err ([qt, bslash] @ cp ''u{200000}'' @ [qt])\<close>

subsection \<open>A small program and positions\<close>

lexer_check
  \<open>toks_of (cp ''module M = {'' @ [nl] @ cp ''  let f = '' @ [bslash] @ cp ''x -> x.1 + -1''
      @ [nl] @ cp ''}'')
    = Some [KModule, UId, Assign, LC, KLet, LId, Assign, KLambda, LId, Arrow, LId, TSelN, Op, IntL,
       RC]\<close>
  \<open>map (\<lambda>t. (s_line (span t), s_col (span t), s_off (span t)))
      (toks (fst (caraml_lex (cp ''ab'' @ [nl] @ cp '' c''))))
    = [(0, 0, 0), (1, 1, 4)]\<close>

text \<open>caraml counts a carriage return before a line feed as one line end and gets

lexer_check
  \<open>[(0, 0, 0), (1, 0, 3), (2, 0, 5), (4, 0, 8), (5, 0, 16)]\<close> here.
  \<^const>\<open>advance\<close> reads one character at a time, so a CRLF counts twice:\<close>

lexer_check
  \<open>map (\<lambda>t. (s_line (span t), s_col (span t), s_off (span t)))
      (toks (fst (caraml_lex (cp ''a'' @ [0x0D, nl] @ cp ''b'' @ [0x0D] @ cp ''c'' @ [nl, nl]
        @ cp ''d -- e'' @ [0x0D, nl] @ cp ''f''))))
    = [(0, 0, 0), (2, 0, 3), (3, 0, 5), (5, 0, 8), (7, 0, 16)]\<close>
  \<open>err (cp ''x'' @ [0x09] @ cp ''y'')\<close>
  \<open>err [0x09]\<close>
  \<open>toks_of ([qt] @ cp ''a'' @ [0x09] @ cp ''b'' @ [qt]) = Some [StrL]\<close>
  \<open>toks_of (cp ''x -- a'' @ [0x09] @ cp ''b'') = Some [LId]\<close>
  \<open>toks_of (cp ''x {-'' @ [0x09] @ cp ''-}'') = Some [LId]\<close>

end
