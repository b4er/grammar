# Lexer

A verified flex-style lexer generator for Isabelle/HOL. A spec gives each mode a
prioritized list of longest-match rules over symbolic regexes, and actions change a
stack of modes. The generator will produce an executable lexer from precomputed DFA
tables, with soundness, completeness and termination against an inductive spec.

## Sessions

`Token` (`token/`) holds spans, positions and the token record. It depends on `HOL`
only (parsers and tooling can import it alone).

`Lexer` holds the symbolic regexes and their derivatives (`Regex`), the inductive spec
(`Spec`), the table generator (`Gen`) and the runner (`Lexer`). It depends on `Token`
and the AFP entry `Regular-Sets`.

`Lexer_Command` (`command/`) holds the front end of the lexer commands on top of
`Lexer`: the pattern sublanguage (`Pattern`), its diagnostic command `pattern` and the
term syntax `PAT‹…›`.

`Lexer_Tests` (`tests/`) holds the tests of both. It builds on `Lexer_Command` and
imports the CaraML prototype (`CaraML_Lexer`) to check that the patterns elaborate to
the prototype's classes and regexes.

## Milestones

1. Symbolic regexes, derivatives, finiteness, the spec judgments, determinism and
   totality of the driver. Done.
2. DFA generation and runner correctness, tables by `eval` on test specs. Done.
3. Modes and locations end to end, and the instance for the consumers.
4. Linearity.
5. The definitional command.

## Decisions

Questions `papers/MAP.md` does not settle, with the answer taken.

- **Atom type (MAP §8 Q1), 2026-11-07.** Atoms are a syntactic predicate type `'p`
  with a denotation `sem :: 'p ⇒ 'ch ⇒ bool`. A regex is the `Regular-Sets` datatype
  `'p rexp` itself, with `Pred` an abbreviation for `Atom` (its `nullable`, `atoms` and
  partial derivatives then apply unchanged). `sem` is the parameter of the locale
  `symbolic`, in whose context `Regex` and `Spec` define the language, the derivatives
  and the judgments (globally they take `sem` as first argument). A rule's `match` has
  type `'p rexp`. The generator needs an effective Boolean algebra on `'p` (dv14 §2):
  equality, conjunction, disjunction, negation and a satisfiability test, all sound for
  `sem`. The first instance is character classes as sorted interval lists over a
  linorder `'ch`. Functions as atoms are out (they have neither equality nor a
  satisfiability test).
- **Interval representation (prompt 02), 2026-11-07.** A character class is a sorted
  list of closed intervals over a bounded discrete order. The bottom, top, successor
  and predecessor are locale parameters, not a type class (the concrete alphabets,
  bytes and codepoints, are bounded and discrete). Closed intervals over an arbitrary
  linorder are out (the complement of `[a, b]` is two open intervals). Boundary lists
  of half-open intervals are out (a one-character class needs a successor anyway).
  The axioms of `discrete_order` speak only about the range from bottom to top, and
  `bounded_discrete_order` adds that the range is the whole type (`nat` below a bound
  is then an instance, and the Boolean algebra laws hold in the bounded locale only).
- **Token interface (MAP §8 Q5), 2026-11-08.** The session `Token` (`token/`, on
  `HOL` only) is the one token interface. It holds what `Grammar_Model.Token` holds
  (`span`, `token`, `tcols`, `col_of`, field names unchanged) and the lexer's
  additions (`pos`, `advance`, `span_at`, `lex_token`, `lexed`). The grammar repo is
  to drop its own `Token.thy` and import this session, so a client of the LR parser
  uses the same token record without importing the lexer. No adapter. Two theories
  named `Token` cannot be imported together, so until grammar switches, a theory
  cannot import both `Lexer` and `Grammar_Model`. Grammar's switch is a change made in
  that repo (a `ROOTS`/`-d` entry for `token/`, `imports Token.Token`). caraml's
  `Lexing.thy` changes only its import.
- **CaraML prototype (prompt 03), 2026-11-08.** `tests/CaraML_Spec.thy` writes
  caraml's token relation and trivia as a spec over codepoints and lexes caraml's
  `Lexer_Test` snippets with caraml's results (the expected values are copied: the
  two `Token` theories keep both lexers out of one theory). No rule needs trailing
  context (`r/s`), and `Spec.thy` is unchanged.
  - *Direct* (longest match and priority): identifiers and reserved symbols as one
    rule each with the keyword/symbol lookup in the action, delimiters, `{-` against
    `{`, selectors, backticked names, strings (`$` not before `{`
    is inside the regex), characters, escapes with the scalar-value range (a regex by
    digit count), whitespace, line comments against longer operators (comment rule
    first: `--` is a comment, `-->` an operator by length), bidirectional controls
    (no rule reads them).
  - *Error rules*: a numeral, selector numeral or `_` followed by an identifier
    character. For a token form `R` and caraml's `¬ starts P tail`, a rejecting rule
    `R P⁺` after the token rule gives the same result (argument in the theory).
  - *Actions*: suffixed integer ranges, backticked keywords.
    A rejecting action returns the empty stack, which stops the driver.
  - *Modes*: the state rules (negative literal unless directly after an operand,
    tight selectors) as three token modes (`spaced`, `after_op`, `after_nonop`),
    nested block comments as a `comment` mode with one stack entry per open `{-`.
  - *Does not fit*: CRLF is two line ends for `Token.advance`, and trivia are kept
    as text, not as caraml's classified, spanned list. The end of input, at first
    a sentinel `U+D800`, is settled below.
  - *Cost*: 82 class-table intervals, 44 minterms and 98 states for each token mode,
    11, 5 and 7 for `comment`; about 5 s per token mode to generate, 2.5 s for
    `comment`. Each `by eval` on the lexer takes about 3 s alone, nearly all of it
    generating and compiling the code of the table constants, so the tests group
    their checks. The generator (`explore`) is not the bottleneck at this size.
- **Interpolation by modes, 2026-11-08.** `tests/CaraML_Spec.thy` departs from caraml's
  `StrI` (one token, holes hold value paths only). A hole `${…}` holds any tokens. A
  string with holes lexes as `StrStart` (`"…${`), `StrMid` (`}…${`) and `StrEnd`
  (`}…"`) with the hole's tokens between them, as in Swift, Kotlin and Scala lexers. The
  token modes get a context (outer, hole, fresh hole), `{` pushes and `}` pops, so
  braces, strings and comments nest in a hole. An empty hole, a `}` in a hole without a
  string piece after it, and the end of the input inside a hole are errors. Cost: two
  more token tables of 124 states.
- **End of input (MAP §8 Q6), 2026-11-09.** `lexes` has a last argument, the final
  stack (`lexes sp nl st q s l r st'`), and the drivers (`drive`, `run_lexer`,
  `char_lexer`, `cp_lexer`) return the triple `(l, r, st')`. `lexes_stop` reports the
  stack it stops in, and no other judgment changes. An unterminated comment or hole
  then ends with an empty residue in a comment or hole mode, which is the consumer's
  error (a top that is not a final mode), so the input needs no sentinel. The
  `lexer` command is to declare the final modes. flex's per-mode `<<EOF>>` actions
  (flex §12) are out: no consumer needs a token at the end, and a post-pass on the
  final stack can add one later.
- **The generated lexer and the byte instance (prompt 08), 2026-11-09.** `cp_lexer` and
  `char_lexer` take a mode index `ix :: 'm ⇒ nat` into the table array, and their
  theorems assume that each mode finds its tables there. The `lexer` command
  builds the lexer `L_lex` along with the spec (`lexer (sketch)` stops after the spec),
  and gives modes with the same rule list (`aconv`) one index, and the old `nat` form is
  the instance `ix = id` with `list_spec`. `lexer (char)` lexes bytes with
  `char_spec L.spec`, which reads each codepoint class on bytes as its part below
  `0x100`, and `L_lex.correct` is stated against that spec. A class that reaches above
  `0xFF` is an error, except one that reaches `0x10FFFF`: the elaboration turns `_`
  and `[^…]` into such complements, and on bytes they mean the remaining bytes.
  Relating the byte lexer to `L.spec` on codepoints is the theorem of the `utf8`
  instance (design §9), not done. caraml: no two token modes share a table, so ten
  tables of up to 216 states, about 90 s to generate and about 40 s for an `eval`
  of `caraml_lex` (compiling the literals).
