# TIGER: Tokenization, Indentation-sensitive Grammars & Executable Recognizers

Definitional packages for lexers and for indentation-sensitive context-free
grammars in Isabelle/HOL. The grammars follow Adams,
*Principled Parsing for Indentation-Sensitive Languages* (POPL 2013).

## Surface

- `grammar G = tokens … terminals … productions …` checks a grammar specification
  with semantic actions. Symbols carry layout annotations (`⇧=`, `⇧≥`, `⇧>`).
  `precedence` and `forbid` lines declare operator precedence.
- A grammar may use a nonterminal `a.X` of an earlier grammar `a`. The productions
  of `a` that `X` reaches are copied in, so every grammar stays closed.
  `grammar b = open a …` lets `b` write `X` for `a.X`.
- Templates `P(X, …) = …` are parametric nonterminals. They are instantiated per use
  as `P(a, …)`. The postfix operators `* + ?` over symbols and groups give lists and
  options. `Grammar_Prelude` provides `List`, `List1`, `Opt`, `Sep` and `Sep1`.
- `@span` in an alternative passes its action the span of the alternative's yield, from
  the first token to the last (`word_span`), in the place where it is written among the
  value symbols. It is not a grammar symbol.
- `parser p for G` emits an executable LALR(1)-style parser.
  `parser p for G and q for G (A)` emits several parsers for one grammar, each from
  its own start symbol, sharing the grammar's decoders and relation.
- `parser (ast) p for G` returns the tree of the word and evaluates no action, for an
  outline in an editor or a grammar whose actions are not written yet.

## What is defined

- `lexer` defines a lexing judgement in the style of flex: regular expressions,
  longest match, and a stack of modes.
- `grammar` defines a grammar constant `G` and one decoder per nonterminal.
- `grammar (relation)` also defines an inductive relation between words and values.
- `parser` defines the parser `p`. For a grammar with precedence declarations it also
  defines the restricted grammar `p_gram` that the parser is built from.

## Theorems

The lexer is specified by a judgement (maximal prefix and first match) under a
stack of modes:

- FIXME

For grammars and parsers:

- `p.sound` and `p.complete` relate `p` to the language of `G`, or to the relation of
  the start symbol under `(relation)`.
- Under `(ast)`, `p.sound` and `p.complete` speak of the parse trees of `G`: the tree
  `p` returns is the erasure of a parse tree of the word, and every parse tree of the
  word erases to it.
- Completeness needs the static determinism check. If the check fails, `mdet` stays
  a premise of `p.complete`.
- A composed grammar has link theorems `b.a_X_iff` back to the relation of `a`.

## Diagnostics

A rejected word is not a dead end. Unless `parser (no_diagnostics)` is given, each
`parser` also defines `p_diag`, which locates the error in the input.

- `errors` attaches hand-written messages by example.
- `parser_error_states` and `[[parser_errors_budget]]` check that the messages cover
  the error states.
- `recover` and `repair` still give a tree from broken input.
- Messages name nonterminals as the grammar writes them, without the grammar's
  qualifier; a generated list or option (`Decl+`, `Sep1(Decl, ;)`) shows as its
  element, a group as its first symbol.

Only accepted trees carry theorems. The error path is unverified, and it cannot change
what `p` accepts.

## Backend

The tables are constants of their own, computed once when the code is loaded. A
grammar without layout annotations and without conflicts runs on the simple driver;
the others run on the state-indexed driver. The documentation describes the drivers
and the options for exported code (`parser_literal_tables`, `parser_int_tables`).

## Documentation

The documentation is the generated PDF, `output/document.pdf`:

```shell
isabelle build -o document=pdf -d . TIGER_LR
```

## Sessions

The sessions are defined in `ROOT`, and each depends on the one before it:

| session | directory | contents |
|---|---|---|
| `TIGER_Token` | `token/` | source spans and the token record |
| `TIGER_Grammar` | `grammar/model/` | the model `Indentation_Sensitive.thy`, `Grammar_Base.thy` |
| `TIGER_LR` | `grammar/`, `grammar/lr/` | the LR tables, drivers and static condition (`lr/`, proofs only); the `grammar` and `parser` commands, their ML, the backend, the document |
| `TIGER_Tests` | `grammar/tests/` | one theory per feature, a few minutes in batch |
| `TIGER_Tests_Slow` | `grammar/tests/slow/` | recovery and repair (`Recover_Tests`, `Repair_Tests`, `Repair_Code_Tests`) |

The tests are split by cost: the parsers with recovery and repair are in
`TIGER_Tests_Slow`, which runs once per change of the error path. `TIGER_Tests`
is the gate for every edit of the commands:

- `Regression_Tests`, `Diag_Tests`, `Reach_Tests`: the commands, the diagnostics and
  their coverage.
- `Prec_Tests`, `Prec_Surface_Tests`: precedence.
- `Compose_Tests`, `Param_Tests`: composition and templates.
- `Span_Tests`: `@span`.
- `Ast_Tests`: `parser (ast)`.
- `Same_Terms`: the facts emitted for a few grammars of `Regression_Tests` and
  `Prec_Surface_Tests`, as hashes of their terms, against `grammar/tests/same_terms.txt`.

A test evaluates its words with `parser_check ‹t›` (`grammar/tests/Parser_Check.thy`), not
`lemma ‹t› by eval`: the command proves nothing, compiles the code of a constant once
per theory chain instead of once per check, and on a failed equation shows the
value of its left-hand side. `by eval` remains where a test needs the theorem.

```shell
isabelle build -d . TIGER_Tests         # the fast tests
isabelle build -d . TIGER_Tests_Slow    # and the slow ones
```

`ROOTS` lists the benchmark sessions in `bench/*/thys`; see `bench/README.md`.

Built with Isabelle2026; depends on the AFP entry `Context_Free_Grammar` (tested with afp-2026-11-06).
