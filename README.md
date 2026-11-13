# TIGER: Tokenization, Indentation-sensitive Grammars & Executable Recognizers

Definitional packages for lexers and for indentation-sensitive context-free
grammars in Isabelle/HOL. The grammars follow Adams,
*Principled Parsing for Indentation-Sensitive Languages* (POPL 2013).

## Documentation

The documentation a single manual for both lexer and grammar/parser commands,
[`output/document.pdf`](output/document.pdf), built by the session `TIGER`:

```shell
isabelle build -o document=pdf -d . TIGER
```

## Sessions

The sessions are defined in `ROOT`. Lexer and parser generator share only
`TIGER_Token`; neither imports the other, and `TIGER` imports both.

```
TIGER_Token ─┬─ TIGER_Grammar_Model ── TIGER_Grammar ─┬─ TIGER
             └─ TIGER_Lexer ──────────────────────────┘
```

| session | directory | contents |
|---|---|---|
| `TIGER_Token` | `token/` | source spans and the token record |
| `TIGER_Grammar_Model` | `grammar/model/` | the model `Indentation_Sensitive.thy`, `Grammar_Base.thy` |
| `TIGER_Grammar` | `grammar/`, `grammar/lr/` | the LR tables, drivers and static condition (`lr/`, proofs only); the `grammar` and `parser` commands, their ML, the backend |
| `TIGER_Grammar_Tests` | `grammar/tests/` | one theory per feature, a few minutes in batch |
| `TIGER_Grammar_Tests_Slow` | `grammar/tests/slow/` | recovery and repair (`Recover_Tests`, `Repair_Tests`, `Repair_Code_Tests`) |
| `TIGER_Lexer` | `lexer/`, `lexer/core/` | regexes, the lexer spec, the table generator and the runner (`core/`); the `pattern`, `lexer` and `lexer_check` commands; see `lexer/README.md` |
| `TIGER_Lexer_Tests` | `lexer/tests/` | the lexer's tests |
| `TIGER` | `.` | the manual, `TIGER.thy`, on both packages |

The tests are split by cost: the parsers with recovery and repair are in
`TIGER_Grammar_Tests_Slow`, which runs once per change of the error path. `TIGER_Grammar_Tests`
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
isabelle build -d . TIGER_Grammar_Tests         # the fast tests
isabelle build -d . TIGER_Grammar_Tests_Slow    # and the slow ones
isabelle build -d . TIGER_Lexer_Tests           # the lexer's tests
```

`ROOTS` lists the benchmark sessions in `bench/*/thys`; see `bench/README.md`.

Built with Isabelle2026; depends on the AFP entries `Context_Free_Grammar` and `Regular-Sets`
(tested with afp-2026-11-06).

## Use of AI

Claude was used to write initial theories, refactor proofs/ML code under the
author's direction.
