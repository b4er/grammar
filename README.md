# The `grammar` and `parser` commands

A definitional package for indentation-sensitive context-free grammars in
Isabelle/HOL, after Adams, *Principled Parsing for Indentation-Sensitive
Languages* (POPL 2013):

- `grammar` elaborates a grammar specification with semantic actions into
  a grammar constant, per-nonterminal decoders and an inductive relation
- `parser` emits an executable LALR(1)-style parser for it, proving soundness
  and completeness

The documentation is the generated PDF, `output/document.pdf`:

```shell
    isabelle build -o document=pdf -d . Grammar_Command
```

Sessions defined in `ROOT`:
- `Grammar_Command` (the model `Indentation_Sensitive.thy` and the commands)
- `LR_Parser` in `lr/` (the LR tables, driver, static condition and backend)
- `Grammar_Tests` in `tests/` (some examples and tests).

Depends on the AFP entry `Context_Free_Grammar`.
