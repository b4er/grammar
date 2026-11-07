# Benchmarks

Each directory compares a parser emitted by `parser` with an established parser for
the same language, on the same inputs. They check that both build the same tree, then
time one parse.

| bench | language | compared with | Isabelle session | inputs |
|---|---|---|---|---|
| `ocaml` | an OCaml subset | Menhir, and OCaml's own parser for `check` | `OCaml_Bench` | `input/*.ml` |
| `ocaml-prec` | the same, written with `precedence` declarations | the same | `OCaml_Prec` | those of `ocaml` |
| `verimon` | VeriMon/MonPoly formulas | ocamlyacc | `VeriMon_Bench` | `input/*.mfotl` |
| `verimon-prec` | the same, written with `precedence` declarations | the same | `VeriMon_Prec` | those of `verimon` |
| `purecake` | PureCake (a Haskell subset), on PureCake's tokens | the PEG parser of PureCake, native and on Poly/ML | `PureCake_Bench` | `input/*.hs` |

The `-prec` twins share `src`, `input` and `vendor` with their base by symlink and its
`Makefile` by `include`; only the grammar theory in `thys/` differs. They show what
declared precedence costs against a hand-levelled grammar. `common/` holds what all five
share: the make targets `bench` and `ci` (`bench.mk`), the measurement (`measure.sh`),
the table (`table.awk`) and the report against a baseline (`report.py`).

## Running

Each `thys/` is a session on top of `LR_Parser`, listed in `../ROOTS`. Its theory exports
the parser's code to `<bench>/isabelle/`. With the repository root as working directory:

```shell
isabelle build -d . -d <afp>/thys -e OCaml_Bench          # or: make -C bench/ocaml export
make -C bench/ocaml check                                  # the parsers agree on every input
make -C bench/ocaml bench                                  # out/results.tsv, printed as a table
make -C bench/ocaml ci                                     # check, then bench with instruction counts
```

`REPS` (parses per run, default 20), `RUNS` (runs, the median is taken, default 5) and
`IR=1` (instruction counts under callgrind) are passed on to `measure.sh`. One row of
`out/results.tsv` is `CASE PARSER METRIC VALUE`, the metrics are `tokens`, `ms` (per
parse, start-up and lexing subtracted) and `instructions`.

What each needs is in its `bench.json` (`apt` packages, `opam` packages) and at the top of
its `Makefile`: OCaml with `ocamlfind`, Zarith and, for `ocaml`, Menhir; for `purecake`,
gcc and Poly/ML's `polyc`. `purecake` builds with the distribution's Poly/ML, whose `int`
is fixed-width, unlike Isabelle's; `src/iarray_intinf.sml` bridges that, and
`nix-shell -p polyml gcc --run 'make check'` reproduces CI locally. The PEG side of
`purecake` is vendored in `vendor/`; how it was produced from PureCake's HOL4 sources is
not part of this repository.

Do not time while another Isabelle process runs, and compare instruction counts rather
than milliseconds across machines. A single large jump in instructions of the Poly/ML
parsers can be a different garbage-collection schedule rather than a change of code.

## Where the numbers are

- Locally: `<bench>/out/results.tsv`, not tracked.
- CI (`.github/workflows/ci.yaml`): every `bench/*/bench.json` is measured with `make ci`.
  The results are the artifacts `bench-<name>`. On a pull request, `common/report.py`
  compares them with the last successful run on the base branch and posts the table as a
  comment, which is replaced on each push. The same table is in the run's summary.
