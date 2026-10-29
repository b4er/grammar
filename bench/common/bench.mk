#   all     builds every parser of the bench
#   check   checks that the parsers agree on every input
#   ROWS    a shell command measuring every parser on every input, printing
#           TSV rows CASE PARSER METRIC VALUE (usually via $(MEASURE))
#
# and gets
#
#   make bench    out/results.tsv, printed as a table
#   make ci       check, then bench with instruction counts (needs valgrind)
#
# REPS, RUNS and IR are passed on to measure.sh.

COMMON := $(dir $(lastword $(MAKEFILE_LIST)))
MEASURE := $(COMMON)measure.sh

REPS ?= 20
RUNS ?= 5
IR ?= 0

.PHONY: all check bench ci

bench: all
	mkdir -p out
	export REPS=$(REPS) RUNS=$(RUNS) IR=$(IR); { $(ROWS); } > out/results.tsv
	awk -f $(COMMON)table.awk out/results.tsv

ci: check
	$(MAKE) bench IR=1
