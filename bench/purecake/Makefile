# needs gcc and Poly/ML's polyc
#
#   make export     re-export isabelle/pure_bench.ML from thys/Pure_Bench.thy
#   make            build the three parsers and the token dumps in _build
#   make check      the three print the same AST for every input/*.hs
#   make bench      per-parse wall-clock -> out/results.tsv
#   make ci         check, then bench with instruction counts (needs valgrind)

B := _build
CC ?= gcc
POLYC ?= polyc

NAMES := $(notdir $(basename $(wildcard input/*.hs)))
PARSERS := peg-native peg-poly isabelle

all: $(addprefix $(B)/,$(PARSERS)) $(NAMES:%=$(B)/tok/%.tok)

export:
	isabelle build -d ../.. -e PureCake_Bench

$(B)/peg-native: vendor/purebench.S vendor/basis_ffi.c
	@mkdir -p $(B)
	$(CC) -O2 -o $@ $^

$(B)/peg-poly: vendor/purebench_poly.sml
	@mkdir -p $(B)
	$(POLYC) -o $@ $<

# the exported code is not ours: its non-exhaustive matches warn, shown only on failure
$(B)/isabelle: src/iarray_intinf.sml isabelle/pure_bench.ML src/pure_bench_main.sml
	@mkdir -p $(B)
	cat $^ > $(B)/isabelle.sml
	$(POLYC) -o $@ $(B)/isabelle.sml > $(B)/isabelle.log 2>&1 || { cat $(B)/isabelle.log; exit 1; }

$(B)/tok/%.tok: input/%.hs $(B)/peg-native
	@mkdir -p $(B)/tok
	$(B)/peg-native tokens $< > $@

# an input every parser accepts, with the same AST
check: all
	@for n in $(NAMES); do \
	  $(B)/peg-native ast input/$$n.hs > $(B)/$$n.peg-native; \
	  $(B)/peg-poly ast input/$$n.hs > $(B)/$$n.peg-poly; \
	  $(B)/isabelle ast $(B)/tok/$$n.tok > $(B)/$$n.isabelle; \
	  grep -q '^(decls' $(B)/$$n.peg-native || { echo "$$n: no AST"; exit 1; }; \
	  for p in peg-poly isabelle; do \
	    cmp -s $(B)/$$n.peg-native $(B)/$$n.$$p || { echo "$$n: $$p differs from peg-native"; exit 1; }; \
	  done; \
	done; echo "check: $(words $(NAMES)) inputs, the parsers agree"

# one GC thread (the parallel GC's spinning varies) and an initial heap no parse
# here fills: a collection inside the one measured parse would count in full, and
# how many land there varies between runs (peg-poly prelude-lists: 28M without
# any, 39M or 56M with), so the instruction counts exclude GC
POLYRTS := --gcthreads 1 -H 512

ROWS = for n in $(NAMES); do \
    export TOKENS=$$(wc -l < $(B)/tok/$$n.tok); \
    $(MEASURE) $$n peg-native $(B)/peg-native parse input/$$n.hs; \
    $(MEASURE) $$n peg-poly $(B)/peg-poly $(POLYRTS) parse input/$$n.hs; \
    $(MEASURE) $$n isabelle $(B)/isabelle $(POLYRTS) parse $(B)/tok/$$n.tok; \
  done

clean:
	rm -rf $(B) out

.PHONY: export clean
include ../common/bench.mk
