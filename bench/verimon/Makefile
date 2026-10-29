# needs OCaml with ocamlfind and Zarith
#
#   make export     re-export isabelle/verimon_parser.ocaml from thys/VeriMon_Parser.thy
#   make            build _build/verimon
#   make check      both parsers agree on every input/*.mfotl (a formula, or both reject)
#   make bench      per-parse wall-clock -> out/results.tsv
#   make ci         check, then bench with instruction counts (needs valgrind)

B := _build
OCAMLFIND ?= ocamlfind
OCAMLOPTFLAGS ?= -g

NAMES := $(notdir $(basename $(wildcard input/*.mfotl)))
PARSERS := ocamlyacc isabelle

# dependency order
MODS := misc predicate MFOTL formula_parser formula_lexer show verimon_tabs verimon_parser isa main

all: $(B)/verimon

export:
	isabelle build -d ../.. -e VeriMon_Bench

$(B):
	mkdir -p $@

$(B)/%.ml: src/%.ml | $(B)
	cp $< $@

$(B)/formula_parser.ml: vendor/formula_parser.mly | $(B)
	cp $< $(B)/formula_parser.mly
	ocamlyacc $(B)/formula_parser.mly

$(B)/formula_lexer.ml: vendor/formula_lexer.mll | $(B)
	ocamllex -q -o $@ $<

# The exported module computes its tables when it is loaded, ~20 s in OCaml
# (Poly/ML does this at compile time).  As Poly/ML would, they are computed
# once here: mktabs (the export with its signature opened) marshals them into
# verimon_tabs.ml, and verimon_parser.ml is the export with the tables'
# definitions replaced by that value.
$(B)/vp_open.ml: isabelle/verimon_parser.ocaml | $(B)
	awk '/^module VeriMon_Parser : sig/ { skip = 1 } \
	     skip && /^end = struct/ { print "module VeriMon_Parser = struct"; skip = 0; next } !skip' $< > $@

$(B)/mktabs: $(B)/vp_open.ml src/mktabs.ml
	cp src/mktabs.ml $(B)/mktabs.ml
	cd $(B) && $(OCAMLFIND) ocamlopt -w -a -package zarith -linkpkg vp_open.ml mktabs.ml -o mktabs

$(B)/verimon_tabs.ml: $(B)/mktabs
	$< > $@

$(B)/verimon_parser.ml: isabelle/verimon_parser.ocaml $(B)/verimon_tabs.ml | $(B)
	awk '/^let verimon_parse_states :/ { skip = 1; \
	       print "let (verimon_parse_ptabs, verimon_parse_i0) : ((char list), mtok) ptabs * nat"; \
	       print "  = Marshal.from_string Verimon_tabs.data 0;;" } \
	     /^let verimon_parse_i0 :/ { skip = 2 } \
	     !skip { print } skip == 1 && /= ptabs_of / || skip == 2 && /;;$$/ { skip = 0 }' $< > $@

# MonPoly's code and the exported code are not ours: compiled without warnings
$(B)/verimon: $(MODS:%=$(B)/%.ml)
	cd $(B) && $(OCAMLFIND) ocamlopt $(OCAMLOPTFLAGS) -w -a -package zarith -linkpkg \
	  $(patsubst formula_parser.ml,formula_parser.mli formula_parser.ml,$(MODS:%=%.ml)) -o verimon

check: all
	@for p in $(PARSERS); do $(B)/verimon ast $$p $(NAMES:%=input/%.mfotl) > $(B)/ast.$$p; done
	@paste -d"\t" $(B)/ast.ocamlyacc $(B)/ast.isabelle | awk -F"\t" -v names="$(NAMES)" \
	  'BEGIN { split(names, n, " ") } $$1 != $$2 { print n[NR] ": the parsers differ"; print "  ocamlyacc " $$1; print "  isabelle  " $$2; bad = 1 } \
	   $$1 != "REJECT" { ok++ } END { if (bad) exit 1; print "check: " NR " inputs, the parsers agree (" ok " accepted)" }'

# a parse takes microseconds (ocamlyacc) to a millisecond (isabelle): many
# repetitions, a hundred times more for ocamlyacc, to rise above start-up noise
REPS ?= 2000

ROWS = for n in $(NAMES); do \
    export TOKENS=$$($(B)/verimon tokens input/$$n.mfotl); \
    REPS=$$((REPS * 100)) $(MEASURE) $$n ocamlyacc $(B)/verimon parse ocamlyacc input/$$n.mfotl; \
    $(MEASURE) $$n isabelle $(B)/verimon parse isabelle input/$$n.mfotl; \
  done

clean:
	rm -rf $(B) out

.PHONY: export clean
include ../common/bench.mk
