# needs OCaml with ocamlfind, Menhir and Zarith
#
#   make export     re-export isabelle/ocaml_parser.ocaml from thys/OCaml_Parser.thy
#   make            build _build/ocaml
#   make check      Menhir, Isabelle and OCaml's own parser build the same tree
#                   for every input/*.ml
#   make bench      per-parse wall-clock -> out/results.tsv
#   make ci         check, then bench with instruction counts (needs valgrind)
#   make inputs     regenerate input/random_*.ml with _build/gen

B := _build
OCAMLFIND ?= ocamlfind
OCAMLOPTFLAGS ?= -g
MENHIR ?= menhir

NAMES := $(notdir $(basename $(wildcard input/*.ml)))
PARSERS := menhir isabelle

# dependency order
MODS := ocaml_tabs ocaml_parser names ocaml_subset lex isa show ref main

all: $(B)/ocaml

export:
	isabelle build -d ../.. -e OCaml_Bench

$(B):
	mkdir -p $@

$(B)/%.ml: src/%.ml | $(B)
	cp $< $@

$(B)/lex.ml: src/lex.mll | $(B)
	ocamllex -q -o $@ $<

# the code back end; no conflicts, also as LALR(1)
$(B)/ocaml_subset.ml: src/ocaml_subset.mly | $(B)
	$(MENHIR) --lalr --explain --base $(B)/ocaml_subset $<
	@test ! -s $(B)/ocaml_subset.conflicts || { cat $(B)/ocaml_subset.conflicts; exit 1; }

TABS = $(shell sed -n 's/^let ocaml_implementation_\([a-z0-9_]*\) :.*/\1/p' isabelle/ocaml_parser.ocaml)

$(B)/op_open.ml: isabelle/ocaml_parser.ocaml | $(B)
	awk '/^module OCaml_Parser : sig/ { skip = 1 } \
	     skip && /^end = struct/ { print "module OCaml_Parser = struct"; skip = 0; next } !skip' $< > $@

$(B)/mktabs.ml: isabelle/ocaml_parser.ocaml | $(B)
	{ echo 'open Op_open.OCaml_Parser'; \
	  for t in $(TABS); do \
	    echo "let () = Printf.printf \"let $$t = %S\\n\" (Marshal.to_string ocaml_implementation_$$t [])"; \
	  done; } > $@

$(B)/mktabs: $(B)/op_open.ml $(B)/mktabs.ml
	cd $(B) && $(OCAMLFIND) ocamlopt -w -a -package zarith -linkpkg op_open.ml mktabs.ml -o mktabs

$(B)/ocaml_tabs.ml: $(B)/mktabs
	$< > $@

# a table's type annotation is kept; its body, from the line starting with
# "  = " to the ";;", becomes the unmarshalled data
$(B)/ocaml_parser.ml: isabelle/ocaml_parser.ocaml $(B)/ocaml_tabs.ml | $(B)
	awk 'match($$0, /^let ocaml_implementation_[a-z0-9_]* :/) { \
	       t = substr($$0, 26, RLENGTH - 27); head = 1 } \
	     head && /^  = / { print "  = Marshal.from_string Ocaml_tabs." t " 0;;"; head = 0; body = 1 } \
	     !body { print } body && /;;$$/ { body = 0 }' $< > $@

# the exported and the generated code are not ours: compiled without warnings
$(B)/ocaml: $(MODS:%=$(B)/%.ml)
	cd $(B) && $(OCAMLFIND) ocamlopt $(OCAMLOPTFLAGS) -w -a \
	  -package zarith,compiler-libs.common -linkpkg \
	  $(patsubst ocaml_subset.ml,ocaml_subset.mli ocaml_subset.ml,$(MODS:%=%.ml)) -o ocaml

$(B)/gen: src/gen.ml | $(B)
	cp $< $(B)/gen.ml
	cd $(B) && $(OCAMLFIND) ocamlopt gen.ml -o gen

inputs: $(B)/gen
	$(B)/gen -n 30 -seed 1 > input/random_small.ml
	$(B)/gen -n 300 -seed 2 > input/random_large.ml

check: all
	@mkdir -p $(B)/ast; bad=0; \
	for n in $(NAMES); do \
	  for p in ocaml $(PARSERS); do $(B)/ocaml ast $$p input/$$n.ml > $(B)/ast/$$n.$$p; done; \
	  if grep -q '^REJECT' $(B)/ast/$$n.ocaml; then echo "$$n: $$(cat $(B)/ast/$$n.ocaml)"; bad=1; fi; \
	  for p in $(PARSERS); do \
	    cmp -s $(B)/ast/$$n.ocaml $(B)/ast/$$n.$$p || \
	      { echo "$$n: $$p differs from OCaml's parser"; diff $(B)/ast/$$n.ocaml $(B)/ast/$$n.$$p | head -6; bad=1; }; \
	  done; \
	done; \
	[ $$bad = 0 ] && echo "check: $(words $(NAMES)) inputs, the parsers agree with OCaml's"

# repetitions, a hundred times more for menhir, to rise above start-up noise
REPS ?= 20

ROWS = for n in $(NAMES); do \
    export TOKENS=$$($(B)/ocaml tokens input/$$n.ml); \
    REPS=$$((REPS * 100)) $(MEASURE) $$n menhir $(B)/ocaml parse menhir input/$$n.ml; \
    $(MEASURE) $$n isabelle $(B)/ocaml parse isabelle input/$$n.ml; \
  done

clean:
	rm -rf $(B) out

.PHONY: export inputs clean
include ../common/bench.mk
