.PHONY: build cache audit roadmap emit-schema check-schema mdgen html pdf docs clean

LIB := InfluenceDiagramsProofs
TITLE := Formal Verification of InfluenceDiagrams.jl
AUTHOR := Simon Frost

# Fetch prebuilt Mathlib oleans (run once per Mathlib revision)
cache:
	lake exe cache get

# Build the default target (everything except Roadmap.lean); must be sorry-free
build:
	lake build --wfail

# Reject missing audit results, nonstandard axioms and source proof escape hatches.
audit:
	@mkdir -p .lake
	@lake env lean Audit.lean > .lake/audit.log 2>&1 || { cat .lake/audit.log; exit 1; }
	@cat .lake/audit.log
	python3 scripts/audit.py .lake/audit.log

# Build the remaining-work module; currently contains no unproved declarations
roadmap:
	lake build $(LIB).Roadmap

# Regenerate schemas/*.schema.json from the Lean schema terms (ACSets.jl format)
emit-schema:
	lake exe emit_schema

# Fail if schemas/*.schema.json are out of date with respect to the Lean schema terms
check-schema:
	lake exe emit_schema --check

# ---------------------------------------------------------------------------------------------
# Documents: $(LIB).md (mdgen), $(LIB).html (pandoc) and $(LIB).pdf (pandoc + lualatex).
# Requires pandoc and a TeX distribution with lualatex (TinyTeX or MacTeX); built locally, not
# in CI. Fonts: STIX Two Text/Math (system or TeX Live) and JuliaMono from ../../fonts/JuliaMono.

# Modules in import (dependency) order, as in $(LIB).lean; Roadmap.lean last.
MD_FILES = \
    Basic.md Finite/InfluenceDiagram.md Finite/Instantiate.md Finite/ExpectedUtility.md \
    Finite/Information.md Finite/Optimization.md Finite/OptimalInformation.md \
    Finite/DVE/Valuation.md Finite/DVE/Semantics.md Finite/DVE/Driver.md \
    Finite/DVE/Solver.md Finite/DVE/Schedule.md Finite/DVE/Evidence.md Finite/DVE/Example.md \
    Finite/DVE/Guard/Positive.md Finite/DVE/Guard/Provenance.md \
    Finite/DVE/Guard/Complete.md Finite/DVE/Guard/Boundary.md \
    Finite/OrderedPolicies.md \
    Roadmap.md

JULIAMONO_DIR = $(abspath ../../fonts/JuliaMono)/
# pandoc >= 3.8 (older: --highlight-style=tango); lean.xml is our syntax definition (pandoc has none)
PANDOC_COMMON = --toc --toc-depth=2 --syntax-definition=lean.xml --syntax-highlighting=tango \
    --metadata title="$(TITLE)" --metadata author="$(AUTHOR)" \
    --metadata date="$(shell date +%Y-%m-%d)"

docs: mdgen html pdf

# One Markdown file per Lean module (module docstrings become prose, everything else a `lean`
# code block), concatenated in MD_FILES order. mdgen emits each module's `import` block before
# its title; the perl one-liner moves it just after the title so that sections start cleanly.
mdgen:
	rm -rf .mdgen_tmp
	lake exe mdgen $(LIB) .mdgen_tmp
	@for f in $(MD_FILES); do \
	  printf '\n\n<!-- $(LIB)/%s -->\n\n' "$${f%.md}.lean"; \
	  perl -0pe 's/\A(```lean\n(?:import [^\n]*\n)+```\n\n)(\# [^\n]*\n\n)/$$2$$1/' .mdgen_tmp/$$f; \
	done > $(LIB).md
	rm -rf .mdgen_tmp
	@echo "Generated $(LIB).md"

html: $(LIB).md
	pandoc $(LIB).md -o $(LIB).html --standalone --mathjax --css=style.css $(PANDOC_COMMON)
	@echo "Generated $(LIB).html"

# pandoc writes the LaTeX source; lualatex is run twice for the table of contents so that the
# .log survives for the missing-glyph check.
pdf: $(LIB).md
	printf '\\newcommand{\\JuliaMonoDir}{%s}\n' "$(JULIAMONO_DIR)" > .fonts.tex
	pandoc $(LIB).md -o $(LIB).tex --standalone --pdf-engine=lualatex $(PANDOC_COMMON) \
	    -V papersize=a4 -V geometry:margin=2.2cm -V colorlinks=true -V linkcolor=NavyBlue \
	    -V urlcolor=NavyBlue -V toccolor=black -H .fonts.tex -H header.tex
	lualatex -interaction=nonstopmode -halt-on-error $(LIB).tex > /dev/null
	lualatex -interaction=nonstopmode -halt-on-error $(LIB).tex > /dev/null
	@grep -c "Missing character" $(LIB).log | sed 's/^/Missing-character warnings in $(LIB).log: /' || true
	@echo "Generated $(LIB).pdf"

clean:
	rm -rf .mdgen_tmp .fonts.tex $(LIB).md $(LIB).html $(LIB).tex $(LIB).pdf \
	    $(LIB).aux $(LIB).log $(LIB).out $(LIB).toc
