# Compile from the repository root: make

ROCQ := rocq c -q -R theories Pasta
ROCQCHK := rocqchk

.PHONY: all clean check

all: theories/Curve.vo
	@echo "Pasta proofs compiled."

theories/Trial.vo: theories/Trial.v
	$(ROCQ) theories/Trial.v

theories/Pocklington.vo: theories/Pocklington.v theories/Trial.vo
	$(ROCQ) theories/Pocklington.v

theories/Certificates.vo: theories/Certificates.v theories/Trial.vo theories/Pocklington.vo
	$(ROCQ) theories/Certificates.v

theories/Curve.vo: theories/Curve.v theories/Certificates.vo
	$(ROCQ) theories/Curve.v

# Fail if a headline theorem depends on an axiom, then re-check every proof
# with the standalone kernel checker.  The kernel check takes several minutes.
check: theories/Curve.vo
	$(ROCQ) theories/Audit.v > .audit.out
	@if grep -q '^Axioms:' .audit.out; then \
	  echo "Audit found axioms:"; cat .audit.out; exit 1; \
	fi
	@echo "Headline theorems depend on no axioms."
	$(ROCQCHK) -o -silent -R theories Pasta Pasta.Curve > .rocqchk.out 2>&1 \
	  || { cat .rocqchk.out; exit 1; }
	@if ! grep -q '^\* Axioms: <none>' .rocqchk.out; then \
	  echo "rocqchk did not report an axiom-free development:"; \
	  cat .rocqchk.out; exit 1; \
	fi
	@echo "rocqchk: no axioms."

clean:
	rm -f theories/*.vo theories/*.vos theories/*.vok theories/*.glob theories/.*.aux
	rm -f .coqdeps.d .Makefile.coq.d .audit.out .rocqchk.out
	rm -f Makefile.coq Makefile.coq.conf CoqMakefile.conf
