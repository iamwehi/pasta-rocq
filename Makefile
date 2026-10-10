# Compile from the repository root: make

ROCQ := rocq c -q -R theories Pasta

.PHONY: all clean

all: theories/Curve.vo
	@echo "Pasta proofs compiled."

theories/Trial.vo: theories/Trial.v
	$(ROCQ) theories/Trial.v

theories/Pocklington.vo: theories/Pocklington.v
	$(ROCQ) theories/Pocklington.v

theories/Certificates.vo: theories/Certificates.v theories/Trial.vo theories/Pocklington.vo
	$(ROCQ) theories/Certificates.v

theories/Curve.vo: theories/Curve.v theories/Certificates.vo
	$(ROCQ) theories/Curve.v

clean:
	rm -f theories/*.vo theories/*.vos theories/*.vok theories/*.glob theories/.*.aux
	rm -f .coqdeps.d Makefile.coq Makefile.coq.conf CoqMakefile.conf
