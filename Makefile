# Makefile originally taken from coq-club

%: Makefile.coq phony
	+make -f Makefile.coq $@

all: Makefile.coq
	mkdir -p hs-src/PlutusIR/Certifier
	+make -f Makefile.coq all
	sed -i 's/module Extracted/module PlutusIR.Certifier.Extracted/' hs-src/PlutusIR/Certifier/Extracted.hs
	sed -i 's/GHC.Base.unsafeCoerce/Unsafe.Coerce.unsafeCoerce/' hs-src/PlutusIR/Certifier/Extracted.hs
	sed -i '/import qualified GHC.Base/a import qualified Unsafe.Coerce' hs-src/PlutusIR/Certifier/Extracted.hs

clean: Makefile.coq
	+make -f Makefile.coq cleanall
	rm -f Makefile.coq
	# CLEANING ALL *.vo *.aux *.glob *.vok *.vos files (files not known in _CoqProject are not removed by cleanall)
	find src -type f -name "*.vo" -delete
	find src -type f -name "*.vos" -delete
	find src -type f -name "*.vok" -delete
	find src -type f -name "*.aux" -delete
	find src -type f -name "*.glob" -delete
	rm -f Makefile.coq

	$(MAKE) -C lib/QuickChick clean


Makefile.coq: _CoqProject Makefile
	coq_makefile COQFLAGS = "-w \"-all\"" -f _CoqProject \
		| sed 's/$$(COQCHK) $$(COQCHKFLAGS) $$(COQLIBS)/$$(COQCHK) $$(COQCHKFLAGS) $$(subst -Q,-R,$$(COQLIBS))/' \
		> Makefile.coq

_CoqProject: ;

Makefile: ;

phony: ;

.PHONY: all clean phony

