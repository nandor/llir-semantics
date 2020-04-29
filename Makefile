# This file is part of the GBC-ML project.
# Licensing information is available in the LICENSE file.
# (C) 2020 Nandor Licker. All rights reserved.

FILES=Cpu.v

COQINCLUDES=-R . LLIR
COQCOPTS ?= -w -undeclared-scope

COQC=$(COQBIN)coqc -q $(COQINCLUDES) $(COQCOPTS)
COQDEP=$(COQBIN)coqdep $(COQINCLUDES)
COQEXEC=$(COQBIN)coqtop $(COQINCLUDES) -batch -load-vernac-source

PROOFS=\
	Values.vo\
	Maps.vo\
	State.vo\
	LLIR.vo\
	Dom.vo\
	Eval.vo\
	Aliasing.vo\
	Verify.vo\
	ReachingStores.vo\
	StoreToLoad.vo

# Toplevel.
all:
	$(MAKE) all-v

# Coq build.
all-v:
	test -f .depend.v || $(MAKE) depend-v
	$(MAKE) proof

depend-v:  $(PROOFS:.vo=.v)
	$(COQDEP) $^ > .depend.v

.PHONY: proof
proof: $(PROOFS)

# Build rules for all languages.
%.vo: %.v
	$(COQC) $*.v

# Clean.
.PHONY: clean
clean:
	rm -f .depend.v
	rm -f *.vo *.vok *.vos *.glob .*.aux .merlin


-include .depend.v
