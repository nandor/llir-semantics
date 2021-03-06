# This file is part of the GBC-ML project.
# Licensing information is available in the LICENSE file.
# (C) 2020 Nandor Licker. All rights reserved.

FILES=Cpu.v

COQINCLUDES=-R . LLIR
COQCOPTS ?= -w -undeclared-scope

COQC=$(COQBIN)coqc -q $(COQINCLUDES) $(COQCOPTS)
COQDEP=$(COQBIN)coqdep $(COQINCLUDES)

PROOFS=\
	Values.vo\
	Maps.vo\
	Types.vo\
	LLIR.vo\
	Frame.vo\
	State.vo\
	Export.vo\
	Syscall.vo\
	Eval.vo\
	SmallStep.vo\
	SmallStep_Progress.vo\
	SmallStep_Valid.vo\
	Closure.vo\
	Transform.vo\
	Dom.vo\
	Block.vo\
	Liveness.vo\
	Aliasing.vo\
	Typing.vo\
	SSA.vo\
	ReachingStores.vo\
	StoreToLoad.vo

# Toplevel.
all:
	$(MAKE) all-v

# LLIR examples.
test/%.v: test/%.llbc all
	llir-opt $< -o $@ -O1

.PRECIOUS: test/%.v
test/simple.llbc: test/simple.c
	llir-clang $^ -o $@ -O1 -static -Wl,-e=_start_c
test/%.llbc: test/%.c
	llir-clang -c $^ -o $@ -O1
test/%.llir: test/%.llbc
	llir-opt $^ -o $@ -O0

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
	rm -f test/*.vo test/*.vok test/*.vos test/*.glob
	rm -f test/*.llbc
	rm -f test/*.v


-include .depend.v
