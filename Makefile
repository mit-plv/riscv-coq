default_target: spec

.PHONY: clean force spec all convert

# absolute paths so that emacs compile mode knows where to find error
# use cygpath -m because Coq on Windows cannot handle cygwin paths
SRCDIR := $(shell cygpath -m "$$(pwd)" 2>/dev/null || pwd)/src

SPEC_VS := $(wildcard $(SRCDIR)/Spec/*.v $(SRCDIR)/Utility/*.v $(SRCDIR)/Platform/*.v)
ALL_VS := $(SPEC_VS) $(wildcard $(SRCDIR)/Proofs/*.v)

SPEC_VOS := $(patsubst %.v,%.vo,$(SPEC_VS))
ALL_VOS := $(patsubst %.v,%.vo,$(ALL_VOS))

spec: Makefile.coq.spec $(SPEC_VS)
	$(MAKE) -f Makefile.coq.spec

all: Makefile.coq.all $(ALL_VS)
	$(MAKE) -f Makefile.coq.all

COQ_MAKEFILE := $(COQBIN)coq_makefile -f _CoqProject INSTALLDEFAULTROOT = riscv $(COQMF_ARGS)

Makefile.coq.spec: force
	 $(COQ_MAKEFILE) $(SPEC_VS) -o Makefile.coq.spec

Makefile.coq.all: force
	$(COQ_MAKEFILE) $(ALL_VS) -o Makefile.coq.all

force:

clean:: Makefile.coq.all
	$(MAKE) -f Makefile.coq.all clean
	find . -type f \( -name '*~' -o -name '*.aux' \) -delete
	rm -f Makefile.coq.all Makefile.coq.all.conf Makefile.coq.spec Makefile.coq.spec.conf


# converting from Haskell using hs-to-coq:

HS_TO_COQ_DIR ?= ../../../hs-to-coq
RISCV_SEMANTICS_DIR ?= ../../../riscv-semantics

riscv-semantics_version_check:
	./check_dep.sh $(RISCV_SEMANTICS_DIR) `cat deps/riscv-semantics`

hs-to-coq_version_check:
	./check_dep.sh $(HS_TO_COQ_DIR) `cat deps/hs-to-coq`

# export because stack will use this environment var
export STACK_YAML=$(HS_TO_COQ_DIR)/stack.yaml

HS_SOURCES = $(RISCV_SEMANTICS_DIR)/src/Spec/Decode.hs $(RISCV_SEMANTICS_DIR)/src/Spec/ExecuteI.hs $(RISCV_SEMANTICS_DIR)/src/Spec/ExecuteI64.hs $(RISCV_SEMANTICS_DIR)/src/Spec/ExecuteM.hs $(RISCV_SEMANTICS_DIR)/src/Spec/ExecuteM64.hs
PREAMBLES = convert-hs-to-coq/Decode_preamble.v convert-hs-to-coq/Execute_preamble.v
EDIT_FILES = convert-hs-to-coq/Decode.edits convert-hs-to-coq/General.edits convert-hs-to-coq/Base.edits  convert-hs-to-coq/Execute.edits
HS_TO_COQ = stack exec hs-to-coq -- -N -i $(RISCV_SEMANTICS_DIR)/src -o ./src --iface-dir ./src
DECODE_OPTS =  -e convert-hs-to-coq/Decode.edits  -p convert-hs-to-coq/Decode_preamble.v  -e convert-hs-to-coq/General.edits -e convert-hs-to-coq/Base.edits
EXECUTE_OPTS = -e convert-hs-to-coq/Execute.edits -p convert-hs-to-coq/Execute_preamble.v -e convert-hs-to-coq/General.edits -e convert-hs-to-coq/Base.edits

convert: riscv-semantics_version_check hs-to-coq_version_check $(HS_SOURCES) $(PREAMBLES) $(EDIT_FILES)
	$(HS_TO_COQ) $(DECODE_OPTS)  $(RISCV_SEMANTICS_DIR)/src/Spec/Decode.hs
	$(HS_TO_COQ) $(EXECUTE_OPTS) $(RISCV_SEMANTICS_DIR)/src/Spec/ExecuteI.hs
	$(HS_TO_COQ) $(EXECUTE_OPTS) $(RISCV_SEMANTICS_DIR)/src/Spec/ExecuteI64.hs
	$(HS_TO_COQ) $(EXECUTE_OPTS) $(RISCV_SEMANTICS_DIR)/src/Spec/ExecuteM.hs
	$(HS_TO_COQ) $(EXECUTE_OPTS) $(RISCV_SEMANTICS_DIR)/src/Spec/ExecuteM64.hs
	$(HS_TO_COQ) $(EXECUTE_OPTS) $(RISCV_SEMANTICS_DIR)/src/Spec/ExecuteA.hs
	$(HS_TO_COQ) $(EXECUTE_OPTS) $(RISCV_SEMANTICS_DIR)/src/Spec/ExecuteA64.hs


# coq-to-other languages conversion:

# do not rm these intermediate files in a chain
#.PRECIOUS: export/c/%.c export/py/%.py

# do not remove any intermediate files
.SECONDARY:

export/extract.vo: export/extract.v spec
	$(COQBIN)coqc -R ./src riscv export/extract.v

export/json/%.json: export/extract.vo src/%.vo
	find . -maxdepth 1 -name '*.json' -type f -exec mv -t export/json -- {} +

export/c/%.h: export/json/%.json $(wildcard export/*.py)
	python3 export/main.py export/json/$*.json export/c/$*.h

export/py/%.py: export/json/%.json $(wildcard export/*.py)
	python3 export/main.py export/json/$*.json export/py/$*.py

# .out files are expected to be empty; this target is just a quick way to check if the
# python3 file parses
export/py/%.out: export/py/%.py
	python3 export/py/$*.py > export/py/$*.out

testPythonDecode: export/py/Decode.py export/py/TestDecode.py
	python3 export/py/TestDecode.py

export/c/TestDecode: export/c/TestDecode.c export/c/Decode.h
	gcc -std=c11 -Wall export/c/TestDecode.c -o export/c/TestDecode

export/c/TestRun: export/c/ExecuteI64.h export/c/ExecuteI.h export/c/ExecuteM64.h export/c/ExecuteM.h export/c/Decode.h export/c/TestRun.c
	gcc -std=c11 -Wall export/c/TestRun.c -o export/c/TestRun

testCDecode: export/c/TestDecode
	export/c/TestDecode

testCRun: export/c/TestRun
	export/c/TestRun

testDecode: testPythonDecode testCDecode
