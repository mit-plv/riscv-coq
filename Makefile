default_target: spec

.PHONY: clean install force spec all convert convert_loc_counts

# absolute paths so that emacs compile mode knows where to find error
# use cygpath -m because Coq on Windows cannot handle cygwin paths
SRCDIR := $(shell cygpath -m "$$(pwd)" 2>/dev/null || pwd)/src/riscv
PARENT_DIR := $(shell cd .. && (cygpath -m "$$(pwd)" 2>/dev/null || pwd))

SPEC_VS := $(wildcard $(SRCDIR)/Spec/*.v $(SRCDIR)/Utility/*.v $(SRCDIR)/Platform/*.v)
ALL_VS := $(SPEC_VS) $(wildcard $(SRCDIR)/Proofs/*.v) $(wildcard $(SRCDIR)/Examples/*.v)

SPEC_VOS := $(patsubst %.v,%.vo,$(SPEC_VS))
ALL_VOS := $(patsubst %.v,%.vo,$(ALL_VOS))

DEPS_DIR?=$(PARENT_DIR)

# Note: make does not interpret "\n", and this is intended
DEPFLAGS_COQUTIL_NL=-Q $(DEPS_DIR)/coqutil/src/coqutil coqutil\n
DEPFLAGS_COQ_RECORD_UPDATE_NL=-Q $(DEPS_DIR)/coq-record-update/src RecordUpdate\n
DEPFLAGS_NL=
CURFLAGS_NL=-R $(SRCDIR) riscv\n

EXTERNAL_DEPENDENCIES?=
EXTERNAL_COQUTIL?=
EXTERNAL_COQ_RECORD_UPDATE?=

ifneq ($(EXTERNAL_COQUTIL),1)
DEPFLAGS_NL+=$(DEPFLAGS_COQUTIL_NL)
endif

ifneq ($(EXTERNAL_COQ_RECORD_UPDATE),1)
DEPFLAGS_NL+=$(DEPFLAGS_COQ_RECORD_UPDATE_NL)
endif

# If we get our dependencies externally, then we should not bind the local versions of things
ifneq ($(EXTERNAL_DEPENDENCIES),1)
ALLDEPFLAGS_NL=$(CURFLAGS_NL)$(DEPFLAGS_NL)
else
ALLDEPFLAGS_NL=$(CURFLAGS_NL)
endif

ALLDEPFLAGS=$(subst \n, ,$(ALLDEPFLAGS_NL))

_CoqProject:
	printf -- '$(ALLDEPFLAGS_NL)' > _CoqProject

spec: Makefile.coq.spec $(SPEC_VS)
	rm -f .coqdeps.d
	$(MAKE) -f Makefile.coq.spec

all: Makefile.coq.all $(ALL_VS)
	rm -f .coqdeps.d
	$(MAKE) -f Makefile.coq.all

COQ_MAKEFILE := $(COQBIN)coq_makefile -f _CoqProject INSTALLDEFAULTROOT = riscv $(COQMF_ARGS)

Makefile.coq.spec: _CoqProject force
	@echo "Generating Makefile.coq.spec"
	@$(COQ_MAKEFILE) $(SPEC_VS) -o Makefile.coq.spec

Makefile.coq.all: _CoqProject force
	@echo "Generating Makefile.coq.all"
	@$(COQ_MAKEFILE) $(ALL_VS) -o Makefile.coq.all

force:

clean:: Makefile.coq.all
	$(MAKE) -f Makefile.coq.all clean
	find . -type f \( -name '*~' -o -name '*.aux' -o -name '.lia.cache' -o -name '.nia.cache' \) -delete
	rm -f Makefile.coq.all Makefile.coq.all.conf Makefile.coq.spec Makefile.coq.spec.conf _CoqProject

install:: Makefile.coq.all
	$(MAKE) -f Makefile.coq.all install


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
PREAMBLES = convert-hs-to-coq/Decode_preamble.v convert-hs-to-coq/Execute_preamble.v convert-hs-to-coq/CSR_preamble.v
EDIT_FILES = convert-hs-to-coq/Decode.edits convert-hs-to-coq/General.edits convert-hs-to-coq/Base.edits convert-hs-to-coq/CSR.edits convert-hs-to-coq/ZOps.edits convert-hs-to-coq/RegisterOps.edits
HS_TO_COQ = stack exec hs-to-coq -- -N -i $(RISCV_SEMANTICS_DIR)/src -o $(SRCDIR) --iface-dir $(SRCDIR) -e convert-hs-to-coq/General.edits -e convert-hs-to-coq/Base.edits
DECODE_OPTS  = -p convert-hs-to-coq/Decode_preamble.v  -e convert-hs-to-coq/ZOps.edits        -e convert-hs-to-coq/Decode.edits
EXECUTE_OPTS = -p convert-hs-to-coq/Execute_preamble.v -e convert-hs-to-coq/RegisterOps.edits
CSR_OPTS     = -p convert-hs-to-coq/CSR_preamble.v     -e convert-hs-to-coq/CSR.edits

convert: riscv-semantics_version_check hs-to-coq_version_check $(HS_SOURCES) $(PREAMBLES) $(EDIT_FILES)
	$(HS_TO_COQ) $(CSR_OPTS)                             -e convert-hs-to-coq/ZOps.edits         $(RISCV_SEMANTICS_DIR)/src/Spec/CSRField.hs
	$(HS_TO_COQ) $(CSR_OPTS)                             -e convert-hs-to-coq/ZOps.edits         $(RISCV_SEMANTICS_DIR)/src/Spec/CSR.hs
	$(HS_TO_COQ) $(CSR_OPTS)                             -e convert-hs-to-coq/ZOps.edits         $(RISCV_SEMANTICS_DIR)/src/Spec/CSRGetSet.hs
	$(HS_TO_COQ) $(DECODE_OPTS)                                                                  $(RISCV_SEMANTICS_DIR)/src/Spec/Decode.hs
	$(HS_TO_COQ) $(EXECUTE_OPTS)                         -e convert-hs-to-coq/ExecuteI.edits     $(RISCV_SEMANTICS_DIR)/src/Spec/ExecuteI.hs
	$(HS_TO_COQ) -p convert-hs-to-coq/Execute_preamble.v -e convert-hs-to-coq/ExecuteCSR.edits   $(RISCV_SEMANTICS_DIR)/src/Spec/ExecuteCSR.hs
	$(HS_TO_COQ) $(EXECUTE_OPTS)                                                                 $(RISCV_SEMANTICS_DIR)/src/Spec/ExecuteI64.hs
	$(HS_TO_COQ) $(EXECUTE_OPTS)                                                                 $(RISCV_SEMANTICS_DIR)/src/Spec/ExecuteM.hs
	$(HS_TO_COQ) $(EXECUTE_OPTS)                                                                 $(RISCV_SEMANTICS_DIR)/src/Spec/ExecuteM64.hs
	$(HS_TO_COQ) $(EXECUTE_OPTS)                                                                 $(RISCV_SEMANTICS_DIR)/src/Spec/ExecuteA.hs
	$(HS_TO_COQ) $(EXECUTE_OPTS)                                                                 $(RISCV_SEMANTICS_DIR)/src/Spec/ExecuteA64.hs

convert_loc_counts:
	wc -l $(RISCV_SEMANTICS_DIR)/src/Spec/CSRField.hs $(RISCV_SEMANTICS_DIR)/src/Spec/CSR.hs $(RISCV_SEMANTICS_DIR)/src/Spec/CSRGetSet.hs $(RISCV_SEMANTICS_DIR)/src/Spec/Decode.hs $(RISCV_SEMANTICS_DIR)/src/Spec/ExecuteI.hs $(RISCV_SEMANTICS_DIR)/src/Spec/ExecuteCSR.hs $(RISCV_SEMANTICS_DIR)/src/Spec/ExecuteI64.hs $(RISCV_SEMANTICS_DIR)/src/Spec/ExecuteM.hs $(RISCV_SEMANTICS_DIR)/src/Spec/ExecuteM64.hs $(RISCV_SEMANTICS_DIR)/src/Spec/ExecuteA.hs $(RISCV_SEMANTICS_DIR)/src/Spec/ExecuteA64.hs
	wc -l convert-hs-to-coq/*.edits

# Currently does not work because of https://github.com/coq/coq/issues/11129
src/riscv/Spec/Decode.v.beautified:
	make -f Makefile.coq.all $(SRCDIR)/Spec/Decode.v.beautified

# coq-to-other languages conversion:

# do not rm these intermediate files in a chain
#.PRECIOUS: export/c/%.c export/py/%.py

# do not remove any intermediate files
.SECONDARY:

export/extract.vo: export/extract.v spec
	$(COQBIN)coqc -R $(SRCDIR) riscv export/extract.v

export/json/%.json: export/extract.vo src/riscv/%.vo
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
