
default_target: spec

.PHONY: clean force spec all

SPEC_VS := $(wildcard src/*.v src/util/*.v)
ALL_VS := $(shell find src -type f -name '*.v')

SPEC_VOS := $(patsubst %.v,%.vo,$(SPEC_VS))
ALL_VOS := $(patsubst %.v,%.vo,$(ALL_VOS))

spec: Makefile.coq.spec $(SPEC_VS)
	$(MAKE) -f Makefile.coq.spec

all: Makefile.coq.all $(ALL_VS)
	$(MAKE) -f Makefile.coq.all

COQ_MAKEFILE := $(COQBIN)coq_makefile -f _CoqProject INSTALLDEFAULTROOT = riscv

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

HS_SOURCES = $(RISCV_SEMANTICS_DIR)/src/Decode.hs $(RISCV_SEMANTICS_DIR)/src/ExecuteI.hs $(RISCV_SEMANTICS_DIR)/src/ExecuteI64.hs $(RISCV_SEMANTICS_DIR)/src/ExecuteM.hs $(RISCV_SEMANTICS_DIR)/src/ExecuteM64.hs
PREAMBLES = convert-hs-to-coq/Decode_preamble.v convert-hs-to-coq/Execute_preamble.v 
EDIT_FILES = convert-hs-to-coq/Decode.edits convert-hs-to-coq/General.edits convert-hs-to-coq/Base.edits  convert-hs-to-coq/Execute.edits 

convert: riscv-semantics_version_check hs-to-coq_version_check $(HS_SOURCES) $(PREAMBLES) $(EDIT_FILES)
	stack exec hs-to-coq -- -e convert-hs-to-coq/Decode.edits  -p convert-hs-to-coq/Decode_preamble.v  -e convert-hs-to-coq/General.edits -e convert-hs-to-coq/Base.edits -N -i $(RISCV_SEMANTICS_DIR)/src -o ./src $(RISCV_SEMANTICS_DIR)/src/Decode.hs
	stack exec hs-to-coq -- -e convert-hs-to-coq/Execute.edits -p convert-hs-to-coq/Execute_preamble.v -e convert-hs-to-coq/General.edits -e convert-hs-to-coq/Base.edits -N -i $(RISCV_SEMANTICS_DIR)/src -o ./src $(RISCV_SEMANTICS_DIR)/src/ExecuteI.hs
	stack exec hs-to-coq -- -e convert-hs-to-coq/Execute.edits -p convert-hs-to-coq/Execute_preamble.v -e convert-hs-to-coq/General.edits -e convert-hs-to-coq/Base.edits -N -i $(RISCV_SEMANTICS_DIR)/src -o ./src $(RISCV_SEMANTICS_DIR)/src/ExecuteI64.hs
	stack exec hs-to-coq -- -e convert-hs-to-coq/Execute.edits -p convert-hs-to-coq/Execute_preamble.v -e convert-hs-to-coq/General.edits -e convert-hs-to-coq/Base.edits -N -i $(RISCV_SEMANTICS_DIR)/src -o ./src $(RISCV_SEMANTICS_DIR)/src/ExecuteM.hs
	stack exec hs-to-coq -- -e convert-hs-to-coq/Execute.edits -p convert-hs-to-coq/Execute_preamble.v -e convert-hs-to-coq/General.edits -e convert-hs-to-coq/Base.edits -N -i $(RISCV_SEMANTICS_DIR)/src -o ./src $(RISCV_SEMANTICS_DIR)/src/ExecuteM64.hs
