
default_target: spec

COQFLAGS= -Q ../bbv/theories bbv  -R ./src riscv  

DEPFLAGS:=$(COQFLAGS)

COQC=$(COQBIN)coqc
COQTOP=$(COQBIN)coqtop
COQDEP=$(COQBIN)coqdep $(DEPFLAGS)
COQDOC=$(COQBIN)coqdoc

%.vo: %.v
	$(COQC) $(COQFLAGS) $*.v 

# Note: riscv-coq depends on ../bbv, but bbv's version is checked by bedrock2's CI

util: $(patsubst %.v,%.vo,$(wildcard src/util/*.v))

spec: util $(patsubst %.v,%.vo,$(wildcard src/*.v))

encode: spec $(patsubst %.v,%.vo,$(wildcard src/encode/*.v))

# beware: the "encode(decode inst) = inst" proof takes about 25min (June 1st, 2018)
proofs: encode $(patsubst %.v,%.vo,$(wildcard src/proofs/*.v))

all: spec encode proofs

.depend depend:
	$(COQDEP) >.depend `find src -name "*.v"`


# converting from Haskell using hs-to-coq:

HS_TO_COQ_DIR ?= ../../hs-to-coq
RISCV_SEMANTICS_DIR ?= ../../riscv-semantics

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



clean:
	find . -type f \( -name '*.glob' -o -name '*.vo' -o -name '*.aux' \) -delete
	rm .depend

include .depend

