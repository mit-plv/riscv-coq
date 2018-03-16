
default_target: all

# Source code of the hs-to-coq project cloned from https://github.com/antalsz/hs-to-coq
HS_TO_COQ_DIR?=../../hs-to-coq

# This is needed for "stack" to choose the right project
export STACK_YAML=$(HS_TO_COQ_DIR)/stack.yaml

HS_INPUT_DIR=../../riscv-semantics/src
EDITS_DIR=.
V_OUTPUT_DIR=./testoutput

CONVERT=stack exec hs-to-coq -- -o $(V_OUTPUT_DIR)

$(V_OUTPUT_DIR)/%.v: $(HS_INPUT_DIR)/%.hs $(EDITS_DIR)/%.edits
	$(CONVERT) $(HS_INPUT_DIR)/$*.hs --edits $(EDITS_DIR)/$*.edits --modules-dir $(HS_INPUT_DIR)

all: $(V_OUTPUT_DIR)/Decode.v

