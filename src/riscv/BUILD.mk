RISCV_DIR := $(patsubst %/,%,$(dir $(lastword $(MAKEFILE_LIST))))
RISCV_VFILES := $(call rwildcard,$(RISCV_DIR),*.v)
RISCV_COQDEPFLAGS := -Q $(RISCV_DIR) $(notdir $(RISCV_DIR))
RISCV_REQUIREFLAGS := -Q $(O)/$(RISCV_DIR) $(notdir $(RISCV_DIR))

RISCV_COQFLAGS := $(COQUTIL_REQUIREFLAGS) -R $(O)/$(RISCV_DIR) $(notdir $(RISCV_DIR)) -w -deprecated-from-Coq,-deprecated-since-9.0,-deprecated-since-8.20
$(O)/$(RISCV_DIR)/%.vo: private COQFLAGS += $(RISCV_COQFLAGS)
$(O)/$(RISCV_DIR)/%.vos: private COQFLAGS += $(RISCV_COQFLAGS)
$(O)/$(RISCV_DIR)/%.vok: private COQFLAGS += $(RISCV_COQFLAGS)
$(RISCV_DIR)/_CoqProject: private COQFLAGS += $(RISCV_COQFLAGS)
