
default_target: spec

COQFLAGS= -Q ../bbv bbv  -Q ./src riscv  

DEPFLAGS:=$(COQFLAGS)

COQC=$(COQBIN)coqc
COQTOP=$(COQBIN)coqtop
COQDEP=$(COQBIN)coqdep $(DEPFLAGS)
COQDOC=$(COQBIN)coqdoc

%.vo: %.v
	$(COQC) $(COQFLAGS) $*.v 

spec: $(patsubst %.v,%.vo,$(wildcard src/*.v))

encode: $(patsubst %.v,%.vo,$(wildcard src/encode/*.v))

# beware: the "encode(decode inst) = inst" proof takes about half an hour
proofs: $(patsubst %.v,%.vo,$(wildcard src/proofs/*.v))

all: spec encode proofs

.depend depend:
	$(COQDEP) >.depend `find src -name "*.v"`

# beware: will overwrite src/Execute.v
convert_execute:
	cd convert && python execute.py

clean:
	find . -type f \( -name '*.glob' -o -name '*.vo' -o -name '*.aux' \) -delete
	rm .depend

include .depend

