default_target: spec

COQFLAGS= -Q ../bbv bbv  -R ./src riscv

DEPFLAGS:=$(COQFLAGS)

COQC=$(COQBIN)coqc
COQTOP=$(COQBIN)coqtop
COQDEP=$(COQBIN)coqdep $(DEPFLAGS)
COQDOC=$(COQBIN)coqdoc

%.vo: %.v
	$(COQC) $(COQFLAGS) $*.v

bbv_version_check:
	./check_dep.sh bbv

riscv-semantics_version_check:
	./check_dep.sh riscv-semantics

hs-to-coq_version_check:
	./check_dep.sh hs-to-coq

util: $(patsubst %.v,%.vo,$(wildcard src/util/*.v))

spec: bbv_version_check util $(patsubst %.v,%.vo,$(wildcard src/*.v))

encode: spec $(patsubst %.v,%.vo,$(wildcard src/encode/*.v))

# beware: the "encode(decode inst) = inst" proof takes about 25min (June 1st, 2018)
proofs: encode $(patsubst %.v,%.vo,$(wildcard src/proofs/*.v))

all: spec encode proofs

.depend depend:
	$(COQDEP) >.depend `find src -name "*.v"` export/extract.v


# Old Python3-based conversion:

# beware: will overwrite src/Execute.v
convert_execute: riscv-semantics_version_check
	cd convert && python3 execute.py

# beware: will overwrite src/Decode.v
convert_decode: riscv-semantics_version_check
	cd convert && python3 decode.py


# New hs-to-coq-based conversion:

convert: riscv-semantics_version_check hs-to-coq_version_check
	cd convert-hs-to-coq && ./convert.sh


# coq-to-other languages conversion:

# do not rm these intermediate files in a chain
#.PRECIOUS: export/c/%.c export/py/%.py

# do not remove any intermediate files
.SECONDARY:

export/json/%.json: export/extract.vo src/%.vo
	find . -maxdepth 1 -name '*.json' -type f -exec mv -t export/json -- {} +

export/c/%.c: export/json/%.json
	python3 export/main.py export/json/$*.json export/c/$*.c

export/py/%.py: export/json/%.json $(wildcard export/*.py)
	python3 export/main.py export/json/$*.json export/py/$*.py

export/c/%.o: export/c/%.c
	gcc -std=c11 -Wall -c export/c/$*.c -o export/c/$*.o

# .out files are expected to be empty; this target is just a quick way to check if the
# python3 file parses
export/py/%.out: export/py/%.py
	python3 export/py/$*.py > export/py/$*.out

testPythonDecode: export/py/Decode.py export/py/TestDecode.py
	python3 export/py/TestDecode.py

clean:
	find . -type f \( -name '*.glob' -o -name '*.vo' -o -name '*.aux' \) -delete
	rm .depend

include .depend
