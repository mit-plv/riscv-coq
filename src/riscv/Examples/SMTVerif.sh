#!/bin/sh

"${COQBIN}rocq" compile -R .. riscv -Q ../../../../coqutil/src/coqutil/ coqutil ./SMTVerif.v | z3 -in
