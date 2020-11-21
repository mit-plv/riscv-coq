#!/bin/sh

coqc -R .. riscv -Q ../../../../coqutil/src/coqutil/ coqutil ./SMTVerif.v | z3 -in
