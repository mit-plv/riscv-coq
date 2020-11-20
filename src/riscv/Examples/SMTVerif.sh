#!/bin/sh

coqc -R .. riscv -Q ../../../../../deps/coqutil/src/coqutil/ coqutil ./SMTVerif.v | z3 -in
