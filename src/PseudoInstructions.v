Require Import riscv.Decode.
Require Import riscv.Run.

Definition Seqz(rd: Register)(rs1: Register) := Sltiu rd rs1 1.
Definition Snez(rd: Register)(rs1: Register) := Sltu rd Register0 rs1.
Definition Nop := Addi Register0 Register0 0.
Definition InfiniteJal := Jal Register0 0.
