Require Import riscv.Decode.
Require Import riscv.Run.
Require Import bbv.WordScope.

Definition Seqz(rd: Register)(rs1: Register): Instruction MachineInt := Sltiu rd rs1 $1.
Definition Snez(rd: Register)(rs1: Register): Instruction MachineInt := Sltu rd Register0 rs1.
Definition Nop := Addi Register0 Register0 0.
