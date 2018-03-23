Require Import riscv.Decode.
Require Import riscv.Run.

Definition Seqz(rd: Register)(rs1: Register): InstructionI := Sltiu rd rs1 1.
Definition Snez(rd: Register)(rs1: Register): InstructionI := Sltu rd Register0 rs1.
