Require Import riscv.Utility.
Require Import riscv.Decode.
Require Import riscv.Run.
Require Import riscv.util.NameWithEq.
Require Import bbv.WordScope.

Local Open Scope Z_scope.

Section Pseudo.

  Context {Name: NameWithEq}. (* register name *)
  Notation Register := (@name Name).

  Variable Register0: Register.

  Record PseudoInstructionsModule := {
    Seqz(rd: Register)(rs1: Register): Instruction;
    Snez(rd: Register)(rs1: Register): Instruction;
    Nop: Instruction;
  }.

  Definition PseudoInstructions: PseudoInstructionsModule := {|
    Seqz(rd: Register)(rs1: Register) := Sltiu rd rs1 1;
    Snez(rd: Register)(rs1: Register) := Sltu rd Register0 rs1;
    Nop := Addi Register0 Register0 0;
  |}.

End Pseudo.

(* Usage:

Definition pseudo := @PseudoInstructions ZName 0.

Check (pseudo.(Seqz)).

*)
