Require Import Coq.ZArith.BinInt.
Require Import riscv.Utility.Encode.
Require Import coqutil.Z.BitOps.
Require Import coqutil.Z.prove_Zeq_bitwise.

Lemma invert_encode_R: forall {opcode rd rs1 rs2 funct3 funct7},
  verify_R opcode rd rs1 rs2 funct3 funct7 ->
  forall inst,
  encode_R opcode rd rs1 rs2 funct3 funct7 = inst ->
  opcode = bitSlice inst 0 7 /\
  funct3 = bitSlice inst 12 15 /\
  funct7 = bitSlice inst 25 32 /\
  rd = bitSlice inst 7 12 /\
  rs1 = bitSlice inst 15 20 /\
  rs2 = bitSlice inst 20 25.
Proof. intros. unfold encode_R, verify_R in *. prove_Zeq_bitwise. Qed.
