Require Import Coq.ZArith.BinInt.
Require Import riscv.Utility.Encode.
Require Import coqutil.Z.BitOps.
Require Import coqutil.Z.prove_Zeq_bitwise.

Lemma invert_encode_FenceI: forall {opcode rd rs1 funct3 imm12},
  verify_FenceI opcode rd rs1 funct3 imm12 ->
  forall inst,
  encode_FenceI opcode rd rs1 funct3 imm12 = inst ->
  opcode = bitSlice inst 0 7 /\
  funct3 = bitSlice inst 12 15 /\
  rd = bitSlice inst 7 12 /\
  rs1 = bitSlice inst 15 20 /\
  imm12 = signExtend 12 (bitSlice inst 20 32).
Proof. intros. unfold encode_FenceI, verify_FenceI in *. prove_Zeq_bitwise. Qed.
