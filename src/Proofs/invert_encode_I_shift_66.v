Require Import Coq.ZArith.BinInt.
Require Import riscv.Encode.
Require Import riscv.util.ZBitOps.
Require Import riscv.util.prove_Zeq_bitwise.

Local Open Scope bool_scope.

Lemma invert_encode_I_shift_66: forall {bitwidth opcode rd rs1 shamt6 funct3 funct6},
  verify_I_shift_66 bitwidth opcode rd rs1 shamt6 funct3 funct6 ->
  forall inst,
  encode_I_shift_66  opcode rd rs1 shamt6 funct3 funct6 = inst ->
  opcode = bitSlice inst 0 7 /\
  funct3 = bitSlice inst 12 15 /\
  funct6 = bitSlice inst 26 32 /\
  rd = bitSlice inst 7 12 /\
  rs1 = bitSlice inst 15 20 /\
  shamt6 = bitSlice inst 20 26 /\
  ((Z.eqb (bitSlice inst 25 26) 0) || (Z.eqb bitwidth 64)) = true.
Proof.
  intros. unfold encode_I_shift_66, verify_I_shift_66 in *.
  rewrite Bool.orb_true_iff.
  rewrite? Z.eqb_eq.
  prove_Zeq_bitwise.
Qed.
