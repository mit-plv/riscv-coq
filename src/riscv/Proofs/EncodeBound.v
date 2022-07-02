Require Import Coq.ZArith.ZArith.
Require Import riscv.Spec.Decode.
Require Import riscv.Utility.Encode.
Require Import riscv.Utility.Utility.
Require Import riscv.Utility.Tactics.
Require Import coqutil.Z.prove_Zeq_bitwise.
Require Import coqutil.Z.Lia.


Local Open Scope bool_scope.
Local Open Scope Z_scope.

Lemma encode_Fence_bitSlice_idemp: forall opcode funct3 z z0 z1 z2 z3,
    bitSlice (encode_Fence opcode z z0 funct3 z1 z2 z3) 0 32 =
              encode_Fence opcode z z0 funct3 z1 z2 z3.
Proof. intros. unfold encode_Fence. prove_Zeq_bitwise. Qed.

Lemma encode_Invalid_bitSlice_idemp: forall z,
     bitSlice (encode_Invalid z) 0 32 = encode_Invalid z.
Proof. intros. unfold encode_Invalid. prove_Zeq_bitwise. Qed.

Lemma encode_I_bitSlice_idemp: forall opcode r r0 funct3 z,
     bitSlice (encode_I opcode r r0 funct3 z) 0 32 = encode_I opcode r r0 funct3 z.
Proof. intros. unfold encode_I. prove_Zeq_bitwise. Qed.

Lemma encode_I_shift_57_bitSlice_idemp: forall opcode r r0 z funct3 funct7,
    bitSlice (encode_I_shift_57 opcode r r0 z funct3 funct7) 0 32 =
              encode_I_shift_57 opcode r r0 z funct3 funct7.
Proof. intros. unfold encode_I_shift_57. prove_Zeq_bitwise. Qed.

Lemma encode_I_shift_66_bitSlice_idemp: forall opcode r r0 z funct3 funct6,
    bitSlice (encode_I_shift_66 opcode r r0 z funct3 funct6) 0 32 =
              encode_I_shift_66 opcode r r0 z funct3 funct6.
Proof. intros. unfold encode_I_shift_66. prove_Zeq_bitwise. Qed.

Lemma encode_I_system_bitSlice_idemp: forall opcode r r0 funct3 z,
    bitSlice (encode_I_system opcode r r0 funct3 z) 0 32 =
              encode_I_system opcode r r0 funct3 z.
Proof. intros. unfold encode_I_system. prove_Zeq_bitwise. Qed.

Lemma encode_R_atomic_bitSlice_idemp: forall opcode r r0 r1 funct3 z funct5,
    bitSlice (encode_R_atomic opcode r r0 r1 funct3 z funct5) 0 32 =
              encode_R_atomic opcode r r0 r1 funct3 z funct5.
Proof. intros. unfold encode_R_atomic. prove_Zeq_bitwise. Qed.

Lemma encode_R_bitSlice_idemp: forall opcode z r r0 funct3 funct7,
    bitSlice (encode_R opcode z r r0 funct3 funct7) 0 32 =
              encode_R opcode z r r0 funct3 funct7.
Proof. intros. unfold encode_R. prove_Zeq_bitwise. Qed.

Lemma encode_SB_bitSlice_idemp: forall opcode r r0 funct3 z,
    bitSlice (encode_SB opcode r r0 funct3 z) 0 32 =
              encode_SB opcode r r0 funct3 z.
Proof. intros. unfold encode_SB. prove_Zeq_bitwise. Qed.

Lemma encode_S_bitSlice_idemp: forall opcode r r0 funct3 z,
    bitSlice (encode_S opcode r r0 funct3 z) 0 32 =
              encode_S opcode r r0 funct3 z.
Proof. intros. unfold encode_S. prove_Zeq_bitwise. Qed.

Lemma encode_UJ_bitSlice_idemp: forall opcode r z,
    bitSlice (encode_UJ opcode r z) 0 32 =
              encode_UJ opcode r z.
Proof. intros. unfold encode_UJ. prove_Zeq_bitwise. Qed.

Lemma encode_U_bitSlice_idemp: forall opcode r z,
    bitSlice (encode_U opcode r z) 0 32 =
              encode_U opcode r z.
Proof. intros. unfold encode_U. prove_Zeq_bitwise. Qed.

#[global] Hint Rewrite
  encode_Fence_bitSlice_idemp
  encode_Invalid_bitSlice_idemp
  encode_I_bitSlice_idemp
  encode_I_shift_57_bitSlice_idemp
  encode_I_shift_66_bitSlice_idemp
  encode_I_system_bitSlice_idemp
  encode_R_atomic_bitSlice_idemp
  encode_R_bitSlice_idemp
  encode_SB_bitSlice_idemp
  encode_S_bitSlice_idemp
  encode_UJ_bitSlice_idemp
  encode_U_bitSlice_idemp
: encode_bitSlice_idemp.

Lemma encode_bitSlice_idemp: forall (i: Instruction),
    bitSlice (encode i) 0 32 = encode i.
Proof.
  intros.
  unfold encode.
  repeat autounfold with mappers.
  destruct i as [i|i|i|i|i|i|i|i|i|i]; [destruct i..|];
    autorewrite with encode_bitSlice_idemp;
    reflexivity.
Qed.

Lemma encode_range: forall (i: Instruction),
    0 <= encode i < 2 ^ 32.
Proof.
  intros.
  rewrite <- encode_bitSlice_idemp.
  apply bitSlice_range.
  blia.
Qed.
