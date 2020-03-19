Require Import Coq.ZArith.BinInt.
Require Import riscv.Utility.Encode.
Require Import coqutil.Z.BitOps.
Require Import coqutil.Z.prove_Zeq_bitwise.

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
  true = ((Z.eqb (bitSlice inst 25 26) 0) || (Z.eqb bitwidth 64)).
Proof.
  intros. unfold encode_I_shift_66, verify_I_shift_66 in *.
  assert ((true = (bitSlice inst 25 26 =? 0)%Z || (bitwidth =? 64)%Z)
          <-> (bitSlice inst 25 26 =? 0)%Z = true \/ (bitwidth =? 64)%Z = true) as E. {
    split; intro.
    - rewrite <- Bool.orb_true_iff. congruence.
    - symmetry. rewrite Bool.orb_true_iff. assumption.
  }
  rewrite E.
  rewrite? Z.eqb_eq.
  (intuition idtac); prove_Zeq_bitwise.
Qed.
