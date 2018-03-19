Require Import Coq.ZArith.BinInt.
Require Import bbv.Word.
Require Import riscv.util.Decidable.
Require Import riscv.Decode.
Require Import riscv.encode.Encode.
Require Import riscv.Utility.

Local Open Scope bool_scope.
Local Open Scope Z_scope.

Lemma invert_encode_InvalidInstruction:
  verify_Invalid ->
  forall inst,
  encode_Invalid = inst ->
  False.
Proof. intros. assumption. Qed.

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
Proof. Admitted.

Lemma invert_encode_I: forall {opcode rd rs1 funct3 oimm12},
  verify_I opcode rd rs1 funct3 oimm12 ->
  forall inst,
  encode_I opcode rd rs1 funct3 oimm12 = inst ->
  opcode = bitSlice inst 0 7 /\
  funct3 = bitSlice inst 12 15 /\
  rd = bitSlice inst 7 12 /\
  rs1 = bitSlice inst 15 20 /\
  oimm12 = signExtend 12 (bitSlice inst 20 32).
Proof. Admitted.

Lemma invert_encode_I_shift: forall {opcode rd rs1 shamt5 funct3 funct7},
  verify_I_shift opcode rd rs1 shamt5 funct3 funct7 ->
  forall inst,
  encode_I_shift opcode rd rs1 shamt5 funct3 funct7 = inst ->
  opcode = bitSlice inst 0 7 /\
  funct3 = bitSlice inst 12 15 /\
  funct7 = bitSlice inst 25 32 /\
  rd = bitSlice inst 7 12 /\
  rs1 = bitSlice inst 15 20 /\
  shamt5 = bitSlice inst 20 25.
Proof. Admitted.

Lemma invert_encode_I_system: forall {opcode rd rs1 funct3 funct12},
  verify_I_system opcode rd rs1 funct3 funct12 ->
  forall inst,
  encode_I_system opcode rd rs1 funct3 funct12 = inst ->
  opcode = bitSlice inst 0 7 /\
  funct3 = bitSlice inst 12 15 /\
  funct12 = bitSlice inst 20 32 /\
  rd = bitSlice inst 7 12 /\
  rs1 = bitSlice inst 15 20.
Proof. Admitted.

Lemma invert_encode_S: forall {opcode rs1 rs2 funct3 simm12},
  verify_S opcode rs1 rs2 funct3 simm12 ->
  forall inst,
  encode_S opcode rs1 rs2 funct3 simm12 = inst ->
  opcode = bitSlice inst 0 7 /\
  funct3 = bitSlice inst 12 15 /\
  rs1 = bitSlice inst 15 20 /\
  rs2 = bitSlice inst 20 25 /\
  simm12 = signExtend 12 (shift (bitSlice inst 25 32) 5 <|> bitSlice inst 7 12).
Proof. Admitted.

Lemma invert_encode_SB: forall {opcode rs1 rs2 funct3 sbimm12},
  verify_SB opcode rs1 rs2 funct3 sbimm12 ->
  forall inst,
  encode_SB opcode rs1 rs2 funct3 sbimm12 = inst ->
  opcode = bitSlice inst 0 7 /\
  funct3 = bitSlice inst 12 15 /\
  rs1 = bitSlice inst 15 20 /\
  rs2 = bitSlice inst 20 25 /\
  sbimm12 = signExtend 13 (shift (bitSlice inst 31 32) 12 <|>
                           shift (bitSlice inst 25 31) 5 <|>
                           shift (bitSlice inst 8 12) 1  <|>
                           shift (bitSlice inst 7 8) 11).
Proof. Admitted.

Lemma invert_encode_U: forall {opcode rd imm20},
  verify_U opcode rd imm20 ->
  forall inst,
  encode_U opcode rd imm20 = inst ->
  opcode = bitSlice inst 0 7 /\
  rd = bitSlice inst 7 12 /\
  imm20 = signExtend 32 (shift (bitSlice inst 12 32) 12).
Proof. Admitted.

Lemma invert_encode_UJ: forall {opcode rd jimm20},
  verify_UJ opcode rd jimm20 ->
  forall inst,
  encode_UJ opcode rd jimm20 = inst ->
  opcode = bitSlice inst 0 7 /\
  rd = bitSlice inst 7 12 /\
  jimm20 = signExtend 21 (shift (bitSlice inst 31 32) 20  <|>
                                shift (bitSlice inst 21 31) 1  <|>
                                shift (bitSlice inst 20 21) 11 <|>
                                shift (bitSlice inst 12 20) 12).
Proof. Admitted.

Lemma invert_encode_Fence: forall {opcode rd rs1 funct3 prd scc msb4},
  verify_Fence opcode rd rs1 funct3 prd scc msb4 ->
  forall inst,
  encode_Fence opcode rd rs1 funct3 prd scc msb4 = inst ->
  opcode = bitSlice inst 0 7 /\
  funct3 = bitSlice inst 12 15 /\
  rd = bitSlice inst 7 12 /\
  rs1 = bitSlice inst 15 20 /\
  scc = bitSlice inst 20 24 /\
  prd = bitSlice inst 24 28 /\
  msb4 = bitSlice inst 28 32.
Proof. Admitted.

(*
Lemma simpl_dec_and_eq: forall (a: Z) (P: bool) (T: Type) (e1 e2 e3: T),
  (if P then e1 else e2) = e3 ->
  (if (a =? a) && P then e1 else e2) = e3.
Proof.
  intros. rewrite Z.eqb_refl. rewrite Bool.andb_true_l. assumption.
Qed.

Lemma simpl_dec_final_eq: forall (a: Z) (T: Type) (e1 e2 e3: T),
  e1 = e3 ->
  (if a =? a then e1 else e2) = e3.
Proof.
  intros. rewrite Z.eqb_refl. assumption.
Qed.

Lemma simpl_dec_and_neq: forall (a1 a2: Z) (P: bool) (T: Type) (e1 e2 e3: T),
  a1 <> a2 ->
  e2 = e3 ->
  (if (a1 =? a2) && P then e1 else e2) = e3.
Proof.
  intros. destruct (a1 =? a2) eqn: F.
  + apply Z.eqb_eq in F. contradiction.
  + simpl. assumption.
Qed.

Lemma simpl_dec_and_neq_2: forall (T: Type) (a1 a2: Z) (P1 P2: bool) (e1 e2 e3: T),
  a1 <> a2 ->
  e2 = e3 ->
  (if P1 && ((a1 =? a2) && P2) then e1 else e2) = e3.
Proof.
  intros. destruct (a1 =? a2) eqn: F.
  + apply Z.eqb_eq in F. contradiction.
  + rewrite Bool.andb_comm. simpl. assumption.
Qed.

Lemma simpl_dec_final_neq: forall (a1 a2: Z) (T: Type) (e1 e2 e3: T),
  a1 <> a2 ->
  e2 = e3 ->
  (if a1 =? a2 then e1 else e2) = e3.
Proof.
  intros. destruct (a1 =? a2) eqn: F.
  + apply Z.eqb_eq in F. contradiction.
  + assumption.
Qed.
*)

Ltac prove_andb_false :=
  repeat (reflexivity || apply Bool.andb_false_r || apply Bool.andb_false_intro1).

Goal forall b1 b3 b4 b5, b1 && false && b3 && b4 && b5 = false. intros. prove_andb_false. Qed.

Lemma decode_encode: forall (inst: Instruction),
  respects_bounds inst ->
  decode 64 (encode inst) = inst.
Proof.
  intros. unfold encode. repeat autounfold with mappers.
  Time
  destruct inst;
  try reflexivity;
  simpl in H;
  match goal with
  | |- decode _ ?inst = _ =>
          try pose proof (invert_encode_InvalidInstruction H inst eq_refl);
          try pose proof (invert_encode_R H inst eq_refl);
          try pose proof (invert_encode_I H inst eq_refl);
          try pose proof (invert_encode_I_shift H inst eq_refl);
          try pose proof (invert_encode_I_system H inst eq_refl);
          try pose proof (invert_encode_S H inst eq_refl);
          try pose proof (invert_encode_SB H inst eq_refl);
          try pose proof (invert_encode_U H inst eq_refl);
          try pose proof (invert_encode_UJ H inst eq_refl);
          try pose proof (invert_encode_Fence H inst eq_refl)
  end;
  repeat match goal with
  | H: _ /\ _ |- _ => destruct H
  end;
  unfold decode;
  repeat match goal with
  | E: _ = ?x |- context [?x] => rewrite <- E
  end;
  repeat match goal with
         | |- (if ?x then ?a else ?b) = ?c =>
           replace x with false by (symmetry; prove_andb_false)
         end;
  try reflexivity.
  admit. (* funct6 *)
  admit. (* funct6 *)
  admit. (* funct6 *)
  admit. (* sfence_vm *)
  (* and 4 left because of Csr typos *)

Abort.
