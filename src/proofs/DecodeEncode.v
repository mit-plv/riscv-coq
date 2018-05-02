Require Import Coq.ZArith.BinInt.
Require Import bbv.Word.
Require Import riscv.Decode.
Require Import riscv.encode.Encode.
Require Import riscv.Utility.

Local Open Scope bool_scope.
Local Open Scope Z_scope.

Lemma invert_encode_InvalidInstruction: forall i,
  verify_Invalid i ->
  forall inst,
  encode_Invalid i = inst ->
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

Lemma invert_encode_I_shift_57: forall {opcode rd rs1 shamt5 funct3 funct7},
  verify_I_shift_57 opcode rd rs1 shamt5 funct3 funct7 ->
  forall inst,
  encode_I_shift_57 opcode rd rs1 shamt5 funct3 funct7 = inst ->
  opcode = bitSlice inst 0 7 /\
  funct3 = bitSlice inst 12 15 /\
  funct7 = bitSlice inst 25 32 /\
  rd = bitSlice inst 7 12 /\
  rs1 = bitSlice inst 15 20 /\
  shamt5 = bitSlice inst 20 25.
Proof. Admitted.

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
  simm12 = signExtend 12 (Z.shiftl (bitSlice inst 25 32) 5 <|> bitSlice inst 7 12).
Proof. Admitted.

Lemma invert_encode_SB: forall {opcode rs1 rs2 funct3 sbimm12},
  verify_SB opcode rs1 rs2 funct3 sbimm12 ->
  forall inst,
  encode_SB opcode rs1 rs2 funct3 sbimm12 = inst ->
  opcode = bitSlice inst 0 7 /\
  funct3 = bitSlice inst 12 15 /\
  rs1 = bitSlice inst 15 20 /\
  rs2 = bitSlice inst 20 25 /\
  sbimm12 = signExtend 13 (Z.shiftl (bitSlice inst 31 32) 12 <|>
                           Z.shiftl (bitSlice inst 25 31) 5 <|>
                           Z.shiftl (bitSlice inst 8 12) 1  <|>
                           Z.shiftl (bitSlice inst 7 8) 11).
Proof. Admitted.

Lemma invert_encode_U: forall {opcode rd imm20},
  verify_U opcode rd imm20 ->
  forall inst,
  encode_U opcode rd imm20 = inst ->
  opcode = bitSlice inst 0 7 /\
  rd = bitSlice inst 7 12 /\
  imm20 = signExtend 32 (Z.shiftl (bitSlice inst 12 32) 12).
Proof. Admitted.

Lemma invert_encode_UJ: forall {opcode rd jimm20},
  verify_UJ opcode rd jimm20 ->
  forall inst,
  encode_UJ opcode rd jimm20 = inst ->
  opcode = bitSlice inst 0 7 /\
  rd = bitSlice inst 7 12 /\
  jimm20 = signExtend 21 (Z.shiftl (bitSlice inst 31 32) 20  <|>
                          Z.shiftl (bitSlice inst 21 31) 1  <|>
                          Z.shiftl (bitSlice inst 20 21) 11 <|>
                          Z.shiftl (bitSlice inst 12 20) 12).
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

Ltac prove_andb_false :=
  reflexivity ||
  assumption ||
  (symmetry; assumption) ||
  (apply Bool.andb_false_intro1; prove_andb_false) ||
  (apply Bool.andb_false_intro2; prove_andb_false).
  
Goal forall b1 b3 b4 b5, b1 && false && b3 && b4 && b5 = false. intros. prove_andb_false. Qed.
Goal forall b1 b2 b4 b5, b1 && (b2 && false) && b4 && b5 = false. intros. prove_andb_false. Qed.
Goal forall b1 b3 b4 b5, (b1 && (false && b3) && b4) && b5 = false. intros. prove_andb_false. Qed.

Lemma andb_true: forall b1 b2,
    b1 = true -> b2 = true -> b1 && b2 = true.
Proof. intros. subst. reflexivity. Qed.

Ltac prove_andb_true :=
  reflexivity ||
  assumption ||
  (symmetry; assumption) ||
  (apply andb_true; prove_andb_true).

Goal forall b1 b2, b1 = true -> b2 = true -> true && b1 && (b2 && true) = true.
  intros. prove_andb_true.
Qed.

Ltac invert_encode :=
  match goal with
  | V: context[verify_Invalid   ], H: _ |- _ => pose proof (invert_encode_InvalidInstruction V _ H)
  | V: context[verify_R         ], H: _ |- _ => pose proof (invert_encode_R                  V _ H)
  | V: context[verify_I         ], H: _ |- _ => pose proof (invert_encode_I                  V _ H)
  | V: context[verify_I_shift_57], H: _ |- _ => pose proof (invert_encode_I_shift_57         V _ H)
  | V: context[verify_I_shift_66], H: _ |- _ => pose proof (invert_encode_I_shift_66         V _ H)
  | V: context[verify_I_system  ], H: _ |- _ => pose proof (invert_encode_I_system           V _ H)
  | V: context[verify_S         ], H: _ |- _ => pose proof (invert_encode_S                  V _ H)
  | V: context[verify_SB        ], H: _ |- _ => pose proof (invert_encode_SB                 V _ H)
  | V: context[verify_U         ], H: _ |- _ => pose proof (invert_encode_U                  V _ H)
  | V: context[verify_UJ        ], H: _ |- _ => pose proof (invert_encode_UJ                 V _ H)
  | V: context[verify_Fence     ], H: _ |- _ => pose proof (invert_encode_Fence              V _ H)
  end.


Lemma pull_let: forall {A B: Type} (a: A) (b: A -> B) (c: B),
  let x := a in (b x = c) ->
  (let x := a in b x) = c.
Proof. intros. simpl. subst x. assumption. Qed.

Lemma decode_encode: forall (inst: Instruction) (z: Z),
    respects_bounds 64 inst ->
    encode inst = z ->
    decode RV64IM z = inst.
Proof.
  intros.
  let d := eval cbv delta [decode] in decode in change decode with d.
  cbv beta.
  repeat match goal with
  | |- (let x := ?a in ?b) = ?c => cut (let x := a in (b = c));
       [apply (pull_let a (fun x => b) c) | intro]
  end.
  repeat match goal with
  | x := ?t : ?T |- _ => assert (x = t) by (subst x; reflexivity); clearbody x
  end.
  unfold encode in *. repeat autounfold with mappers in *.
  destruct inst;  [destruct i..|subst; exfalso; assumption];
  try reflexivity;
  try (time (
  simpl in H;
  invert_encode;
  try (exfalso; assumption);
  repeat match goal with
         | H: _ /\ _ |- _ =>
           let E := fresh "E" in
           destruct H as [E H];
           rewrite <- E in *;
           clear E;
           try (rewrite <- H in *; clear H)
  end;
  subst;
  repeat lazymatch goal with
         | |- context [if (?x && ?y) then ?a else ?b] =>
           (replace (x && y) with false by (symmetry; prove_andb_false)) ||
           (replace (x && y) with true  by (symmetry; prove_andb_true))
         end;
  (reflexivity || (idtac "Failed to solve:"; match goal with
                   | |- ?G => idtac G
                   end))
  )).
Time Qed.
