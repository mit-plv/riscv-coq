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

Ltac prove_andb_false :=
  reflexivity ||
  match goal with
  | E: _ = ?t |- ?t =? _ = false => rewrite <- E; reflexivity
  end ||
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
  match goal with
  | E: _ = ?t |- ?t =? _ = true => rewrite <- E; reflexivity
  end ||
  (apply andb_true; prove_andb_true).

Goal forall b1 b2, b1 = true -> b2 = true -> true && b1 && (b2 && true) = true.
  intros. prove_andb_true.
Qed.

Ltac invert_encode :=
  match goal with
  | V: context[verify_Invalid   ] |- decode _ ?inst = _ => pose proof (invert_encode_InvalidInstruction V inst eq_refl)
  | V: context[verify_R         ] |- decode _ ?inst = _ => pose proof (invert_encode_R                  V inst eq_refl)
  | V: context[verify_I         ] |- decode _ ?inst = _ => pose proof (invert_encode_I                  V inst eq_refl)
  | V: context[verify_I_shift_57] |- decode _ ?inst = _ => pose proof (invert_encode_I_shift_57         V inst eq_refl)
  | V: context[verify_I_shift_66] |- decode _ ?inst = _ => pose proof (invert_encode_I_shift_66         V inst eq_refl)
  | V: context[verify_I_system  ] |- decode _ ?inst = _ => pose proof (invert_encode_I_system           V inst eq_refl)
  | V: context[verify_S         ] |- decode _ ?inst = _ => pose proof (invert_encode_S                  V inst eq_refl)
  | V: context[verify_SB        ] |- decode _ ?inst = _ => pose proof (invert_encode_SB                 V inst eq_refl)
  | V: context[verify_U         ] |- decode _ ?inst = _ => pose proof (invert_encode_U                  V inst eq_refl)
  | V: context[verify_UJ        ] |- decode _ ?inst = _ => pose proof (invert_encode_UJ                 V inst eq_refl)
  | V: context[verify_Fence     ] |- decode _ ?inst = _ => pose proof (invert_encode_Fence              V inst eq_refl)
  end.

Lemma pull_let: forall {A B: Type} (a: A) (b: A -> B) (c: B),
  let x := a in (b x = c) ->
  (let x := a in b x) = c.
Proof. intros. simpl. subst x. assumption. Qed.

Lemma decode_encode: forall (inst: Instruction),
  respects_bounds 64 inst ->
  decode RV64IM (encode inst) = inst.
Proof.
  intros.
  let d := eval cbv delta [decode] in decode in change decode with d.
  cbv beta.
  repeat match goal with
  | |- (let x := ?a in ?b) = ?c => cut (let x := a in (b = c));
       [apply (pull_let a (fun x => b) c) | intro]
  end.
  unfold encode in *. repeat autounfold with mappers in *.
  Time
  destruct inst; [destruct i..|reflexivity];
  try reflexivity;
  simpl in H;
  invert_encode;
  repeat match goal with
  | H: _ /\ _ |- _ => destruct H
  end.

  Focus 23.
  let d := eval cbv delta [decode] in decode in change decode with d.
  cbv beta.
  unfold decode.
{

repeat lazymatch goal with
         | |- context [if ?x then ?a else ?b] =>
           replace x with false by (symmetry; prove_andb_false) ||
           replace x with true  by (symmetry; prove_andb_true)
         end.

  lazymatch goal with
         | |- context [if ?x then ?a else ?b] =>
           replace x with true
  end.

repeat lazymatch goal with
         | |- context [if ?x then ?a else ?b] =>
           replace x with false (*by (symmetry; prove_andb_false) ||
           replace x with true  by (symmetry; prove_andb_true) *)
         end.

  
  reflexivity.
  admit.

  
symmetry.

apply andb_true.
{

  match goal with
  | E: _ = ?t |- ?t =? _ = true => rewrite <- E; reflexivity
  end.
  }

apply andb_true.
{

  match goal with
  | E: _ = ?t |- ?t =? _ = true => rewrite <- E; reflexivity
  end.
  }
{

  match goal with
  | E: _ = ?t |- ?t =? _ = true => rewrite <- E; reflexivity
  end.
  }
}


(apply andb_true; prove_andb_true).


  reflexivity ||
  assumption ||              
  match goal with
  | E: _ = ?t |- ?t =? _ = false => rewrite <- E; reflexivity
  end ||
  (apply andb_true; prove_andb_true).


prove_andb_true.

Ltac prove_andb_false2 :=
  reflexivity ||
  match goal with
  | E: _ = ?t |- ?t =? _ = false => rewrite <- E; reflexivity
  end ||
  (apply Bool.andb_false_intro1; prove_andb_false2) ||
  (apply Bool.andb_false_intro2; prove_andb_false2).


prove_andb_false2.
  
  repeat match goal with
         | |- context [if ?x then ?a else ?b] =>
           replace x with false by (symmetry; prove_andb_false) ||
           replace x with true  by (symmetry; prove_andb_true)
         end;
  try reflexivity.
{
  lazymatch goal with
         | |- context [if ?x then ?a else ?b] =>
           replace x with true
  end.
  
admit.
{ symmetry.
prove_andb_false.
Search (?b1 && ?b2 = true).

Lemma andb_true: forall b1 b2,
    b1 = true -> b2 = true -> b1 && b2 = true.
Proof. intros. subst. reflexivity. Qed.

Ltac prove_andb_true :=
  reflexivity ||
  assumption ||
  (apply andb_true; prove_andb_true).

Goal forall b1 b2, b1 = true -> b2 = true -> true && b1 && (b2 && true) = true.
  intros. prove_andb_true.
Qed.
{
match goal with
         | |- context [if ?x then ?a else ?b] =>
           replace x with true by (symmetry; prove_andb_true)
         end.
reflexivity.
Focus 16.
symmetry.
prove_andb_false2.

  cbv [List.map List.app supportsM bitwidth].
  admit. (* funct6 *)
  admit. (* funct6 *)
  admit. (* funct6 *)
  admit. (* sfence_vm *)
  (* and 4 left because of Csr typos *)

Abort.
