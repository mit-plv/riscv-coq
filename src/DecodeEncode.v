Require Import Coq.ZArith.BinInt.
Require Import bbv.Word.
Require Import riscv.Decidable.
Require Import riscv.Decode.
Require Import riscv.Encode.

Local Open Scope Z_scope.

Lemma invert_encode_InvalidInstruction: forall (inst: word 32),
  None = Some inst -> False.
Proof. intros. discriminate H. Qed.

Lemma invert_encode_R: forall opcode rd rs1 rs2 funct3 funct7 inst,
  encode_R opcode rd rs1 rs2 funct3 funct7 = Some inst ->
  opcode = bitSlice' inst 0 7 /\
  funct3 = bitSlice' inst 12 15 /\
  funct7 = bitSlice' inst 25 32 /\
  rd = bitSlice' inst 7 12 /\
  rs1 = bitSlice' inst 15 20 /\
  rs2 = bitSlice' inst 20 25.
Proof. Admitted.

Lemma invert_encode_I: forall opcode rd rs1 funct3 oimm12 inst,
  encode_I opcode rd rs1 funct3 oimm12 = Some inst ->
  - 2 ^ 11 <= oimm12 < 2 ^ 11 /\
  opcode = bitSlice' inst 0 7 /\
  funct3 = bitSlice' inst 12 15 /\
  rd = bitSlice' inst 7 12 /\
  rs1 = bitSlice' inst 15 20 /\
  oimm12 = signExtend 12 (bitSlice inst 20 32).
Proof. Admitted.

Lemma invert_encode_I_shift: forall opcode rd rs1 shamt5 funct3 funct7 inst,
  encode_I_shift opcode rd rs1 shamt5 funct3 funct7 = Some inst ->
  (shamt5 < 32)%nat /\
  opcode = bitSlice' inst 0 7 /\
  funct3 = bitSlice' inst 12 15 /\
  funct7 = bitSlice' inst 25 32 /\
  rd = bitSlice' inst 7 12 /\
  rs1 = bitSlice' inst 15 20 /\
  shamt5 = wordToNat (bitSlice inst 20 25).
Proof. Admitted.

Lemma invert_encode_I_system: forall opcode rd rs1 funct3 funct12 inst,
  encode_I_system opcode rd rs1 funct3 funct12 = Some inst ->
  opcode = bitSlice' inst 0 7 /\
  funct3 = bitSlice' inst 12 15 /\
  funct12 = bitSlice' inst 20 32 /\
  rd = bitSlice' inst 7 12 /\
  rs1 = bitSlice' inst 15 20.
Proof. Admitted.

Lemma invert_encode_S(opcode: word 7)(rs1 rs2: word 5)(funct3: word 3)(simm12: Z)(inst: word 32):
  encode_S opcode rs1 rs2 funct3 simm12 = Some inst ->
  - 2 ^ 11 <= simm12 < 2 ^ 11 /\
  opcode = bitSlice' inst 0 7 /\
  funct3 = bitSlice' inst 12 15 /\
  rs1 = bitSlice' inst 15 20 /\
  rs2 = bitSlice' inst 20 25 /\
  simm12 = signExtend 12 (shift (bitSlice inst 25 32) 5 <|> bitSlice inst 7 12).
Proof. Admitted.

Lemma invert_encode_SB(opcode: word 7)(rs1 rs2: word 5)(funct3: word 3)(sbimm12: Z)(inst: word 32):
  encode_SB opcode rs1 rs2 funct3 sbimm12 = Some inst ->
  - 2 ^ 12 <= sbimm12 < 2 ^ 12 /\ sbimm12 mod 2 = 0 /\
  opcode = bitSlice' inst 0 7 /\
  funct3 = bitSlice' inst 12 15 /\
  rs1 = bitSlice' inst 15 20 /\
  rs2 = bitSlice' inst 20 25 /\
  sbimm12 = signExtend 13 (shift (bitSlice inst 31 32) 12 <|>
                           shift (bitSlice inst 25 31) 5 <|>
                           shift (bitSlice inst 8 12) 1  <|>
                           shift (bitSlice inst 7 8) 11).
Proof. Admitted.

Lemma invert_encode_U(opcode: word 7)(rd: word 5)(imm20: Z)(inst: word 32):
  encode_U opcode rd imm20 = Some inst ->
  - 2 ^ 31 <= imm20 < 2 ^ 31 /\ imm20 mod 2 ^ 12 = 0 /\
  opcode = bitSlice' inst 0 7 /\
  rd = bitSlice' inst 7 12 /\
  imm20 = signExtend 32 (shift (bitSlice inst 12 32) 12).
Proof. Admitted.

Lemma invert_encode_UJ(opcode: word 7)(rd: word 5)(jimm20: Z)(inst: word 32):
  encode_UJ opcode rd jimm20 = Some inst ->
  - 2 ^ 20 <= jimm20 < 2 ^ 20 /\ jimm20 mod 2 = 0 /\
  opcode = bitSlice' inst 0 7 /\
  rd = bitSlice' inst 7 12 /\
  jimm20 = signExtend 21 (shift (bitSlice inst 31 32) 20  <|>
                                shift (bitSlice inst 21 31) 1  <|>
                                shift (bitSlice inst 20 21) 11 <|>
                                shift (bitSlice inst 12 20) 12).
Proof. Admitted.

Lemma simpl_dec_and_eq: forall (A: Type) (a: A) (P: Prop) (T: Type) (e1 e2 e3: T) da dP,
  (if @dec P dP then e1 else e2) = e3 ->
  (if @dec_and (a = a) P da dP then e1 else e2) = e3.
Proof.
  intros. destruct da; [|contradiction]. destruct (@dec P dP) eqn: E.
  - unfold dec_and. unfold dec in E. rewrite E. assumption.
  - unfold dec_and. unfold dec in E. rewrite E. assumption.
Qed.

Lemma simpl_dec_final_eq: forall (A: Type) (a: A) (T: Type) (e1 e2 e3: T) da,
  e1 = e3 ->
  (if @dec (a = a) da then e1 else e2) = e3.
Proof.
  intros. unfold dec. destruct da; [|contradiction]. assumption.
Qed.

Lemma simpl_dec_and_neq: forall (A: Type) (a1 a2: A) (P: Prop) (T: Type) (e1 e2 e3: T) da dP,
  a1 <> a2 ->
  e2 = e3 ->
  (if @dec_and (a1 = a2) P da dP then e1 else e2) = e3.
Proof.
  intros. destruct da; [contradiction|]. destruct (@dec P dP) eqn: E.
  - unfold dec_and. unfold dec in E. rewrite E. assumption.
  - unfold dec_and. unfold dec in E. rewrite E. assumption.
Qed.

Lemma simpl_dec_and_neq_2: forall (A T: Type) (a1 a2: A) (P1 P2: Prop) (e1 e2 e3: T) da dP1 dP2,
  a1 <> a2 ->
  e2 = e3 ->
  (if @dec_and P1 (a1 = a2 /\ P2) dP1 (@dec_and (a1 = a2) P2 da dP2) then e1 else e2) = e3.
Proof.
  intros. destruct da; [contradiction|]. destruct (@dec P1 dP1) eqn: E.
  - unfold dec_and. unfold dec in E. rewrite E. destruct dP2 eqn: E2; assumption.
  - unfold dec_and. unfold dec in E. rewrite E. destruct dP2 eqn: E2; assumption.
Qed.

Lemma simpl_dec_final_neq: forall (A: Type) (a1 a2: A) (T: Type) (e1 e2 e3: T) da,
  a1 <> a2 ->
  e2 = e3 ->
  (if @dec (a1 = a2) da then e1 else e2) = e3.
Proof.
  intros. unfold dec. destruct da; [contradiction|]. assumption.
Qed.

Ltac deep_destruct_and H :=
  lazymatch type of H with
  | _ /\ _ => let H' := fresh H in destruct H as [H' H]; deep_destruct_and H'; deep_destruct_and H
  | _ => idtac
  end.

Set Ltac Profiling.

Lemma decode_encode: forall (inst: Instruction) (w: word 32),
  encode inst = Some w ->
  decode w = inst.
Proof.
  intros.
  let d := eval cbv delta [decode] in decode in change decode with d.
  cbv beta zeta.
  destruct inst;
  let force_evaluation_order_dummy := constr:(0) in time (
  tryif (solve [ abstract (
    unfold encode in H;
    first
    [ apply invert_encode_R in H
    | apply invert_encode_I in H
    | apply invert_encode_I_shift in H
    | apply invert_encode_I_system in H
    | apply invert_encode_S in H
    | apply invert_encode_SB in H
    | apply invert_encode_U in H
    | apply invert_encode_UJ in H
    | apply invert_encode_InvalidInstruction in H; contradiction H ];
    deep_destruct_and H;
    repeat match goal with
    | v: _ |- _ => subst v
    end;
    repeat match goal with
    | E: _ = _ |- _ => rewrite <- E
    end;
    repeat (
       (apply simpl_dec_and_neq; [
        match goal with
        | |- ?x <> ?y => unfold x, y; intro C; discriminate C
        end | ])
    || (apply simpl_dec_and_neq_2; [
        match goal with
        | |- ?x <> ?y => unfold x, y; intro C; discriminate C
        end | ])
    || (apply simpl_dec_final_neq; [
        match goal with
        | |- ?x <> ?y => unfold x, y; intro C; discriminate C
        end | ])
    || (apply simpl_dec_and_eq)
    || (apply simpl_dec_final_eq; reflexivity))
  )]) then (
    idtac "subgoal solved"
  ) else (
    match goal with
    | |- ?G => fail 100 "subgoal not solved:" G
    end
  )).
Time Qed.

Show Ltac Profile.
