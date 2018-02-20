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
  rs2 = bitSlice' inst 20 25.
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

(*
Hint Unfold encode_R encode_I encode_I_shift encode_I_system encode_S encode_SB encode_U encode_UJ :
  unfold_encode_helpers.

Lemma Some_inj: forall {A: Type} (a1 a2: A), Some a1 = Some a2 -> a1 = a2.
Proof. intros. inversion H. reflexivity. Qed.
*)

Lemma pull_let: forall {A B: Type} (a: A) (b: A -> B) (c: B),
  let x := a in (b x = c) ->
  (let x := a in b x) = c.
Proof. intros. simpl. subst x. assumption. Qed.

(*
Lemma get_opcode_I: forall (opcode: word 7) (funct3: word 3) (rd rs1: word 5) (oimm12: word 12),
  opcode = bitSlice' (combine (combine (combine (combine
              opcode rd) funct3) rs1) oimm12) 0 7.
Proof.
  intros. unfold bitSlice'. simpl. unfold split_middle, split_upper, split_lower.
  unfold id.
Admitted.

Lemma get_funct3_I: forall (opcode: word 7) (funct3: word 3) (rd rs1: word 5) (oimm12: word 12),
  funct3 = bitSlice' (combine (combine (combine (combine
              opcode rd) funct3) rs1) oimm12) 12 15.
Proof.
  intros. unfold bitSlice'. simpl. unfold split_middle, split_upper, split_lower.
  unfold id.
Admitted.
*)

  (*
Lemma decode_encode: forall (inst: Instruction) (w: word 32),
  encode inst = Some w ->
  decode w = inst.
Proof.
  intros. destruct inst; simpl in *; try discriminate;
  autounfold with unfold_encode_helpers in *;
  lazymatch goal with
  | H: context [ @dec ?P ?D ] |- _ => destruct (@dec P D); [|discriminate]
  | _ => idtac
  end;
  apply Some_inj in H;
  subst w.
  let d := eval cbv delta [decode] in decode in change decode with d.
  cbv beta.
- repeat match goal with
  | |- (let x := ?a in ?b) = ?c => cut (let x := a in (b = c));
       [apply (pull_let a (fun x => b) c) | intro]
  end.
  Admitted.
  evar (oc: word 7).
  replace opcode with oc by (subst oc opcode; apply get_opcode_I).
  subst oc opcode.
  evar (f3: word 3).
  replace funct3 with f3 by (subst f3 funct3; apply get_funct3_I).
  subst f3 funct3.
  lazymatch goal with
  | |- (if ?A then ?B else ?C) = ?D =>
     let r := eval hnf in A in
     change ((if r then B else C) = D);
     cbv beta iota
  end.
  f_equal; clear -a.
  + admit.
  + admit.
  + admit.
-
Admitted.
*)

Lemma simpl_dec_and_eq: forall (A: Type) (a: A) (P: Prop) (T: Type) (e1 e2 e3: T) da dP,
  (if @dec P dP then e1 else e2) = e3 ->
  (if @dec_and (a = a) P da dP then e1 else e2) = e3.
Proof.
  intros. destruct da; [|contradiction]. destruct (@dec P dP) eqn: E.
  - unfold dec_and. unfold dec in E. rewrite E. assumption.
  - unfold dec_and. unfold dec in E. rewrite E. assumption.
Qed.

Lemma simpl_dec_and_eq_final: forall (A: Type) (a: A) (T: Type) (e1 e2 e3: T) da,
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

Ltac deep_destruct_and H :=
  lazymatch type of H with
  | _ /\ _ => let H' := fresh H in destruct H as [H' H]; deep_destruct_and H'; deep_destruct_and H
  | _ => idtac
  end.

Lemma decode_encode: forall (inst: Instruction) (w: word 32),
  encode inst = Some w ->
  decode w = inst.
Proof.
  intros.
  let d := eval cbv delta [decode] in decode in change decode with d.
  cbv beta.
  repeat match goal with
  | |- (let x := ?a in ?b) = ?c => cut (let x := a in (b = c));
       [apply (pull_let a (fun x => b) c) | intro]
  end.
  repeat match goal with
    | v: if _ then _ else _ |- _ => progress compute in (type of v)
  end.
  destruct inst; time (
  tryif (solve [
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
      || apply simpl_dec_and_eq
      || (apply simpl_dec_and_eq_final; reflexivity))
  ]) then (
    idtac "subgoal solved"
  ) else (
    match goal with
    | |- ?G => idtac "subgoal not solved:" G
    end
  )).
Qed.
