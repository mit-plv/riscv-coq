Require Import Coq.ZArith.BinInt.
Require Import bbv.Word.
Require Import riscv.Decidable.
Require Import riscv.Decode.
Require Import riscv.Encode.

Hint Unfold encode_R encode_I encode_I_shift encode_I_system encode_S encode_SB encode_U encode_UJ :
  unfold_encode_helpers.

Lemma Some_inj: forall {A: Type} (a1 a2: A), Some a1 = Some a2 -> a1 = a2.
Proof. intros. inversion H. reflexivity. Qed.

Lemma pull_let: forall {A B: Type} (a: A) (b: A -> B) (c: B),
  let x := a in (b x = c) ->
  (let x := a in b x) = c.
Proof. intros. simpl. subst x. assumption. Qed.

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


(*
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
  destruct inst.
  - discriminate H.
  - simpl in H; autounfold with unfold_encode_helpers in H.
  lazymatch goal with
  | H: context [ @dec ?P ?D ] |- _ => destruct (@dec P D); [|discriminate]
  | _ => idtac
  end;
  apply Some_inj in H.

Abstracting over term s leads to blah error
*)