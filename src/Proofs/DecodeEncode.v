Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List. Import ListNotations.
Require Import riscv.Spec.Decode.
Require Import riscv.Utility.Encode.
Require Import riscv.Utility.Utility.
Require Import riscv.Utility.Tactics.
Require Import riscv.Utility.div_mod_to_quot_rem.
Require Import riscv.Proofs.invert_encode_R.
Require Import riscv.Proofs.invert_encode_R_atomic.
Require Import riscv.Proofs.invert_encode_I.
Require Import riscv.Proofs.invert_encode_I_shift_57.
Require Import riscv.Proofs.invert_encode_I_shift_66.
Require Import riscv.Proofs.invert_encode_I_system.
Require Import riscv.Proofs.invert_encode_S.
Require Import riscv.Proofs.invert_encode_SB.
Require Import riscv.Proofs.invert_encode_U.
Require Import riscv.Proofs.invert_encode_UJ.
Require Import riscv.Proofs.invert_encode_Fence.
Require Import riscv.Proofs.invert_encode_FenceI.

Local Open Scope bool_scope.
Local Open Scope Z_scope.


Ltac somega_pre :=
  rewrite? bitSlice_alt in * by omega; unfold bitSlice' in *;
  repeat (so fun hyporgoal => match hyporgoal with
  | context [signExtend ?l ?n] =>
      let E := fresh "E" in
      destruct (signExtend_alt' l n) as [[? [? E]] | [? [? E]]];
      [ omega | rewrite E in *; clear E .. ]
  end);
  rewrite? Z.shiftl_mul_pow2 in * by omega;
  repeat (so fun hyporgoal => match hyporgoal with
     | context [2 ^ ?x] => let r := eval cbv in (2 ^ x) in change (2 ^ x) with r in *
  end);
  div_mod_to_quot_rem;
  repeat match goal with
         | z: ?T |- _ => progress change T with Z in *
         end.

(* omega which understands bitSlice and shift *)
Ltac somega := somega_pre; omega.

Lemma invert_encode_InvalidInstruction: forall i,
  verify_Invalid i ->
  forall inst,
  encode_Invalid i = inst ->
  False.
Proof. intros. assumption. Qed.

Ltac invert_encode :=
  match goal with
  | E: _, V: _ |- _ => case (invert_encode_InvalidInstruction _ V _ E)
  | E: _, V: _ |- _ => pose proof (invert_encode_I V _ E); clear E V
  | E: _, V: _ |- _ => pose proof (invert_encode_Fence V _ E); clear E V
  | E: _, V: _ |- _ => pose proof (invert_encode_FenceI V _ E); clear E V
  | E: _, V: _ |- _ => pose proof (invert_encode_I_shift_66 V _ E); clear E V
  | E: _, V: _ |- _ => pose proof (invert_encode_I_shift_57 V _ E); clear E V
  | E: _, V: _ |- _ => pose proof (invert_encode_R V _ E); clear E V
  | E: _, V: _ |- _ => pose proof (invert_encode_R_atomic V _ E); clear E V
  | E: _, V: _ |- _ => pose proof (invert_encode_I_system V _ E); clear E V
  | E: _, V: _ |- _ => pose proof (invert_encode_U V _ E); clear E V
  | E: _, V: _ |- _ => pose proof (invert_encode_UJ V _ E); clear E V
  | E: _, V: _ |- _ => pose proof (invert_encode_S V _ E); clear E V
  | E: _, V: _ |- _ => pose proof (invert_encode_SB V _ E); clear E V
  end.

Ltac lets_to_eqs :=
  repeat lazymatch goal with
         | |- (let x := ?a in ?b) = ?c =>
           change (let x := a in b = c); intro
         | x := bitSlice _ 25 26 |- _ =>
           (* shamtHi is the only field which another field depends on *)
           subst x
         | x := ?t : ?T |- _ =>
           pose proof (eq_refl t : x = t); clearbody x
         end.

Ltac subst_lets_from_encode_inversion :=
  let substlets HencPart :=
      match type of HencPart with
      | ?x = ?rhs =>
        repeat match goal with
               | HLet: ?y = rhs |- _  =>
                 assert_fails (constr_eq x y);
                 replace y with x in * by
                     exact (eq_trans HencPart (eq_sym HLet));
                 idtac y HLet;
                 clear HLet y
               end
      end in
  let Henc := lazymatch goal with Henc: _ /\ _ |- _ => Henc end in
  repeat match type of Henc with
         |  _ /\ _ => let H := fresh "H" in destruct Henc as [H Henc]; substlets H
         end;
  substlets Henc.

Ltac bitSlice_boundary_mismatch_case :=
  subst;
  repeat match goal with
         | |- context [?a =?  _] => unfold a
         | |- context [_  =? ?a] => unfold a
         end;
  repeat match goal with
         | |- ?x = ?x => exact_no_check (eq_refl x)
         | |- context [?x =? ?y] =>
           let H := fresh "H" in
           destruct (x =? y) eqn:H;
           apply Z.eqb_eq in H || apply Z.eqb_neq in H
         | _ => progress cbn in *
         end;
  try (intuition discriminate);
  try solve [ exfalso;
              try (match goal with H: _ <> _ |- _ => apply H; clear H end);
              somega ].

Ltac simpl_ifs_in H :=
  match type of H with
  | @eq (list _) _ _ => fail 1
  | _ => idtac
  end;
  repeat match type of H with
         | ?d = (if ?b then ?x else ?y) => change (d = y) in H
         end;
  try match type of H with
      | ?d = (if ?b then ?x else ?y) => change (d = x) in H
      end.

Ltac prove_decode_encode :=
  let inst := fresh "inst" in let iset := fresh "iset" in let V := fresh "V" in
  intros inst iset V; unfold verify in V; destruct V;
  unfold verify_iset in *;
  let Henc := fresh "Henc" in
  match goal with
  | |- ?D ?I (encode ?x) = _ =>
    remember (encode x) as encoded eqn:Henc; symmetry in Henc
  end;
  cbv [ encode
        Encoder
        Verifier
        apply_InstructionMapper
        map_Fence
        map_FenceI
        map_I
        map_I_shift_57
        map_I_shift_66
        map_I_system
        map_Invalid
        map_R
        map_R_atomic
        map_S
        map_SB
        map_U
        map_UJ
    ] in Henc;
  match goal with
  | |- ?D ?I _ = _ => cbv beta delta [D]
  end;
  destruct inst;
  invert_encode;
  lets_to_eqs;
  subst_lets_from_encode_inversion;
  repeat match goal with
         | H: _ |- _ => progress simpl_ifs_in H
         end;
  first [ subst; reflexivity
        | destruct iset; subst; reflexivity
        | idtac ].

Lemma decodeI_encode: forall (inst: InstructionI) (iset: InstructionSet),
    verify (IInstruction inst) iset ->
    decode iset (encode (IInstruction inst)) = IInstruction inst.
Proof.
  Time prove_decode_encode.
Time Qed.

(*
Lemma decodeI_encode: forall (inst: InstructionI) (iset: InstructionSet),
    verify (IInstruction inst) iset ->
    decode iset (encode (IInstruction inst)) = IInstruction inst.
Proof.
  let inst := fresh "inst" in let iset := fresh "iset" in let V := fresh "V" in
  intros inst iset V; unfold verify in V; destruct V;
  unfold verify_iset in *;
  let Henc := fresh "Henc" in
  match goal with
  | |- ?D ?I (encode ?x) = _ =>
    remember (encode x) as encoded eqn:Henc; symmetry in Henc
  end.
  cbv [ encode
        Encoder
        Verifier
        apply_InstructionMapper
        map_Fence
        map_I
        map_I_shift_57
        map_I_shift_66
        map_I_system
        map_Invalid
        map_R
        map_R_atomic
        map_S
        map_SB
        map_U
        map_UJ
    ] in Henc;
  match goal with
  | |- ?D ?I _ = _ => cbv beta delta [D]
  end.

  Time destruct inst;
    invert_encode;
    lets_to_eqs;
    subst_lets_from_encode_inversion;
    repeat match goal with
           | H: _ |- _ => progress simpl_ifs_in H
           end;
    first [ subst; reflexivity
          | destruct iset; subst; reflexivity
          | idtac ].

Time Qed.



Lemma decode_encode: forall (inst: Instruction) (iset: InstructionSet),
    verify inst iset ->
    decode iset (encode inst) = inst.
Proof.
  destruct inst; intros.
  - apply decodeI_encode; assumption.
  -
Abort.
 *)
