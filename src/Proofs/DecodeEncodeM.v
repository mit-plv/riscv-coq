Require Import riscv.Proofs.DecodeEncodeProver.

Ltac destruct_ors :=
  repeat match goal with
         | H: _ \/ _ |- _ => destruct H
         end.

Lemma decodeM_encode: forall (inst: InstructionM) (iset: InstructionSet),
    verify (MInstruction inst) iset ->
    decode iset (encode (MInstruction inst)) = MInstruction inst.
Proof.
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
  end.

  destruct inst;
  invert_encode;
  lets_to_eqs;
  subst_lets_from_encode_inversion;
  repeat match goal with
         | H: _ |- _ => progress simpl_ifs_in H
         end;
  first [ subst; reflexivity
        | (progress destruct_ors); subst; reflexivity
        | destruct iset; subst; reflexivity
        | idtac ].
Qed.
