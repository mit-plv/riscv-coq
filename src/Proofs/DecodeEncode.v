Require Import riscv.Proofs.DecodeEncodeProver.
Require Import riscv.Proofs.DecodeEncodeI.
Require Import riscv.Proofs.DecodeEncodeM.
Require Import riscv.Proofs.DecodeEncodeA.
Require Import riscv.Proofs.DecodeEncodeI64.
Require Import riscv.Proofs.DecodeEncodeM64.
Require Import riscv.Proofs.DecodeEncodeA64.
Require Import riscv.Proofs.DecodeEncodeCSR.

Lemma decode_encode: forall (inst: Instruction) (iset: InstructionSet),
    verify inst iset ->
    decode iset (encode inst) = inst.
Proof.
  destruct inst; intros.
  - apply decodeI_encode; assumption.
  - apply decodeM_encode; assumption.
  - apply decodeA_encode; assumption.
  - destruct H as [R V].
    (* F is not supported and therefore verify_iset returns False for it *)
    change False in V. destruct V.
  - apply decodeI64_encode; assumption.
  - apply decodeM64_encode; assumption.
  - apply decodeA64_encode; assumption.
  - destruct H as [R V].
    (* F64 is not supported and therefore verify_iset returns False for it *)
    change False in V. destruct V.
  - apply decodeCSR_encode; assumption.
  - destruct H as [R V].
    (* invalid instruction is invalid *)
    change False in V. destruct V.
Qed.
