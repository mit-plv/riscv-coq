Require Import riscv.Proofs.DecodeEncodeProver.
Require Import riscv.Proofs.DecodeEncodeI.
Require Import riscv.Proofs.DecodeEncodeM.

Lemma decode_encode: forall (inst: Instruction) (iset: InstructionSet),
    verify inst iset ->
    decode iset (encode inst) = inst.
Proof.
  destruct inst; intros.
  - apply decodeI_encode; assumption.
  - apply decodeM_encode; assumption.

Abort.
