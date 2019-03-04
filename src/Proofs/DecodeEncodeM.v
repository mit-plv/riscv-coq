Require Import riscv.Proofs.DecodeEncodeProver.

Lemma decodeM_encode: forall (inst: InstructionM) (iset: InstructionSet),
    verify (MInstruction inst) iset ->
    decode iset (encode (MInstruction inst)) = MInstruction inst.
Proof. prove_decode_encode. Qed.
