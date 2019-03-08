Require Import riscv.Proofs.DecodeEncodeProver.

Lemma decodeA_encode: forall (inst: InstructionA) (iset: InstructionSet),
    verify (AInstruction inst) iset ->
    decode iset (encode (AInstruction inst)) = AInstruction inst.
Proof. prove_decode_encode. Qed.
