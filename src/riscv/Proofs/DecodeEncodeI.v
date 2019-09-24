Require Import riscv.Proofs.DecodeEncodeProver.

Lemma decodeI_encode: forall (inst: InstructionI) (iset: InstructionSet),
    verify (IInstruction inst) iset ->
    decode iset (encode (IInstruction inst)) = IInstruction inst.
Proof. prove_decode_encode. Qed.
