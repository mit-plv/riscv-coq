Require Import riscv.Proofs.DecodeEncodeProver.

Lemma decodeA64_encode: forall (inst: InstructionA64) (iset: InstructionSet),
    verify (A64Instruction inst) iset ->
    decode iset (encode (A64Instruction inst)) = A64Instruction inst.
Proof. prove_decode_encode. Qed.
