Require Import riscv.Proofs.DecodeEncodeProver.

Lemma decodeM64_encode: forall (inst: InstructionM64) (iset: InstructionSet),
    verify (M64Instruction inst) iset ->
    decode iset (encode (M64Instruction inst)) = M64Instruction inst.
Proof. prove_decode_encode. Qed.
