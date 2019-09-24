Require Import riscv.Proofs.DecodeEncodeProver.

Lemma decodeI64_encode: forall (inst: InstructionI64) (iset: InstructionSet),
    verify (I64Instruction inst) iset ->
    decode iset (encode (I64Instruction inst)) = I64Instruction inst.
Proof. prove_decode_encode. Qed.
