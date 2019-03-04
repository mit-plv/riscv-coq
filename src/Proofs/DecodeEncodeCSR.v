Require Import riscv.Proofs.DecodeEncodeProver.

Lemma decodeCSR_encode: forall (inst: InstructionCSR) (iset: InstructionSet),
    verify (CSRInstruction inst) iset ->
    decode iset (encode (CSRInstruction inst)) = CSRInstruction inst.
Proof. prove_decode_encode. Qed.
