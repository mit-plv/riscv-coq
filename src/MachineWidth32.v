Require Import Coq.ZArith.ZArith.
Require Import riscv.Utility.
Require Import riscv.MachineWidth_XLEN.
Local Open Scope Z_scope.

Lemma bound832: 8 <= 32. cbv. discriminate. Qed.

Definition word32: Type := word_sz 32 bound832.

Instance MachineWidth32: MachineWidth word32 := MachineWidth_XLEN 32 bound832.
