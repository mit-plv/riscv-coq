Require Import Coq.ZArith.ZArith.
Require Import riscv.Utility.
Require Import riscv.MachineWidth_XLEN.
Local Open Scope Z_scope.

Lemma bound864: 8 <= 64. cbv. discriminate. Qed.

Definition word64: Type := word_sz 64 bound864.

Instance MachineWidth64: MachineWidth word64 := MachineWidth_XLEN 64 bound864.
