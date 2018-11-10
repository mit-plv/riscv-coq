Require Import riscv.util.Word.
Require Import riscv.Utility.

Inductive MMIOAction := MMInput | MMOutput.

Definition MMIOEvent(Addr: Set): Set := MMIOAction * Addr * word 32.
