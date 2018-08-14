Require Import riscv.Utility.
Require Import riscv.MachineWidth_XLEN.

Instance MachineWidth64: MachineWidth (word 64) := MachineWidth_XLEN 64 _.
  cbv. discriminate.
Defined.
