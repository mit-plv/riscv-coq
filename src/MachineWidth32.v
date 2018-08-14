Require Import riscv.Utility.
Require Import riscv.MachineWidth_XLEN.

Instance MachineWidth32: MachineWidth (word 32) := MachineWidth_XLEN 32 _.
  cbv. discriminate.
Defined.
