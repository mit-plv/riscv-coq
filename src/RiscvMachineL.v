Require Import riscv.Decode.
Require Import riscv.Memory.
Require Import riscv.Utility.
Require Export riscv.RiscvMachine.


Section Riscv.

  Context {t: Set}.
  Context {Mem: Set}.
  Context {RF: Type}.

  (* MMIO trace *)
  Inductive LogEvent :=
  | EvInput(addr: Z)(v: word 32)
  | EvOutput(addr: Z)(v: word 32).

  Definition Log := list LogEvent.

  Record RiscvMachineL := mkRiscvMachineL {
    machine: @RiscvMachine t Mem RF;
    log: Log;
  }.

  Definition with_machine m ml := mkRiscvMachineL m ml.(log).
  Definition with_log l ml := mkRiscvMachineL ml.(machine) l.

End Riscv.
