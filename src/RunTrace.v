Require Import Coq.ZArith.BinInt.
Require Import bbv.WordScope.
Require Import bbv.DepEqNat.
Require Import riscv.util.NameWithEq.
Require Import riscv.RiscvBitWidths.
Require Import riscv.util.Monads.
Require Import riscv.Decode.
Require Import riscv.Memory. (* should go before Program because both define loadByte etc *)
Require Import riscv.Program.
Require Import riscv.Execute.
Require Import riscv.util.PowerFunc.
Require Import riscv.Utility.
Require Import Coq.Lists.List.
Require Import riscv.Minimal.
Require Import riscv.Run.
Import ListNotations.


Section Riscv.

  Context {B: RiscvBitWidths}.

  Definition LoggingMemory: Set. Admitted.

  Definition RiscvMachine := @RiscvMachine _ LoggingMemory.

End Riscv.
