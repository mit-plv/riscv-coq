Require Import Coq.ZArith.ZArith.
Require Import coqutil.Map.Interface.
Require Import coqutil.Z.HexNotation.
Require Import riscv.Utility.Utility.
Require Import riscv.Platform.MinimalMMIO.

Local Open Scope Z_scope.

Section MMIO.
  Context {W: Words}.

  (* Using the memory layout of FE310-G000 *)
  Definition isOTP  (addr: word): Prop := Ox"00020000" <= word.unsigned addr < Ox"00022000".
  Definition isPRCI (addr: word): Prop := Ox"10008000" <= word.unsigned addr < Ox"10010000".
  Definition isGPIO0(addr: word): Prop := Ox"10012000" <= word.unsigned addr < Ox"10013000".
  Definition isUART0(addr: word): Prop := Ox"10013000" <= word.unsigned addr < Ox"10014000".
  Definition isSPI1 (addr: word): Prop := Ox"10024000" <= word.unsigned addr < Ox"10025000".

  Instance FE310_mmio: MMIOSpec := {|
    isMMIOAddr(addr: word) := isOTP addr \/ isPRCI addr \/ isGPIO0 addr \/ isUART0 addr \/ isSPI1 addr;
    isMMIOAligned(n: nat)(addr: word) := n = 4%nat /\ (word.unsigned addr) mod 4 = 0;
  |}.

End MMIO.

Hint Resolve FE310_mmio: typeclass_instances.
