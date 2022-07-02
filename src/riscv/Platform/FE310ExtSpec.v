Require Import Coq.ZArith.ZArith.
Require Import coqutil.Map.Interface.
Require Import riscv.Utility.Utility.
Require Import riscv.Platform.MinimalMMIO.

Local Open Scope Z_scope.

Section MMIO.
  Context {width: Z} {BW: Bitwidth width} {word: word width} {word_ok: word.ok word}.
  Context {Mem : map.map word byte}.

  (* Using the memory layout of FE310-G000 *)
  Definition isOTP  (addr: word): Prop := 0x00020000 <= word.unsigned addr < 0x00022000.
  Definition isPRCI (addr: word): Prop := 0x10008000 <= word.unsigned addr < 0x10010000.
  Definition isGPIO0(addr: word): Prop := 0x10012000 <= word.unsigned addr < 0x10013000.
  Definition isUART0(addr: word): Prop := 0x10013000 <= word.unsigned addr < 0x10014000.
  Definition isSPI1 (addr: word): Prop := 0x10024000 <= word.unsigned addr < 0x10025000.

  Instance FE310_mmio: MMIOSpec := {|
    isMMIOAddr(addr: word) := isOTP addr \/ isPRCI addr \/ isGPIO0 addr \/ isUART0 addr \/ isSPI1 addr;
    isMMIOAligned(n: nat)(addr: word) := n = 4%nat /\ (word.unsigned addr) mod 4 = 0;
    MMIOReadOK := fun _ _ _ _ => True;
  |}.

End MMIO.

#[global] Hint Resolve FE310_mmio: typeclass_instances.
