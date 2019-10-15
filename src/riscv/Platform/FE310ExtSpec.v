Require Import Coq.ZArith.ZArith.
Require Import coqutil.Map.Interface.
Require Import coqutil.Z.HexNotation.
Require Import riscv.Utility.Utility.
Require Import riscv.Platform.MinimalMMIO.

Local Open Scope Z_scope.

Section MMIO.
  Context {W: Words}
          {Mem: map.map word byte}.

  (* Using the memory layout of FE310-G000 *)
  Definition isOTP  (addr: word): Prop := Ox"00020000" <= word.unsigned addr < Ox"00022000".
  Definition isPRCI (addr: word): Prop := Ox"10008000" <= word.unsigned addr < Ox"10010000".
  Definition isGPIO0(addr: word): Prop := Ox"10012000" <= word.unsigned addr < Ox"10013000".
  Definition isUART0(addr: word): Prop := Ox"10013000" <= word.unsigned addr < Ox"10014000".
  Definition isMMIOAddr(addr: word): Prop :=
    word.unsigned addr mod 4 = 0 /\ (isOTP addr \/ isPRCI addr \/ isGPIO0 addr \/ isUART0 addr).

  Local Instance processor_mmio : ExtSpec := {|
    mmio_load n ctxid a m t post := isMMIOAddr a /\ forall v, post m v;
    mmio_store n ctxid a v m t post := isMMIOAddr a /\ post m;
  |}.

End MMIO.
