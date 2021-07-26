Require Import coqutil.Map.Interface.
Require Import coqutil.Word.Interface.
Require Import riscv.Spec.Decode.
Require Import riscv.Utility.Utility.
Require Import riscv.Platform.RiscvMachine.

Section Machine.

  Context {width: Z} {BW: Bitwidth width} {word: word width} {word_ok: word.ok word}.
  Context {Registers: map.map Register word}.
  Context {Mem: map.map word byte}.
  Context {Action: Type}.

  Record AtomicRiscvMachine := mkAtomicRiscvMachine {
    getMachine :> RiscvMachine;
    getReservation: option word;
  }.

  Definition withReservation : option word -> AtomicRiscvMachine -> AtomicRiscvMachine :=
    fun reservation '(mkAtomicRiscvMachine m _) =>
          mkAtomicRiscvMachine m reservation.

  Definition updateReservation(fr: option word -> option word)(m: AtomicRiscvMachine) :=
    withReservation (fr m.(getReservation)) m.

  Definition withRegs: Registers -> AtomicRiscvMachine -> AtomicRiscvMachine :=
    fun regs2 '(mkAtomicRiscvMachine mach rv) =>
      (mkAtomicRiscvMachine (withRegs regs2 mach) rv).

  Definition withPc: word -> AtomicRiscvMachine -> AtomicRiscvMachine :=
    fun pc2 '(mkAtomicRiscvMachine mach rv) =>
      (mkAtomicRiscvMachine (withPc pc2 mach) rv).

  Definition withNextPc: word -> AtomicRiscvMachine -> AtomicRiscvMachine :=
    fun nextPC2 '(mkAtomicRiscvMachine mach rv) =>
      (mkAtomicRiscvMachine (withNextPc nextPC2 mach) rv).

  Definition withMem: Mem -> AtomicRiscvMachine -> AtomicRiscvMachine :=
    fun mem2 '(mkAtomicRiscvMachine mach rv) =>
      (mkAtomicRiscvMachine (withMem mem2 mach) rv).

  Definition withXAddrs: XAddrs -> AtomicRiscvMachine -> AtomicRiscvMachine :=
    fun xAddrs2 '(mkAtomicRiscvMachine mach rv) =>
      (mkAtomicRiscvMachine (withXAddrs xAddrs2 mach) rv).

  Definition withLog: list LogItem -> AtomicRiscvMachine -> AtomicRiscvMachine :=
    fun log2 '(mkAtomicRiscvMachine mach rv) =>
      (mkAtomicRiscvMachine (withLog log2 mach) rv).

  Definition withLogItem: LogItem -> AtomicRiscvMachine -> AtomicRiscvMachine :=
    fun item '(mkAtomicRiscvMachine mach rv) =>
      (mkAtomicRiscvMachine (withLogItem item mach) rv).

  Definition withLogItems: list LogItem -> AtomicRiscvMachine -> AtomicRiscvMachine :=
    fun items '(mkAtomicRiscvMachine mach rv) =>
      (mkAtomicRiscvMachine (withLogItems items mach) rv).

  Definition forgetReservation(m: AtomicRiscvMachine): RiscvMachine := m.(getMachine).
  Definition addReservation(m: RiscvMachine)(rv: option word): AtomicRiscvMachine :=
    mkAtomicRiscvMachine m rv.

  Definition putProgram(prog: list MachineInt)(addr: word)(ma: AtomicRiscvMachine): AtomicRiscvMachine :=
    mkAtomicRiscvMachine (putProgram prog addr ma.(getMachine)) ma.(getReservation).

End Machine.

Ltac destruct_RiscvMachine m :=
  lazymatch type of m with
  | AtomicRiscvMachine =>
    let r := fresh m "_regs" in
    let p := fresh m "_pc" in
    let n := fresh m "_npc" in
    let me := fresh m "_mem" in
    let x := fresh m "_xaddrs" in
    let l := fresh m "_log" in
    let rv := fresh m "_reservation" in
    destruct m as [ [r p n me x l] rv ];
    simpl in *
  | _ => let expected := constr:(@AtomicRiscvMachine) in fail "not a" expected
  end.
