Require Import Coq.Strings.String.
Require Import coqutil.Map.Interface.
Require Import coqutil.Word.Interface.
Require Import coqutil.Word.LittleEndian.
Require Import riscv.Spec.Decode.
Require Import riscv.Platform.Memory.
Require Import riscv.Utility.Utility.
Require Import riscv.Platform.RiscvMachine.
Require Import riscv.Platform.MetricLogging.

Section Machine.

  Context {W: Words}.
  Context {Registers: map.map Register word}.
  Context {Mem: map.map word byte}.

  Record MetricRiscvMachine := mkMetricRiscvMachine {
    getMachine :> RiscvMachine;
    getMetrics: MetricLog;
  }.

  Definition withMetrics : MetricLog -> MetricRiscvMachine -> MetricRiscvMachine :=
    fun metrics '(mkMetricRiscvMachine m _) =>
                  mkMetricRiscvMachine m metrics.

  Definition updateMetrics(fm: MetricLog -> MetricLog)(m: MetricRiscvMachine) :=
    withMetrics (fm m.(getMetrics)) m.

  Definition liftGet{A: Type}(getF: RiscvMachine -> A): (MetricRiscvMachine -> A) :=
    fun m => getF m.

  Definition liftWith{A: Type}(withF: A -> RiscvMachine -> RiscvMachine) :=
    fun a m =>
      mkMetricRiscvMachine (withF a m.(getMachine)) m.(getMetrics).

  Definition withRegs := liftWith withRegs.
  Definition withPc := liftWith withPc.
  Definition withNextPc := liftWith withNextPc.
  Definition withMem := liftWith withMem.
  Definition withXAddrs := liftWith withXAddrs.
  Definition withLog := liftWith withLog.
  Definition withLogItem := liftWith withLogItem.
  Definition withLogItems := liftWith withLogItems.

  Definition forgetMetrics(m: MetricRiscvMachine): RiscvMachine := m.(getMachine).
  Definition addMetrics(m: RiscvMachine)(mc: MetricLog): MetricRiscvMachine :=
    mkMetricRiscvMachine m mc.

  Definition putProgram(prog: list MachineInt)(addr: word)(ma: MetricRiscvMachine): MetricRiscvMachine :=
    mkMetricRiscvMachine (putProgram prog addr ma.(getMachine)) ma.(getMetrics).

End Machine.

Ltac destruct_RiscvMachine m :=
  lazymatch type of m with
  | MetricRiscvMachine =>
    let r := fresh m "_regs" in
    let p := fresh m "_pc" in
    let n := fresh m "_npc" in
    let me := fresh m "_mem" in
    let x := fresh m "_xaddrs" in
    let l := fresh m "_log" in
    let mc := fresh m "_metrics" in
    destruct m as [ [r p n me x l] mc ];
    simpl in *
  | _ => let expected := constr:(@MetricRiscvMachine) in fail "not a" expected
  end.
