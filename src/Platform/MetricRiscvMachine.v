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

  Definition withRegs: Registers -> MetricRiscvMachine -> MetricRiscvMachine :=
    fun regs2 '(mkMetricRiscvMachine mach mc) =>
      let '(mkRiscvMachine regs1 pc nextPC mem xAddrs log) := mach in
      (mkMetricRiscvMachine (mkRiscvMachine regs2 pc nextPC mem xAddrs log) mc).

  Definition withPc: word -> MetricRiscvMachine -> MetricRiscvMachine :=
    fun pc2 '(mkMetricRiscvMachine mach mc) =>
      let '(mkRiscvMachine regs pc1 nextPC mem xAddrs log) := mach in
      (mkMetricRiscvMachine (mkRiscvMachine regs pc2 nextPC mem xAddrs log) mc).

  Definition withNextPc: word -> MetricRiscvMachine -> MetricRiscvMachine :=
    fun nextPC2 '(mkMetricRiscvMachine mach mc) =>
      let '(mkRiscvMachine regs pc nextPC1 mem xAddrs log) := mach in
      (mkMetricRiscvMachine (mkRiscvMachine regs pc nextPC2 mem xAddrs log) mc).

  Definition withMem: Mem -> MetricRiscvMachine -> MetricRiscvMachine :=
    fun mem2 '(mkMetricRiscvMachine mach mc) =>
      let '(mkRiscvMachine regs pc nextPC mem1 xAddrs log) := mach in
      (mkMetricRiscvMachine (mkRiscvMachine regs pc nextPC mem2 xAddrs log) mc).

  Definition withXAddrs: XAddrs -> MetricRiscvMachine -> MetricRiscvMachine :=
    fun xAddrs2 '(mkMetricRiscvMachine mach mc) =>
      let '(mkRiscvMachine regs pc nextPC mem xAddrs1 log) := mach in
      (mkMetricRiscvMachine (mkRiscvMachine regs pc nextPC mem xAddrs2 log) mc).

  Definition withLog: list LogItem -> MetricRiscvMachine -> MetricRiscvMachine :=
    fun log2 '(mkMetricRiscvMachine mach mc) =>
      let '(mkRiscvMachine regs pc nextPC mem xAddrs log1) := mach in
      (mkMetricRiscvMachine (mkRiscvMachine regs pc nextPC mem xAddrs log2) mc).

  Definition withLogItem: LogItem -> MetricRiscvMachine -> MetricRiscvMachine :=
    fun item '(mkMetricRiscvMachine mach mc) =>
      let '(mkRiscvMachine regs pc nextPC mem xAddrs log) := mach in
      (mkMetricRiscvMachine (mkRiscvMachine regs pc nextPC mem xAddrs (item :: log)) mc).

  Definition withLogItems: list LogItem -> MetricRiscvMachine -> MetricRiscvMachine :=
    fun items '(mkMetricRiscvMachine mach mc) =>
      let '(mkRiscvMachine regs pc nextPC mem xAddrs log) := mach in
      (mkMetricRiscvMachine (mkRiscvMachine regs pc nextPC mem xAddrs (items ++ log)) mc).

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
