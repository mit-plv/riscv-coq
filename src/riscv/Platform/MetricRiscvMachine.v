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

  Context {width: Z} {BW: Bitwidth width} {word: word width} {word_ok: word.ok word}.
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
      (mkMetricRiscvMachine (withRegs regs2 mach) mc).

  Definition withPc: word -> MetricRiscvMachine -> MetricRiscvMachine :=
    fun pc2 '(mkMetricRiscvMachine mach mc) =>
      (mkMetricRiscvMachine (withPc pc2 mach) mc).

  Definition withNextPc: word -> MetricRiscvMachine -> MetricRiscvMachine :=
    fun nextPC2 '(mkMetricRiscvMachine mach mc) =>
      (mkMetricRiscvMachine (withNextPc nextPC2 mach) mc).

  Definition withMem: Mem -> MetricRiscvMachine -> MetricRiscvMachine :=
    fun mem2 '(mkMetricRiscvMachine mach mc) =>
      (mkMetricRiscvMachine (withMem mem2 mach) mc).

  Definition withXAddrs: XAddrs -> MetricRiscvMachine -> MetricRiscvMachine :=
    fun xAddrs2 '(mkMetricRiscvMachine mach mc) =>
      (mkMetricRiscvMachine (withXAddrs xAddrs2 mach) mc).

  Definition withLog: list LogItem -> MetricRiscvMachine -> MetricRiscvMachine :=
    fun log2 '(mkMetricRiscvMachine mach mc) =>
      (mkMetricRiscvMachine (withLog log2 mach) mc).

  Definition withLogItem: LogItem -> MetricRiscvMachine -> MetricRiscvMachine :=
    fun item '(mkMetricRiscvMachine mach mc) =>
      (mkMetricRiscvMachine (withLogItem item mach) mc).

  Definition withLogItems: list LogItem -> MetricRiscvMachine -> MetricRiscvMachine :=
    fun items '(mkMetricRiscvMachine mach mc) =>
      (mkMetricRiscvMachine (withLogItems items mach) mc).

  Definition forgetMetrics(m: MetricRiscvMachine): RiscvMachine := m.(getMachine).
  Definition addMetrics(m: RiscvMachine)(mc: MetricLog): MetricRiscvMachine :=
    mkMetricRiscvMachine m mc.

  Definition putProgram(prog: list MachineInt)(addr: word)(ma: MetricRiscvMachine): MetricRiscvMachine :=
    mkMetricRiscvMachine (putProgram prog addr ma.(getMachine)) ma.(getMetrics).

End Machine.

Ltac only_destruct_RiscvMachine m :=
  lazymatch type of m with
  | MetricRiscvMachine =>
    let r := fresh m "_regs" in
    let p := fresh m "_pc" in
    let n := fresh m "_npc" in
    let me := fresh m "_mem" in
    let x := fresh m "_xaddrs" in
    let l := fresh m "_log" in
    let mc := fresh m "_metrics" in
    destruct m as [ [r p n me x l] mc ]
  | _ => let expected := constr:(@MetricRiscvMachine) in fail "not a" expected
  end.

Ltac unfold_RiscvMachine_get_set :=
  cbv [getMachine getMetrics
       RiscvMachine.getRegs RiscvMachine.getPc RiscvMachine.getNextPc
       RiscvMachine.getMem RiscvMachine.getXAddrs RiscvMachine.getLog
       withMetrics withRegs withPc withNextPc withMem withXAddrs withLog withLogItem withLogItems
       RiscvMachine.withRegs RiscvMachine.withPc RiscvMachine.withNextPc RiscvMachine.withMem
       RiscvMachine.withXAddrs RiscvMachine.withLog RiscvMachine.withLogItem RiscvMachine.withLogItems] in *.

Ltac destr_RiscvMachine state := only_destruct_RiscvMachine state; unfold_RiscvMachine_get_set.

Ltac destruct_RiscvMachine m := only_destruct_RiscvMachine m; simpl in *.
