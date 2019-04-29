Require Import coqutil.Map.Interface.
Require Import coqutil.Word.Interface.
Require Import coqutil.Word.LittleEndian.
Require Import riscv.Platform.Memory.
Require Import riscv.Utility.Utility.
Require Import riscv.Platform.RiscvMachine.
Require Import riscv.Platform.MetricLogging.

Section Machine.

  Context {Reg: Type}.
  Context {W: Words}.
  Context {Registers: map.map Reg word}.
  Context {Mem: map.map word byte}.
  Context {Action: Type}.

  Local Notation RiscvMachineL := (RiscvMachine Reg Action).

  Record MetricRiscvMachine := mkMetricRiscvMachine {
    getMachine :> RiscvMachineL;
    getMetrics: MetricLog;
  }.

  Definition withMetrics : MetricLog -> MetricRiscvMachine -> MetricRiscvMachine :=
    fun metrics '(mkMetricRiscvMachine m _) =>
                  mkMetricRiscvMachine m metrics.

  Definition updateMetrics(fm: MetricLog -> MetricLog)(m: MetricRiscvMachine) :=
    withMetrics (fm m.(getMetrics)) m.

  Definition liftGet{A: Type}(getF: RiscvMachineL -> A): (MetricRiscvMachine -> A) :=
    fun m => getF m.

  Definition liftWith{A: Type}(withF: A -> RiscvMachineL -> RiscvMachineL) :=
    fun a m =>
      mkMetricRiscvMachine (withF a m.(getMachine)) m.(getMetrics).

  Definition withRegs := liftWith withRegs.
  Definition withPc := liftWith withPc.
  Definition withNextPc := liftWith withNextPc.
  Definition withMem := liftWith withMem.
  Definition withLog := liftWith withLog.
  Definition withLogItem := liftWith withLogItem.
  Definition withLogItems := liftWith withLogItems.

  Definition forgetMetrics(m: MetricRiscvMachine): RiscvMachineL := m.(getMachine).
  Definition addMetrics(m: RiscvMachineL)(mc: MetricLog): MetricRiscvMachine :=
    mkMetricRiscvMachine m mc.

  Definition putProgram(prog: list MachineInt)(addr: word)(ma: MetricRiscvMachine): MetricRiscvMachine :=
    (withPc addr
    (withNextPc (word.add addr (word.of_Z 4))
    (withMem (unchecked_store_byte_list addr (Z32s_to_bytes prog) ma.(getMem)) ma))).

End Machine.

Arguments MetricRiscvMachine Reg {W} {Registers} {Mem} Action.

Ltac destruct_RiscvMachine m :=
  lazymatch type of m with
  | MetricRiscvMachine _ _ =>
    let r := fresh m "_regs" in
    let p := fresh m "_pc" in
    let n := fresh m "_npc" in
    let me := fresh m "_mem" in
    let l := fresh m "_log" in
    let mc := fresh m "_metrics" in
    destruct m as [ [r p n me l] mc ];
    simpl in *
  | _ => let expected := constr:(@MetricRiscvMachine) in fail "not a" expected
  end.
