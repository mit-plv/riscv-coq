Require Import Coq.ZArith.BinInt.
Require Import coqutil.Map.Interface.
Require Import coqutil.Word.Interface.
Require Import coqutil.Word.LittleEndian.
Require Import riscv.Memory.
Require Import riscv.Utility.
Require Import riscv.MetricLogging.


Section Machine.

  Context {Reg: Type}.
  Context {W: Words}.
  Context {Registers: map.map Reg word}.
  Context {Mem: map.map word byte}.
  Context {Action: Type}.

  (* (memory before call, call name, arg values) and (memory after call, return values) *)
  Definition LogItem: Type := (Mem * Action * list word) * (Mem * list word).

  Record RiscvMachine := mkRiscvMachine {
    getRegs: Registers;
    getPc: word;
    getNextPc: word;
    getMem: Mem;
    getLog: list LogItem;
    getMetrics: MetricLog;
  }.

  Definition withRegs: Registers -> RiscvMachine -> RiscvMachine :=
    fun regs2 '(mkRiscvMachine regs1 pc nextPC mem log metrics) =>
                mkRiscvMachine regs2 pc nextPC mem log metrics.

  Definition withPc: word -> RiscvMachine -> RiscvMachine :=
    fun pc2 '(mkRiscvMachine regs pc1 nextPC mem log metrics) =>
              mkRiscvMachine regs pc2 nextPC mem log metrics.

  Definition withNextPc: word -> RiscvMachine -> RiscvMachine :=
    fun nextPC2 '(mkRiscvMachine regs pc nextPC1 mem log metrics) =>
                  mkRiscvMachine regs pc nextPC2 mem log metrics.

  Definition withMem: Mem -> RiscvMachine -> RiscvMachine :=
    fun mem2 '(mkRiscvMachine regs pc nextPC mem1 log metrics)  =>
               mkRiscvMachine regs pc nextPC mem2 log metrics.

  Definition withLog: list LogItem -> RiscvMachine -> RiscvMachine :=
    fun log2 '(mkRiscvMachine regs pc nextPC mem log1 metrics) =>
               mkRiscvMachine regs pc nextPC mem log2 metrics.

  Definition withLogItem: LogItem -> RiscvMachine -> RiscvMachine :=
    fun item '(mkRiscvMachine regs pc nextPC mem log metrics) =>
               mkRiscvMachine regs pc nextPC mem (item :: log) metrics.

  Definition withLogItems: list LogItem -> RiscvMachine -> RiscvMachine :=
    fun items '(mkRiscvMachine regs pc nextPC mem log metrics) =>
                mkRiscvMachine regs pc nextPC mem (items ++ log) metrics.

  Definition withMetrics : MetricLog -> RiscvMachine -> RiscvMachine :=
    fun metrics2 '(mkRiscvMachine regs pc nextPc mem log metrics1) =>
                   mkRiscvMachine regs pc nextPc mem log metrics2.

  Definition updateMetrics(fm: MetricLog -> MetricLog)(ma: RiscvMachine): RiscvMachine :=
    withMetrics (fm ma.(getMetrics)) ma.

  Definition putProgram(prog: list MachineInt)(addr: word)(ma: RiscvMachine): RiscvMachine :=
    (withPc addr
    (withNextPc (word.add addr (word.of_Z 4))
    (withMem (unchecked_store_byte_tuple_list addr (List.map (split 4) prog) ma.(getMem)) ma))).

End Machine.

Arguments RiscvMachine Reg {W} {Registers} {Mem} Action.
Arguments LogItem {W} {Mem} Action.
