Require Import Coq.Strings.String.
Require Import Coq.ZArith.BinInt.
Require Import coqutil.Map.Interface.
Require Import coqutil.Word.Interface.
Require Import coqutil.Word.LittleEndian.
Require Import riscv.Spec.Decode.
Require Import riscv.Platform.Memory.
Require Import riscv.Utility.Utility.


Section Machine.

  Context {W: Words}.
  Context {Registers: map.map Register word}.
  Context {Mem: map.map word byte}.

  (* (memory before call, call name, arg values) and (memory after call, return values) *)
  Definition LogItem: Type := (Mem * string * list word) * (Mem * list word).

  Record RiscvMachine := mkRiscvMachine {
    getRegs: Registers;
    getPc: word;
    getNextPc: word;
    getMem: Mem;
    getLog: list LogItem;
  }.

  Definition withRegs: Registers -> RiscvMachine -> RiscvMachine :=
    fun regs2 '(mkRiscvMachine regs1 pc nextPC mem log) =>
                mkRiscvMachine regs2 pc nextPC mem log.

  Definition withPc: word -> RiscvMachine -> RiscvMachine :=
    fun pc2 '(mkRiscvMachine regs pc1 nextPC mem log) =>
              mkRiscvMachine regs pc2 nextPC mem log.

  Definition withNextPc: word -> RiscvMachine -> RiscvMachine :=
    fun nextPC2 '(mkRiscvMachine regs pc nextPC1 mem log) =>
                  mkRiscvMachine regs pc nextPC2 mem log.

  Definition withMem: Mem -> RiscvMachine -> RiscvMachine :=
    fun mem2 '(mkRiscvMachine regs pc nextPC mem1 log)  =>
               mkRiscvMachine regs pc nextPC mem2 log.

  Definition withLog: list LogItem -> RiscvMachine -> RiscvMachine :=
    fun log2 '(mkRiscvMachine regs pc nextPC mem log1) =>
               mkRiscvMachine regs pc nextPC mem log2.

  Definition withLogItem: LogItem -> RiscvMachine -> RiscvMachine :=
    fun item '(mkRiscvMachine regs pc nextPC mem log) =>
               mkRiscvMachine regs pc nextPC mem (item :: log).

  Definition withLogItems: list LogItem -> RiscvMachine -> RiscvMachine :=
    fun items '(mkRiscvMachine regs pc nextPC mem log) =>
                mkRiscvMachine regs pc nextPC mem (items ++ log).

  Definition Z32s_to_bytes(l: list Z): list byte :=
    List.flat_map (fun z => HList.tuple.to_list (LittleEndian.split 4 z)) l.

  Definition putProgram(prog: list MachineInt)(addr: word)(ma: RiscvMachine): RiscvMachine :=
    (withPc addr
    (withNextPc (word.add addr (word.of_Z 4))
    (withMem (unchecked_store_byte_list addr (Z32s_to_bytes prog) ma.(getMem)) ma))).

End Machine.
