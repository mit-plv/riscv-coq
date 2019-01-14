Require Import Coq.ZArith.BinInt.
Require Import coqutil.Map.Interface.
Require Import coqutil.Word.Interface.
Require Import coqutil.Word.LittleEndian.
Require Import riscv.Memory.
Require Import riscv.Utility.

Class RegisterFileFunctions(R V: Type) := mkRegisterFileFunctions {
  RegisterFile: Type;
  getReg: RegisterFile -> R -> V;
  setReg: RegisterFile -> R -> V -> RegisterFile;
  initialRegs: RegisterFile;
}.

Arguments RegisterFile _ _ {_}.


Section Machine.

  Context {Reg: Type}.
  Context {W: Words}.
  Context {RFF: RegisterFileFunctions Reg word}.
  Context {Mem: map.map word (option byte)}.
  Context {Action: Type}.

  (* (memory before call, call name, arg values) and (memory after call, return values) *)
  Definition LogItem: Type := (Mem * Action * list word) * (Mem * list word).

  Record RiscvMachine := mkRiscvMachine {
    getRegs: RegisterFile Reg word;
    getPc: word;
    getNextPc: word;
    getMem: Mem;
    getLog: list LogItem;
  }.

  Definition setRegs: RiscvMachine -> RegisterFile Reg word -> RiscvMachine :=
    fun '(mkRiscvMachine regs1 pc nextPC mem log) regs2 =>
          mkRiscvMachine regs2 pc nextPC mem log.

  Definition setPc: RiscvMachine -> word -> RiscvMachine :=
    fun '(mkRiscvMachine regs pc1 nextPC mem log) pc2 =>
          mkRiscvMachine regs pc2 nextPC mem log.

  Definition setNextPc: RiscvMachine -> word -> RiscvMachine :=
    fun '(mkRiscvMachine regs pc nextPC1 mem log) nextPC2 =>
          mkRiscvMachine regs pc nextPC2 mem log.

  Definition setMem: RiscvMachine -> Mem -> RiscvMachine :=
    fun '(mkRiscvMachine regs pc nextPC mem1 log) mem2 =>
          mkRiscvMachine regs pc nextPC mem2 log.

  Definition setLog: RiscvMachine -> list LogItem -> RiscvMachine :=
    fun '(mkRiscvMachine regs pc nextPC mem log1) log2 =>
          mkRiscvMachine regs pc nextPC mem log2.

  Definition logCons(m: RiscvMachine)(i: LogItem): RiscvMachine :=
    setLog m (i :: m.(getLog)).

  Definition logAppend(m: RiscvMachine)(items: list LogItem): RiscvMachine :=
    setLog m (items ++ m.(getLog)).

  Definition withRegs: RegisterFile Reg word -> RiscvMachine -> RiscvMachine :=
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

  Definition putProgram(prog: list MachineInt)(addr: word)(ma: RiscvMachine): RiscvMachine :=
    (withPc addr
    (withNextPc (word.add addr (word.of_Z 4))
    (withMem (unchecked_store_byte_tuple_list addr (List.map (split 4) prog) ma.(getMem)) ma))).

End Machine.

Arguments RiscvMachine Reg {W} {RFF} {Mem} Action.
Arguments LogItem {W} {Mem} Action.

(* Using techniques such as
   https://gist.github.com/JasonGross/9608584f872149ec6f1115835cbb2c48
   https://github.com/coq/coq/issues/4728
   we could get notations without requiring one notation for each field and each record type,
   but would trade our sanity for it *)
Module InfixUpdates.
  Notation "m 'withRegs' a" := (setRegs m a) (at level 50, left associativity, a at level 0).
  Notation "m 'withPc' a" := (setPc m a) (at level 50, left associativity, a at level 0).
  Notation "m 'withNextPc' a" := (setNextPc m a) (at level 50, left associativity, a at level 0).
  Notation "m 'withMem' a" := (setMem m a) (at level 50, left associativity, a at level 0).
  Notation "m 'withLog' a" := (setLog m a) (at level 50, left associativity, a at level 0).
  Notation "m 'withLogItem' a" := (logCons m a) (at level 50, left associativity, a at level 0).
  Notation "m 'withLogItems' a" := (logAppend m a) (at level 50, left associativity, a at level 0).
End InfixUpdates.
