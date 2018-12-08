From coqutil Require Export sanity.
Require Import BinInt.
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

  Context {Reg: Set}.
  Context {mword: Set}.
  Context {MW: MachineWidth mword}.
  Context {RFF: RegisterFileFunctions Reg mword}.
  Context {Mem: map.map mword Utility.byte}.
  Context {Action: Set}.

  (* name of the external call, list of arguments, list of return values *)
  Definition LogItem: Set := Action * list mword * list mword.

  Record RiscvMachine := mkRiscvMachine {
    getRegs: RegisterFile Reg mword;
    getPc: mword;
    getNextPc: mword;
    isMem: mword -> bool;
    getMem: Mem;
    getLog: list LogItem;
  }.

  Definition setRegs: RiscvMachine -> RegisterFile Reg mword -> RiscvMachine :=
    fun '(mkRiscvMachine regs1 pc nextPC im mem log) regs2 =>
          mkRiscvMachine regs2 pc nextPC im mem log.

  Definition setPc: RiscvMachine -> mword -> RiscvMachine :=
    fun '(mkRiscvMachine regs pc1 nextPC im mem log) pc2 =>
          mkRiscvMachine regs pc2 nextPC im mem log.

  Definition setNextPc: RiscvMachine -> mword -> RiscvMachine :=
    fun '(mkRiscvMachine regs pc nextPC1 im mem log) nextPC2 =>
          mkRiscvMachine regs pc nextPC2 im mem log.

  Definition setIsMem: RiscvMachine -> (mword -> bool) -> RiscvMachine :=
    fun '(mkRiscvMachine regs pc nextPC im1 mem log) im2 =>
          mkRiscvMachine regs pc nextPC im2 mem log.

  Definition setMem: RiscvMachine -> Mem -> RiscvMachine :=
    fun '(mkRiscvMachine regs pc nextPC im mem1 log) mem2 =>
          mkRiscvMachine regs pc nextPC im mem2 log.

  Definition setLog: RiscvMachine -> list LogItem -> RiscvMachine :=
    fun '(mkRiscvMachine regs pc nextPC im mem log1) log2 =>
          mkRiscvMachine regs pc nextPC im mem log2.

  Definition logCons(m: RiscvMachine)(i: LogItem): RiscvMachine :=
    setLog m (i :: m.(getLog)).

  Definition logAppend(m: RiscvMachine)(items: list LogItem): RiscvMachine :=
    setLog m (items ++ m.(getLog)).

  Definition withRegs: RegisterFile Reg mword -> RiscvMachine -> RiscvMachine :=
    fun regs2 '(mkRiscvMachine regs1 pc nextPC im mem log) =>
                mkRiscvMachine regs2 pc nextPC im mem log.

  Definition withPc: mword -> RiscvMachine -> RiscvMachine :=
    fun pc2 '(mkRiscvMachine regs pc1 nextPC im mem log) =>
              mkRiscvMachine regs pc2 nextPC im mem log.

  Definition withNextPc: mword -> RiscvMachine -> RiscvMachine :=
    fun nextPC2 '(mkRiscvMachine regs pc nextPC1 im mem log) =>
                  mkRiscvMachine regs pc nextPC2 im mem log.

  Definition withIsMem: (mword -> bool) -> RiscvMachine -> RiscvMachine :=
    fun im2 '(mkRiscvMachine regs pc nextPC im1 mem log)  =>
              mkRiscvMachine regs pc nextPC im2 mem log.

  Definition withMem: Mem -> RiscvMachine -> RiscvMachine :=
    fun mem2 '(mkRiscvMachine regs pc nextPC im mem1 log)  =>
               mkRiscvMachine regs pc nextPC im mem2 log.

  Definition withLog: list LogItem -> RiscvMachine -> RiscvMachine :=
    fun log2 '(mkRiscvMachine regs pc nextPC im mem log1) =>
               mkRiscvMachine regs pc nextPC im mem log2.

  Definition withLogItem: LogItem -> RiscvMachine -> RiscvMachine :=
    fun item '(mkRiscvMachine regs pc nextPC im mem log) =>
               mkRiscvMachine regs pc nextPC im mem (item :: log).

  Definition withLogItems: list LogItem -> RiscvMachine -> RiscvMachine :=
    fun items '(mkRiscvMachine regs pc nextPC im mem log) =>
                mkRiscvMachine regs pc nextPC im mem (items ++ log).

  Definition putProgram(prog: list MachineInt)(addr: mword)(ma: RiscvMachine): RiscvMachine :=
    (withPc addr
    (withNextPc (add addr (ZToReg 4))
    (withMem (unchecked_store_byte_tuple_list addr (List.map (split 4) prog) ma.(getMem)) ma))).
End Machine.

Arguments RiscvMachine _ _ {_} {_} {_} _.
Arguments LogItem _ _ : clear implicits.

(* Using techniques such as
   https://gist.github.com/JasonGross/9608584f872149ec6f1115835cbb2c48
   https://github.com/coq/coq/issues/4728
   we could get notations without requiring one notation for each field and each record type,
   but would trade our sanity for it *)
Module InfixUpdates.
  Notation "m 'withRegs' a" := (setRegs m a) (at level 50, left associativity, a at level 0).
  Notation "m 'withPc' a" := (setPc m a) (at level 50, left associativity, a at level 0).
  Notation "m 'withNextPc' a" := (setNextPc m a) (at level 50, left associativity, a at level 0).
  Notation "m 'withIsMem' a" := (setIsMem m a) (at level 50, left associativity, a at level 0).
  Notation "m 'withMem' a" := (setMem m a) (at level 50, left associativity, a at level 0).
  Notation "m 'withLog' a" := (setLog m a) (at level 50, left associativity, a at level 0).
  Notation "m 'withLogItem' a" := (logCons m a) (at level 50, left associativity, a at level 0).
  Notation "m 'withLogItems' a" := (logAppend m a) (at level 50, left associativity, a at level 0).
End InfixUpdates.
