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
  Context {mword: Type}.
  Context {MW: MachineWidth mword}.
  Context {RFF: RegisterFileFunctions Reg mword}.
  Context {Mem: map.map mword byte}.
  Context {Action: Type}.

  (* name of the external call, list of arguments, list of return values *)
  Definition LogItem: Type := Action * list mword * list mword.

  Record RiscvMachine := mkRiscvMachine {
    getRegs: RegisterFile Reg mword;
    getPc: mword;
    getNextPc: mword;
    getMem: Mem;
    getLog: list LogItem;
  }.

  Definition setRegs: RiscvMachine -> RegisterFile Reg mword -> RiscvMachine :=
    fun '(mkRiscvMachine regs1 pc nextPC mem log) regs2 =>
          mkRiscvMachine regs2 pc nextPC mem log.

  Definition setPc: RiscvMachine -> mword -> RiscvMachine :=
    fun '(mkRiscvMachine regs pc1 nextPC mem log) pc2 =>
          mkRiscvMachine regs pc2 nextPC mem log.

  Definition setNextPc: RiscvMachine -> mword -> RiscvMachine :=
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

  Definition withRegs: RegisterFile Reg mword -> RiscvMachine -> RiscvMachine :=
    fun regs2 '(mkRiscvMachine regs1 pc nextPC mem log) =>
                mkRiscvMachine regs2 pc nextPC mem log.

  Definition withPc: mword -> RiscvMachine -> RiscvMachine :=
    fun pc2 '(mkRiscvMachine regs pc1 nextPC mem log) =>
              mkRiscvMachine regs pc2 nextPC mem log.

  Definition withNextPc: mword -> RiscvMachine -> RiscvMachine :=
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
  Notation "m 'withMem' a" := (setMem m a) (at level 50, left associativity, a at level 0).
  Notation "m 'withLog' a" := (setLog m a) (at level 50, left associativity, a at level 0).
  Notation "m 'withLogItem' a" := (logCons m a) (at level 50, left associativity, a at level 0).
  Notation "m 'withLogItems' a" := (logAppend m a) (at level 50, left associativity, a at level 0).
End InfixUpdates.
