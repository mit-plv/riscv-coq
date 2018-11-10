Require Import riscv.Memory.
Require Import riscv.Utility.
(*
Require Import Coq.ZArith.BinInt.
Require Import riscv.util.BitWidths.
Require Import riscv.Decode.

*)

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
  Context {MF: MemoryFunctions mword}.
  Context {LogItem: Set}.

  Record RiscvMachine := mkRiscvMachine {
    getRegs: RegisterFile Reg mword;
    getPc: mword;
    getNextPc: mword;
    getMem: Mem mword;
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

  Definition setMem: RiscvMachine -> Mem mword -> RiscvMachine :=
    fun '(mkRiscvMachine regs pc nextPC mem1 log) mem2 =>
          mkRiscvMachine regs pc nextPC mem2 log.

  Definition logAppend: RiscvMachine -> LogItem -> RiscvMachine :=
    fun '(mkRiscvMachine regs pc nextPC mem log) item =>
          mkRiscvMachine regs pc nextPC mem (item :: log).

  Definition putProgram(prog: list (word 32))(addr: mword)(ma: RiscvMachine): RiscvMachine :=
    setPc (setNextPc (setMem ma
                             (store_word_list prog addr ma.(getMem)))
                     (add addr (ZToReg 4)))
          addr.

End Machine.

Arguments RiscvMachine _ _ {_} {_} {_} _.
