Require Import Coq.ZArith.BinInt.
Require Import riscv.util.BitWidths.
Require Import riscv.util.Monads. Import OStateOperations.
Require Import riscv.Decode.
Require Import riscv.Memory. (* should go before Program because both define loadByte etc *)
Require Import riscv.Program.
Require Import riscv.Execute.
Require Import riscv.util.PowerFunc.
Require Import riscv.Utility.
Require Import Coq.Lists.List. Import ListNotations.
Require Import riscv.Minimal.

Section Riscv.

  Context {t: Set}.

  Context {MW: MachineWidth t}.

  Context {MFMemIsMem: MemoryFunctions t}.

  Context {RFF: RegisterFileFunctions Register t}.

  Inductive LogEvent :=
  | EvLoadWord(addr: Z)(i: Instruction)
  | EvStoreWord(addr: Z)(v: word 32).

  Local Notation RiscvMachine := (riscv.RiscvMachine.RiscvMachine Register t Empty_set).
  Local Notation RiscvMachineL := (riscv.RiscvMachine.RiscvMachine Register t LogEvent).

  Definition downgrade: RiscvMachineL -> RiscvMachine :=
    fun '(mkRiscvMachine regs pc nextPC mem log) => mkRiscvMachine regs pc nextPC mem nil.

  Definition upgrade: RiscvMachine -> list LogEvent -> RiscvMachineL :=
    fun '(mkRiscvMachine regs pc nextPC mem _) log => mkRiscvMachine regs pc nextPC mem log.

  Definition liftL0{B: Type}(f: OState RiscvMachine B):  OState RiscvMachineL B :=
    fun s => let (ob, s') := f (downgrade s) in (ob, upgrade s' s.(getLog)).

  Definition liftL1{A B: Type}(f: A -> OState RiscvMachine B): A -> OState RiscvMachineL B :=
    fun a s => let (ob, s') := f a (downgrade s) in (ob, upgrade s' s.(getLog)).

  Definition liftL2{A1 A2 B: Type}(f: A1 -> A2 -> OState RiscvMachine B):
    A1 -> A2 -> OState RiscvMachineL B :=
    fun a1 a2 s => let (ob, s') := f a1 a2 (downgrade s) in (ob, upgrade s' s.(getLog)).

  Instance IsRiscvMachineL: RiscvProgram (OState RiscvMachineL) t :=  {|
      getRegister := liftL1 getRegister;
      setRegister := liftL2 setRegister;
      getPC := liftL0 getPC;
      setPC := liftL1 setPC;
      loadByte   := liftL1 loadByte;
      loadHalf   := liftL1 loadHalf;
      loadWord a :=
        m <- get;
        res <- (liftL1 loadWord a);
        put (logCons m (EvLoadWord (regToZ_unsigned a) (decode RV64IM (uwordToZ res))));;
        Return res;
      loadDouble := liftL1 loadDouble;
      storeByte   := liftL2 storeByte;
      storeHalf   := liftL2 storeHalf;
      storeWord a v :=
        m <- get;
        put (logCons m (EvStoreWord (regToZ_unsigned a) v));;
        liftL2 storeWord a v;
      storeDouble := liftL2 storeDouble;
      step := liftL0 step;
      isMMIOAddr := isMMIOAddr;
      raiseException{A} := liftL2 (raiseException (A := A));
  |}.

End Riscv.

Existing Instance IsRiscvMachineL. (* needed because it was defined inside a Section *)
