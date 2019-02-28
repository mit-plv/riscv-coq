Require Import Coq.ZArith.BinInt.
Require Import riscv.Utility.Monads. Import OStateOperations.
Require Import riscv.Utility.MonadNotations.
Require Import riscv.Spec.Decode.
Require Import riscv.Platform.Memory. (* should go before Program because both define loadByte etc *)
Require Import riscv.Spec.Machine.
Require Import riscv.Spec.Execute.
Require Import riscv.Utility.PowerFunc.
Require Import riscv.Utility.Utility.
Require Import Coq.Lists.List. Import ListNotations.
Require Import riscv.Platform.Minimal.
Require Import coqutil.Map.Interface.


Section Riscv.
  Context {W: Words}.
  Context {Mem: map.map word byte}.
  Context {Registers: map.map Register word}.

  Inductive LogEvent :=
  | EvLoadWord(addr: Z)(i: Instruction)
  | EvStoreWord(addr: Z)(v: w32).

  Definition mkLogItem(e: LogEvent): LogItem LogEvent :=
    (* we don't log the memory because that would be too big to read *)
    ((map.empty, e, nil), (map.empty, nil)).

  Local Notation RiscvMachine := (riscv.Platform.RiscvMachine.RiscvMachine Register Empty_set).
  Local Notation RiscvMachineL := (riscv.Platform.RiscvMachine.RiscvMachine Register LogEvent).

  Definition downgrade: RiscvMachineL -> RiscvMachine :=
    fun '(mkRiscvMachine regs pc nextPC mem log) => mkRiscvMachine regs pc nextPC mem nil.

  Definition upgrade: RiscvMachine -> list (LogItem LogEvent) -> RiscvMachineL :=
    fun '(mkRiscvMachine regs pc nextPC mem _) log => mkRiscvMachine regs pc nextPC mem log.

  Definition liftL0{B: Type}(f: OState RiscvMachine B):  OState RiscvMachineL B :=
    fun s => let (ob, s') := f (downgrade s) in (ob, upgrade s' s.(getLog)).

  Definition liftL1{A B: Type}(f: A -> OState RiscvMachine B): A -> OState RiscvMachineL B :=
    fun a s => let (ob, s') := f a (downgrade s) in (ob, upgrade s' s.(getLog)).

  Definition liftL2{A1 A2 B: Type}(f: A1 -> A2 -> OState RiscvMachine B):
    A1 -> A2 -> OState RiscvMachineL B :=
    fun a1 a2 s => let (ob, s') := f a1 a2 (downgrade s) in (ob, upgrade s' s.(getLog)).

  Definition liftL3{A1 A2 A3 B: Type}(f: A1 -> A2 -> A3 -> OState RiscvMachine B):
    A1 -> A2 -> A3 -> OState RiscvMachineL B :=
    fun a1 a2 a3 s => let (ob, s') := f a1 a2 a3 (downgrade s) in (ob, upgrade s' s.(getLog)).

  Instance IsRiscvMachineL: RiscvProgram (OState RiscvMachineL) word := {
      getRegister := liftL1 getRegister;
      setRegister := liftL2 setRegister;
      getPC := liftL0 getPC;
      setPC := liftL1 setPC;
      loadByte   := liftL2 loadByte;
      loadHalf   := liftL2 loadHalf;
      loadWord kind a :=
        m <- get;
        res <- (liftL2 loadWord kind a);
        put (withLogItem (mkLogItem (EvLoadWord (regToZ_unsigned a) (decode RV64IM (LittleEndian.combine 4 res)))) m);;
        Return res;
      loadDouble := liftL2 loadDouble;
      storeByte   := liftL3 storeByte;
      storeHalf   := liftL3 storeHalf;

      storeWord kind a v :=
        Bind get
             (fun m =>
                Bind (Monad := (OState_Monad _)) (* why does Coq infer OStateND_Monad?? *)
                     (put (withLogItem (mkLogItem (EvStoreWord (regToZ_unsigned a) v)) m))
                     (fun (_: unit) =>
                        liftL3 storeWord kind a v));

      storeDouble := liftL3 storeDouble;
      step := liftL0 step;
      raiseExceptionWithInfo{A} := liftL3 (raiseExceptionWithInfo (A := A));
  }.

End Riscv.

Existing Instance IsRiscvMachineL. (* needed because it was defined inside a Section *)
