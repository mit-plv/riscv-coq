Require Import Coq.ZArith.BinInt.
Require Import riscv.util.Monads. Import OStateOperations.
Require Import riscv.util.MonadNotations.
Require Import riscv.Decode.
Require Import riscv.Memory. (* should go before Program because both define loadByte etc *)
Require Import riscv.Program.
Require Import riscv.Execute.
Require Import riscv.util.PowerFunc.
Require Import riscv.Utility.
Require Import Coq.Lists.List. Import ListNotations.
Require Import riscv.Minimal.
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

  Local Notation RiscvMachine := (riscv.RiscvMachine.RiscvMachine Register Empty_set).
  Local Notation RiscvMachineL := (riscv.RiscvMachine.RiscvMachine Register LogEvent).

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

  Instance IsRiscvMachineL: RiscvProgram (OState RiscvMachineL) word := {|
      getRegister := liftL1 getRegister;
      setRegister := liftL2 setRegister;
      getPC := liftL0 getPC;
      setPC := liftL1 setPC;
      loadByte   := liftL1 loadByte;
      loadHalf   := liftL1 loadHalf;
      loadWord a :=
        m <- get;
        res <- (liftL1 loadWord a);
        put (logCons m (mkLogItem (EvLoadWord (regToZ_unsigned a) (decode RV64IM (LittleEndian.combine 4 res)))));;
        Return res;
      loadDouble := liftL1 loadDouble;
      storeByte   := liftL2 storeByte;
      storeHalf   := liftL2 storeHalf;

      storeWord a v :=
        Bind get
             (fun m =>
                Bind (Monad := (OState_Monad _)) (* why does Coq infer OStateND_Monad?? *)
                     (put (logCons m (mkLogItem (EvStoreWord (regToZ_unsigned a) v))))
                     (fun (_: unit) =>
                        liftL2 storeWord a v));

      storeDouble := liftL2 storeDouble;
      step := liftL0 step;
      raiseException{A} := liftL2 (raiseException (A := A));
  |}.

End Riscv.

Existing Instance IsRiscvMachineL. (* needed because it was defined inside a Section *)
