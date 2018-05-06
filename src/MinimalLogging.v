Require Import Coq.ZArith.BinInt.
Require Import bbv.WordScope.
Require Import riscv.RiscvBitWidths.
Require Import riscv.util.Monads.
Require Import riscv.Decode.
Require Import riscv.Memory. (* should go before Program because both define loadByte etc *)
Require Import riscv.Program.
Require Import riscv.Execute.
Require Import riscv.util.PowerFunc.
Require Import riscv.Utility.
Require Import Coq.Lists.List. Import ListNotations.
Require Import riscv.Minimal.

Section Riscv.

  Context {B: RiscvBitWidths}.

  Context {MW: MachineWidth (word wXLEN)}.

  Context {Mem: Set}.

  Context {MemIsMem: Memory Mem wXLEN}.

  Context {RF: Type}.
  Context {RFI: RegisterFile RF Register (word wXLEN)}.
  
  Definition Log := list (Z * Instruction). (* addr, decoded instruction *)
  
  Record RiscvMachineL := mkRiscvMachineL {
    machine: @RiscvMachine _ Mem RF;
    log: Log;
  }.

  Definition with_machine m ml := mkRiscvMachineL m ml.(log).
  Definition with_log l ml := mkRiscvMachineL ml.(machine) l.  

  Definition liftL0{B: Type}(f: OState RiscvMachine B):  OState RiscvMachineL B :=
    fun s => let (ob, ma) := f s.(machine) in (ob, with_machine ma s).

  Definition liftL1{A B: Type}(f: A -> OState RiscvMachine B): A -> OState RiscvMachineL B :=
    fun a s => let (ob, ma) := f a s.(machine) in (ob, with_machine ma s).

  Definition liftL2{A1 A2 B: Type}(f: A1 -> A2 -> OState RiscvMachine B):
    A1 -> A2 -> OState RiscvMachineL B :=
    fun a1 a2 s => let (ob, ma) := f a1 a2 s.(machine) in (ob, with_machine ma s).
                                           
  Instance IsRiscvMachineL: RiscvProgram (OState RiscvMachineL) (word wXLEN) :=  {|
      getRegister := liftL1 getRegister;
      setRegister := liftL2 setRegister;
      getPC := liftL0 getPC;
      setPC := liftL1 setPC;
      loadByte   := liftL1 loadByte;
      loadHalf   := liftL1 loadHalf;
      loadWord a :=
        m <- get;
        res <- (liftL1 loadWord a);
        put (with_log (m.(log) ++ [(wordToZ a, decode RV64IM (wordToZ res))]) m);;
        Return res;
      loadDouble := liftL1 loadDouble;
      storeByte   := liftL2 storeByte;
      storeHalf   := liftL2 storeHalf;
      storeWord   := liftL2 storeWord;
      storeDouble := liftL2 storeDouble;
      step := liftL0 step;
      getCSRField_MTVecBase := liftL0 getCSRField_MTVecBase;
      endCycle A := Return None;
  |}.

  Definition putProgram(prog: list (word 32))(ma: RiscvMachineL): RiscvMachineL :=
    with_machine (putProgram prog ma.(machine)) ma.

End Riscv.

Existing Instance IsRiscvMachineL. (* needed because it was defined inside a Section *)
