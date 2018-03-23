Require Import Coq.ZArith.BinInt.
Require Import bbv.WordScope.
Require Import bbv.DepEqNat.
Require Import riscv.util.NameWithEq.
Require Import riscv.RiscvBitWidths.
Require Import riscv.util.Monads.
Require Import riscv.Decode.
Require Import riscv.Memory. (* should go before Program because both define loadByte etc *)
Require Import riscv.Program.
Require Import riscv.Execute.
Require Import riscv.util.PowerFunc.
Require Import riscv.Utility.
Require Import Coq.Lists.List.

Section Riscv.

  Context {B: RiscvBitWidths}.

  Context {MW: MachineWidth (word wXLEN)}.

  Context {Mem: Set}.

  Context {MemIsMem: Memory Mem (word wXLEN)}.

  Definition Register0: Register := 0%Z.

  Instance ZName: NameWithEq := {|
    name := Z
  |}.

  Record RiscvMachineCore := mkRiscvMachineCore {
    registers: Register -> word wXLEN;
    pc: word wXLEN;
    nextPC: word wXLEN;
    exceptionHandlerAddr: MachineInt;
  }.

  Record RiscvMachine := mkRiscvMachine {
    core: RiscvMachineCore;
    machineMem: Mem;
  }.

  Definition with_registers r ma :=
    mkRiscvMachine (mkRiscvMachineCore
        r ma.(core).(pc) ma.(core).(nextPC) ma.(core).(exceptionHandlerAddr))
        ma.(machineMem).
  Definition with_pc p ma :=
    mkRiscvMachine (mkRiscvMachineCore
        ma.(core).(registers) p ma.(core).(nextPC) ma.(core).(exceptionHandlerAddr))
        ma.(machineMem).
  Definition with_nextPC npc ma :=
    mkRiscvMachine (mkRiscvMachineCore
        ma.(core).(registers) ma.(core).(pc) npc ma.(core).(exceptionHandlerAddr))
        ma.(machineMem).
  Definition with_exceptionHandlerAddr eh ma :=
    mkRiscvMachine (mkRiscvMachineCore
        ma.(core).(registers) ma.(core).(pc) ma.(core).(nextPC) eh)
        ma.(machineMem).
  Definition with_machineMem m ma :=
    mkRiscvMachine ma.(core) m.

  Definition liftLoad{R}(f: Mem -> word wXLEN -> R): word wXLEN -> OState RiscvMachine R :=
    fun a => m <- gets machineMem; Return (f m a).

  Definition liftStore{R}(f: Mem -> word wXLEN -> R -> Mem):
    word wXLEN -> R -> OState RiscvMachine unit :=
    fun a v => m <- get; put (with_machineMem (f m.(machineMem) a v) m).
  
  Instance IsRiscvMachine: RiscvProgram (OState RiscvMachine) (word wXLEN) :=
  {|
      getRegister := fun (reg: Register) =>
        if dec (reg = Register0) then
          Return $0
        else
          machine <- get; Return (machine.(core).(registers) reg);

      setRegister := fun (reg: Register) v =>
        if dec (reg = Register0) then
          Return tt
        else
          machine <- get;
          let newRegs := (fun reg2 => if dec (reg = reg2)
                                      then v
                                      else machine.(core).(registers) reg2) in
          put (with_registers newRegs machine);

      getPC := machine <- get; Return machine.(core).(pc);

      setPC := fun newPC =>
        machine <- get;
        put (with_nextPC newPC machine);

      loadByte   := liftLoad Memory.loadByte;
      loadHalf   := liftLoad Memory.loadHalf;
      loadWord   := liftLoad Memory.loadWord;
      loadDouble := liftLoad Memory.loadDouble;

      storeByte   := liftStore Memory.storeByte;
      storeHalf   := liftStore Memory.storeHalf;
      storeWord   := liftStore Memory.storeWord;
      storeDouble := liftStore Memory.storeDouble;

      step :=
        m <- get;
        put (with_nextPC (m.(core).(nextPC) ^+ $4) (with_pc m.(core).(nextPC) m));

      getCSRField_MTVecBase :=
        machine <- get;
        Return machine.(core).(exceptionHandlerAddr);

      endCycle A := Return None;
  |}.

  (* Puts given program at address 0, and makes pc point to beginning of program, i.e. 0.
     TODO maybe later allow any address?
     Note: Keeps the original exceptionHandlerAddr, and the values of the registers,
     which might contain any undefined garbage values, so the compiler correctness proof
     will show that the program is correct even then, i.e. no initialisation of the registers
     is needed. *)
  Definition putProgram(prog: list (word 32))(ma: RiscvMachine): RiscvMachine :=
    with_pc $0 (with_nextPC $4 (with_machineMem (store_word_list prog $0 ma.(machineMem)) ma)).

End Riscv.

Existing Instance IsRiscvMachine. (* needed because it was defined inside a Section *)
