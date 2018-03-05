Require Import Coq.ZArith.BinInt.
Require Import bbv.WordScope.
Require Import bbv.DepEqNat.
Require Import riscv.util.NameWithEq.
Require Import riscv.RiscvBitWidths.
Require Import riscv.util.Monad.
Require Import riscv.util.StateMonad.
Require Import riscv.Decode.
Require Import riscv.Memory. (* should go before Program because both define loadByte etc *)
Require Import riscv.Program.
Require Import riscv.Execute.
Require Import riscv.util.PowerFunc.
Require Import riscv.Utility.
Require Import Coq.Lists.List.

Section Riscv.

  Context {B: RiscvBitWidths}.

  Instance A: Alu (word wXLEN) (word wXLEN). Admitted.

  Instance immmm: IntegralConversion MachineInt (word wXLEN). Admitted.
  Instance immmm': IntegralConversion (word wXLEN) MachineInt. Admitted.

  (* TODO this is not the way to do it *)
  Instance c: Convertible (word wXLEN) (word wXLEN). Admitted.
  Instance ic8: IntegralConversion Int8 (word wXLEN). Admitted.
  Instance ic16: IntegralConversion Int16 (word wXLEN). Admitted.
  Instance ic32: IntegralConversion Int32 (word wXLEN). Admitted.
  Instance ic8': IntegralConversion (word wXLEN) Int8. Admitted.
  Instance ic16': IntegralConversion (word wXLEN) Int16. Admitted.
  Instance ic32': IntegralConversion (word wXLEN) Int32. Admitted.
  Instance ic8u: IntegralConversion Word8 (word wXLEN). Admitted.
  Instance ic16u: IntegralConversion Word16 (word wXLEN). Admitted.
  Instance ic32u: IntegralConversion Word32 (word wXLEN). Admitted.
  Instance icZt: IntegralConversion Z (word wXLEN). Admitted.
  Instance icZu: IntegralConversion Z (word wXLEN). Admitted.
  Instance icut: IntegralConversion (word wXLEN) (word wXLEN). Admitted.
  Instance ictu: IntegralConversion (word wXLEN) (word wXLEN). Admitted.

  Definition MW: MachineWidth (word wXLEN) := MachineWidthInst (Z.of_nat log2wXLEN) (word wXLEN).

  Existing Instance MW.

  Definition Register := Z.

  Definition Register0: Register := 0%Z.

  Instance ZName: NameWithEq := {|
    name := Z
  |}.

  Definition run1{M: Type -> Type}{MM: Monad M}{RVS: RiscvState M}: M unit :=
    pc <- getPC;
    inst <- loadWord pc;
    execute (decode (Z.of_nat wXLEN) (Int32ToMachineInt inst));;
    step.

  Definition run{M: Type -> Type}{MM: Monad M}{RVS: RiscvState M}: nat -> M unit :=
    fun n => power_func (fun m => run1 ;; m) n (Return tt).

  Record RiscvMachine := mkRiscvMachine {
    machineMem: mem 8;
    registers: Register -> word wXLEN;
    pc: word wXLEN;
    nextPC: word wXLEN;
    exceptionHandlerAddr: word wXLEN;
  }.

  Definition with_machineMem me ma :=
    mkRiscvMachine me ma.(registers) ma.(pc) ma.(nextPC) ma.(exceptionHandlerAddr).
  Definition with_registers r ma :=
    mkRiscvMachine ma.(machineMem) r ma.(pc) ma.(nextPC) ma.(exceptionHandlerAddr).
  Definition with_pc p ma :=
    mkRiscvMachine ma.(machineMem) ma.(registers) p ma.(nextPC) ma.(exceptionHandlerAddr).
  Definition with_nextPC npc ma :=
    mkRiscvMachine ma.(machineMem) ma.(registers) ma.(pc) npc ma.(exceptionHandlerAddr).
  Definition with_exceptionHandlerAddr eh ma :=
    mkRiscvMachine ma.(machineMem) ma.(registers) ma.(pc) ma.(nextPC) eh.

  Definition TODO{T: Type}: T. Admitted.

  Instance IsRiscvMachine: RiscvState (State RiscvMachine) :=
  {|
      getRegister := fun (reg: name) =>
        if dec (reg = Register0) then
          Return $0
        else
          machine <- get; Return (machine.(registers) reg);

      setRegister := fun s ic (reg: name) (v: s) =>
        if dec (reg = Register0) then
          Return tt
        else
          machine <- get;
          let newRegs := (fun reg2 => if dec (reg = reg2)
                                      then (fromIntegral v)
                                      else machine.(registers) reg2) in
          put (with_registers newRegs machine);

      getPC := gets pc;

      setPC := fun newPC =>
        machine <- get;
        put (with_nextPC newPC machine);

      loadByte a := m <- get; match Memory.loadByte m.(machineMem) a with
      | Some v => Return v
      | None => put (with_nextPC m.(exceptionHandlerAddr) m);; Return (mkSignedWord $0)
      end;

      loadHalf := TODO;
      loadWord := TODO;
      loadDouble := TODO;

      storeByte := TODO;
      storeHalf := TODO;
      storeWord := TODO;
      storeDouble := TODO;

      step :=
        machine <- get;
        match machine with
        | mkRiscvMachine imem regs pc npc eh =>
            put (mkRiscvMachine imem regs npc (npc ^+ $4) eh)
        end;

      raiseException := TODO;
  |}.

  (* Puts given program at address 0, and makes pc point to beginning of program, i.e. 0.
     TODO maybe later allow any address?
     Note: Keeps the original exceptionHandlerAddr, and the values of the registers,
     which might contain any undefined garbage values, so the compiler correctness proof
     will show that the program is correct even then, i.e. no initialisation of the registers
     is needed. *)
  Definition putProgram(prog: list (word 32))(m: RiscvMachine): RiscvMachine. Admitted. (*
    match m with
    | mkRiscvMachine _ regs _ _ eh =>
        mkRiscvMachine (list_to_mem _ prog) regs $0 $4 eh
    end. *)

End Riscv.

Existing Instance IsRiscvMachine. (* needed because it was defined inside a Section *)
