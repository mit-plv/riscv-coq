Require Import Coq.ZArith.BinInt.
Require Import bbv.WordScope.
Require Import bbv.DepEqNat.
Require Import riscv.NameWithEq.
Require Import riscv.RiscvBitWidths.
Require Import riscv.Monad.
Require Import riscv.StateMonad.
Require Import riscv.Decode.
Require Import riscv.Program.
Require Import riscv.Execute.
Require Import riscv.PowerFunc.
Require Import riscv.Memory.
Require Import Coq.Lists.List.

Section Riscv.

  Context {B: RiscvBitWidths}.

  Definition Register0: Register := $0.

  Definition run1{M: Type -> Type}{MM: Monad M}{RVS: RiscvState M}: M unit :=
    pc <- getPC;
    inst <- loadWord pc;
    setPC (pc + 4)%Z;;
    execute (decode inst).

  Definition run{M: Type -> Type}{MM: Monad M}{RVS: RiscvState M}: nat -> M unit :=
    fun n => power_func (fun m => run1 ;; m) n (Return tt).

  Record RiscvMachine := mkRiscvMachine {
    machineMem: mem 32;
    registers: Register -> word wXLEN;
    pc: word wXLEN;
    exceptionHandlerAddr: word wXLEN;
  }.

  Definition TODO{T: Type}: T. Admitted.

  Instance IsRiscvMachine: RiscvState (State RiscvMachine) :=
  {|
      getRegister := fun (reg: Register) =>
        if dec (reg = Register0) then
          Return $0
        else
          machine <- get; Return (machine.(registers) reg);

      setRegister := fun (reg: Register) (v: word wXLEN) =>
        if dec (reg = Register0) then
          Return tt
        else
          machine <- get;
          match machine with
          | mkRiscvMachine imem regs pc eh =>
              put (mkRiscvMachine imem 
                                  (fun reg2 => if dec (reg = reg2) then v else regs reg2)
                                  pc eh)
          end;

      getPC := 
        p <- gets pc;
        Return (wordToZ p); (* TODO this should be unsigned *)

      setPC := fun (newPC: Z) =>
        machine <- get;
        match machine with
        | mkRiscvMachine imem regs pc eh =>
            put (mkRiscvMachine imem regs (ZToWord _ newPC) eh)
        end;

      loadByte := TODO;
      loadHalf := TODO;

      loadWord := fun x => 
        m <- gets machineMem;
        match read_mem (ZToWord 32 (x / 4)) m with
        | Some v => Return v
        | None => Return $0
        end;

      loadDouble := TODO;

      storeByte := TODO;
      storeHalf := TODO;
      storeWord := TODO;
      storeDouble := TODO;

  |}.

  Definition InfiniteJal := Jal Register0 (-4).

  (* Puts given program at address 0, and makes pc point to beginning of program, i.e. 0.
     TODO maybe later allow any address?
     Note: Keeps the original exceptionHandlerAddr, and the values of the registers,
     which might contain any undefined garbage values, so the compiler correctness proof
     will show that the program is correct even then, i.e. no initialisation of the registers
     is needed. *)
  Definition putProgram(prog: list (word 32))(m: RiscvMachine): RiscvMachine :=
    match m with
    | mkRiscvMachine _ regs _ eh =>
        mkRiscvMachine (list_to_mem _ prog) regs $0 eh
    end.

End Riscv.

Existing Instance IsRiscvMachine. (* needed because it was defined inside a Section *)
