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
Require Import Coq.Lists.List.

Section Riscv.

  Context {B: RiscvBitWidths}.

  Context {Name: NameWithEq}. (* register name *)
  Notation Reg := (@name Name).
  Existing Instance eq_name_dec.

  Definition run1{M: Type -> Type}{MM: Monad M}{RVS: RiscvState M}: M unit :=
    pc <- getPC;
    inst <- loadInst pc;
    setPC (pc ^+ $4);;
    execute inst.

  Definition run{M: Type -> Type}{MM: Monad M}{RVS: RiscvState M}: nat -> M unit :=
    fun n => power_func (fun m => run1 ;; m) n (Return tt).

  Record RiscvMachine := mkRiscvMachine {
    instructionMem: word wXLEN -> Instruction;
    registers: Reg -> word wXLEN;
    pc: word wXLEN;
    exceptionHandlerAddr: word wXLEN;
  }.

  Instance IsRiscvMachine: RiscvState (State RiscvMachine) :=
  {|
      getRegister := fun (reg: Register) =>
        match reg with
        | RegO => Return $0
        | RegS r => machine <- get; Return (machine.(registers) r)
        end;
      setRegister := fun (reg: Register) (v: word wXLEN) =>
        match reg with
        | RegO => Return tt
        | RegS r => machine <- get;
                    match machine with
                    | mkRiscvMachine imem regs pc eh =>
                        put (mkRiscvMachine imem 
                                            (fun reg2 => if dec (r = reg2) then v else regs reg2)
                                            pc eh)
                    end
        end;
      loadInst := fun (addr: word wXLEN) =>
        im <- gets instructionMem;
        Return (im addr);
      getPC := gets pc;
      setPC := fun (newPC: word wXLEN) =>
        machine <- get;
        match machine with
        | mkRiscvMachine imem regs pc eh =>
            put (mkRiscvMachine imem regs newPC eh)
        end;
  |}.

  (* Puts given program at address 0, and makes pc point to beginning of program, i.e. 0.
     TODO maybe later allow any address?
     Note: Keeps the original exceptionHandlerAddr, and the values of the registers,
     which might contain any undefined garbage values, so the compiler correctness proof
     will show that the program is correct even then, i.e. no initialisation of the registers
     is needed. *)
  Definition putProgram(prog: list Instruction)(m: RiscvMachine): RiscvMachine :=
    match m with
    | mkRiscvMachine _ regs _ eh =>
        mkRiscvMachine (fun (i: word wXLEN) => nth (Nat.div (wordToNat i) 4) prog InfiniteJal)
                       regs $0 eh
    end.

End Riscv.

Existing Instance IsRiscvMachine. (* needed because it was defined inside a Section *)
