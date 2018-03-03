Require Import Coq.ZArith.BinInt.
Require Import bbv.WordScope.
Require Import bbv.DepEqNat.
Require Import riscv.util.NameWithEq.
Require Import riscv.RiscvBitWidths.
Require Import riscv.util.Monad.
Require Import riscv.util.StateMonad.
Require Import riscv.Decode.
Require Import riscv.Program.
Require Import riscv.Execute.
Require Import riscv.util.PowerFunc.
Require Import riscv.Memory.
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
    machineMem: mem wXLEN;
    registers: Register -> word wXLEN;
    pc: word wXLEN;
    nextPC: word wXLEN;
    exceptionHandlerAddr: word wXLEN;
  }.

  Definition ensure_aligned{RVS: RiscvState (State RiscvMachine)}(addr: Z)(m: nat):
    State RiscvMachine unit :=
    if dec (Z.modulo addr 4 = 0)%Z then
      Return tt
    else
      h <- gets exceptionHandlerAddr;
      setPC h.
  (* TODO generalize? *)

(*
  Definition ensure_aligned{RVS: RiscvState (State RiscvMachine)}(addr: word wXLEN)(m: nat):
    State RiscvMachine unit :=
    if dec (wmod addr $m = $0) then
      Return tt
    else
      h <- gets exceptionHandlerAddr;
      setPC h.
  (* TODO generalize? *)

  Definition ensure_aligned{RVS: RiscvState (State RiscvMachine)}: State RiscvMachine unit :=
    Return tt.

  Definition ensure_aligned{MM: Monad (State RiscvMachine)}{RVS: RiscvState (State RiscvMachine)}:
  State RiscvMachine unit. refine (Return tt).

  Definition ensure_aligned{RVS: RiscvState (State RiscvMachine)}(addr: word wXLEN)(m: nat):
     RiscvState (State RiscvMachine).
     refine (@Return _ _ RVS _ _).

  Definition ensure_aligned(addr: word wXLEN)(m: nat):
     State RiscvMachine unit := Return tt.


  Definition ensure_aligned{RVS: RiscvState (State RiscvMachine)}(addr: word wXLEN)(m: nat):
     State RiscvMachine unit := Return tt.

  Definition ensure_aligned{MM: Monad (State RiscvMachine)}{RVS: RiscvState (State RiscvMachine)}(addr: word wXLEN)(m: nat):
     State RiscvMachine unit. refine (@Return _ MM _ tt).
  *)

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
          match machine with
          | mkRiscvMachine imem regs pc npc eh =>
              put (mkRiscvMachine imem 
                      (fun reg2 => if dec (reg = reg2) then (fromIntegral v) else regs reg2)
                      pc npc eh)
          end;

      getPC := gets pc;

      setPC := fun newPC =>
        machine <- get;
        match machine with
        | mkRiscvMachine imem regs pc npc eh =>
            put (mkRiscvMachine imem regs pc newPC eh)
        end;

      loadByte := TODO;
      loadHalf := TODO;
      loadWord := TODO;
(*
      loadWord := fun x => 
        let x := wordToZ x in (* TODO fix *)
        ensure_aligned x 4;;
        m <- get;
        match read_mem x m.(machineMem) with
        | Some v => Return $123 (* TODO should be v *)
        | None => setPC m.(exceptionHandlerAddr)
        end;
      (* TODO if wXLEN = 64, we have to split *)
*)
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
