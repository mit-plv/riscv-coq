(* For debugging purposes *)

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
Require Import Coq.Lists.List.
Import ListNotations.
Require Import riscv.Run.

Section Riscv.

  Context {B: RiscvBitWidths}.

  Inductive TraceEvent: Set :=
  | TraceLoad(addr: Z)(val: word 32)
  | TraceLoadFailure(addr: Z).

  Record TraceRiscvMachine := mkTraceRiscvMachine {
    machineMem: mem 32;
    registers: Register -> word wXLEN;
    pc: word wXLEN;
    nextPC: word wXLEN;
    exceptionHandlerAddr: word wXLEN;
    executionTrace: list TraceEvent;
  }.

  Definition TODO{T: Type}: T. Admitted.

  Instance IsTraceRiscvMachine: RiscvState (State TraceRiscvMachine) :=
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
          | mkTraceRiscvMachine imem regs pc npc eh tr =>
              put (mkTraceRiscvMachine imem 
                                  (fun reg2 => if dec (reg = reg2) then v else regs reg2)
                                  pc npc eh tr)
          end;

      getPC := 
        p <- gets pc;
        Return (wordToZ p); (* TODO this should be unsigned *)

      setPC := fun (newPC: Z) =>
        machine <- get;
        match machine with
        | mkTraceRiscvMachine imem regs pc npc eh tr =>
            put (mkTraceRiscvMachine imem regs pc (ZToWord _ newPC) eh tr)
        end;

      loadByte := TODO;
      loadHalf := TODO;

      loadWord := fun x => 
        machine <- get;
        match machine with
        | mkTraceRiscvMachine imem regs pc npc eh tr =>
            let addr := (ZToWord 32 (x / 4)) in
            match read_mem addr imem with
            | Some v => 
                put (mkTraceRiscvMachine imem regs pc npc eh (tr ++ [TraceLoad x v]));;
                Return v
            | None =>
                put (mkTraceRiscvMachine imem regs pc npc eh (tr ++ [TraceLoadFailure x]));;
                Return $0
            end
        end;

      loadDouble := TODO;

      storeByte := TODO;
      storeHalf := TODO;
      storeWord := TODO;
      storeDouble := TODO;

      step :=
        machine <- get;
        match machine with
        | mkTraceRiscvMachine imem regs pc npc eh tr =>
            put (mkTraceRiscvMachine imem regs npc (npc ^+ $4) eh tr)
        end;
  |}.

End Riscv.

Existing Instance IsTraceRiscvMachine. (* needed because it was defined inside a Section *)
