Require Import Coq.ZArith.BinInt.
Require Import bbv.WordScope.
Require Import riscv.RiscvBitWidths.
Require Import riscv.util.Monads.
Require Import riscv.Decode.
Require Import riscv.RiscvBitWidths.
Require Import riscv.Memory. (* should go before Program because both define loadByte etc *)
Require Import riscv.Program.
Require Import riscv.Execute.
Require Import riscv.util.PowerFunc.
Require Import riscv.Utility.

Section Riscv.

  Context {B: RiscvBitWidths}.

  Context {MW: MachineWidth (word wXLEN)}.

  Definition Register0: Register := 0%Z.

  Context {M: Type -> Type}.
  Context {MM: Monad M}.
  Context {MP: MonadPlus M}.
  Context {RVP: RiscvProgram M (word wXLEN)}.
  Context {RVS: RiscvState M (word wXLEN)}.

  Definition RV_wXLEN_IM: InstructionSet :=
    match bitwidth with
    | Bitwidth32 => RV32IM
    | Bitwidth64 => RV64IM
    end.
  
  Definition run1:
    M unit :=
    pc <- getPC;
    inst <- loadWord pc;
    execute (decode RV_wXLEN_IM (uwordToZ inst));;
    step.

  Definition run: nat -> M unit :=
    fun n => power_func (fun m => run1 ;; m) n (Return tt).

End Riscv.
