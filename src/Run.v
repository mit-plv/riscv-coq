Require Import Coq.ZArith.BinInt.
Require Import coqutil.Word.LittleEndian.
Require Import riscv.util.BitWidths.
Require Import riscv.util.Monads.
Require Import riscv.util.MonadNotations.
Require Import riscv.Decode.
Require Import riscv.util.BitWidths.
Require Import riscv.Memory. (* should go before Program because both define loadByte etc *)
Require Import riscv.Program.
Require Import riscv.Execute.
Require Import riscv.util.PowerFunc.
Require Import riscv.Utility.

Section Riscv.

  Context {B: BitWidths}.
  Context {mword: Set}.
  Context {MW: MachineWidth mword}.

  Context {M: Type -> Type}.
  Context {MM: Monad M}.
  Context {RVP: RiscvProgram M mword}.
  Context {RVS: RiscvState M mword}.

  Definition RV_wXLEN_IM: InstructionSet :=
    match bitwidth with
    | BW32 => RV32IM
    | BW64 => RV64IM
    end.

  Definition exe: Instruction -> M unit.
    refine execute.
    Fail exact RVS.
    (* TODO universe inconsistency *)
  Abort.

  Definition run1:
    M unit :=
    pc <- getPC;
    inst <- loadWord pc;
    execute (decode RV_wXLEN_IM (combine 4 inst));;
    step.

  Definition run: nat -> M unit :=
    fun n => power_func (fun m => run1 ;; m) n (Return tt).

End Riscv.
