Require Import Coq.ZArith.BinInt.
Require Import coqutil.Word.LittleEndian.
Require Import riscv.Utility.Monads.
Require Import riscv.Utility.MonadNotations.
Require Import riscv.Spec.Decode.
Require Import riscv.Platform.Memory. (* should go before Program because both define loadByte etc *)
Require Import riscv.Spec.Machine.
Require Import riscv.Spec.Execute.
Require Import riscv.Utility.Utility.

Section Riscv.

  Context {mword: Type}.
  Context {MW: MachineWidth mword}.

  Context {M: Type -> Type}.
  Context {MM: Monad M}.
  Context {RVM: RiscvProgramWithLeakage}.
  Context {RVS: RiscvMachine M mword}.

  Print leakage_of_instr. Print decode. Print leakEvent. Print getRegister. Print MachineWidth.

  Definition run1(iset: InstructionSet):
    M unit :=
    pc <- getPC;
  inst <- loadWord Fetch pc;
  let inst' := decode iset (combine 4 inst) in
  leakage_event <- leakage_of_instr regToZ_unsigned regToZ_signed getRegister inst';
  leakEvent leakage_event;;
  execute inst';;
  endCycleNormal.

  (* Note: We cannot use
     power_func (fun m => run1 iset;; m) n (Return tt)
     to obtain a monadic computation executing n instructions,
     because if one cycle ends early (due to an exception),
     all the remaining operations are skipped.
     The lifting from run1 to run-many has to be done in a
     monad-specific way. *)

End Riscv.
