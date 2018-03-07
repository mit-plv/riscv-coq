Require Import Coq.ZArith.BinInt.
Require Import riscv.util.NameWithEq.
Require Import riscv.RiscvBitWidths.
Require Import riscv.util.StateMonad.
Require Import riscv.Utility.
Require Import riscv.NoVirtualMemory.
Require Import riscv.Decode.
Require Import riscv.Program.

Local Open Scope Z.
Local Open Scope alu_scope.

Section Riscv.

  Context {Name: NameWithEq}. (* register name *)
  Notation Register := (@name Name).
  Existing Instance eq_name_dec.

  Context {B: RiscvBitWidths}.

  Context {t: Set}.

  Context {MW: MachineWidth t}.

  Definition execute{M: Type -> Type}{MM: Monad M}{MP: MonadPlus M}{RVS: RiscvState M}
    (i: Instruction): M unit :=
    match i with
    (* begin ast *)
    (* end ast *)
    | _ => mzero
    end.

End Riscv.
