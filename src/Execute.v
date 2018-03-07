Require Import Coq.ZArith.BinInt.
Require Import Coq.Lists.List.
Import ListNotations.
Require Import riscv.util.NameWithEq.
Require Import riscv.RiscvBitWidths.
Require Import riscv.util.MonadPlus.
Require Import riscv.Utility.
Require Import riscv.NoVirtualMemory.
Require Import riscv.Decode.
Require Import riscv.Program.
Require riscv.ExecuteI.
Require riscv.ExecuteM.

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
    | InvalidInstruction =>
        raiseException zero two
    | _ => msum (map (fun f => f i) [ExecuteI.execute; ExecuteM.execute])
    end.

End Riscv.
