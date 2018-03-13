Require Import Coq.Lists.List.
Import ListNotations.
Require Import riscv.util.NameWithEq.
Require Import riscv.RiscvBitWidths.
Require Import riscv.util.Monads.
Require Import riscv.Utility.
Require Import riscv.Decode.
Require Import riscv.Program.
Require riscv.ExecuteI.
Require riscv.ExecuteM.
Require riscv.ExecuteI64.
Require riscv.ExecuteM64.

Section Riscv.

  Context {Name: NameWithEq}. (* register name *)
  Notation Register := (@name Name).
  Existing Instance eq_name_dec.

  Context {t: Set}.

  Context {MW: MachineWidth t}.

  Context {M: Type -> Type}.

  Context {MM: Monad M}.

  Context {MP: MonadPlus M}.

  Context {RVS: RiscvState M}.

  Context {B: RiscvBitWidths}.

  Definition get_execute_list: list (Instruction -> M unit) :=
    match bitwidth with
    | Bitwidth32 => [ExecuteI.execute; ExecuteM.execute]
    | Bitwidth64 => [ExecuteI.execute; ExecuteM.execute; ExecuteI64.execute; ExecuteM64.execute]
    end.

  Definition execute(i: Instruction): M unit :=
    match i with
    | InvalidInstruction => raiseException zero two
    | _                  => msum (map (fun f => f i) get_execute_list)
    end.

End Riscv.
