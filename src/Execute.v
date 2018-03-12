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

  Definition execute(l: list (Instruction -> M unit))(i: Instruction): M unit :=
    match i with
    | InvalidInstruction => raiseException zero two
    | _                  => msum (map (fun f => f i) l)
    end.

  Definition execute32: Instruction -> M unit :=
    execute [ExecuteI.execute; ExecuteM.execute].

  Definition execute64: Instruction -> M unit :=
    execute [ExecuteI.execute; ExecuteM.execute; ExecuteI64.execute; ExecuteM64.execute].

End Riscv.
