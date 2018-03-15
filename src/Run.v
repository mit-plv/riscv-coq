Require Import Coq.ZArith.BinInt.
Require Import bbv.WordScope.
Require Import bbv.DepEqNat.
Require Import riscv.util.NameWithEq.
Require Import riscv.RiscvBitWidths.
Require Import riscv.util.Monads.
Require Import riscv.Decode.
Require Import riscv.Memory. (* should go before Program because both define loadByte etc *)
Require Import riscv.Program.
Require Import riscv.Execute.
Require Import riscv.util.PowerFunc.
Require Import riscv.Utility.
Require Import Coq.Lists.List.
Require Import riscv.Minimal.

Section Riscv.

  Context {B: RiscvBitWidths}.

  Context {MW: MachineWidth (word wXLEN)}.

  Definition Register := Z.

  Definition Register0: Register := 0%Z.

  Instance ZName: NameWithEq := {|
    name := Z
  |}.

  Context {M: Type -> Type}.
  Context {MM: Monad M}.
  Context {MP: MonadPlus M}.
  Context {RVP: RiscvProgram M (word wXLEN)}.
  Context {RVS: RiscvState M (word wXLEN)}.

  Definition run1:
    M unit :=
    pc <- getPC;
    inst <- loadWord pc;
    execute (decode (Z.of_nat wXLEN) (wordToZ inst));;
    step.

  Definition run: nat -> M unit :=
    fun n => power_func (fun m => run1 ;; m) n (Return tt).

End Riscv.
