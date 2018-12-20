(* equivalence between Run.run, where the composition of several steps is done
   using monadic bind, and runsToNonDet.runsTo, where the composition of several
   steps is done by the Inductive *)
Require Import coqutil.Word.Interface.
Require Import riscv.Run.
Require Import riscv.runsToNonDet.
Require Import riscv.AxiomaticRiscv.
Require Import riscv.RiscvMachine.
Require Import riscv.Decode.
Require Import riscv.util.BitWidths.
Require Import riscv.MkMachineWidth.
Require Import riscv.Program.
Require Import riscv.Utility.


Section Equiv.

  Context `{AxiomaticRiscv}.
  Context {RVS: RiscvState M word}.
  Variable BW: BitWidths.

  Definition run: nat -> M unit := run. (* just to make sure all implicit arguments are there *)

  Lemma runsToNonDet_to_Run_aux: forall (initial: RiscvMachine Register Action)
                                    (P: RiscvMachine Register Action -> Prop),
      runsTo (mcomp_sat run1) initial P ->
      runsTo (mcomp_sat run1) initial (fun final =>
         P final /\ exists (n: nat), mcomp_sat (run n) initial P).
  Proof.
    induction 1.
    - apply runsToDone.
      split; [assumption|].
      exists O.
      unfold run, Run.run.
      simpl.
      apply go_done.
      assumption.
    - eapply runsToStep; [eassumption|].
      intros.
      pose proof H2 as A.
      specialize H2 with (1 := H3).

(*

      eapply runsTo_weaken; [eassumption|].
      intros final F.
      simpl in F.
      destruct F as [? [n F]].
      split; [assumption|].
      exists (S n).
      unfold run, Run.run.
      simpl.
      eapply go_seq; [eassumption|].
      intros middleL MI.
      specialize H1 with (1 := MI).

      specialize A with (1 := H4).

eauto.
      unfold run1
      simpl.
eassumption.


      simpl.

      eapply H2.
      eauto.
      About runsTo_ind.
*)

  Abort.

  Lemma runsToNonDet_to_Run: forall (initial: RiscvMachine Register Action)
                                    (P: RiscvMachine Register Action -> Prop),
      runsTo (mcomp_sat run1) initial P ->
      exists (n: nat), mcomp_sat (run n) initial P.
  Proof.
    induction 1.
    - exists O.
      unfold run, Run.run.
      simpl.
      apply go_done.
      assumption.
    -
  Abort.


  Lemma Run_to_runsToNonDet: forall (n: nat) (initial: RiscvMachine Register Action)
                                    (P: RiscvMachine Register Action -> Prop),
      mcomp_sat (run n) initial P ->
      runsTo (mcomp_sat run1) initial P.
  Proof.
    induction n; intros.
    - unfold run, Run.run in H0. simpl in H0.
      apply runsToDone.
      About go_done.
      (* needs inverse direction *)
      admit.
    - unfold run, Run.run in H0. simpl in H0.
  Abort.

End Equiv.
