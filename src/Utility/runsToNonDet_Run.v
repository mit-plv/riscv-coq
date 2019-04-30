(* equivalence between Run.run, where the composition of several steps is done
   using monadic bind, and runsToNonDet.runsTo, where the composition of several
   steps is done by the Inductive *)
Require Import coqutil.Word.Interface.
Require Import riscv.Platform.Run.
Require Import riscv.Utility.runsToNonDet.
Require Import riscv.Spec.Primitives.
Require Import riscv.Platform.RiscvMachine.
Require Import riscv.Spec.Decode.
Require Import riscv.Utility.MkMachineWidth.
Require Import riscv.Spec.Machine.
Require Import riscv.Utility.Utility.


Section Equiv.

  Context `{Primitives}.
  Variable iset: InstructionSet.

  (* redefine mcomp_sat to simplify for the case where no answer is returned *)
  Definition mcomp_sat(m: M unit)(initialL: RiscvMachine.RiscvMachine)
             (post: RiscvMachine.RiscvMachine -> Prop): Prop :=
    mcomp_sat m initialL (fun (_: unit) => post).

  Lemma runsToNonDet_to_Run_aux: forall (initial: RiscvMachine.RiscvMachine)
                                    (P: RiscvMachine.RiscvMachine -> Prop),
      runsTo (mcomp_sat (run1 iset)) initial P ->
      runsTo (mcomp_sat (run1 iset)) initial (fun final =>
         P final /\ exists (n: nat), mcomp_sat (run iset n) initial P).
  Proof.
    induction 1.
    - apply runsToDone.
      split; [assumption|].
      exists O.
      unfold run, Run.run.
      simpl.
      apply spec_Return.
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

  Lemma runsToNonDet_to_Run: forall (initial: RiscvMachine.RiscvMachine)
                                    (P: RiscvMachine.RiscvMachine -> Prop),
      runsTo (mcomp_sat (run1 iset)) initial P ->
      exists (n: nat), mcomp_sat (run iset n) initial P.
  Proof.
    induction 1.
    - exists O.
      unfold run, Run.run.
      simpl.
      apply spec_Return.
      assumption.
    -
  Abort.


  Lemma Run_to_runsToNonDet: forall (n: nat) (initial: RiscvMachine.RiscvMachine)
                                    (P: RiscvMachine.RiscvMachine -> Prop),
      mcomp_sat (run iset n) initial P ->
      runsTo (mcomp_sat (run1 iset)) initial P.
  Proof.
    induction n; intros.
    - unfold run, Run.run in H0. simpl in H0.
      apply runsToDone.
      (* needs inverse direction *)
      admit.
    - unfold run, Run.run in H0. simpl in H0.
  Abort.

End Equiv.
