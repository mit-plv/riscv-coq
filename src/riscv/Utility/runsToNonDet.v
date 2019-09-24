Require Import coqutil.sanity.
Unset Universe Minimization ToSet.
Require Export riscv.Utility.PowerFunc.


Section RunsTo.

  Context {State: Type}.
  Variable step: State -> (State -> Prop) -> Prop.

  Inductive runsTo(initial: State)(P: State -> Prop): Prop :=
    | runsToDone:
        P initial ->
        runsTo initial P
    | runsToStep: forall midset,
        step initial midset ->
        (forall mid, midset mid -> runsTo mid P) ->
        runsTo initial P.

  Hint Constructors runsTo.

  Lemma runsTo_trans: forall P Q initial,
    runsTo initial P ->
    (forall middle, P middle -> runsTo middle Q) ->
    runsTo initial Q.
  Proof.
    induction 1; eauto.
  Qed.

  Hint Resolve runsTo_trans.

  Lemma runsTo_weaken: forall (P Q : State -> Prop) initial,
    runsTo initial P ->
    (forall final, P final -> Q final) ->
    runsTo initial Q.
  Proof.
    eauto.
  Qed.

  Lemma runsTo_det_step : forall initialL midL P,
    step initialL (eq midL) ->
    runsTo midL P ->
    runsTo initialL P.
  Proof.
    intros.
    eapply runsToStep; [eassumption|].
    intros. subst.
    assumption.
  Qed.

End RunsTo.
