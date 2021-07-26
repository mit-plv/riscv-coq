Require Import Coq.Lists.List.
Require Import coqutil.Map.Interface coqutil.Map.Properties.
Require Import coqutil.Tactics.Tactics.
Require Import riscv.Spec.Machine.
Require Import riscv.Utility.Monads.
Require Import riscv.Spec.Decode.
Require Import riscv.Utility.Utility.
Require Import riscv.Spec.Primitives.
Require Import riscv.Platform.RiscvMachine.
Require Import riscv.Platform.MetricRiscvMachine.
Require Import riscv.Spec.MetricPrimitives.
Require Import riscv.Platform.Run.

Import ListNotations.

Section Sane.

  Context {width: Z} {BW: Bitwidth width} {word: word width} {word_ok: word.ok word}.
  Context {Registers: map.map Register word}.
  Context {mem: map.map word byte}.
  Context {M: Type -> Type}.
  Context {MM: Monad M}.
  Context {RVM: RiscvProgram M word}.
  Context {PRParams: PrimitivesParams M MetricRiscvMachine}.
  Context {mcomp_sat_ok: mcomp_sat_spec PRParams}.

  Lemma mcomp_sat_weaken: forall A initialL m (post1 post2: A -> MetricRiscvMachine -> Prop),
      (forall a mach, post1 a mach -> post2 a mach) ->
      mcomp_sat m initialL post1 ->
      mcomp_sat m initialL post2.
  Proof.
    intros.
    rewrite <- (@right_identity M MM A m).
    eapply spec_Bind.
    eexists. split.
    - exact H0.
    - intros. simpl in *. apply spec_Return. eapply H. assumption.
  Qed.

  Lemma Return_sane: forall {A: Type} (a: A),
      mcomp_sane (Return a).
  Proof.
    unfold mcomp_sane.
    intros. eapply spec_Return in H0.
    split.
    - eauto.
    - eapply (proj1 (spec_Return _ _ _)).
      ssplit.
      + assumption.
      + exists nil. reflexivity.
      + assumption.
  Qed.

  Lemma Bind_sane: forall {A B: Type} (m: M A) (f: A -> M B),
      mcomp_sane m ->
      (forall a, mcomp_sane (f a)) ->
      mcomp_sane (Bind m f).
  Proof.
    intros *.
    intros S1 S2.
    unfold mcomp_sane in *.
    intros.
    eapply (proj2 (spec_Bind _ _ _ _)) in H0.
    destruct H0 as (mid & C1 & C2).
    split.
    - specialize S1 with (1 := H) (2 := C1). destruct S1 as ((a & middle & S1a & S1b) & S1c).
      specialize C2 with (1 := S1a).
      specialize S2 with (1 := S1b) (2 := C2). destruct S2 as ((b & final & S2a) & S2b).
      eauto.
    - eapply spec_Bind.
      exists (fun a middle => (mid a middle /\
                               exists diff1, getLog middle = diff1 ++ getLog st) /\
                              valid_machine middle).
      split.
      + specialize S1 with (1 := H) (2 := C1). destruct S1 as ((a & middle & S1a & S1b) & S1c).
        exact S1c.
      + intros. destruct H0 as ((HM & (diff1 & E1)) & V1).
        specialize C2 with (1 := HM).
        specialize S2 with (1 := V1) (2 := C2). destruct S2 as ((b & final & S2a & S2b) & S2c).
        eapply mcomp_sat_weaken; [|exact S2c].
        simpl. intros. destruct H0 as ((? & (diff2 & E2)) & V2).
        split; [|assumption].
        split; [assumption|].
        rewrite E1 in E2.
        rewrite List.app_assoc in E2.
        eexists. exact E2.
  Qed.

  Ltac t_step :=
    first [ progress intros
          | apply Bind_sane
          | apply Return_sane
          | apply getRegister_sane
          | apply setRegister_sane
          | apply loadByte_sane
          | apply loadHalf_sane
          | apply loadWord_sane
          | apply loadDouble_sane
          | apply storeByte_sane
          | apply storeHalf_sane
          | apply storeWord_sane
          | apply storeDouble_sane
          | apply makeReservation_sane
          | apply clearReservation_sane
          | apply checkReservation_sane
          | apply getCSRField_sane
          | apply setCSRField_sane
          | apply getPrivMode_sane
          | apply setPrivMode_sane
          | apply fence_sane
          | apply endCycleNormal_sane
          | apply endCycleEarly_sane
          | apply getPC_sane
          | apply setPC_sane
          | match goal with
            | |- context [match ?x with _ => _ end] => destruct x
            end ].

  Context {PRSane: MetricPrimitivesSane PRParams}.

  Lemma raiseExceptionWithInfo_sane: forall A i1 i2 i3,
      mcomp_sane (raiseExceptionWithInfo (A := A) i1 i2 i3).
  Proof.
    unfold raiseExceptionWithInfo. repeat t_step.
  Qed.

  Lemma raiseException_sane: forall A i1 i2,
      mcomp_sane (raiseException (A := A) i1 i2).
  Proof.
    unfold raiseException. intros. apply raiseExceptionWithInfo_sane.
  Qed.

  Lemma getCSR_sane: forall f,
      mcomp_sane (CSRGetSet.getCSR f).
  Proof.
    intros. destruct f; simpl; unfold when; repeat t_step.
  Qed.

  Lemma setCSR_sane: forall f v,
      mcomp_sane (CSRSpec.setCSR f v).
  Proof.
    intros. destruct f; simpl; unfold when; repeat t_step.
  Qed.

  Ltac t_step' :=
    first [ apply raiseException_sane
          | apply raiseExceptionWithInfo_sane
          | apply getCSR_sane
          | apply setCSR_sane
          | t_step ].

  Ltac t := repeat (simpl; unfold when; repeat t_step').

  Lemma execute_sane: forall inst,
      mcomp_sane (Execute.execute inst).
  Proof.
    intros.
    destruct inst as [inst | inst | inst | inst | inst | inst | inst | inst | inst | inst];
      simpl; try apply raiseExceptionWithInfo_sane; destruct inst; t.
      (* to debug performance: [ > time "outer" (destruct inst; [ > time "inner" t .. ]) .. ] *)
  Qed.

  Lemma run1_sane: forall iset, mcomp_sane (run1 iset).
  Proof.
    unfold run1. intros.
    apply Bind_sane; [apply getPC_sane|intros].
    apply Bind_sane; [apply loadWord_sane|intros].
    apply Bind_sane; [apply execute_sane|intros].
    apply endCycleNormal_sane.
  Qed.

End Sane.
