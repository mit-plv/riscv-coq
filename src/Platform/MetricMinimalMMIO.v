Require Import Coq.ZArith.ZArith.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Logic.PropExtensionality.
Require Import riscv.Utility.Monads. Import OStateNDOperations.
Require Import riscv.Utility.MonadNotations.
Require Import riscv.Spec.Decode.
Require Import riscv.Spec.Machine.
Require Import riscv.Utility.Utility.
Require Import riscv.Spec.Primitives.
Require Import riscv.Spec.MetricPrimitives.
Require Import Coq.Lists.List. Import ListNotations.
Require Export riscv.Utility.MMIOTrace.
Require Export riscv.Platform.RiscvMachine.
Require Export riscv.Platform.MetricRiscvMachine.
Require Import riscv.Platform.MinimalMMIO.
Require Import riscv.Platform.MetricLogging.
Require Import coqutil.Z.Lia.
Require Import coqutil.Map.Interface.
Require Import coqutil.Tactics.Tactics.


Local Open Scope Z_scope.
Local Open Scope bool_scope.

Section Riscv.

  Context {W: Words}.
  Context {Mem: map.map word byte}.
  Context {Registers: map.map Register word}.

  (* note: ext_spec does not have access to the metrics *)
  Context {ext_spec: ExtSpec (OStateND RiscvMachine)}.

  Definition liftL0{B : Type}(fl: MetricLog -> MetricLog)(f: OStateND RiscvMachine B):
    OStateND MetricRiscvMachine B :=
    fun s p => (exists b mach, p = Some (b, {| getMachine := mach;
                                               getMetrics := fl s.(getMetrics) |}) /\
                               f s.(getMachine) (Some (b, mach))) \/
               (p = None /\ f s.(getMachine) None).

  (* alternative definition, should be equivalent:
  Definition liftL0{B : Type}(fl: MetricLog -> MetricLog)(f: OStateND RiscvMachine B):
    OStateND MetricRiscvMachine B :=
    fun s p => match p with
               | Some (b, m) => (f s.(getMachine)) (Some (b, m.(getMachine))) /\
                                (fl s.(getMetrics)) = m.(getMetrics)
               | None => (f s.(getMachine)) None
               end.
   *)

  Definition liftL1{A B: Type} fl (f: A -> OStateND RiscvMachine B) :=
    fun a => liftL0 fl (f a).

  Definition liftL2{A1 A2 B: Type} fl (f: A1 -> A2 -> OStateND RiscvMachine B) :=
    fun a1 a2 => liftL0 fl (f a1 a2).

  Definition liftL3{A1 A2 A3 B: Type} fl (f: A1 -> A2 -> A3 -> OStateND RiscvMachine B) :=
    fun a1 a2 a3 => liftL0 fl (f a1 a2 a3).

  Instance IsMetricRiscvMachine: RiscvProgram (OStateND MetricRiscvMachine) word := {
    getRegister := liftL1 id getRegister;
    setRegister := liftL2 id setRegister;
    getPC := liftL0 id getPC;
    setPC := liftL1 (addMetricJumps 1) setPC;
    loadByte := liftL2 (addMetricLoads 1) loadByte;
    loadHalf := liftL2 (addMetricLoads 1) loadHalf;
    loadWord := liftL2 (addMetricLoads 1) loadWord;
    loadDouble := liftL2 (addMetricLoads 1) loadDouble;
    storeByte := liftL3 (addMetricStores 1) storeByte;
    storeHalf := liftL3 (addMetricStores 1) storeHalf;
    storeWord := liftL3 (addMetricStores 1) storeWord;
    storeDouble := liftL3 (addMetricStores 1) storeDouble;
    step := liftL0 (addMetricInstructions 1) step;
    raiseExceptionWithInfo{A} := liftL3 id (raiseExceptionWithInfo (A := A));
  }.

  Definition pLoad (m : MetricRiscvMachine) := updateMetrics (addMetricLoads 1) m.
  Definition pStore (m : MetricRiscvMachine) := updateMetrics (addMetricStores 1) m.

  Arguments Memory.load_bytes: simpl never.
  Arguments Memory.store_bytes: simpl never.

  Lemma not_load_fails_but_store_succeeds: forall {m: Mem} {addr: word} {n v m'},
      Memory.load_bytes n m addr = None ->
      Memory.store_bytes n m addr v = Some m' ->
      False.
  Proof.
    intros. unfold Memory.store_bytes in *.
    rewrite H in H0.
    discriminate.
  Qed.

  Lemma not_store_fails_but_load_succeeds: forall {m: Mem} {addr: word} {n v0 v1},
      Memory.load_bytes n m addr = Some v0 ->
      Memory.store_bytes n m addr v1 = None ->
      False.
  Proof.
    intros. unfold Memory.store_bytes in *.
    rewrite H in H0.
    discriminate.
  Qed.

  Ltac t0 :=
    match goal with
       | |- _ => reflexivity
       | |- _ => progress (
                     unfold computation_satisfies, computation_with_answer_satisfies,
                            IsMetricRiscvMachine,
                            valid_register, Register0,
                            is_initial_register_value,
                            get, put, fail_hard,
                            arbitrary,
                            logEvent,
                            ZToReg, MkMachineWidth.MachineWidth_XLEN,
                            Memory.loadByte, Memory.storeByte,
                            Memory.loadHalf, Memory.storeHalf,
                            Memory.loadWord, Memory.storeWord,
                            Memory.loadDouble, Memory.storeDouble,
                            liftL0, liftL1, liftL2, liftL3, id,
                            withRegs,
                            updateMetrics, withMetrics,
                            pLoad, pStore,
                            fail_if_None, loadN, storeN in *;
                     subst;
                     simpl in *)
       | |- _ => intro
       | |- _ => split
       | |- _ => apply functional_extensionality
       | |- _ => apply propositional_extensionality; split; intros
       | u: unit |- _ => destruct u
       | H: exists x, _ |- _ => destruct H
       | H: {_ : _ | _} |- _ => destruct H
       | H: _ /\ _ |- _ => destruct H
       | p: _ * _ |- _ => destruct p
       | |- context [ let (_, _) := ?p in _ ] => let E := fresh "E" in destruct p eqn: E
       | H: Some _ = Some _ |- _ => inversion H; clear H; subst
       | H: (_, _) = (_, _) |- _ => inversion H; clear H; subst
       | H: forall x, x = _ -> _ |- _ => specialize (H _ eq_refl)
       | H: _ && _ = true |- _ => apply andb_prop in H
       | H: _ && _ = false |- _ => apply Bool.andb_false_iff in H
       | H: isXAddrB _ _ = false |- _ => apply isXAddrB_not in H
       | H: isXAddrB _ _ = true  |- _ => apply isXAddrB_holds in H
       | H: ?x = ?x -> _ |- _ => specialize (H eq_refl)
       | |- _ * _ => constructor
       | |- option _ => exact None
       | |- _ => discriminate
       | |- _ => congruence
       | |- _ => solve [exfalso; bomega]
       | |- _ => solve [eauto 15]
       | H: false = ?rhs |- _ => match rhs with
                                 | false => fail 1
                                 | _ => symmetry in H
                                 end
       | |- _ => progress (rewrite? Z.ltb_nlt in *; rewrite? Z.ltb_lt in *)
       | |- _ => bomega
       | H: context[let (_, _) := ?y in _] |- _ => let E := fresh "E" in destruct y eqn: E
       | E: ?x = Some _, H: context[match ?x with _ => _ end] |- _ => rewrite E in H
       | E: ?x = Some _  |- context[match ?x with _ => _ end]      => rewrite E
       | E: ?x = None, H: context[match ?x with _ => _ end] |- _ => rewrite E in H
       | E: ?x = None  |- context[match ?x with _ => _ end]      => rewrite E
       | H: context[match ?x with _ => _ end] |- _ => let E := fresh "E" in destruct x eqn: E
       | |- context[match ?x with _ => _ end]      => let E := fresh "E" in destruct x eqn: E
       | H1: _, H2: _ |- _ => exfalso; apply (not_load_fails_but_store_succeeds H1 H2)
       | H1: _, H2: _ |- _ => exfalso; apply (not_store_fails_but_load_succeeds H1 H2)
       | |- exists a b, Some (a, b) = _ /\ _ => do 2 eexists; split; [reflexivity|]
       | |- exists a, _ = _ /\ _ => eexists; split; [reflexivity|]
       | H: ?P -> exists _, _ |- _ =>
         let N := fresh in
         assert P as N by (clear H; repeat t0);
         specialize (H N);
         clear N
       | H: _ \/ _ |- _ => destruct H
       | r: MetricRiscvMachine |- _ =>
         destruct r as [[regs pc npc m l] mc];
         simpl in *
       | H: {| getRegs := _;
               getPc := _;
               getNextPc := _;
               getMem := _;
               getLog := _ |} = _ |- _ => rewrite H in * || rewrite <- H in *
       | |- context[?x] =>
         match x with
         | {| getMachine := getMachine ?y;
              getMetrics := getMetrics ?y |} => replace x with y in * by (destruct y; reflexivity)
         end
       | o: option _ |- _ => destruct o
       (* introduce evars as late as possible (after all destructs), to make sure everything
          is in their scope*)
(*       | |- exists (P: ?A -> ?S -> Prop), _ =>
            let a := fresh "a" in evar (a: A);
            let s := fresh "s" in evar (s: S);
            exists (fun a0 s0 => a0 = a /\ s0 = s);
            subst a s*)
       | H1: _, H2: _ |- _ => specialize H1 with (1 := H2)
       | |- _ \/ _ => left; solve [repeat t0]
       | |- _ \/ _ => right; solve [repeat t0]
       end.

  Ltac t := repeat t0.

  Arguments LittleEndian.combine: simpl never.

  Instance MetricMinimalMMIOPrimitivesParams:
    PrimitivesParams (OStateND MetricRiscvMachine) MetricRiscvMachine :=
  {
    Primitives.mcomp_sat := @computation_with_answer_satisfies MetricRiscvMachine;

    (* any value can be found in an uninitialized register *)
    Primitives.is_initial_register_value x := True;

    Primitives.nonmem_load n := liftL1 (addMetricLoads 1) (run_and_log_mmio_load n);
    Primitives.nonmem_store n := liftL2 (addMetricStores 1) (run_and_log_mmio_store n);
  }.

  Lemma some_none_falsomatic: forall (A : Type) (a : A),
      @None A = Some a ->
      False.
  Proof.
    discriminate.
  Qed.

  Lemma computation_with_answer_satisfies_liftL0{A: Type}:
    forall f (m: OStateND RiscvMachine A) initial post,
      computation_with_answer_satisfies (liftL0 f m) initial post ->
      computation_with_answer_satisfies m initial.(getMachine) (fun a final =>
        post a {| getMachine := final; getMetrics := f initial.(getMetrics) |}).
  Proof.
    unfold computation_with_answer_satisfies, liftL0. intros.
    destruct o as [(? & ?)|].
    - specialize (H (Some (a, {| getMachine := r; getMetrics := f (getMetrics initial) |}))).
      destruct H as (? & ? & ? & ?); cycle 1.
      + do 2 eexists. split; [reflexivity|]. inversion H. subst. assumption.
      + left. eauto.
    - specialize (H None).
      destruct H as (? & ? & ? & ?); [|discriminate]. right. auto.
  Qed.

  Lemma computation_with_answer_satisfies_liftL0_bw{A: Type}:
    forall f (m: OStateND RiscvMachine A) initial post,
      computation_with_answer_satisfies m initial.(getMachine) (fun a final =>
        post a {| getMachine := final; getMetrics := f initial.(getMetrics) |}) ->
      computation_with_answer_satisfies (liftL0 f m) initial post.
  Proof.
    unfold computation_with_answer_satisfies, liftL0. intros.
    destruct H0.
    - destruct H0 as (? & ? & ? & ?). subst. do 2 eexists. split; [reflexivity|].
      specialize (H _ H1).
      destruct H as (? & ? & ? & ?). inversion H. subst. assumption.
    - destruct H0. subst.
      specialize (H _ H1).
      destruct H as (? & ? & ? & ?). discriminate.
  Qed.

  Instance MinimalMMIOSatisfiesPrimitives: MetricPrimitives MetricMinimalMMIOPrimitivesParams.
  Proof.
    constructor.
    all: split.
    (* spec_Bind *)
    - t.
    - intros.
      unfold mcomp_sat, MetricMinimalMMIOPrimitivesParams in *.
      apply computation_with_answer_satisfies_Bind in H. exact H.
    (* spec_Return *)
    - t.
    - t.
    (* spec_getRegister *)
    - t.
    - unfold getRegister, IsMetricRiscvMachine.
      intros. unfold liftL1 in *.
      unfold mcomp_sat, MetricMinimalMMIOPrimitivesParams in *.
      apply computation_with_answer_satisfies_liftL0 in H.
      eapply (proj2 (Primitives.spec_getRegister
                       (primitives_params := MinimalMMIOPrimitivesParams) _ _ _)) in H.
      unfold mcomp_sat, MetricMinimalMMIOPrimitivesParams, MinimalMMIOPrimitivesParams in *.
      destruct_RiscvMachine initialL.
      exact H.
    (* spec_setRegister *)
    - t.
    - unfold setRegister, IsMetricRiscvMachine.
      intros. unfold liftL2 in *.
      unfold mcomp_sat, MetricMinimalMMIOPrimitivesParams in *.
      apply computation_with_answer_satisfies_liftL0 in H.
      eapply (proj2 (Primitives.spec_setRegister
                       (primitives_params := MinimalMMIOPrimitivesParams) _ _ _ _)) in H.
      unfold mcomp_sat, MetricMinimalMMIOPrimitivesParams, MinimalMMIOPrimitivesParams in *.
      destruct_RiscvMachine initialL.
      exact H.
    (* spec_loadByte *)
    - t.
    - unfold loadByte, IsMetricRiscvMachine.
      intros. unfold liftL2 in *.
      unfold mcomp_sat, MetricMinimalMMIOPrimitivesParams in *.
      apply computation_with_answer_satisfies_liftL0 in H.
      eapply (proj2 (Primitives.spec_loadByte
                       (primitives_params := MinimalMMIOPrimitivesParams) _ _ _ _)) in H.
      unfold mcomp_sat, MetricMinimalMMIOPrimitivesParams, MinimalMMIOPrimitivesParams in *.
      destruct_RiscvMachine initialL.
      destruct H.
      + left. exact H.
      + right. destruct H. split.
        * assumption.
        * unfold nonmem_load in *.
          unfold liftL1.
          eapply computation_with_answer_satisfies_liftL0_bw.
          exact H0.
    (* spec_loadHalf *)
    - t.
    - unfold loadHalf, IsMetricRiscvMachine.
      intros. unfold liftL2 in *.
      unfold mcomp_sat, MetricMinimalMMIOPrimitivesParams in *.
      apply computation_with_answer_satisfies_liftL0 in H.
      eapply (proj2 (Primitives.spec_loadHalf
                       (primitives_params := MinimalMMIOPrimitivesParams) _ _ _ _)) in H.
      unfold mcomp_sat, MetricMinimalMMIOPrimitivesParams, MinimalMMIOPrimitivesParams in *.
      destruct_RiscvMachine initialL.
      destruct H.
      + left. exact H.
      + right. destruct H. split.
        * assumption.
        * unfold nonmem_load in *.
          unfold liftL1.
          eapply computation_with_answer_satisfies_liftL0_bw.
          exact H0.
    (* spec_loadWord *)
    - t.
    - unfold loadWord, IsMetricRiscvMachine.
      intros. unfold liftL2 in *.
      unfold mcomp_sat, MetricMinimalMMIOPrimitivesParams in *.
      apply computation_with_answer_satisfies_liftL0 in H.
      eapply (proj2 (Primitives.spec_loadWord
                       (primitives_params := MinimalMMIOPrimitivesParams) _ _ _ _)) in H.
      unfold mcomp_sat, MetricMinimalMMIOPrimitivesParams, MinimalMMIOPrimitivesParams in *.
      destruct_RiscvMachine initialL.
      destruct H.
      + left. exact H.
      + right. destruct H. split.
        * assumption.
        * unfold nonmem_load in *.
          unfold liftL1.
          eapply computation_with_answer_satisfies_liftL0_bw.
          exact H0.
    (* spec_loadDouble *)
    - t.
    - unfold loadDouble, IsMetricRiscvMachine.
      intros. unfold liftL2 in *.
      unfold mcomp_sat, MetricMinimalMMIOPrimitivesParams in *.
      apply computation_with_answer_satisfies_liftL0 in H.
      eapply (proj2 (Primitives.spec_loadDouble
                       (primitives_params := MinimalMMIOPrimitivesParams) _ _ _ _)) in H.
      unfold mcomp_sat, MetricMinimalMMIOPrimitivesParams, MinimalMMIOPrimitivesParams in *.
      destruct_RiscvMachine initialL.
      destruct H.
      + left. exact H.
      + right. destruct H. split.
        * assumption.
        * unfold nonmem_load in *.
          unfold liftL1.
          eapply computation_with_answer_satisfies_liftL0_bw.
          exact H0.
    (* spec_storeByte *)
    - t.
    - unfold storeByte, IsMetricRiscvMachine.
      intros. unfold liftL3 in *.
      unfold mcomp_sat, MetricMinimalMMIOPrimitivesParams in *.
      apply computation_with_answer_satisfies_liftL0 in H.
      eapply (proj2 (Primitives.spec_storeByte
                       (primitives_params := MinimalMMIOPrimitivesParams) _ _ _ _ _)) in H.
      unfold mcomp_sat, MetricMinimalMMIOPrimitivesParams, MinimalMMIOPrimitivesParams in *.
      destruct_RiscvMachine initialL.
      destruct H.
      + left. exact H.
      + right. destruct H. split.
        * assumption.
        * unfold nonmem_store in *.
          unfold liftL2.
          eapply computation_with_answer_satisfies_liftL0_bw.
          exact H0.
    (* spec_storeHalf *)
    - t.
    - unfold storeHalf, IsMetricRiscvMachine.
      intros. unfold liftL3 in *.
      unfold mcomp_sat, MetricMinimalMMIOPrimitivesParams in *.
      apply computation_with_answer_satisfies_liftL0 in H.
      eapply (proj2 (Primitives.spec_storeHalf
                       (primitives_params := MinimalMMIOPrimitivesParams) _ _ _ _ _)) in H.
      unfold mcomp_sat, MetricMinimalMMIOPrimitivesParams, MinimalMMIOPrimitivesParams in *.
      destruct_RiscvMachine initialL.
      destruct H.
      + left. exact H.
      + right. destruct H. split.
        * assumption.
        * unfold nonmem_store in *.
          unfold liftL2.
          eapply computation_with_answer_satisfies_liftL0_bw.
          exact H0.
    (* spec_storeWord *)
    - t.
    - unfold storeWord, IsMetricRiscvMachine.
      intros. unfold liftL3 in *.
      unfold mcomp_sat, MetricMinimalMMIOPrimitivesParams in *.
      apply computation_with_answer_satisfies_liftL0 in H.
      eapply (proj2 (Primitives.spec_storeWord
                       (primitives_params := MinimalMMIOPrimitivesParams) _ _ _ _ _)) in H.
      unfold mcomp_sat, MetricMinimalMMIOPrimitivesParams, MinimalMMIOPrimitivesParams in *.
      destruct_RiscvMachine initialL.
      destruct H.
      + left. exact H.
      + right. destruct H. split.
        * assumption.
        * unfold nonmem_store in *.
          unfold liftL2.
          eapply computation_with_answer_satisfies_liftL0_bw.
          exact H0.
    (* spec_storeDouble *)
    - t.
    - unfold storeDouble, IsMetricRiscvMachine.
      intros. unfold liftL3 in *.
      unfold mcomp_sat, MetricMinimalMMIOPrimitivesParams in *.
      apply computation_with_answer_satisfies_liftL0 in H.
      eapply (proj2 (Primitives.spec_storeDouble
                       (primitives_params := MinimalMMIOPrimitivesParams) _ _ _ _ _)) in H.
      unfold mcomp_sat, MetricMinimalMMIOPrimitivesParams, MinimalMMIOPrimitivesParams in *.
      destruct_RiscvMachine initialL.
      destruct H.
      + left. exact H.
      + right. destruct H. split.
        * assumption.
        * unfold nonmem_store in *.
          unfold liftL2.
          eapply computation_with_answer_satisfies_liftL0_bw.
          exact H0.
    (* spec_getPC *)
    - t.
    - t. edestruct H as [b [? ?]]; [solve [left; t]|]. t.
    (* spec_setPC *)
    - t.
    - t. edestruct H as [b [? ?]]; [solve [left; t]|]. t.
    (* spec_step *)
    - t.
    - t. edestruct H as [b [? ?]]; [solve [left; t]|]. t.
  Qed.

End Riscv.

(* needed because defined inside a Section *)
Existing Instance IsMetricRiscvMachine.
Existing Instance MinimalMMIOSatisfiesPrimitives.
