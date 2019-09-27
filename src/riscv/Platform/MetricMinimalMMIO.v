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
Import MetricRiscvMachine.

Local Open Scope Z_scope.
Local Open Scope bool_scope.

Section Riscv.
  Import List.
  Import free.

  Context {W: Words}.
  Context {Mem: map.map word byte}.
  Context {Registers: map.map Register word}.

  (* note: ext_spec does not have access to the metrics *)
  Context {ext_spec: ExtSpec}.

  Definition action : Type := (MetricLog -> MetricLog) * action.
  Definition result (a : action) := result (snd a).
  Local Notation M := (free action result).

  Instance IsRiscvMachine: RiscvProgram M word := {|
    Machine.getRegister a := act (id, getRegister a) ret;
    Machine.setRegister a b := act (id, setRegister a b) ret;
    Machine.loadByte a b := act (addMetricLoads 1, loadByte a b) ret;
    Machine.loadHalf a b := act (addMetricLoads 1, loadHalf a b) ret;
    Machine.loadWord a b := act (addMetricLoads 1, loadWord a b) ret;
    Machine.loadDouble a b := act (addMetricLoads 1, loadDouble a b) ret;
    Machine.storeByte a b c := act (addMetricStores 1, storeByte a b c) ret;
    Machine.storeHalf a b c := act (addMetricStores 1, storeHalf a b c) ret;
    Machine.storeWord a b c := act (addMetricStores 1, storeWord a b c) ret;
    Machine.storeDouble a b c := act (addMetricStores 1, storeDouble a b c) ret;
    Machine.makeReservation a := act (id, makeReservation a) ret;
    Machine.clearReservation a := act (id, clearReservation a) ret;
    Machine.checkReservation a := act (id, checkReservation a) ret;
    Machine.getPC := act (id, getPC) ret;
    Machine.setPC a := act (addMetricJumps 1, setPC a) ret;
    Machine.step := act (addMetricInstructions 1, step) ret;
    Machine.raiseExceptionWithInfo a b c d := act (id, raiseExceptionWithInfo a b c d) ret;
  |}.

  Definition interp_action a metmach post :=
    interp_action (snd a) (metmach.(getMachine)) (fun r mach =>
      post r (mkMetricRiscvMachine mach (fst a (metmach.(getMetrics))))).

  Notation interp a mach post := (free.interp interp_action a mach post).

  Arguments Memory.load_bytes: simpl never.
  Arguments Memory.store_bytes: simpl never.
  Arguments LittleEndian.combine: simpl never.

  Global Instance MetricMinimalMMIOPrimitivesParams: PrimitivesParams M MetricRiscvMachine :=
  {
    Primitives.mcomp_sat := @free.interp _ _ _ interp_action;
    Primitives.is_initial_register_value x := True;
    Primitives.nonmem_load := @Primitives.nonmem_load _ _ _ _ _ MinimalMMIOPrimitivesParams;
    Primitives.nonmem_store := @Primitives.nonmem_store _ _ _ _ _ MinimalMMIOPrimitivesParams;
  }.

  Context
    (mmio_load_weaken_post : forall n c a m t (post1 post2:_->_->Prop), (forall m r, post1 m r -> post2 m r) -> mmio_load n c a m t post1 -> mmio_load n c a m t post2)
    (mmio_store_weaken_post : forall n c a v m t (post1 post2:_->Prop), (forall m, post1 m -> post2 m) -> mmio_store n c a v m t post1 -> mmio_store n c a v m t post2)
    (mmio_load_total : forall n c a m t post, mmio_load n c a m t post -> exists v s, post v s)
    (mmio_store_total : forall n c a v m t post, mmio_store n c a v m t post -> exists s, post s).

  Global Instance MinimalMMIOSatisfies_mcomp_sat_spec: mcomp_sat_spec MetricMinimalMMIOPrimitivesParams.
  Proof.
    split; cbv [mcomp_sat MetricMinimalMMIOPrimitivesParams Monad_free Bind Return].
    { symmetry. eapply interp_bind_ex_mid; intros.
      eapply MinimalMMIO.interp_action_weaken_post; eauto; cbn; eauto. }
    { symmetry. rewrite interp_ret; eapply iff_refl. }
  Qed.

  Lemma interp_action_weaken_post a (post1 post2:_->_->Prop)
    (H: forall r s, post1 r s -> post2 r s) s
    : interp_action a s post1 -> interp_action a s post2.
  Proof. eapply MinimalMMIO.interp_action_weaken_post; eauto. Qed.
  Lemma interp_action_appendonly a s post :
    interp_action a s post ->
    interp_action a s (fun _ s' => endswith s'.(getLog) s.(getLog)).
  Proof. eapply MinimalMMIO.interp_action_appendonly; eauto. Qed.
  Lemma interp_action_appendonly' a s post :
    interp_action a s post ->
    interp_action a s (fun v s' => post v s' /\ endswith s'.(getLog) s.(getLog)).
  Proof. eapply MinimalMMIO.interp_action_appendonly'; eauto. Qed.
  Lemma interp_action_total a s post :
    interp_action a s post -> exists v s, post v s.
  Proof.
    intros H.
    unshelve epose proof (MinimalMMIO.interp_action_total _ _ _ _ _ H) as H0; eauto.
    destruct H0 as (?&?&?); eauto.
  Qed.
  Global Instance MetricMinimalMMIOPrimitivesSane : MetricPrimitivesSane MetricMinimalMMIOPrimitivesParams.
  Proof.
    split; cbv [mcomp_sane]; intros; 
      exact (conj (interp_action_total _ st _ H)
                  (interp_action_appendonly' _ _ _ H)).
  Qed.

  Global Instance MetricMinimalMMIOSatisfiesPrimitives:
    MetricPrimitives MetricMinimalMMIOPrimitivesParams.
  Proof.
    split; try exact _.
    all : cbv [mcomp_sat spec_load spec_store MetricMinimalMMIOPrimitivesParams invalidateWrittenXAddrs].
    all: intros; destruct initialL;
      repeat match goal with
      | _ => progress subst
      | _ => Option.inversion_option
      | _ => progress cbn -[Memory.load_bytes Memory.store_bytes HList.tuple] in *
      | _ => progress cbv [id Register0 valid_register is_initial_register_value load store Memory.loadByte Memory.loadHalf Memory.loadWord Memory.loadDouble Memory.storeByte Memory.storeHalf Memory.storeWord Memory.storeDouble] in *
      | H : exists _, _ |- _ => destruct H
      | H : _ /\ _ |- _ => destruct H
      | |- _ => solve [ intuition (eauto || Lia.lia) ]
      | H : _ \/ _ |- _ => destruct H
      | |- context[match ?x with _ => _ end] => destruct x eqn:?
      | |-_ /\ _ => split
      end.
      (* setRegister *)
      destruct getMachine; eassumption.
  Qed.

End Riscv.
