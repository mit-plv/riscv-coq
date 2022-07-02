Require Import Coq.ZArith.BinInt.
Require Import riscv.Utility.Monads. Import OStateOperations.
Require Import riscv.Utility.MonadNotations.
Require Import riscv.Spec.Decode.
Require Import riscv.Platform.Memory. (* should go before Program because both define loadByte etc *)
Require Import riscv.Spec.Machine.
Require Import riscv.Spec.Execute.
Require Import riscv.Utility.PowerFunc.
Require Import riscv.Utility.Utility.
Require Import riscv.Spec.Primitives.
Require Import coqutil.Map.Interface.
Require Import riscv.Platform.RiscvMachine.
Require Import riscv.Platform.Minimal.
Require Import riscv.Platform.MetricRiscvMachine.
Require Import riscv.Platform.MetricLogging.
Require Import riscv.Spec.MetricPrimitives.
Require Import coqutil.Z.Lia.
Require Import coqutil.Z.Lia.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Logic.PropExtensionality.

Local Open Scope Z_scope.
Local Open Scope bool_scope.

Section Riscv.
  Context {width: Z} {BW: Bitwidth width} {word: word width} {word_ok: word.ok word}.
  Context {Mem: map.map word byte}.
  Context {Registers: map.map Register word}.

  Definition liftL0{B: Type}(fl: MetricLog -> MetricLog)(f: OState RiscvMachine B):
    OState MetricRiscvMachine B :=
    fun s => let (ob, s') := f s.(getMachine) in
             (ob, mkMetricRiscvMachine s' (fl s.(getMetrics))).

  Definition liftL1{A B: Type} fl (f: A -> OState RiscvMachine B) :=
    fun a => liftL0 fl (f a).

  Definition liftL2{A1 A2 B: Type} fl (f: A1 -> A2 -> OState RiscvMachine B) :=
    fun a1 a2 => liftL0 fl (f a1 a2).

  Definition liftL3{A1 A2 A3 B: Type} fl (f: A1 -> A2 -> A3 -> OState RiscvMachine B) :=
    fun a1 a2 a3 => liftL0 fl (f a1 a2 a3).

  Instance IsMetricRiscvMachine: RiscvProgram (OState MetricRiscvMachine) word := {
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
    makeReservation := liftL1 id makeReservation;
    clearReservation := liftL1 id clearReservation;
    checkReservation := liftL1 id checkReservation;
    getCSRField := liftL1 id getCSRField;
    setCSRField := liftL2 id setCSRField;
    getPrivMode := liftL0 id getPrivMode;
    setPrivMode := liftL1 id setPrivMode;
    fence := liftL2 id fence;
    endCycleNormal := liftL0 (addMetricInstructions 1) endCycleNormal;
    endCycleEarly{A} := liftL0 (addMetricInstructions 1) (@endCycleEarly _ _ _ _ _ A);
  }.

  Arguments Memory.load_bytes: simpl never.
  Arguments Memory.store_bytes: simpl never.

  Ltac t :=
    repeat match goal with
       | |- _ => reflexivity
       | |- _ => progress (
                     unfold computation_satisfies, computation_with_answer_satisfies,
                            IsRiscvMachine,
                            valid_register,
                            is_initial_register_value,
                            get, put, fail_hard,
                            Memory.loadByte, Memory.storeByte,
                            Memory.loadHalf, Memory.storeHalf,
                            Memory.loadWord, Memory.storeWord,
                            Memory.loadDouble, Memory.storeDouble,
                            fail_if_None, loadN, storeN,
                            liftL0, liftL1, liftL2, liftL3, id,
                            getRegs, getMem in *;
                     subst;
                     simpl in * )
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
       | H: _ && _ = true |- _ => apply andb_prop in H
       | H: _ && _ = false |- _ => apply Bool.andb_false_iff in H
       | |- _ * _ => constructor
       | |- option _ => exact None
       | |- _ => discriminate
       | |- _ => congruence
       | |- _ => solve [exfalso; blia]
       | |- _ => solve [eauto 15]
       | |- _ => progress (rewrite? Z.ltb_nlt in *; rewrite? Z.ltb_lt in * )
       | |- _ => blia
       | H: context[let (_, _) := ?y in _] |- _ => let E := fresh "E" in destruct y eqn: E
       | E: ?x = Some _, H: context[match ?x with _ => _ end] |- _ => rewrite E in H
       | E: ?x = Some _  |- context[match ?x with _ => _ end]      => rewrite E
       | H: context[match ?x with _ => _ end] |- _ => let E := fresh "E" in destruct x eqn: E
       | |- context[match ?x with _ => _ end]      => let E := fresh "E" in destruct x eqn: E
       | H0: ?l = Some ?r0, H1:?l = Some ?r1 |- _ =>
         assert (r0 = r1) by (rewrite H1 in H0; inversion H0; reflexivity)
       | H: _ \/ _ |- _ => destruct H
       | r: MetricRiscvMachine |- _ =>
         destruct r as [[regs pc npc m l] mc];
         simpl in *
(*       | H: context[match ?x with _ => _ end] |- _ => let E := fresh in destruct x eqn: E*)
       | o: option _ |- _ => destruct o
       (* introduce evars as late as possible (after all destructs), to make sure everything
          is in their scope*)
       | |- exists (P: ?A -> ?S -> Prop), _ =>
            let a := fresh "a" in evar (a: A);
            let s := fresh "s" in evar (s: S);
            exists (fun a0 s0 => a0 = a /\ s0 = s);
            subst a s
       | |- _ \/ _ => left; solve [t]
       | |- _ \/ _ => right; solve [t]
       end.

  Instance MetricMinimalMetricPrimitivesParams:
    PrimitivesParams (OState MetricRiscvMachine) MetricRiscvMachine :=
  {
    Primitives.mcomp_sat := @computation_with_answer_satisfies MetricRiscvMachine;
    Primitives.is_initial_register_value := eq (word.of_Z 0);
    Primitives.nonmem_load n kind addr _ _ := False;
    Primitives.nonmem_store n kind addr v _ _ := False;
    Primitives.valid_machine mach := True;
  }.

  Instance MetricMinimalSatisfiesMetricPrimitives: MetricPrimitives MetricMinimalMetricPrimitivesParams.
  Proof.
    constructor.
    (* all: try t. *)
  Admitted. (* TODO! *)

End Riscv.

#[global] Existing Instance IsMetricRiscvMachine.
