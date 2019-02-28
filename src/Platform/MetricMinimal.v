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
Require Import Coq.micromega.Lia.
Require Import Coq.omega.Omega.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Logic.PropExtensionality.

Local Open Scope Z_scope.
Local Open Scope bool_scope.

Section Riscv.
  Context {W: Words}.
  Context {Mem: map.map word byte}.
  Context {Registers: map.map Register word}.

  Local Notation RiscvMachineL := (RiscvMachine Register Empty_set).
  Local Notation MetricRiscvMachineL := (MetricRiscvMachine Register Empty_set).

  Definition liftL0{B: Type}(fl: MetricLog -> MetricLog)(f: OState RiscvMachineL B):
    OState MetricRiscvMachineL B :=
    fun s => let (ob, s') := f s.(getMachine) in
             (ob, mkMetricRiscvMachine s' (fl s.(getMetrics))).

  Definition liftL1{A B: Type} fl (f: A -> OState RiscvMachineL B) :=
    fun a => liftL0 fl (f a).

  Definition liftL2{A1 A2 B: Type} fl (f: A1 -> A2 -> OState RiscvMachineL B) :=
    fun a1 a2 => liftL0 fl (f a1 a2).

  Instance IsMetricRiscvMachineL: RiscvProgram (OState MetricRiscvMachineL) word := {|
    getRegister := liftL1 id getRegister;
    setRegister := liftL2 id setRegister;
    getPC := liftL0 id getPC;
    setPC := liftL1 (addMetricJumps 1) setPC;
    loadByte := liftL1 (addMetricLoads 1) loadByte;
    loadHalf := liftL1 (addMetricLoads 1) loadHalf;
    loadWord := liftL1 (addMetricLoads 1) loadWord;
    loadDouble := liftL1 (addMetricLoads 1) loadDouble;
    storeByte := liftL2 (addMetricStores 1) storeByte;
    storeHalf := liftL2 (addMetricStores 1) storeHalf;
    storeWord := liftL2 (addMetricStores 1) storeWord;
    storeDouble := liftL2 (addMetricStores 1) storeDouble;
    step := liftL0 (addMetricInstructions 1) step;
    raiseException{A} := liftL2 id (raiseException (A := A));
  |}.

  Arguments Memory.load_bytes: simpl never.
  Arguments Memory.store_bytes: simpl never.

  Ltac t :=
    repeat match goal with
       | |- _ => reflexivity
       | |- _ => progress (
                     unfold computation_satisfies, computation_with_answer_satisfies,
                            IsRiscvMachineL,
                            valid_register, Register0,
                            is_initial_register_value,
                            get, put, fail_hard,
                            Memory.loadByte, Memory.storeByte,
                            Memory.loadHalf, Memory.storeHalf,
                            Memory.loadWord, Memory.storeWord,
                            Memory.loadDouble, Memory.storeDouble,
                            fail_if_None, loadN, storeN,
                            liftL0, liftL1, liftL2, id,
                            getRegs, getMem, liftGet in *;
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
       | H: _ && _ = true |- _ => apply andb_prop in H
       | H: _ && _ = false |- _ => apply Bool.andb_false_iff in H
       | |- _ * _ => constructor
       | |- option _ => exact None
       | |- _ => discriminate
       | |- _ => congruence
       | |- _ => solve [exfalso; lia]
       | |- _ => solve [eauto 15]
       | |- _ => progress (rewrite? Z.ltb_nlt in *; rewrite? Z.ltb_lt in *)
       | |- _ => omega
       | H: context[let (_, _) := ?y in _] |- _ => let E := fresh "E" in destruct y eqn: E
       | E: ?x = Some _, H: context[match ?x with _ => _ end] |- _ => rewrite E in H
       | E: ?x = Some _  |- context[match ?x with _ => _ end]      => rewrite E
       | H: context[match ?x with _ => _ end] |- _ => let E := fresh "E" in destruct x eqn: E
       | |- context[match ?x with _ => _ end]      => let E := fresh "E" in destruct x eqn: E
       | H0: ?l = Some ?r0, H1:?l = Some ?r1 |- _ =>
         assert (r0 = r1) by (rewrite H1 in H0; inversion H0; reflexivity)
       | H: _ \/ _ |- _ => destruct H
       | r: MetricRiscvMachineL |- _ =>
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

  Instance MetricMinimalMetricPrimitivesParams: PrimitivesParams (OState MetricRiscvMachineL) MetricRiscvMachineL := {|
    Primitives.mcomp_sat := @computation_with_answer_satisfies MetricRiscvMachineL;
    Primitives.is_initial_register_value := eq (word.of_Z 0);
    Primitives.nonmem_loadByte_sat   initialL addr post := False;
    Primitives.nonmem_loadHalf_sat   initialL addr post := False;
    Primitives.nonmem_loadWord_sat   initialL addr post := False;
    Primitives.nonmem_loadDouble_sat initialL addr post := False;
    Primitives.nonmem_storeByte_sat   initialL addr v post := False;
    Primitives.nonmem_storeHalf_sat   initialL addr v post := False;
    Primitives.nonmem_storeWord_sat   initialL addr v post := False;
    Primitives.nonmem_storeDouble_sat initialL addr v post := False;
  |}.

  Instance MetricMinimalSatisfiesMetricPrimitives: MetricPrimitives MetricMinimalMetricPrimitivesParams.
  Proof.
    constructor.
    all: try t.
  Qed.

End Riscv.

Existing Instance IsMetricRiscvMachineL.