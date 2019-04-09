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
Require Import Coq.micromega.Lia.
Require Import coqutil.Map.Interface.
Require Import coqutil.Tactics.Tactics.


Local Open Scope Z_scope.
Local Open Scope bool_scope.

Section Riscv.

  Context {W: Words}.
  Context {Mem: map.map word byte}.
  Context {Registers: map.map Register word}.

  Local Notation RiscvMachineL := (RiscvMachine Register MMIOAction).
  Local Notation MetricRiscvMachineL := (MetricRiscvMachine Register MMIOAction).

  Definition liftL0{B : Type}(fl: MetricLog -> MetricLog)(f: OStateND RiscvMachineL B):
    OStateND MetricRiscvMachineL B :=
    fun s p => match p with
               | Some (b, m) => (f s.(getMachine)) (Some (b, m.(getMachine))) /\
                                (fl s.(getMetrics)) = m.(getMetrics)
               | None => (f s.(getMachine)) None
               end.

  Definition liftL1{A B: Type} fl (f: A -> OStateND RiscvMachineL B) :=
    fun a => liftL0 fl (f a).

  Definition liftL2{A1 A2 B: Type} fl (f: A1 -> A2 -> OStateND RiscvMachineL B) :=
    fun a1 a2 => liftL0 fl (f a1 a2).

  Definition liftL3{A1 A2 A3 B: Type} fl (f: A1 -> A2 -> A3 -> OStateND RiscvMachineL B) :=
    fun a1 a2 a3 => liftL0 fl (f a1 a2 a3).

  Instance IsMetricRiscvMachineL: RiscvProgram (OStateND MetricRiscvMachineL) word := {
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

  
  Definition pLoad (m : MetricRiscvMachineL) := updateMetrics (addMetricLoads 1) m.
  Definition pStore (m : MetricRiscvMachineL) := updateMetrics (addMetricStores 1) m.
  
  Arguments Memory.load_bytes: simpl never.
  Arguments Memory.store_bytes: simpl never.

  Lemma not_load_fails_but_store_succeeds: forall {m addr n v m'},
      Memory.load_bytes m n addr = None ->
      Memory.store_bytes m n addr v = Some m' ->
      False.
  Proof.
    intros. unfold Memory.store_bytes in *.
    rewrite H in H0.
    discriminate.
  Qed.

  Lemma not_store_fails_but_load_succeeds: forall {m addr n v0 v1},
      Memory.load_bytes m n addr = Some v0 ->
      Memory.store_bytes m n addr v1 = None ->
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
                            IsMetricRiscvMachineL,
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
                            withRegs, liftWith,
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
       | |- _ * _ => constructor
       | |- option _ => exact None
       | |- _ => discriminate
       | |- _ => congruence
       | |- _ => solve [exfalso; lia]
       | |- _ => solve [eauto 15]
       | H: false = ?rhs |- _ => match rhs with
                                 | false => fail 1
                                 | _ => symmetry in H
                                 end
       | |- _ => progress (rewrite? Z.ltb_nlt in *; rewrite? Z.ltb_lt in *)
       | |- _ => omega
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
       | r: MetricRiscvMachineL |- _ =>
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

  Instance MetricMinimalMMIOPrimitivesParams: PrimitivesParams (OStateND MetricRiscvMachineL) MetricRiscvMachineL := {|
    Primitives.mcomp_sat := @OStateNDOperations.computation_with_answer_satisfies MetricRiscvMachineL;

    (* any value can be found in an uninitialized register *)
    Primitives.is_initial_register_value x := True;

    Primitives.nonmem_loadByte_sat initialL addr post :=
      forall (v: w8), post v (pLoad (withLogItem (mmioLoadEvent addr v) initialL));
    Primitives.nonmem_loadHalf_sat initialL addr post :=
      forall (v: w16), post v (pLoad (withLogItem (mmioLoadEvent addr v) initialL));
    Primitives.nonmem_loadWord_sat initialL addr post :=
      forall (v: w32), post v (pLoad (withLogItem (mmioLoadEvent addr v) initialL));
    Primitives.nonmem_loadDouble_sat initialL addr post :=
      forall (v: w64), post v (pLoad (withLogItem (mmioLoadEvent addr v) initialL));

    Primitives.nonmem_storeByte_sat initialL addr v post :=
      post (pStore (withLogItem (mmioStoreEvent addr v) initialL));
    Primitives.nonmem_storeHalf_sat initialL addr v post :=
      post (pStore (withLogItem (mmioStoreEvent addr v) initialL));
    Primitives.nonmem_storeWord_sat initialL addr v post :=
      post (pStore (withLogItem (mmioStoreEvent addr v) initialL));
    Primitives.nonmem_storeDouble_sat initialL addr v post :=
      post (pStore (withLogItem (mmioStoreEvent addr v) initialL));
  |}.

  Lemma some_none_falsomatic: forall (A : Type) (a : A),
      @None A = Some a ->
      False.
  Proof.
    discriminate.
  Qed.
                                                           
  Instance MinimalMMIOSatisfiesPrimitives: MetricPrimitives MetricMinimalMMIOPrimitivesParams.
  Proof.
    constructor.
    all: split; [solve [t]|].
    - t.
      unfold OStateND in m.
      exists (fun (a: A) (middleL: MetricRiscvMachineL) => m initialL (Some (a, middleL))).
      t.
      edestruct H as [b [? ?]]; [eauto|]; t.
    - t.
    - t; admit.
    - t; admit.
    - intros. simpl in *. unfold computation_with_answer_satisfies in *.
      destruct (Memory.loadByte (getMem initialL) addr) eqn: F; [left|right].
      + t; match goal with
           | |- context [?post ?inp ?mach] => specialize (H (Some (inp, mach)))
           end; t.
      + t. match goal with
           | |- context [?post ?inp ?mach] => specialize (H (Some (inp, mach)))
           end; t.
    - intros. simpl in *. unfold computation_with_answer_satisfies in *.
      destruct (Memory.loadHalf (getMem initialL) addr) eqn: F; [left|right].
      + t; match goal with
           | |- context [?post ?inp ?mach] => specialize (H (Some (inp, mach)))
           end; t.
      + t. match goal with
           | |- context [?post ?inp ?mach] => specialize (H (Some (inp, mach)))
           end; t.
    - intros. simpl in *. unfold computation_with_answer_satisfies in *.
      destruct (Memory.loadWord (getMem initialL) addr) eqn: F; [left|right].
      + t; match goal with
           | |- context [?post ?inp ?mach] => specialize (H (Some (inp, mach)))
           end; t.
      + t. match goal with
           | |- context [?post ?inp ?mach] => specialize (H (Some (inp, mach)))
           end; t.
    - intros. simpl in *. unfold computation_with_answer_satisfies in *.
      destruct (Memory.loadDouble (getMem initialL) addr) eqn: F; [left|right].
      + t; match goal with
           | |- context [?post ?inp ?mach] => specialize (H (Some (inp, mach)))
           end; t.
      + t. match goal with
           | |- context [?post ?inp ?mach] => specialize (H (Some (inp, mach)))
           end; t.

    - intros. simpl in *. unfold computation_with_answer_satisfies in *.
      destruct (Memory.storeByte (getMem initialL) addr v) eqn: F.
      + destruct (Memory.loadByte (getMem initialL) addr) eqn: G; [ | exfalso; t ].
       left.
        t; match goal with
        | |- post ?inp ?mach => specialize (H (Some (inp, mach)))
        end; t.
      + destruct (Memory.loadByte (getMem initialL) addr) eqn: G; [ exfalso; t | ].
        right.
        t; match goal with
           | |- post ?inp ?mach => specialize (H (Some (inp, mach)))
           end; t.
    - intros. simpl in *. unfold computation_with_answer_satisfies in *.
      destruct (Memory.storeHalf (getMem initialL) addr v) eqn: F.
      + destruct (Memory.loadHalf (getMem initialL) addr) eqn: G; [ | exfalso; t ].
       left.
        t; match goal with
        | |- post ?inp ?mach => specialize (H (Some (inp, mach)))
        end; t.
      + destruct (Memory.loadHalf (getMem initialL) addr) eqn: G; [ exfalso; t | ].
        right.
        t; match goal with
           | |- post ?inp ?mach => specialize (H (Some (inp, mach)))
           end; t.
    - intros. simpl in *. unfold computation_with_answer_satisfies in *.
      destruct (Memory.storeWord (getMem initialL) addr v) eqn: F.
      + destruct (Memory.loadWord (getMem initialL) addr) eqn: G; [ | exfalso; t ].
        left.
        t; match goal with
        | |- post ?inp ?mach => specialize (H (Some (inp, mach)))
        end; t.
      + destruct (Memory.loadWord (getMem initialL) addr) eqn: G; [ exfalso; t | ].
        right.
        t; match goal with
           | |- post ?inp ?mach => specialize (H (Some (inp, mach)))
           end; t.
    - intros. simpl in *. unfold computation_with_answer_satisfies in *.
      destruct (Memory.storeDouble (getMem initialL) addr v) eqn: F.
      + destruct (Memory.loadDouble (getMem initialL) addr) eqn: G; [ | exfalso; t ].
       left.
        t; match goal with
        | |- post ?inp ?mach => specialize (H (Some (inp, mach)))
        end; t.
      + destruct (Memory.loadDouble (getMem initialL) addr) eqn: G; [ exfalso; t | ].
        right.
        t; match goal with
           | |- post ?inp ?mach => specialize (H (Some (inp, mach)))
           end; t.
    - t; admit.
    - t; admit.
    - t; admit.
  Admitted.

End Riscv.

(* needed because defined inside a Section *)
Existing Instance IsRiscvMachineL.
Existing Instance MinimalMMIOSatisfiesPrimitives.
