Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Logic.PropExtensionality.
Require Import riscv.Utility.Monads. Import OStateOperations.
Require Import riscv.Utility.MonadNotations.
Require Import riscv.Spec.Decode.
Require Import riscv.Spec.Machine.
Require Import riscv.Utility.Utility.
Require Import riscv.Spec.Primitives.
Require Export riscv.Platform.RiscvMachine.
Require Import coqutil.Z.Lia.
Require Import coqutil.Map.Interface.
Require Import riscv.Platform.Sane.

Local Open Scope Z_scope.
Local Open Scope bool_scope.
Import ListNotations.

Section Riscv.

  Context {width: Z} {BW: Bitwidth width} {word: word width} {word_ok: word.ok word}.
  Context {Mem: map.map word byte}.
  Context {Registers: map.map Register word}.

  Definition update(f: RiscvMachine -> RiscvMachine): OState RiscvMachine unit :=
    m <- get; put (f m).

  Definition fail_if_None{R}(o: option R): OState RiscvMachine R :=
    match o with
    | Some x => Return x
    | None => fail_hard
    end.

  Definition loadN(n: nat)(kind: SourceType)(a: word): OState RiscvMachine (HList.tuple byte n) :=
    mach <- get;
    v <- fail_if_None (Memory.load_bytes n mach.(getMem) a);
    match kind with
    | Fetch => if isXAddr4B a mach.(getXAddrs) then Return v else fail_hard
    | _ => Return v
    end.

  Definition storeN(n: nat)(kind: SourceType)(a: word)(v: HList.tuple byte n) :=
    mach <- get;
    m <- fail_if_None (Memory.store_bytes n mach.(getMem) a v);
    update (fun mach =>
              withXAddrs (invalidateWrittenXAddrs n a mach.(getXAddrs)) (withMem m mach)).

  Instance IsRiscvMachine: RiscvProgram (OState RiscvMachine) word :=  {
      getRegister reg :=
        if Z.eq_dec reg Register0 then
          Return (ZToReg 0)
        else
          if (0 <? reg) && (reg <? 32) then
            mach <- get;
            match map.get mach.(getRegs) reg with
            | Some v => Return v
            | None => Return (word.of_Z 0)
            end
          else
            fail_hard;

      setRegister reg v :=
        if Z.eq_dec reg Register0 then
          Return tt
        else
          if (0 <? reg) && (reg <? 32) then
            update (fun mach => withRegs (map.put mach.(getRegs) reg v) mach)
          else
            fail_hard;

      getPC := mach <- get; Return mach.(getPc);

      setPC newPC := update (withNextPc newPC);

      loadByte   := loadN 1;
      loadHalf   := loadN 2;
      loadWord   := loadN 4;
      loadDouble := loadN 8;

      storeByte   := storeN 1;
      storeHalf   := storeN 2;
      storeWord   := storeN 4;
      storeDouble := storeN 8;

      makeReservation  addr := fail_hard;
      clearReservation addr := fail_hard;
      checkReservation addr := fail_hard;
      getCSRField f := fail_hard;
      setCSRField f v := fail_hard;
      getPrivMode := fail_hard;
      setPrivMode v := fail_hard;
      fence _ _ := fail_hard;

      endCycleNormal := update (fun m => (withPc m.(getNextPc)
                                         (withNextPc (word.add m.(getNextPc) (word.of_Z 4)) m)));

      (* fail hard if exception is thrown because at the moment, we want to prove that
         code output by the compiler never throws exceptions *)
      endCycleEarly{A: Type} := fail_hard;
  }.

  Arguments Memory.load_bytes: simpl never.
  Arguments Memory.store_bytes: simpl never.

  Lemma VirtualMemoryFetchP: forall (addr: word) xAddrs,
      VirtualMemory = Fetch -> isXAddr4 addr xAddrs.
  Proof. intros. discriminate. Qed.

  Lemma ExecuteFetchP: forall (addr: word) xAddrs,
      Execute = Fetch -> isXAddr4 addr xAddrs.
  Proof. intros. discriminate. Qed.

  Ltac t :=
    repeat match goal with
       | |- _ => reflexivity
       | |- _ => progress (
                     unfold computation_satisfies, computation_with_answer_satisfies,
                            IsRiscvMachine,
                            valid_register,
                            is_initial_register_value,
                            get, put, fail_hard,
                            update,
                            Memory.loadByte, Memory.storeByte,
                            Memory.loadHalf, Memory.storeHalf,
                            Memory.loadWord, Memory.storeWord,
                            Memory.loadDouble, Memory.storeDouble,
                            fail_if_None, loadN, storeN in *;
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
       | H: isXAddr4B _ _ = false |- _ => apply isXAddr4B_not in H
       | H: isXAddr4B _ _ = true  |- _ => apply isXAddr4B_holds in H
       | H: ?x = ?x -> _ |- _ => specialize (H eq_refl)
       | |- _ * _ => constructor
       | |- option _ => exact None
       | |- _ => discriminate
       | |- _ => congruence
       | |- _ => solve [exfalso; blia]
       | |- _ => solve [eauto 15 using VirtualMemoryFetchP, ExecuteFetchP]
       | |- _ => progress (rewrite? Z.ltb_nlt in *; rewrite? Z.ltb_lt in * )
       | |- _ => blia
       | H: context[let (_, _) := ?y in _] |- _ => let E := fresh "E" in destruct y eqn: E
       | E: ?x = Some _, H: context[match ?x with _ => _ end] |- _ => rewrite E in H
       | E: ?x = Some _  |- context[match ?x with _ => _ end]      => rewrite E
       | H: context[match ?x with _ => _ end] |- _ => let E := fresh "E" in destruct x eqn: E
       | |- context[match ?x with _ => _ end]      => let E := fresh "E" in destruct x eqn: E
       | H: _ \/ _ |- _ => destruct H
       | r: RiscvMachine |- _ =>
         destruct r as [regs pc npc m l];
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

  Instance MinimalPrimitivesParams: PrimitivesParams (OState RiscvMachine) RiscvMachine := {
    Primitives.mcomp_sat := @OStateOperations.computation_with_answer_satisfies RiscvMachine;
    Primitives.is_initial_register_value := eq (word.of_Z 0);
    Primitives.nonmem_load n kind addr _ _ := False;
    Primitives.nonmem_store n kind addr v _ _ := False;
    Primitives.valid_machine _ := True;
  }.

  Instance MinimalSatisfies_mcomp_sat_spec: mcomp_sat_spec MinimalPrimitivesParams.
  Proof. constructor; t. Qed.

  Lemma get_sane: mcomp_sane get.
  Proof.
    unfold mcomp_sane, get. simpl. unfold computation_with_answer_satisfies. intros.
    destruct H0 as (? & ? & ? & ?). inversion H0. subst. clear H0.
    split.
    - eauto.
    - intros. do 2 eexists. split; [reflexivity|].
      split; [|trivial].
      split; [assumption|].
      exists nil. reflexivity.
  Qed.

  (* does not hold in general, because we could put a machine with a shorter log *)
  Lemma put_sane: forall m, mcomp_sane (put m). Abort.

  Lemma fail_hard_sane: forall A, mcomp_sane (fail_hard (A := A)).
  Proof.
    unfold mcomp_sane, fail_hard. simpl. unfold computation_with_answer_satisfies. intros.
    destruct H0 as (? & ? & ? & ?). discriminate.
  Qed.

  Lemma update_sane: forall f,
      (forall mach, exists diff, (f mach).(getLog) = diff ++ mach.(getLog)) ->
      mcomp_sane (update f).
  Proof.
    unfold mcomp_sane, update, get, put. simpl. unfold computation_with_answer_satisfies. intros.
    split.
    - edestruct H1 as (? & ? & ? & ?); eauto.
    - intros. destruct H1 as (? & ? & ? & ?).
      inversion H1. subst. clear H1.
      eauto 10.
  Qed.

  Lemma logEvent_sane: forall e,
      mcomp_sane (update (withLogItem e)).
  Proof.
    intros. eapply update_sane. intros. exists [e]. destruct mach. reflexivity.
  Qed.

  Instance MinimalSane: PrimitivesSane MinimalPrimitivesParams.
  Proof.
    constructor.
    all: intros;
      unfold getRegister, setRegister,
         loadByte, loadHalf, loadWord, loadDouble,
         storeByte, storeHalf, storeWord, storeDouble,
         getPC, setPC,
         endCycleNormal, endCycleEarly, raiseExceptionWithInfo,
         IsRiscvMachine,
         loadN, storeN, fail_if_None.

    all: repeat match goal with
                | |- _ => apply logEvent_sane
                | |- mcomp_sane (Bind _ _) => apply Bind_sane
                | |- _ => apply Return_sane
                | |- _ => apply get_sane
                | |- _ => apply fail_hard_sane
                | |- _ => apply update_sane; intros [? ? ? ? ? ?]; simpl; exists nil; reflexivity
                | |- context [match ?b with _ => _ end] => destruct b
                | |- _ => progress intros
                end.
  Qed.

  Instance MinimalSatisfiesPrimitives: Primitives MinimalPrimitivesParams.
  Proof.
    constructor.
    1: exact MinimalSatisfies_mcomp_sat_spec.
    1: exact MinimalSane.
    all: try t.
  Qed.

End Riscv.

(* needed because defined inside a Section *)
#[global] Existing Instance IsRiscvMachine.
#[global] Existing Instance MinimalSatisfiesPrimitives.
