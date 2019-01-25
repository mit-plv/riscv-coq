Require Import Coq.ZArith.ZArith.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Logic.PropExtensionality.
Require Import riscv.util.BitWidths.
Require Import riscv.util.Monads. Import OStateNDOperations.
Require Import riscv.util.MonadNotations.
Require Import riscv.Decode.
Require Import riscv.Program.
Require Import riscv.Utility.
Require Import riscv.AxiomaticRiscvMMIO.
Require Import riscv.AxiomaticRiscv.
Require Import riscv.Primitives.
Require Import Coq.Lists.List. Import ListNotations.
Require Export riscv.MMIOTrace.
Require Export riscv.RiscvMachine.
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

  Definition theMMIOAddr: word := (ZToReg 65524). (* maybe like spike *)

  Definition simple_isMMIOAddr: word -> bool := reg_eqb theMMIOAddr.

  Definition logEvent(e: LogItem MMIOAction): OStateND RiscvMachineL unit :=
    m <- get; put (withLogItem e m).

  Definition fail_if_None{R}(o: option R): OStateND RiscvMachineL R :=
    match o with
    | Some x => Return x
    | None => fail_hard
    end.

  Definition loadN(n: nat)(a: word): OStateND RiscvMachineL (HList.tuple byte n) :=
    mach <- get; fail_if_None (Memory.load_bytes n mach.(getMem) a).

  Definition storeN(n: nat)(a: word)(v: HList.tuple byte n): OStateND RiscvMachineL unit :=
    mach <- get;
    m <- fail_if_None (Memory.store_bytes n mach.(getMem) a v);
    put (withMem m mach).

  Instance IsRiscvMachineL: RiscvProgram (OStateND RiscvMachineL) word :=  {|
      getRegister reg :=
        if Z.eq_dec reg Register0 then
          Return (ZToReg 0)
        else
          if (0 <? reg) && (reg <? 32) then
            mach <- get;
            match map.get mach.(getRegs) reg with
            | Some v => Return v
            | None => arbitrary word
            end
          else
            fail_hard;

      setRegister reg v :=
        if Z.eq_dec reg Register0 then
          Return tt
        else
          if (0 <? reg) && (reg <? 32) then
            mach <- get;
            let newRegs := map.put mach.(getRegs) reg v in
            put (setRegs mach newRegs)
          else
            fail_hard;

      getPC := mach <- get; Return mach.(getPc);

      setPC newPC :=
        mach <- get;
        put (setNextPc mach newPC);

      loadByte   := loadN 1;
      loadHalf   := loadN 2;
      loadWord a :=
        mach <- get;
        match Memory.loadWord mach.(getMem) a with
        | Some v => Return v
        | None => if simple_isMMIOAddr a then
                    inp <- arbitrary w32;
                    logEvent ((mach.(getMem), MMInput, [a]), (mach.(getMem), [uInt32ToReg inp]));;
                    Return inp
                  else
                    fail_hard
        end;
      loadDouble := loadN 8;

      storeByte   := storeN 1;
      storeHalf   := storeN 2;
      storeWord a v :=
        mach <- get;
        match Memory.storeWord mach.(getMem) a v with
        | Some m => put (withMem m mach)
        | None => if simple_isMMIOAddr a then
                    logEvent ((mach.(getMem), MMOutput, [a; uInt32ToReg v]), (mach.(getMem), []))
                  else
                    fail_hard
        end;
      storeDouble := storeN 8;

      step :=
        m <- get;
        let m' := setPc m m.(getNextPc) in
        let m'' := setNextPc m' (add m.(getNextPc) (ZToReg 4)) in
        put m'';

      (* fail hard if exception is thrown because at the moment, we want to prove that
         code output by the compiler never throws exceptions *)
      raiseException{A: Type}(isInterrupt: word)(exceptionCode: word) := fail_hard;
  |}.

  Arguments Memory.load_bytes: simpl never.
  Arguments Memory.store_bytes: simpl never.

  Lemma not_loadWord_fails_but_storeWord_succeeds: forall {m addr v m'},
      Memory.loadWord m addr = None ->
      Memory.storeWord m addr v = Some m' ->
      False.
  Proof.
    intros. unfold Memory.loadWord, Memory.storeWord, Memory.store_bytes in *.
    rewrite H in H0.
    discriminate.
  Qed.

  Lemma not_storeWord_fails_but_loadWord_succeeds: forall {m addr v0 v1},
      Memory.loadWord m addr = Some v0 ->
      Memory.storeWord m addr v1 = None ->
      False.
  Proof.
    intros. unfold Memory.loadWord, Memory.storeWord, Memory.store_bytes in *.
    rewrite H in H0.
    discriminate.
  Qed.

  Ltac t0 :=
    match goal with
       | |- _ => reflexivity
       | |- _ => progress (
                     unfold computation_satisfies, computation_with_answer_satisfies,
                            IsRiscvMachineL,
                            Primitives.valid_register, AxiomaticRiscv.valid_register, Register0,
                            Primitives.is_initial_register_value,
                            get, put, fail_hard,
                            arbitrary,
                            logEvent,
                            simple_isMMIOAddr, theMMIOAddr,
                            ZToReg, MkMachineWidth.MachineWidth_XLEN,
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
       | H1: _, H2: _ |- _ => exfalso; apply (not_loadWord_fails_but_storeWord_succeeds H1 H2)
       | H1: _, H2: _ |- _ => exfalso; apply (not_storeWord_fails_but_loadWord_succeeds H1 H2)
       | |- exists a b, Some (a, b) = _ /\ _ => do 2 eexists; split; [reflexivity|]
       | H: _ \/ _ |- _ => destruct H
       | r: RiscvMachineL |- _ =>
         destruct r as [regs pc npc m l];
         simpl in *
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

  Local Set Refine Instance Mode.

  Arguments LittleEndian.combine: simpl never.

  Instance MinimalMMIOSatisfiesPrimitives: Primitives MMIOAction (OStateND RiscvMachineL) := {|
    Primitives.mcomp_sat := @OStateNDOperations.computation_with_answer_satisfies RiscvMachineL;

    (* any value can be found in an uninitialized register *)
    Primitives.is_initial_register_value x := True;

    Primitives.nonmem_loadWord_sat initialL addr post :=
      simple_isMMIOAddr addr = true /\
      forall v, post v (withLogItem ((initialL.(getMem), MMInput, [addr]),
                                     (initialL.(getMem), [word.of_Z (LittleEndian.combine 4 v)]))
                                    initialL);

    Primitives.nonmem_storeWord_sat initialL addr v post :=
      simple_isMMIOAddr addr = true /\
      post (withLogItem
              ((initialL.(getMem), MMOutput, [addr; word.of_Z (LittleEndian.combine 4 v)]),
               (initialL.(getMem), []))
              initialL);
  |}.
  Proof.
    all: split; [solve [t]|].
    - t.
      unfold OStateND in m.
      exists (fun (a: A) (middleL: RiscvMachineL) => m initialL (Some (a, middleL))).
      t.
      edestruct H as [b [? ?]]; [eauto|]. t.
    - t.
    - t.
      + (edestruct H as [b [? ?]]; [eauto|]); t.
      + left. t. edestruct H as [b [? ?]]; t.
    - t.
      (edestruct H as [b [? ?]]; [eauto|]); t.
    - intros. unfold computation_with_answer_satisfies in *.
      destruct (Memory.loadWord (getMem initialL) addr) eqn: F.
      + left. eexists; split; eauto.
        match goal with
        | |- post ?inp ?mach => specialize (H (Some (inp, mach)))
        end.
        destruct H.
        * (* hypothesis of H *)
          right.
          do 2 eexists; split; [reflexivity|].
          simpl.
          rewrite F.
          reflexivity.
        * t.
      + right.
        destruct (simple_isMMIOAddr addr) eqn: G.
        * t.
          match goal with
          | |- post ?inp ?mach => specialize (H (Some (inp, mach)))
          end.
          destruct H; [|t].
          (* hypothesis of H *) right. do 2 eexists; split; [reflexivity|]. t.
        * exfalso.
          t.
          specialize (H None).
          destruct H; [|t].
          right.
          do 2 eexists; split; [reflexivity|].
          t.
    - intros. unfold computation_with_answer_satisfies in *.
      destruct (Memory.storeWord (getMem initialL) addr v) eqn: F.
      + destruct (Memory.loadWord (getMem initialL) addr) eqn: G; [ | exfalso; t ].
        left.
        eexists; split; [reflexivity|].
        match goal with
        | |- post ?inp ?mach => specialize (H (Some (inp, mach)))
        end.
        destruct H; [|solve [t]].
        t.
      + destruct (Memory.loadWord (getMem initialL) addr) eqn: G; [ exfalso; t | ].
        right.
        destruct (simple_isMMIOAddr addr) eqn: A.
        * t.
          match goal with
          | |- post ?inp ?mach => specialize (H (Some (inp, mach)))
          end.
          destruct H; [|t].
          (* hypothesis of H *) right. do 2 eexists; split; [reflexivity|]. t.
        * exfalso.
          t.
          specialize (H None).
          destruct H; [|t].
          right.
          do 2 eexists; split; [reflexivity|].
          t.
    - t.
      (edestruct H as [b [? ?]]; [eauto|]); t.
    - t.
      (edestruct H as [b [? ?]]; [eauto|]); t.
    - t.
      (edestruct H as [b [? ?]]; [eauto|]); t.
  Defined.

  Instance MinimalMMIOSatisfiesAxioms:
    AxiomaticRiscv MMIOAction (OStateND RiscvMachineL) :=
  {|
    AxiomaticRiscv.mcomp_sat := @OStateNDOperations.computation_satisfies RiscvMachineL;
  |}.
  Proof.
    all: abstract t.
  Defined.

  Arguments LittleEndian.combine: simpl never.

  Instance MinimalMMIOSatisfiesMMIOAxioms:
    AxiomaticRiscvMMIO (OStateND RiscvMachineL).
  Proof.
    constructor. all: t.
  Qed.

End Riscv.

(* needed because defined inside a Section *)
Existing Instance IsRiscvMachineL.
Existing Instance MinimalMMIOSatisfiesPrimitives.
Existing Instance MinimalMMIOSatisfiesAxioms.
Existing Instance MinimalMMIOSatisfiesMMIOAxioms.
