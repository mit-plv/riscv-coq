Require Import Coq.ZArith.ZArith.
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

Local Open Scope Z_scope.
Local Open Scope bool_scope.

Section Riscv.

  Context {W: Words}.
  Context {Mem: map.map word byte}.
  Context {Registers: map.map Register word}.

  Local Notation RiscvMachineL := (RiscvMachine Register bool).

  Definition fail_if_None{R}(o: option R): OState RiscvMachineL R :=
    match o with
    | Some x => Return x
    | None => fail_hard
    end.

  Definition loadN(n: nat)(a: word): OState RiscvMachineL (HList.tuple byte n) :=
    mach <- get; fail_if_None (Memory.load_bytes n mach.(getMem) a).

  Definition storeN(n: nat)(a: word)(v: HList.tuple byte n): OState RiscvMachineL unit :=
    mach <- get;
    m <- fail_if_None (Memory.store_bytes n mach.(getMem) a v);
    put (withMem m mach).

  Definition getRegister(reg: Register): OState RiscvMachineL word :=
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
        fail_hard.

  Definition setRegister(reg: Register)(v: word): OState RiscvMachineL unit :=
    if Z.eq_dec reg Register0 then
      Return tt
    else
      if (0 <? reg) && (reg <? 32) then
        mach <- get;
        let newRegs := map.put mach.(getRegs) reg v in
        put (withRegs newRegs mach)
      else
        fail_hard.

  Definition getPC: OState RiscvMachineL word :=
    mach <- get;
    Return mach.(getPc).

  Definition setPC(newPC: word): OState RiscvMachineL unit :=
    mach <- get;
    put (withNextPc newPC mach).

  Definition step: OState RiscvMachineL unit :=
    m <- get;
    let m' := withPc m.(getNextPc) m in
    let m'' := withNextPc (add m.(getNextPc) (ZToReg 4)) m' in
    put m''.

  (* fail hard if exception is thrown because at the moment, we want to prove that
     code output by the compiler never throws exceptions *)
  Definition raiseExceptionWithInfo{A: Type}(isInterrupt exceptionCode info: word):
    OState RiscvMachineL A := fail_hard.

  Instance IsRiscvMachineL: RiscvProgram (OState RiscvMachineL) word :=  {
    riscv.Spec.Machine.getRegister := getRegister;
    riscv.Spec.Machine.setRegister := setRegister;
    riscv.Spec.Machine.getPC := getPC;
    riscv.Spec.Machine.setPC := setPC;
    riscv.Spec.Machine.loadByte   kind := loadN 1;
    riscv.Spec.Machine.loadHalf   kind := loadN 2;
    riscv.Spec.Machine.loadWord   kind := loadN 4;
    riscv.Spec.Machine.loadDouble kind := loadN 8;
    riscv.Spec.Machine.storeByte   kind := storeN 1;
    riscv.Spec.Machine.storeHalf   kind := storeN 2;
    riscv.Spec.Machine.storeWord   kind := storeN 4;
    riscv.Spec.Machine.storeDouble kind := storeN 8;
    riscv.Spec.Machine.step := step;
    riscv.Spec.Machine.raiseExceptionWithInfo := @raiseExceptionWithInfo;
  }.

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
                            getRegister, setRegister, getPC, setPC, step, raiseExceptionWithInfo,
                            Memory.loadByte, Memory.storeByte,
                            Memory.loadHalf, Memory.storeHalf,
                            Memory.loadWord, Memory.storeWord,
                            Memory.loadDouble, Memory.storeDouble,
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
       | H: _ && _ = true |- _ => apply andb_prop in H
       | H: _ && _ = false |- _ => apply Bool.andb_false_iff in H
       | |- _ * _ => constructor
       | |- option _ => exact None
       | |- _ => discriminate
       | |- _ => congruence
       | |- _ => solve [exfalso; bomega]
       | |- _ => solve [eauto 15]
       | |- _ => progress (rewrite? Z.ltb_nlt in *; rewrite? Z.ltb_lt in *)
       | |- _ => bomega
       | H: context[let (_, _) := ?y in _] |- _ => let E := fresh "E" in destruct y eqn: E
       | E: ?x = Some _, H: context[match ?x with _ => _ end] |- _ => rewrite E in H
       | E: ?x = Some _  |- context[match ?x with _ => _ end]      => rewrite E
       | H: context[match ?x with _ => _ end] |- _ => let E := fresh "E" in destruct x eqn: E
       | |- context[match ?x with _ => _ end]      => let E := fresh "E" in destruct x eqn: E
       | H: _ \/ _ |- _ => destruct H
       | r: RiscvMachineL |- _ =>
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

  Instance MinimalPrimitivesParams: PrimitivesParams (OState RiscvMachineL) RiscvMachineL := {|
    Primitives.mcomp_sat := @OStateOperations.computation_with_answer_satisfies RiscvMachineL;
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

  Instance MinimalSatisfiesPrimitives: Primitives MinimalPrimitivesParams.
  Proof.
    constructor.
    all: try t.
  Qed.

End Riscv.

(* needed because defined inside a Section *)
Existing Instance IsRiscvMachineL.
Existing Instance MinimalSatisfiesPrimitives.
