Require Import Coq.ZArith.ZArith.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Logic.PropExtensionality.
Require Import riscv.util.BitWidths.
Require Import riscv.util.Monads. Import OStateNDOperations.
Require Import riscv.util.MonadNotations.
Require Import riscv.Decode.
Require Import riscv.Memory. (* should go before Program because both define loadByte etc *)
Require Import riscv.Program.
Require Import riscv.Utility.
Require Import riscv.AxiomaticRiscv.
Require Import Coq.Lists.List. Import ListNotations.
Require Export riscv.MMIOTrace.
Require Export riscv.RiscvMachine.
Require Import Coq.micromega.Lia.


Section Riscv.

  Context {t: Set}.
  Context {MW: MachineWidth t}.
  Context {MF: MemoryFunctions t}.
  Context {RFF: RegisterFileFunctions Register t}.

  Local Notation RiscvMachineL := (RiscvMachine Register t (MMIOEvent t)).

  Definition simple_isMMIOAddr: t -> bool := reg_eqb (ZToReg 65524). (* maybe like spike *)


  Definition logEvent(e: MMIOEvent t): OStateND RiscvMachineL unit :=
    m <- get; put (logCons m e).

  Definition addrInRange(a: t): OStateND RiscvMachineL bool :=
    mach <- get;
    Return (regToZ_unsigned a <? mach.(getMem).(memSize)).

  Definition assert(cond: OStateND RiscvMachineL bool): OStateND RiscvMachineL unit :=
    b <- cond; if b then (Return tt) else fail_hard.

  Definition liftLoad{R}(f: Mem t -> t -> R): t -> OStateND RiscvMachineL R :=
    fun a => assert (addrInRange a);; m <- get; Return (f (m.(getMem)) a).

  Definition liftStore{R}(f: Mem t -> t -> R -> Mem t):
    t -> R -> OStateND RiscvMachineL unit :=
    fun a v =>
      assert (addrInRange a);;
      m <- get;
      put (setMem m (f m.(getMem) a v)).

  Instance IsRiscvMachineL: RiscvProgram (OStateND RiscvMachineL) t :=  {|
      getRegister reg :=
        if Z.eq_dec reg Register0 then
          Return (ZToReg 0)
        else
          mach <- get;
          Return (getReg mach.(getRegs) reg);

      setRegister reg v :=
        if Z.eq_dec reg Register0 then
          Return tt
        else
          mach <- get;
          let newRegs := setReg mach.(getRegs) reg v in
          put (setRegs mach newRegs);

      getPC := mach <- get; Return mach.(getPc);

      setPC newPC :=
        mach <- get;
        put (setNextPc mach newPC);

      loadByte   := liftLoad Memory.loadByte;
      loadHalf   := liftLoad Memory.loadHalf;
      loadWord a := if simple_isMMIOAddr a
                    then
                      inp <- arbitrary (word 32);
                      logEvent (MMInput, a, inp);;
                      Return inp
                    else liftLoad Memory.loadWord a;
      loadDouble := liftLoad Memory.loadDouble;

      storeByte   := liftStore Memory.storeByte;
      storeHalf   := liftStore Memory.storeHalf;
      storeWord a v := if simple_isMMIOAddr a
                       then logEvent (MMOutput, a, v)
                       else liftStore Memory.storeWord a v;
      storeDouble := liftStore Memory.storeDouble;

      step :=
        m <- get;
        let m' := setPc m m.(getNextPc) in
        let m'' := setNextPc m' (add m.(getNextPc) (ZToReg 4)) in
        put m'';

      isPhysicalMemAddr := addrInRange;

      (* fail hard if exception is thrown because at the moment, we want to prove that
         code output by the compiler never throws exceptions *)
      raiseException{A: Type}(isInterrupt: t)(exceptionCode: t) := fail_hard;
  |}.

  Ltac t :=
    repeat match goal with
       | |- _ => reflexivity
       | |- _ => progress (
                     unfold computation_satisfies,
                            IsRiscvMachineL,
                            valid_register, Register0,
                            get, put, fail_hard, arbitrary,
                            logEvent,
                            addrInRange, assert, liftLoad, liftStore in *;
                     subst;
                     simpl in *)
       | |- _ => intro
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
       | |- _ * _ => constructor
       | |- option _ => exact None
       | |- _ => discriminate
       | |- _ => congruence
       | |- _ => solve [exfalso; lia]
       | |- _ => solve [eauto 15]
       | |- context [if ?x then _ else _] => let E := fresh "E" in destruct x eqn: E
       | _: context [if ?x then _ else _] |- _ => let E := fresh "E" in destruct x eqn: E
       | H: _ \/ _ |- _ => destruct H
       | r: RiscvMachineL |- _ =>
         destruct r as [regs pc npc m l];
         simpl in *;
         rewrite @storeWord_preserves_memSize in *
       end.


  Instance MinimalMMIOSatisfiesAxioms:
    AxiomaticRiscv t (MMIOEvent t) (OStateND RiscvMachineL) :=
  {|
    mcomp_sat := @OStateNDOperations.computation_satisfies RiscvMachineL;
  |}.
  (* TODO this should be possible without destructing so deeply *)
  all: t.
  admit.

 {
  match goal with
  | H: _ |- _ =>
    let p1 := fresh "p1" in let o1 := fresh "o1" in
    evar (p1: option (unit * RiscvMachineL) -> Prop);
    evar (o1: option (unit * RiscvMachineL));
    specialize (H (fun _ => p1) o1);
    subst p1 o1
  end.
  eapply H.
  right.
  do 2 eexists. split.
  - right. eauto.
  - rewrite <- H5. instantiate (1 := fun _ => 42 = 42). reflexivity.
}

 {
  match goal with
  | H: _ |- _ =>
    let p1 := fresh "p1" in let o1 := fresh "o1" in
    evar (p1: option (unit * RiscvMachineL) -> Prop);
    evar (o1: option (unit * RiscvMachineL));
    specialize (H (fun _ => p1) o1);
    subst p1 o1
  end.
  eapply H.
  right.
  do 2 eexists. split.
  - right. eauto.
  - rewrite <- H4. assumption.
}

 {
  match goal with
  | H: _ |- _ =>
    let p1 := fresh "p1" in let o1 := fresh "o1" in
    evar (p1: option (unit * RiscvMachineL) -> Prop);
    evar (o1: option (unit * RiscvMachineL));
    specialize (H (fun _ => p1) o1);
    subst p1 o1
  end.
  eapply H. clear H.
  right.
  do 2 eexists. split.
  - right. eauto.
  - (* need additional hypothesis
  simple_isMMIOAddr addr = true -> isPhysicalMemAddr addr = Return false,
  maybe as an argument to the Instance? *)
  Admitted.

End Riscv.

(* needed because defined inside a Section *)
Existing Instance IsRiscvMachineL.
Existing Instance MinimalMMIOSatisfiesAxioms.
