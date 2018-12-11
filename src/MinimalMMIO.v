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

  Context {t: Type}.
  Context {MW: MachineWidth t}.
  Context {MF: MemoryFunctions t}.
  Context {RFF: RegisterFileFunctions Register t}.

  Local Notation RiscvMachineL := (RiscvMachine Register t MMIOAction).

  Definition theMMIOAddr: t := (ZToReg 65524). (* maybe like spike *)

  Definition simple_isMMIOAddr: t -> bool := reg_eqb theMMIOAddr.

  Definition logEvent(e: LogItem t MMIOAction): OStateND RiscvMachineL unit :=
    m <- get; put (withLogItem e m).

  Definition isMemAddr(a: t): OStateND RiscvMachineL bool :=
    mach <- get; Return (mach.(isMem) a).

  Definition assert(cond: OStateND RiscvMachineL bool): OStateND RiscvMachineL unit :=
    b <- cond; if b then (Return tt) else fail_hard.

  Definition liftLoad{R}(f: Mem t -> t -> R): t -> OStateND RiscvMachineL R :=
    fun a => assert (isMemAddr a);; m <- get; Return (f (m.(getMem)) a).

  Definition liftStore{R}(f: Mem t -> t -> R -> Mem t):
    t -> R -> OStateND RiscvMachineL unit :=
    fun a v =>
      assert (isMemAddr a);;
      m <- get;
      put (withMem (f m.(getMem) a v) m).

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

      loadWord a :=
        mach <- get;
        if mach.(isMem) a then
          liftLoad Memory.loadWord a
        else
          if simple_isMMIOAddr a then
            inp <- arbitrary (word 32);
            logEvent (MMInput, [a], [uInt32ToReg inp]);;
            Return inp
          else
            fail_hard;
      loadDouble := liftLoad Memory.loadDouble;

      storeByte   := liftStore Memory.storeByte;
      storeHalf   := liftStore Memory.storeHalf;
      storeWord a v :=
        mach <- get;
        if mach.(isMem) a then
          liftStore Memory.storeWord a v
        else
          if simple_isMMIOAddr a then
            logEvent (MMOutput, [a; uInt32ToReg v], [])
          else
            fail_hard;

      storeDouble := liftStore Memory.storeDouble;

      step :=
        m <- get;
        let m' := setPc m m.(getNextPc) in
        let m'' := setNextPc m' (add m.(getNextPc) (ZToReg 4)) in
        put m'';

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
                            in_range,
                            simple_isMMIOAddr,
                            isMemAddr, assert, liftLoad, liftStore in *;
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
       | H: false = ?rhs |- _ => match rhs with
                                 | false => fail 1
                                 | _ => symmetry in H
                                 end
       | |- _ => rewrite! Z.ltb_nlt in *
       | |- _ => omega
       | |- context [if ?x then _ else _] => let E := fresh "E" in destruct x eqn: E
       | _: context [if ?x then _ else _] |- _ => let E := fresh "E" in destruct x eqn: E
       | H: _ \/ _ |- _ => destruct H
       | r: RiscvMachineL |- _ =>
         destruct r as [regs pc npc m l];
         simpl in *;
         rewrite @storeWord_preserves_memSize in *
       end.


  Instance MinimalMMIOSatisfiesAxioms:
    AxiomaticRiscv t MMIOAction (OStateND RiscvMachineL) :=
  {|
    mcomp_sat := @OStateNDOperations.computation_satisfies RiscvMachineL;
  |}.
  (* TODO this should be possible without destructing so deeply *)
  all: abstract t.
  Defined.

End Riscv.

(* needed because defined inside a Section *)
Existing Instance IsRiscvMachineL.
Existing Instance MinimalMMIOSatisfiesAxioms.
