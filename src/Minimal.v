Require Import Coq.ZArith.ZArith.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Logic.PropExtensionality.
Require Import riscv.util.BitWidths.
Require Import riscv.util.Monads. Import OStateOperations.
Require Import riscv.util.MonadNotations.
Require Import riscv.Decode.
Require Import riscv.Memory. (* should go before Program because both define loadByte etc *)
Require Import riscv.Program.
Require Import riscv.Utility.
Require Import riscv.AxiomaticRiscv.
Require Export riscv.RiscvMachine.
Require Import Coq.micromega.Lia.


Section Riscv.

  Context {t: Set}.
  Context {MW: MachineWidth t}.
  Context {MF: MemoryFunctions t}.
  Context {RFF: RegisterFileFunctions Register t}.

  Local Notation RiscvMachineL := (RiscvMachine Register t Empty_set).

  Definition addrInRange(a: t): OState RiscvMachineL bool :=
    mach <- get;
    Return (regToZ_unsigned a <? mach.(getMem).(memSize)).

  Definition assert(cond: OState RiscvMachineL bool): OState RiscvMachineL unit :=
    b <- cond; if b then (Return tt) else fail_hard.

  Definition liftLoad{R}(f: Mem t -> t -> R): t -> OState RiscvMachineL R :=
    fun a => assert (addrInRange a);; m <- get; Return (f (m.(getMem)) a).

  Definition liftStore{R}(f: Mem t -> t -> R -> Mem t):
    t -> R -> OState RiscvMachineL unit :=
    fun a v =>
      assert (addrInRange a);;
      m <- get;
      put (setMem m (f m.(getMem) a v)).

  Instance IsRiscvMachineL: RiscvProgram (OState RiscvMachineL) t :=  {|
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
      loadWord   := liftLoad Memory.loadWord;
      loadDouble := liftLoad Memory.loadDouble;

      storeByte   := liftStore Memory.storeByte;
      storeHalf   := liftStore Memory.storeHalf;
      storeWord   := liftStore Memory.storeWord;
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
                            get, put, fail_hard,
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
       | H: _ |- _ => refine (H (fun _ => _)) (* undef behavior of load/store outside range *)
       end.

  Instance MinimalSatisfiesAxioms: AxiomaticRiscv t Empty_set (OState RiscvMachineL) := {|
    mcomp_sat := @OStateOperations.computation_satisfies RiscvMachineL;
  |}.
  (* TODO this should be possible without destructing so deeply *)
  all: abstract t.
  Defined.

End Riscv.

(* needed because defined inside a Section *)
Existing Instance IsRiscvMachineL.
Existing Instance MinimalSatisfiesAxioms.
