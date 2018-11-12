Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Logic.PropExtensionality.
Require Import Coq.ZArith.BinInt.
Require Import riscv.util.BitWidths.
Require Import riscv.util.Monads. Import OStateNDOperations.
Require Import riscv.Decode.
Require Import riscv.Memory. (* should go before Program because both define loadByte etc *)
Require Import riscv.Program.
Require Import riscv.Execute.
Require Import riscv.util.PowerFunc.
Require Import riscv.Utility.
Require Import Coq.Lists.List. Import ListNotations.
Require Import riscv.RiscvMachine.
Require Export riscv.MMIOTrace.
Require Import riscv.AxiomaticRiscv.
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

  Definition liftLoad{R}(f: Mem t -> t -> R): t -> OStateND RiscvMachineL R :=
    fun a => m <- get; Return (f (m.(getMem)) a).

  Definition liftStore{R}(f: Mem t -> t -> R -> Mem t):
    t -> R -> OStateND RiscvMachineL unit :=
    fun a v =>
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
      storeWord   := liftStore Memory.storeWord;
      storeDouble := liftStore Memory.storeDouble;

      step :=
        m <- get;
        let m' := setPc m m.(getNextPc) in
        let m'' := setNextPc m' (add m.(getNextPc) (ZToReg 4)) in
        put m'';

      isMMIOAddr := simple_isMMIOAddr;

      (* fail hard if exception is thrown because at the moment, we want to prove that
         code output by the compiler never throws exceptions *)
      raiseException{A: Type}(isInterrupt: t)(exceptionCode: t) := fail_hard;
  |}.

  Instance MinimalNDSatisfiesAxioms:
    AxiomaticRiscv t (MMIOEvent t) (OStateND RiscvMachineL) :=
  {|
    mcomp_sat := @OStateNDOperations.computation_satisfies RiscvMachineL;
    mkInputEvent a v := (MMInput, proj1_sig a, v);
    mkOutputEvent a v := (MMOutput, proj1_sig a, v);
  |}.
  (* TODO this should be possible without destructing so deeply *)
  all: abstract (
    repeat match goal with
           | |- _ => reflexivity
           | |- _ => progress (
                         unfold computation_satisfies,
                                valid_register, Register0,
                                get, put, fail_hard, arbitrary,
                                liftLoad, liftStore, logEvent in *;
                         subst;
                         simpl in *)
           | |- _ => intro
           | |- _ => apply functional_extensionality
           | |- _ => apply propositional_extensionality; split; intros
           | u: unit |- _ => destruct u
           | H: exists x, _ |- _ => destruct H
           | H: _ /\ _ |- _ => destruct H
           | p: _ * _ |- _ => destruct p
           | |- context [ let (_, _) := ?p in _ ] => let E := fresh "E" in destruct p eqn: E
           | H: Some _ = Some _ |- _ => inversion H; clear H; subst
           | H: (_, _) = (_, _) |- _ => inversion H; clear H; subst
           | |- _ => discriminate
           | |- _ => solve [exfalso; lia]
           | |- _ => solve [eauto 15]
           | |- context [if ?x then _ else _] => let E := fresh "E" in destruct x eqn: E
           | _: context [if ?x then _ else _] |- _ => let E := fresh "E" in destruct x eqn: E
           | H: _ \/ _ |- _ => destruct H
           end).
  Defined.

End Riscv.

(* needed because defined inside a Section *)
Existing Instance IsRiscvMachineL.
Existing Instance MinimalNDSatisfiesAxioms.
