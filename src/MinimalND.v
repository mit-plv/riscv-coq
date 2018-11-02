Require Import Coq.ZArith.BinInt.
Require Import riscv.util.BitWidths.
Require Import riscv.util.Monads.
Require Import riscv.Decode.
Require Import riscv.Memory. (* should go before Program because both define loadByte etc *)
Require Import riscv.Program.
Require Import riscv.Execute.
Require Import riscv.util.PowerFunc.
Require Import riscv.Utility.
Require Import Coq.Lists.List. Import ListNotations.
Require Import riscv.Minimal.

Section Riscv.

  Context {t: Set}.

  Context {MW: MachineWidth t}.

  Context {Mem: Set}.

  Context {MemIsMem: Memory Mem t}.

  Context {RF: Type}.
  Context {RFI: RegisterFile RF Register t}.

  (* MMIO trace *)
  Inductive LogEvent :=
  | EvInput(addr: Z)(v: word 32)
  | EvOutput(addr: Z)(v: word 32).

  Definition Log := list LogEvent.

  Record RiscvMachineL := mkRiscvMachineL {
    machine: @RiscvMachine t Mem RF;
    log: Log;
  }.

  Definition with_machine m ml := mkRiscvMachineL m ml.(log).
  Definition with_log l ml := mkRiscvMachineL ml.(machine) l.

(*
  Definition liftL0{B: Type}(f: OStateND (@RiscvMachine t Mem RF) B):  OStateND RiscvMachineL B (*:=
    fun s => let (ob, ma) := f s.(machine) in (ob, with_machine ma s).*)
. Admitted.

  Definition liftL1{A B: Type}(f: A -> OStateND (@RiscvMachine t Mem RF) B): A -> OStateND RiscvMachineL B. (* :=
    fun a s => let (ob, ma) := f a s.(machine) in (ob, with_machine ma s).*) Admitted.

  Definition liftL2{A1 A2 B: Type}(f: A1 -> A2 -> OStateND (@RiscvMachine t Mem RF) B):
    A1 -> A2 -> OStateND RiscvMachineL B. (*  :=
    fun a1 a2 s => let (ob, ma) := f a1 a2 s.(machine) in (ob, with_machine ma s). *)
  Admitted.
*)
  Definition liftL0{B: Type}(f: OState (@RiscvMachine t Mem RF) B):  OStateND RiscvMachineL B (*:=
    fun s => let (ob, ma) := f s.(machine) in (ob, with_machine ma s).*)
. Admitted.

  Definition liftL1{A B: Type}(f: A -> OState (@RiscvMachine t Mem RF) B): A -> OStateND RiscvMachineL B. (* :=
    fun a s => let (ob, ma) := f a s.(machine) in (ob, with_machine ma s).*) Admitted.

  Definition liftL2{A1 A2 B: Type}(f: A1 -> A2 -> OState (@RiscvMachine t Mem RF) B):
    A1 -> A2 -> OStateND RiscvMachineL B. (*  :=
    fun a1 a2 s => let (ob, ma) := f a1 a2 s.(machine) in (ob, with_machine ma s). *)
  Admitted.

  Definition TODO{A: Type}: A. Admitted.

  Definition get: OStateND RiscvMachineL RiscvMachineL.
    intro s. intro set.
    apply (forall mach ans, set mach ans <-> ans = Some mach /\ mach = s).
  Defined.

  Definition put(s: RiscvMachineL): OStateND RiscvMachineL unit.
    refine (fun initial set => forall mach ans, set mach ans <-> mach = s /\ ans = Some tt).
  Defined.

  Definition failure{A}: OStateND RiscvMachineL A := fun s outcomes => False.

  Definition success{A}(set: RiscvMachineL -> option A -> Prop): OStateND RiscvMachineL A.
    refine (fun initial set' => forall mach ans, set' mach ans <-> set mach ans).
  Defined.

  Definition deterministic{S A}(m: S)(ans: option A): S -> option A -> Prop :=
    fun s ans' => s = m /\ ans = ans'. (* todo * instead of curry and jus eq *)

  Definition arbitrary(A: Type): OStateND RiscvMachineL A.
    refine (s <- get; success _).
    refine (fun s' oa => s = s' /\ exists a, oa = Some a).
  Defined.

  Definition answer{A: Type}(ans: A): OStateND RiscvMachineL A :=
    s <- get; success (deterministic s (Some ans)).

  (* recoverable (through option) *)
  Definition throw{A}: OStateND RiscvMachineL A :=
    s <- get; success (deterministic s None).

  Definition logEvent(e: LogEvent): OStateND RiscvMachineL unit :=
    m <- get; put (with_log (e :: m.(log)) m).

  Definition isMMIOAddr(a: t): bool. Admitted.

  Instance IsRiscvMachineL: RiscvProgram (OStateND RiscvMachineL) t :=  {|
      getRegister := liftL1 getRegister;
      setRegister := liftL2 setRegister;
      getPC := liftL0 getPC;
      setPC := liftL1 setPC;
      loadByte   := liftL1 loadByte;
      loadHalf   := liftL1 loadHalf;
      loadWord a := if isMMIOAddr a
                    then
                      inp <- arbitrary (word 32);
                      logEvent (EvInput (regToZ_unsigned a) inp);; answer inp
                    else liftL1 loadWord a;
      loadDouble := liftL1 loadDouble;
      storeByte   := liftL2 storeByte;
      storeHalf   := liftL2 storeHalf;
      storeWord a v := TODO;
      storeDouble := liftL2 storeDouble;
      step := liftL0 step;
      getCSRField_MTVecBase := liftL0 getCSRField_MTVecBase;
      endCycle A := TODO;
  |}.
(*
  - refine (if isMMIOAddr a then _ else _).
    { refine (inp <- arbitrary (word 32); _).
      refine (logEvent (EvInput (regToZ_unsigned a) inp);; answer inp).
    }
    {
      exact (liftL1 loadWord a).
    }
  Defined.
*)
  Definition putProgram(prog: list (word 32))(addr: t)(ma: RiscvMachineL): RiscvMachineL :=
    with_machine (putProgram prog addr ma.(machine)) ma.

End Riscv.

Existing Instance IsRiscvMachineL. (* needed because it was defined inside a Section *)
