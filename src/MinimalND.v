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

  Definition liftL0{B: Type}(f: OState (@RiscvMachine t Mem RF) B):  OStateND RiscvMachineL B (*:=
    fun s => let (ob, ma) := f s.(machine) in (ob, with_machine ma s).*)
. Admitted.

  Definition liftL1{A B: Type}(f: A -> OState (@RiscvMachine t Mem RF) B): A -> OStateND RiscvMachineL B. (* :=
    fun a s => let (ob, ma) := f a s.(machine) in (ob, with_machine ma s).*) Admitted.

  Definition liftL2{A1 A2 B: Type}(f: A1 -> A2 -> OState (@RiscvMachine t Mem RF) B):
    A1 -> A2 -> OStateND RiscvMachineL B. (*  :=
    fun a1 a2 s => let (ob, ma) := f a1 a2 s.(machine) in (ob, with_machine ma s). *)
  Admitted.
*)
  Definition TODO{A: Type}: A. Admitted.
(*
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
*)

  Definition logEvent(e: LogEvent): OStateND RiscvMachineL unit :=
    m <- get; put (with_log (e :: m.(log)) m).

  Definition isMMIOAddr(a: t): bool. Admitted.

  Definition liftLoad{R}(f: Mem -> t -> R): t -> OStateND RiscvMachineL R :=
    fun a => m <- get; Return (f (m.(machine).(machineMem)) a).

  Definition liftStore{R}(f: Mem -> t -> R -> Mem):
    t -> R -> OStateND RiscvMachineL unit :=
    fun a v =>
      m <- get;
      let newMem := f m.(machine).(machineMem) a v in
      put (with_machine (with_machineMem newMem (m.(machine))) m).

  Instance IsRiscvMachineL: RiscvProgram (OStateND RiscvMachineL) t :=  {|
      getRegister reg :=
        if Z.eq_dec reg Register0 then
          Return (ZToReg 0)
        else
          mach <- get;
          Return (getReg mach.(machine).(core).(registers) reg);

      setRegister reg v :=
        if Z.eq_dec reg Register0 then
          Return tt
        else
          mach <- get;
          let newRegs := setReg mach.(machine).(core).(registers) reg v in
          put (with_machine (with_registers newRegs mach.(machine)) mach);

      getPC := mach <- get; Return mach.(machine).(core).(pc);

      setPC newPC :=
        mach <- get;
        put (with_machine (with_nextPC newPC mach.(machine)) mach);

      loadByte   := liftLoad Memory.loadByte;
      loadHalf   := liftLoad Memory.loadHalf;
      loadWord a := if isMMIOAddr a
                    then
                      inp <- arbitrary (word 32);
                      logEvent (EvInput (regToZ_unsigned a) inp);;
                      Return inp
                    else liftLoad Memory.loadWord a;
      loadDouble := liftLoad Memory.loadDouble;

      storeByte   := liftStore Memory.storeByte;
      storeHalf   := liftStore Memory.storeHalf;
      storeWord   := liftStore Memory.storeWord;
      storeDouble := liftStore Memory.storeDouble;

      step :=
        mach <- get;
        let m := mach.(machine) in
        let m' := with_nextPC (add m.(core).(nextPC) (ZToReg 4)) (with_pc m.(core).(nextPC) m) in
        put (with_machine m' mach);

      getCSRField_MTVecBase := fail_hard;

      endCycle A := fail_hard;
  |}.

End Riscv.

Existing Instance IsRiscvMachineL. (* needed because it was defined inside a Section *)
