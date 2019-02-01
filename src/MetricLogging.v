Require Import Coq.ZArith.BinInt.
Require Import riscv.util.Monads. Import OStateOperations.
Require Import riscv.util.MonadNotations.
Require Import Coq.omega.Omega.
Require Import Coq.micromega.Lia.
Require Import riscv.Decode.
Require Import riscv.Utility.
Require Import riscv.Memory.
Require Import riscv.Program.
Require Import riscv.MinimalLogging.
Require Import coqutil.Map.Interface.

Section Riscv.
  
  Record MetricLog := mkMetricLog {
    instructions: Z;
    stores: Z;
    loads: Z; (* Note that this also includes loads of the PC *)
    jumps: Z;
  }.

  Definition EmptyMetricLog := mkMetricLog 0 0 0 0.

  Definition withInstructions i log := mkMetricLog i (stores log) (loads log) (jumps log).
  Definition withStores s log := mkMetricLog (instructions log) s (loads log) (jumps log).
  Definition withLoads l log := mkMetricLog (instructions log) (stores log) l (jumps log).
  Definition withJumps j log := mkMetricLog (instructions log) (stores log) (loads log) j.

  Definition addMetricInstructions n log := withInstructions (instructions log + n) log.
  Definition addMetricStores n log := withStores (stores log + n) log.
  Definition addMetricLoads n log := withLoads (loads log + n) log.
  Definition addMetricJumps n log := withJumps (jumps log + n) log.
  
  Definition subMetricInstructions n log := withInstructions (instructions log - n) log.
  Definition subMetricStores n log := withStores (stores log - n) log.
  Definition subMetricLoads n log := withLoads (loads log - n) log.
  Definition subMetricJumps n log := withJumps (jumps log - n) log.

  Hint Unfold
       withInstructions
       withLoads
       withStores
       withJumps
       addMetricInstructions
       addMetricLoads
       addMetricStores
       addMetricJumps
       subMetricInstructions
       subMetricLoads
       subMetricStores
       subMetricJumps
  : unf_metric_log.
  
  Ltac unfold_MetricLog := autounfold with unf_metric_log in *.

  Ltac fold_MetricLog :=
    match goal with
    | _ : _ |- context[?x] =>
      match x with
      | {| instructions := instructions ?y;
           stores := stores ?y;
           loads := loads ?y;
           jumps := jumps ?y; |} => replace x with y by (destruct y; reflexivity)
      end
    end.

  Ltac simpl_MetricLog :=
    cbn [fst snd] in *; (* Unfold logs in tuples *)
    cbn [instructions loads stores jumps] in *.

  Ltac try_equality_MetricLog :=
    repeat match goal with
           | H : MetricLog |- context[{| instructions := ?i; |}] =>
             progress replace i with (instructions H) by omega
           | H : MetricLog |- context[{| stores := ?i; |}] =>
             progress replace i with (stores H) by omega      
           | H : MetricLog |- context[{| loads := ?i; |}] =>
             progress replace i with (loads H) by omega      
           | H : MetricLog |- context[{| jumps := ?i; |}] =>
             progress replace i with (jumps H) by omega
           end.

  Ltac solve_MetricLog :=
    repeat unfold_MetricLog;
    repeat simpl_MetricLog;
    try_equality_MetricLog;
    lia || fold_MetricLog.

  Context {W: Words}.
  Context {Mem: map.map word byte}.
  Context {Registers: map.map Register word}.

  Local Notation RiscvMachine := (riscv.RiscvMachine.RiscvMachine Register LogEvent).

  Record RiscvMachineLog{Log : Type} := mkRiscvMachineLog {
    machine:> RiscvMachine;
    log: Log;
  }.

  Definition with_machine{Log: Type} m (ml : @RiscvMachineLog Log) :=
    mkRiscvMachineLog Log m ml.(log).
  Definition with_log{Log: Type} (l : Log) (ml : @RiscvMachineLog Log) :=
    mkRiscvMachineLog Log ml.(machine) l.

  Definition RiscvMachineMetricLog := @RiscvMachineLog MetricLog.

  Definition liftL0{B: Type} (fl: MetricLog -> MetricLog) (f: OState RiscvMachine B):
    OState RiscvMachineMetricLog B :=
    fun s => let (ob, s') := f s.(machine) in
             (ob, mkRiscvMachineLog MetricLog s' (fl s.(log))).

  Definition liftL1{A B: Type} fl (f: A -> OState RiscvMachine B) :=
    fun a => liftL0 fl (f a).

  Definition liftL2{A1 A2 B: Type} fl (f: A1 -> A2 -> OState RiscvMachine B) :=
    fun a1 a2 => liftL0 fl (f a1 a2).

  Instance IsRiscvMachineMetricLog: RiscvProgram (OState RiscvMachineMetricLog) word := {|
    getRegister := liftL1 id getRegister;
    setRegister := liftL2 id setRegister;
    getPC := liftL0 id getPC;
    setPC := liftL1 (addMetricJumps 1) setPC;
    loadByte   := liftL1 (addMetricLoads 1) loadByte;
    loadHalf   := liftL1 (addMetricLoads 1) loadHalf;
    loadWord := liftL1 (addMetricLoads 1) loadWord;
    loadDouble := liftL1 (addMetricLoads 1) loadDouble;
    storeByte   := liftL2 (addMetricStores 1) storeByte;
    storeHalf   := liftL2 (addMetricStores 1) storeHalf;
    storeWord := liftL2 (addMetricStores 1) storeWord;
    storeDouble := liftL2 (addMetricStores 1) storeDouble;
    step := liftL0 (addMetricInstructions 1) step;
    raiseException{A} := liftL2 id (raiseException (A := A));
  |}.

End Riscv.