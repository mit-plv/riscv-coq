Require Import Coq.ZArith.BinInt.
Require Import riscv.util.Monads. Import OStateOperations.
Require Import riscv.util.MonadNotations.
Require Import riscv.Decode.
Require Import riscv.Memory. (* should go before Program because both define loadByte etc *)
Require Import riscv.Program.
Require Import riscv.Execute.
Require Import riscv.util.PowerFunc.
Require Import riscv.Utility.
Require Import riscv.Minimal.
Require Import riscv.Primitives.
Require Import riscv.MetricPrimitives.
Require Import coqutil.Map.Interface.
Require Import riscv.RiscvMachine.
Require Import riscv.MetricRiscvMachine.
Require Import riscv.MetricLogging.
Require Import Coq.omega.Omega.
Require Import Coq.micromega.Lia.
Require Import coqutil.Map.Interface.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Logic.PropExtensionality.

Local Open Scope Z_scope.
Local Open Scope bool_scope.

Section Riscv.
  Context {W: Words}.
  Context {Mem: map.map word byte}.
  Context {Registers: map.map Register word}.

  Local Notation RiscvMachineL := (RiscvMachine Register Empty_set).
  Local Notation MetricRiscvMachineL := (MetricRiscvMachine Register Empty_set).

  Definition liftL0{B: Type}(fl: MetricLog -> MetricLog)(f: OState RiscvMachineL B):
    OState MetricRiscvMachineL B :=
    fun s => let (ob, s') := f s.(getMachine) in
             (ob, mkMetricRiscvMachine s' (fl s.(getMetrics))).

  Definition liftL1{A B: Type} fl (f: A -> OState RiscvMachineL B) :=
    fun a => liftL0 fl (f a).

  Definition liftL2{A1 A2 B: Type} fl (f: A1 -> A2 -> OState RiscvMachineL B) :=
    fun a1 a2 => liftL0 fl (f a1 a2).

  Instance IsMetricRiscvMachineL: RiscvProgram (OState MetricRiscvMachineL) word := {|
    getRegister := liftL1 id getRegister;
    setRegister := liftL2 id setRegister;
    getPC := liftL0 id getPC;
    setPC := liftL1 (addMetricJumps 1) setPC;
    loadByte := liftL1 (addMetricLoads 1) loadByte;
    loadHalf := liftL1 (addMetricLoads 1) loadHalf;
    loadWord := liftL1 (addMetricLoads 1) loadWord;
    loadDouble := liftL1 (addMetricLoads 1) loadDouble;
    storeByte := liftL2 (addMetricStores 1) storeByte;
    storeHalf := liftL2 (addMetricStores 1) storeHalf;
    storeWord := liftL2 (addMetricStores 1) storeWord;
    storeDouble := liftL2 (addMetricStores 1) storeDouble;
    step := liftL0 (addMetricInstructions 1) step;
    raiseException{A} := liftL2 id (raiseException (A := A));
  |}.

End Riscv.

Existing Instance IsMetricRiscvMachineL.