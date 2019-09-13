Require Import Coq.ZArith.ZArith.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Logic.PropExtensionality.
Require Import riscv.Utility.Monads. Import OStateNDOperations.
Require Import riscv.Utility.MonadNotations.
Require Import riscv.Spec.Decode.
Require Import riscv.Spec.Machine.
Require Import riscv.Utility.Utility.
Require Import riscv.Spec.Primitives.
Require Import riscv.Spec.MetricPrimitives.
Require Import Coq.Lists.List. Import ListNotations.
Require Export riscv.Utility.MMIOTrace.
Require Export riscv.Platform.RiscvMachine.
Require Export riscv.Platform.MetricRiscvMachine.
Require Import riscv.Platform.MinimalMMIO.
Require Import riscv.Platform.MetricLogging.
Require Import coqutil.Z.Lia.
Require Import coqutil.Map.Interface.
Require Import coqutil.Tactics.Tactics.
Import MetricRiscvMachine.

Local Open Scope Z_scope.
Local Open Scope bool_scope.

Section Riscv.
  Import free.

  Context {W: Words}.
  Context {Mem: map.map word byte}.
  Context {Registers: map.map Register word}.

  (* note: ext_spec does not have access to the metrics *)
  Context {ext_spec: ExtSpec}.

  Definition action : Type := (MetricLog -> MetricLog) * action.
  Definition result (a : action) := result (snd a).
  Local Notation M := (free action result).

  Instance IsRiscvMachine: RiscvProgram M word := {|
    Machine.getRegister a := act (id, getRegister a) ret;
    Machine.setRegister a b := act (id, setRegister a b) ret;
    Machine.loadByte a b := act (addMetricLoads 1, loadByte a b) ret;
    Machine.loadHalf a b := act (addMetricLoads 1, loadHalf a b) ret;
    Machine.loadWord a b := act (addMetricLoads 1, loadWord a b) ret;
    Machine.loadDouble a b := act (addMetricLoads 1, loadDouble a b) ret;
    Machine.storeByte a b c := act (addMetricStores 1, storeByte a b c) ret;
    Machine.storeHalf a b c := act (addMetricStores 1, storeHalf a b c) ret;
    Machine.storeWord a b c := act (addMetricStores 1, storeWord a b c) ret;
    Machine.storeDouble a b c := act (addMetricStores 1, storeDouble a b c) ret;
    Machine.makeReservation a := act (id, makeReservation a) ret;
    Machine.clearReservation a := act (id, clearReservation a) ret;
    Machine.checkReservation a := act (id, checkReservation a) ret;
    Machine.getPC := act (id, getPC) ret;
    Machine.setPC a := act (id, setPC a) ret;
    Machine.step := act (addMetricInstructions 1, step) ret;
    Machine.raiseExceptionWithInfo a b c d := act (id, raiseExceptionWithInfo a b c d) ret;
  |}.

  Definition interp_action a metmach post :=
    interp_action (snd a) (metmach.(getMachine)) (fun r mach =>
      post r (mkMetricRiscvMachine mach (fst a (metmach.(getMetrics))))).

  Definition interp {T} a mach post := @free.interp_fix action result MetricRiscvMachine interp_action T post a mach.

  Arguments Memory.load_bytes: simpl never.
  Arguments Memory.store_bytes: simpl never.
  Arguments LittleEndian.combine: simpl never.

  Global Instance MetricMinimalMMIOPrimitivesParams: PrimitivesParams M MetricRiscvMachine :=
  {
    Primitives.mcomp_sat := @interp;
    Primitives.is_initial_register_value x := True;
    Primitives.nonmem_load n := TODO_REMOVE;
    Primitives.nonmem_store n := TODO_REMOVE;
  }.

  Global Instance MinimalMMIOSatisfies_mcomp_sat_spec: mcomp_sat_spec MetricMinimalMMIOPrimitivesParams.
  Proof.
  Admitted.

  Global Instance MetricMinimalMMIOSatisfiesPrimitives:
    MetricPrimitives MetricMinimalMMIOPrimitivesParams.
  Proof.
  Admitted.

End Riscv.
