Require Import Coq.ZArith.ZArith.
Require Import coqutil.Word.Interface coqutil.Word.Bitwidth.
Require Import riscv.Utility.Monads.
Require Import riscv.Utility.FreeMonad.
Require Import riscv.Spec.Machine.
Require Import riscv.Platform.MetricLogging.
Require Import riscv.Platform.MaterializeRiscvProgram.

Section Riscv.
  Import free.

  Context {width: Z} {BW: Bitwidth width} {word: word width}.

  Definition action : Type := (MetricLog -> MetricLog) * riscv_primitive.
  Definition result (a : action) := primitive_result (snd a).

  Global Instance MetricMaterialize: RiscvProgram (free action result) word := {|
    getRegister a := act (id, GetRegister a) ret;
    setRegister a b := act (id, SetRegister a b) ret;
    loadByte a b := act (addMetricLoads 1, LoadByte a b) ret;
    loadHalf a b := act (addMetricLoads 1, LoadHalf a b) ret;
    loadWord a b := act (addMetricLoads 1, LoadWord a b) ret;
    loadDouble a b := act (addMetricLoads 1, LoadDouble a b) ret;
    storeByte a b c := act (addMetricStores 1, StoreByte a b c) ret;
    storeHalf a b c := act (addMetricStores 1, StoreHalf a b c) ret;
    storeWord a b c := act (addMetricStores 1, StoreWord a b c) ret;
    storeDouble a b c := act (addMetricStores 1, StoreDouble a b c) ret;
    makeReservation a := act (id, MakeReservation a) ret;
    clearReservation a := act (id, ClearReservation a) ret;
    checkReservation a := act (id, CheckReservation a) ret;
    getCSRField f := act (id, GetCSRField f) ret;
    setCSRField f v := act (id, SetCSRField f v) ret;
    getPrivMode := act (id, GetPrivMode) ret;
    setPrivMode m := act (id, SetPrivMode m) ret;
    fence a b := act (id, Fence a b) ret;
    getPC := act (id, GetPC) ret;
    setPC a := act (addMetricJumps 1, SetPC a) ret;
    endCycleNormal := act (addMetricInstructions 1, EndCycleNormal) ret;
    endCycleEarly A := act (addMetricInstructions 1, EndCycleEarly A) ret;
  |}.

  Global Instance MetricMaterializeWithLeakage : RiscvProgramWithLeakage (free action result) word := {|
    RVP := MetricMaterialize;
    leakEvent a := act (id, LeakEvent a) ret
  |}.

End Riscv.
