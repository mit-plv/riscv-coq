Require Import Coq.Lists.List.
Require Import Coq.ZArith.BinInt.
Require Import coqutil.Map.Interface.
Require Import riscv.Utility.Monads.
Require Import riscv.Utility.Utility.
Require Import riscv.Spec.Decode.
Require Import riscv.Platform.Memory.
Require Import riscv.Platform.RiscvMachine.
Require Import riscv.Spec.Machine.
Require Import riscv.Platform.MetricRiscvMachine.
Require Import riscv.Utility.MkMachineWidth.
Require Import riscv.Platform.MetricLogging.
Require Import riscv.Spec.Primitives.

Section MetricPrimitives.

  Context {width: Z} {BW: Bitwidth width} {word: word width} {word_ok: word.ok word}.
  Context {Registers: map.map Register word}.
  Context {mem: map.map word byte}.

  Context {M: Type -> Type}.
  Context {MM: Monad M}.
  Context {RVM: RiscvProgram M word}.
  Context {RVS: @RiscvMachine M word _ _ RVM}.

  (* monadic computations used for specifying the behavior of RiscvMachines should be "sane"
     in the sense that we never step to the empty set (that's not absence of failure, since
     failure is modeled as "steps to no set at all"), and that the trace of events is
     append-only *)
  Definition mcomp_sane{p: PrimitivesParams M MetricRiscvMachine}{A: Type}(comp: M A): Prop :=
    forall (st: MetricRiscvMachine) (post: A -> MetricRiscvMachine -> Prop),
      valid_machine st ->
      mcomp_sat comp st post ->
      (exists a st', post a st' /\ valid_machine st') /\
      (mcomp_sat comp st (fun a st' =>
         (post a st' /\ exists diff, st'.(getLog) = diff ++ st.(getLog)) /\ valid_machine st')).

  Class MetricPrimitivesSane(p: PrimitivesParams M MetricRiscvMachine): Prop := {
    getRegister_sane: forall r, mcomp_sane (getRegister r);
    setRegister_sane: forall r v, mcomp_sane (setRegister r v);
    loadByte_sane: forall kind addr, mcomp_sane (loadByte kind addr);
    loadHalf_sane: forall kind addr, mcomp_sane (loadHalf kind addr);
    loadWord_sane: forall kind addr, mcomp_sane (loadWord kind addr);
    loadDouble_sane: forall kind addr, mcomp_sane (loadDouble kind addr);
    storeByte_sane: forall kind addr v, mcomp_sane (storeByte kind addr v);
    storeHalf_sane: forall kind addr v, mcomp_sane (storeHalf kind addr v);
    storeWord_sane: forall kind addr v, mcomp_sane (storeWord kind addr v);
    storeDouble_sane: forall kind addr v, mcomp_sane (storeDouble kind addr v);
    makeReservation_sane: forall addr, mcomp_sane (makeReservation addr);
    clearReservation_sane: forall addr, mcomp_sane (clearReservation addr);
    checkReservation_sane: forall addr, mcomp_sane (checkReservation addr);
    getCSRField_sane: forall f, mcomp_sane (getCSRField f);
    setCSRField_sane: forall f v, mcomp_sane (setCSRField f v);
    getPrivMode_sane: mcomp_sane getPrivMode;
    setPrivMode_sane: forall m, mcomp_sane (setPrivMode m);
    fence_sane: forall a b, mcomp_sane (fence a b);
    getPC_sane: mcomp_sane getPC;
    setPC_sane: forall newPc, mcomp_sane (setPC newPc);
    endCycleNormal_sane: mcomp_sane endCycleNormal;
    endCycleEarly_sane: forall A, mcomp_sane (@endCycleEarly _ _ _ _ _ A);
  }.

  Definition spec_load{p: PrimitivesParams M MetricRiscvMachine}(n: nat)
             (riscv_load: SourceType -> word -> M (HList.tuple byte n))
             (mem_load: mem -> word -> option (HList.tuple byte n))
    : Prop :=
    forall (initialL: MetricRiscvMachine) addr (kind: SourceType)
           (post: HList.tuple byte n -> MetricRiscvMachine -> Prop),
      (kind = Fetch -> isXAddr4 addr initialL.(getXAddrs)) /\
      ((exists v, mem_load initialL.(getMem) addr = Some v /\
                  post v (updateMetrics (addMetricLoads 1) initialL)) \/
       (mem_load initialL.(getMem) addr = None /\
        nonmem_load n kind addr initialL (fun v m => post v (mkMetricRiscvMachine m (addMetricLoads 1 initialL.(getMetrics)))))) ->
      mcomp_sat (riscv_load kind addr) initialL post.

  Definition spec_store{p: PrimitivesParams M MetricRiscvMachine}(n: nat)
             (riscv_store: SourceType -> word -> HList.tuple byte n -> M unit)
             (mem_store: mem -> word -> HList.tuple byte n -> option mem)
             : Prop :=
    forall (initialL: MetricRiscvMachine) addr v (kind: SourceType)
           (post: unit -> MetricRiscvMachine -> Prop),
      (exists m', mem_store initialL.(getMem) addr v = Some m' /\
                  post tt (withXAddrs (invalidateWrittenXAddrs n addr initialL.(getXAddrs))
                          (withMem m' (updateMetrics (addMetricStores 1) initialL)))) \/
      (mem_store initialL.(getMem) addr v = None /\
       nonmem_store n kind addr v initialL (fun m => post tt (mkMetricRiscvMachine m (addMetricStores 1 initialL.(getMetrics))))) ->
      mcomp_sat (riscv_store kind addr v) initialL post.

  (* primitives_params is a paramater rather than a field because Primitives lives in Prop and
     is opaque, but the fields of primitives_params need to be visible *)
  Class MetricPrimitives(primitives_params: PrimitivesParams M MetricRiscvMachine): Prop := {
    mcomp_sat_ok :> mcomp_sat_spec primitives_params;

    primitives_sane :> MetricPrimitivesSane primitives_params;

    spec_getRegister: forall (initialL: MetricRiscvMachine) (x: Register)
                             (post: word -> MetricRiscvMachine -> Prop),
        (valid_register x /\
         match map.get initialL.(getRegs) x with
         | Some v => post v initialL
         | None => forall v, is_initial_register_value v -> post v initialL
         end) \/
        (x = Register0 /\ post (word.of_Z 0) initialL) ->
        mcomp_sat (getRegister x) initialL post;

    spec_setRegister: forall (initialL: MetricRiscvMachine) x v (post: unit -> MetricRiscvMachine -> Prop),
      (valid_register x /\ post tt (withRegs (map.put initialL.(getRegs) x v) initialL) \/
       x = Register0 /\ post tt initialL) ->
      mcomp_sat (setRegister x v) initialL post;

    spec_loadByte: spec_load 1 (Machine.loadByte (RiscvProgram := RVM)) Memory.loadByte;
    spec_loadHalf: spec_load 2 (Machine.loadHalf (RiscvProgram := RVM)) Memory.loadHalf;
    spec_loadWord: spec_load 4 (Machine.loadWord (RiscvProgram := RVM)) Memory.loadWord;
    spec_loadDouble: spec_load 8 (Machine.loadDouble (RiscvProgram := RVM)) Memory.loadDouble;

    spec_storeByte: spec_store 1 (Machine.storeByte (RiscvProgram := RVM)) Memory.storeByte;
    spec_storeHalf: spec_store 2 (Machine.storeHalf (RiscvProgram := RVM)) Memory.storeHalf;
    spec_storeWord: spec_store 4 (Machine.storeWord (RiscvProgram := RVM)) Memory.storeWord;
    spec_storeDouble: spec_store 8 (Machine.storeDouble (RiscvProgram := RVM)) Memory.storeDouble;

    spec_getPC: forall (initialL: MetricRiscvMachine) (post: word -> MetricRiscvMachine -> Prop),
        post initialL.(getPc) initialL ->
        mcomp_sat getPC initialL post;

    spec_setPC: forall initialL v (post: unit -> MetricRiscvMachine -> Prop),
        post tt (withNextPc v
                (updateMetrics (addMetricJumps 1)
                               initialL)) ->
        mcomp_sat (setPC v) initialL post;

    spec_endCycleNormal: forall (initialL: MetricRiscvMachine) (post: unit -> MetricRiscvMachine -> Prop),
        post tt (withPc     initialL.(getNextPc)
                (withNextPc (word.add initialL.(getNextPc) (word.of_Z 4))
                (updateMetrics (addMetricInstructions 1)
                               initialL))) ->
        mcomp_sat endCycleNormal initialL post;
  }.

End MetricPrimitives.
