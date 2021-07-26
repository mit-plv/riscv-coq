Require Import Coq.Lists.List.
Require Import Coq.ZArith.BinInt.
Require Import coqutil.Map.Interface.
Require Import riscv.Utility.Monads.
Require Import riscv.Utility.Utility.
Require Import riscv.Spec.Decode.
Require Import riscv.Platform.Memory.
Require Import riscv.Spec.Machine.
Require Import riscv.Platform.RiscvMachine.
Require Import riscv.Utility.MkMachineWidth.


(* Note: Register 0 is not considered valid because it cannot be written *)
Definition valid_register(r: Register): Prop := (0 < r < 32)%Z.

Section Primitives.

  Context {width: Z} {BW: Bitwidth width} {word: word width} {word_ok: word.ok word}.
  Context {Registers: map.map Register word}.
  Context {mem: map.map word byte}.

  Context {M: Type -> Type}.
  Context {MM: Monad M}.

  Class PrimitivesParams(Machine: Type) := {
    (* Abstract predicate specifying when a monadic computation satisfies a
       postcondition when run on given initial machine *)
    mcomp_sat: forall {A: Type}, M A -> Machine -> (A -> Machine -> Prop) -> Prop;

    (* Tells whether the given value can be found in an uninitialized register.
       On instances supporting non-determinism, it returns True for all values.
       On instances without non-determinism, it only accepts a default value, eg 0 *)
    is_initial_register_value: word -> Prop;

    (* tells what happens if an n-byte read at a non-memory address is performed *)
    nonmem_load : forall (n: nat), SourceType -> word -> RiscvMachine -> (HList.tuple byte n -> RiscvMachine -> Prop) -> Prop;

    (* tells what happens if an n-byte write at a non-memory address is performed *)
    nonmem_store: forall (n: nat), SourceType -> word -> HList.tuple byte n -> RiscvMachine -> (RiscvMachine -> Prop) -> Prop;

    (* an invariant which is preserved by each primitive operation
       TODO it might also be useful to have invariants which are only preserved by whole
       instructions, such as eg the concrete nextPc = pc + 4 *)
    valid_machine: Machine -> Prop;
  }.

  Class mcomp_sat_spec{Machine: Type}(p: PrimitivesParams Machine): Prop := {
    spec_Bind{A B: Type}: forall (initialL: Machine) (post: B -> Machine -> Prop)
                                 (m: M A) (f : A -> M B),
        (exists mid: A -> Machine -> Prop,
            mcomp_sat m initialL mid /\
            (forall a middle, mid a middle -> mcomp_sat (f a) middle post)) <->
        mcomp_sat (Bind m f) initialL post;

    spec_Return{A: Type}: forall (initialL: Machine)
                                 (post: A -> Machine -> Prop) (a: A),
        post a initialL <->
        mcomp_sat (Return a) initialL post;
  }.

  (* monadic computations used for specifying the behavior of RiscvMachines should be "sane"
     in the sense that we never step to the empty set (that's not absence of failure, since
     failure is modeled as "steps to no set at all"), and that the trace of events is
     append-only, and that valid_machine is preserved *)
  Definition mcomp_sane{p: PrimitivesParams RiscvMachine}{A: Type}(comp: M A): Prop :=
    forall (st: RiscvMachine) (post: A -> RiscvMachine -> Prop),
      valid_machine st ->
      mcomp_sat comp st post ->
      (exists a st', post a st' /\ valid_machine st') /\
      (mcomp_sat comp st (fun a st' =>
         (post a st' /\ exists diff, st'.(getLog) = diff ++ st.(getLog)) /\ valid_machine st')).

  Context {RVM: RiscvProgram M word}.
  Context {RVS: @riscv.Spec.Machine.RiscvMachine M word _ _ RVM}.

  Class PrimitivesSane(p: PrimitivesParams RiscvMachine): Prop := {
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

  Definition spec_load{p: PrimitivesParams RiscvMachine}(n: nat)
             (riscv_load: SourceType -> word -> M (HList.tuple byte n))
             (mem_load: mem -> word -> option (HList.tuple byte n))
    : Prop :=
    forall initialL addr (kind: SourceType) (post: HList.tuple byte n -> RiscvMachine -> Prop),
      (kind = Fetch -> isXAddr4 addr initialL.(getXAddrs)) /\
      ((exists v, mem_load initialL.(getMem) addr = Some v /\
                  post v initialL) \/
       (mem_load initialL.(getMem) addr = None /\
        nonmem_load n kind addr initialL post)) ->
      mcomp_sat (riscv_load kind addr) initialL post.

  (* After an address has been written, we make it non-executable, to make sure a processor
     with an instruction cache won't execute a stale instruction. *)
  Fixpoint invalidateWrittenXAddrs(nBytes: nat)(addr: word)(xAddrs: XAddrs): XAddrs :=
    match nBytes with
    | O => xAddrs
    | S n => removeXAddr addr (invalidateWrittenXAddrs n (word.add addr (word.of_Z 1)) xAddrs)
    end.

  Definition spec_store{p: PrimitivesParams RiscvMachine}(n: nat)
             (riscv_store: SourceType -> word -> HList.tuple byte n -> M unit)
             (mem_store: mem -> word -> HList.tuple byte n -> option mem)
             : Prop :=
    forall initialL addr v (kind: SourceType) (post: unit -> RiscvMachine -> Prop),
      (exists m', mem_store initialL.(getMem) addr v = Some m' /\
                  post tt (withXAddrs (invalidateWrittenXAddrs n addr initialL.(getXAddrs))
                          (withMem m' initialL))) \/
      (mem_store initialL.(getMem) addr v = None /\
       nonmem_store n kind addr v initialL (post tt)) ->
      mcomp_sat (riscv_store kind addr v) initialL post.

  (* primitives_params is a paramater rather than a field because Primitives lives in Prop and
     is opaque, but the fields of primitives_params need to be visible *)
  Class Primitives(primitives_params: PrimitivesParams RiscvMachine): Prop := {
    mcomp_sat_ok :> mcomp_sat_spec primitives_params;
    primitives_sane :> PrimitivesSane primitives_params;

    spec_getRegister: forall (initialL: RiscvMachine) (x: Register)
                             (post: word -> RiscvMachine -> Prop),
        (valid_register x /\
         match map.get initialL.(getRegs) x with
         | Some v => post v initialL
         | None => forall v, is_initial_register_value v -> post v initialL
         end) \/
        (x = Register0 /\ post (word.of_Z 0) initialL) ->
        mcomp_sat (getRegister x) initialL post;

    spec_setRegister: forall initialL x v (post: unit -> RiscvMachine -> Prop),
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

    spec_getPC: forall initialL (post: word -> RiscvMachine -> Prop),
        post initialL.(getPc) initialL ->
        mcomp_sat getPC initialL post;

    spec_setPC: forall initialL v (post: unit -> RiscvMachine -> Prop),
        post tt (withNextPc v initialL) ->
        mcomp_sat (setPC v) initialL post;

    spec_endCycleNormal: forall initialL (post: unit -> RiscvMachine -> Prop),
        post tt (withPc     initialL.(getNextPc)
                (withNextPc (word.add initialL.(getNextPc) (word.of_Z 4))
                            initialL)) ->
        mcomp_sat endCycleNormal initialL post;
  }.

End Primitives.

Arguments PrimitivesParams {_ _ _ _ _} M Machine.
