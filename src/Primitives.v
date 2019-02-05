Require Import Coq.Lists.List.
Require Import Coq.ZArith.BinInt.
Require Import coqutil.Map.Interface.
Require Import riscv.util.Monads.
Require Import riscv.Utility.
Require Import riscv.Decode.
Require Import riscv.Memory.
Require Import riscv.Program.
Require Import riscv.RiscvMachine.
Require Import riscv.MkMachineWidth.
Require Import riscv.MetricLogging.


(* Note: Register 0 is not considered valid because it cannot be written *)
Definition valid_register(r: Register): Prop := (0 < r < 32)%Z.

Section Primitives.

  Context {W: Words}.
  Context {Registers: map.map Register word}.
  Context {Action: Type}.
  Context {mem: map.map word byte}.

  Local Notation RiscvMachineL := (RiscvMachine Register Action).

  Context {M: Type -> Type}.
  Context {MM: Monad M}.

  Class PrimitivesParams := {
    (* Abstract predicate specifying when a monadic computation satisfies a
       postcondition when run on given initial machine *)
    mcomp_sat: forall {A: Type}, M A -> RiscvMachineL -> (A -> RiscvMachineL -> Prop) -> Prop;

    (* Tells whether the given value can be found in an uninitialized register.
       On instances supporting non-determinism, it returns True for all values.
       On instances without non-determinism, it only accepts a default value, eg 0 *)
    is_initial_register_value: word -> Prop;

    (* Given an initial RiscvMachine state, an address, and a postcondition on
       (input, final state), tells if this postcondition characterizes the
       behavior of the machine *)
    nonmem_loadByte_sat  :  RiscvMachineL -> word -> (w8  -> RiscvMachineL -> Prop) -> Prop;
    nonmem_loadHalf_sat  :  RiscvMachineL -> word -> (w16 -> RiscvMachineL -> Prop) -> Prop;
    nonmem_loadWord_sat  :  RiscvMachineL -> word -> (w32 -> RiscvMachineL -> Prop) -> Prop;
    nonmem_loadDouble_sat:  RiscvMachineL -> word -> (w64 -> RiscvMachineL -> Prop) -> Prop;

    (* Given an initial RiscvMachine state, an address, a value to write,
       and a postcondition on final states, tells if this postcondition characterizes the
       behavior of the machine *)
    nonmem_storeByte_sat  : RiscvMachineL -> word -> w8  -> (RiscvMachineL -> Prop) -> Prop;
    nonmem_storeHalf_sat  : RiscvMachineL -> word -> w16 -> (RiscvMachineL -> Prop) -> Prop;
    nonmem_storeWord_sat  : RiscvMachineL -> word -> w32 -> (RiscvMachineL -> Prop) -> Prop;
    nonmem_storeDouble_sat: RiscvMachineL -> word -> w64 -> (RiscvMachineL -> Prop) -> Prop;
  }.

  Context {RVM: RiscvProgram M word}.
  Context {RVS: @RiscvState M word _ _ RVM}.

  Definition spec_load{p: PrimitivesParams}(V: Type)
             (riscv_load: word -> M V)
             (mem_load: mem -> word -> option V)
             (nonmem_load: RiscvMachineL -> word -> (V  -> RiscvMachineL -> Prop) -> Prop)
             : Prop :=
    forall initialL addr (post: V -> RiscvMachineL -> Prop),
        let initialLMetrics := updateMetrics (addMetricLoads 1) initialL in
        (exists v: V, mem_load initialL.(getMem) addr = Some v /\ post v initialLMetrics) \/
        (mem_load initialL.(getMem) addr = None /\ nonmem_load initialL addr post) <->
        mcomp_sat (riscv_load addr) initialL post.

  Definition spec_store{p: PrimitivesParams}(V: Type)
             (riscv_store: word -> V -> M unit)
             (mem_store: mem -> word -> V -> option mem)
             (nonmem_store: RiscvMachineL -> word -> V -> (RiscvMachineL -> Prop) -> Prop)
             : Prop :=
    forall initialL addr v (post: unit -> RiscvMachineL -> Prop),
      let initialLMetrics := updateMetrics (addMetricStores 1) initialL in
      (exists m', mem_store initialL.(getMem) addr v = Some m' /\ post tt (withMem m' initialLMetrics)) \/
      (mem_store initialL.(getMem) addr v = None /\ nonmem_store initialL addr v (post tt)) <->
      mcomp_sat (riscv_store addr v) initialL post.

  Class Primitives :=  {
    primitives_params :> PrimitivesParams;

    spec_Bind{A B: Type}: forall (initialL: RiscvMachineL) (post: B -> RiscvMachineL -> Prop)
                                 (m: M A) (f : A -> M B),
        (exists mid: A -> RiscvMachineL -> Prop,
            mcomp_sat m initialL mid /\
            (forall a middle, mid a middle -> mcomp_sat (f a) middle post)) <->
        mcomp_sat (Bind m f) initialL post;

    spec_Return{A: Type}: forall (initialL: RiscvMachineL)
                                 (post: A -> RiscvMachineL -> Prop) (a: A),
        post a initialL <->
        mcomp_sat (Return a) initialL post;

    spec_getRegister: forall (initialL: RiscvMachineL) (x: Register)
                             (post: word -> RiscvMachineL -> Prop),
        (valid_register x /\
         match map.get initialL.(getRegs) x with
         | Some v => post v initialL
         | None => forall v, is_initial_register_value v -> post v initialL
         end) \/
        (x = Register0 /\ post (word.of_Z 0) initialL) <->
        mcomp_sat (getRegister x) initialL post;

    spec_setRegister: forall initialL x v (post: unit -> RiscvMachineL -> Prop),
      (valid_register x /\ post tt (withRegs (map.put initialL.(getRegs) x v) initialL) \/
       x = Register0 /\ post tt initialL) <->
      mcomp_sat (setRegister x v) initialL post;

    spec_loadByte: spec_load w8 (Program.loadByte (RiscvProgram := RVM))
                                Memory.loadByte
                                nonmem_loadByte_sat;

    spec_loadHalf: spec_load w16 (Program.loadHalf (RiscvProgram := RVM))
                                 Memory.loadHalf
                                 nonmem_loadHalf_sat;

    spec_loadWord: spec_load w32 (Program.loadWord (RiscvProgram := RVM))
                                 Memory.loadWord
                                 nonmem_loadWord_sat;

    spec_loadDouble: spec_load w64 (Program.loadDouble (RiscvProgram := RVM))
                                   Memory.loadDouble
                                   nonmem_loadDouble_sat;

    spec_storeByte: spec_store w8 (Program.storeByte (RiscvProgram := RVM))
                                  Memory.storeByte
                                  nonmem_storeByte_sat;

    spec_storeHalf: spec_store w16 (Program.storeHalf (RiscvProgram := RVM))
                                    Memory.storeHalf
                                    nonmem_storeHalf_sat;

    spec_storeWord: spec_store w32 (Program.storeWord (RiscvProgram := RVM))
                                    Memory.storeWord
                                    nonmem_storeWord_sat;

    spec_storeDouble: spec_store w64 (Program.storeDouble (RiscvProgram := RVM))
                                     Memory.storeDouble
                                     nonmem_storeDouble_sat;

    spec_getPC: forall initialL (post: word -> RiscvMachineL -> Prop),
        post initialL.(getPc) initialL <->
        mcomp_sat getPC initialL post;

    spec_setPC: forall initialL v (post: unit -> RiscvMachineL -> Prop),
        post tt (withNextPc v
                (updateMetrics (addMetricJumps 1)
                               initialL)) <->
        mcomp_sat (setPC v) initialL post;

    spec_step: forall initialL (post: unit -> RiscvMachineL -> Prop),
        post tt (withNextPc (word.add initialL.(getNextPc) (word.of_Z 4))
                (withPc     initialL.(getNextPc)
                (updateMetrics (addMetricInstructions 1)
                               initialL))) <->
        mcomp_sat step initialL post;
  }.

End Primitives.

Arguments PrimitivesParams {_} {_} Action {_} M.
Arguments Primitives {_} {_} Action {_} M {_} {_}.
