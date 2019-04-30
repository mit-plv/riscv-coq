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

  Context {W: Words}.
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

    (* Given an address, an initial RiscvMachine state, and a postcondition on
       (input, final state), tells if this postcondition characterizes the
       behavior of the machine *)
    nonmem_loadByte_sat  :  word -> Machine -> (w8  -> Machine -> Prop) -> Prop;
    nonmem_loadHalf_sat  :  word -> Machine -> (w16 -> Machine -> Prop) -> Prop;
    nonmem_loadWord_sat  :  word -> Machine -> (w32 -> Machine -> Prop) -> Prop;
    nonmem_loadDouble_sat:  word -> Machine -> (w64 -> Machine -> Prop) -> Prop;

    (* Given an address, a value to write, an initial RiscvMachine state,
       and a postcondition on final states, tells if this postcondition characterizes the
       behavior of the machine *)
    nonmem_storeByte_sat  : word -> w8  -> Machine -> (unit -> Machine -> Prop) -> Prop;
    nonmem_storeHalf_sat  : word -> w16 -> Machine -> (unit -> Machine -> Prop) -> Prop;
    nonmem_storeWord_sat  : word -> w32 -> Machine -> (unit -> Machine -> Prop) -> Prop;
    nonmem_storeDouble_sat: word -> w64 -> Machine -> (unit -> Machine -> Prop) -> Prop;
  }.

  Context {RVM: RiscvProgram M word}.
  Context {RVS: @riscv.Spec.Machine.RiscvMachine M word _ _ RVM}.

  Definition spec_load{p: PrimitivesParams RiscvMachine}(V: Type)
             (riscv_load: SourceType -> word -> M V)
             (mem_load: mem -> word -> option V)
             (nonmem_load: word -> RiscvMachine -> (V -> RiscvMachine -> Prop) -> Prop)
             : Prop :=
    forall initialL addr (kind: SourceType) (post: V -> RiscvMachine -> Prop),
        (exists v: V, mem_load initialL.(getMem) addr = Some v /\ post v initialL) \/
        (mem_load initialL.(getMem) addr = None /\ nonmem_load addr initialL post) <->
        mcomp_sat (riscv_load kind addr) initialL post.

  Definition spec_store{p: PrimitivesParams RiscvMachine}(V: Type)
             (riscv_store: SourceType -> word -> V -> M unit)
             (mem_store: mem -> word -> V -> option mem)
             (nonmem_store: word -> V -> RiscvMachine -> (unit -> RiscvMachine -> Prop) -> Prop)
             : Prop :=
    forall initialL addr v (kind: SourceType) (post: unit -> RiscvMachine -> Prop),
      (exists m', mem_store initialL.(getMem) addr v = Some m' /\ post tt (withMem m' initialL)) \/
      (mem_store initialL.(getMem) addr v = None /\ nonmem_store addr v initialL post) <->
      mcomp_sat (riscv_store kind addr v) initialL post.

  (* primitives_params is a paramater rather than a field because Primitives lives in Prop and
     is opaque, but the fields of primitives_params need to be visible *)
  Class Primitives(primitives_params: PrimitivesParams RiscvMachine): Prop := {

    spec_Bind{A B: Type}: forall (initialL: RiscvMachine) (post: B -> RiscvMachine -> Prop)
                                 (m: M A) (f : A -> M B),
        (exists mid: A -> RiscvMachine -> Prop,
            mcomp_sat m initialL mid /\
            (forall a middle, mid a middle -> mcomp_sat (f a) middle post)) <->
        mcomp_sat (Bind m f) initialL post;

    spec_Return{A: Type}: forall (initialL: RiscvMachine)
                                 (post: A -> RiscvMachine -> Prop) (a: A),
        post a initialL <->
        mcomp_sat (Return a) initialL post;

    spec_getRegister: forall (initialL: RiscvMachine) (x: Register)
                             (post: word -> RiscvMachine -> Prop),
        (valid_register x /\
         match map.get initialL.(getRegs) x with
         | Some v => post v initialL
         | None => forall v, is_initial_register_value v -> post v initialL
         end) \/
        (x = Register0 /\ post (word.of_Z 0) initialL) <->
        mcomp_sat (getRegister x) initialL post;

    spec_setRegister: forall initialL x v (post: unit -> RiscvMachine -> Prop),
      (valid_register x /\ post tt (withRegs (map.put initialL.(getRegs) x v) initialL) \/
       x = Register0 /\ post tt initialL) <->
      mcomp_sat (setRegister x v) initialL post;

    spec_loadByte: spec_load w8 (Machine.loadByte (RiscvProgram := RVM))
                                Memory.loadByte
                                nonmem_loadByte_sat;

    spec_loadHalf: spec_load w16 (Machine.loadHalf (RiscvProgram := RVM))
                                 Memory.loadHalf
                                 nonmem_loadHalf_sat;

    spec_loadWord: spec_load w32 (Machine.loadWord (RiscvProgram := RVM))
                                 Memory.loadWord
                                 nonmem_loadWord_sat;

    spec_loadDouble: spec_load w64 (Machine.loadDouble (RiscvProgram := RVM))
                                   Memory.loadDouble
                                   nonmem_loadDouble_sat;

    spec_storeByte: spec_store w8 (Machine.storeByte (RiscvProgram := RVM))
                                  Memory.storeByte
                                  nonmem_storeByte_sat;

    spec_storeHalf: spec_store w16 (Machine.storeHalf (RiscvProgram := RVM))
                                    Memory.storeHalf
                                    nonmem_storeHalf_sat;

    spec_storeWord: spec_store w32 (Machine.storeWord (RiscvProgram := RVM))
                                    Memory.storeWord
                                    nonmem_storeWord_sat;

    spec_storeDouble: spec_store w64 (Machine.storeDouble (RiscvProgram := RVM))
                                     Memory.storeDouble
                                     nonmem_storeDouble_sat;

    spec_getPC: forall initialL (post: word -> RiscvMachine -> Prop),
        post initialL.(getPc) initialL <->
        mcomp_sat getPC initialL post;

    spec_setPC: forall initialL v (post: unit -> RiscvMachine -> Prop),
        post tt (withNextPc v initialL) <->
        mcomp_sat (setPC v) initialL post;

    spec_step: forall initialL (post: unit -> RiscvMachine -> Prop),
        post tt (withNextPc (word.add initialL.(getNextPc) (word.of_Z 4))
                (withPc     initialL.(getNextPc)
                            initialL)) <->
        mcomp_sat step initialL post;
  }.

End Primitives.

Arguments PrimitivesParams {_} M Machine.
