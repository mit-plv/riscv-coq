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


(* Note: Register 0 is not considered valid because it cannot be written *)
Definition valid_register(r: Register): Prop := (0 < r < 32)%Z.

Section Primitives.

  Context {W: Words}.
  Context {RFF: RegisterFileFunctions Register word}.
  Context {Action: Type}.
  Context {mem: map.map word byte}.

  Local Notation RiscvMachineL := (RiscvMachine Register Action).

  Context {M: Type -> Type}.
  Context {MM: Monad M}.
  Context {RVM: RiscvProgram M word}.
  Context {RVS: @RiscvState M word _ _ RVM}.

  Class Primitives :=  {

    (* Abstract predicate specifying when a monadic computation satisfies a
       postcondition when run on given initial machine *)
    mcomp_sat: forall {A: Type}, M A -> RiscvMachineL -> (A -> RiscvMachineL -> Prop) -> Prop;

    (* Given an initial RiscvMachine state, an address, and a postcondition on
       (4-byte word input, final state), tells if this postcondition is a safe approximation
       of the behavior of the machine *)
    nonmem_loadWord_sat:  RiscvMachineL -> word -> (w32 -> RiscvMachineL -> Prop) -> Prop;

    (* Given an initial RiscvMachine state, an address, a 4-byte word to store,
       and a postcondition on final states, tells if this postcondition is a safe approximation
       of the behavior of the machine *)
    nonmem_storeWord_sat: RiscvMachineL -> word -> w32 -> (RiscvMachineL -> Prop) -> Prop;

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
        (valid_register x /\ post (getReg initialL.(getRegs) x) initialL \/
         x = Register0 /\ post (word.of_Z 0) initialL) <->
        mcomp_sat (getRegister x) initialL post;

    spec_setRegister: forall initialL x v (post: unit -> RiscvMachineL -> Prop),
      (valid_register x /\ post tt (setRegs initialL (setReg initialL.(getRegs) x v)) \/
       x = Register0 /\ post tt initialL) <->
      mcomp_sat (setRegister x v) initialL post;

    spec_loadWord: forall initialL addr (post: w32 -> RiscvMachineL -> Prop),
        (exists v: w32, Memory.loadWord initialL.(getMem) addr = Some v /\
                        post v initialL) \/
        (Memory.loadWord initialL.(getMem) addr = None /\
         nonmem_loadWord_sat initialL addr post) <->
        mcomp_sat (Program.loadWord (RiscvProgram := RVM) addr) initialL post;

    spec_storeWord: forall initialL addr v (post: unit -> RiscvMachineL -> Prop),
        (exists m',
            Memory.storeWord initialL.(getMem) addr v = Some m' /\
            post tt (withMem m' initialL)) \/
        (Memory.loadWord initialL.(getMem) addr = None /\
         nonmem_storeWord_sat initialL addr v (post tt)) <->
        mcomp_sat (Program.storeWord addr v) initialL post;

    spec_getPC: forall initialL (post: word -> RiscvMachineL -> Prop),
        post initialL.(getPc) initialL <->
        mcomp_sat getPC initialL post;

    spec_setPC: forall initialL v (post: unit -> RiscvMachineL -> Prop),
        post tt (withNextPc v initialL) <->
        mcomp_sat (setPC v) initialL post;

    spec_step: forall initialL (post: unit -> RiscvMachineL -> Prop),
        post tt (withNextPc (word.add initialL.(getNextPc) (word.of_Z 4))
                (withPc     initialL.(getNextPc)
                            initialL)) <->
        mcomp_sat step initialL post;
  }.

End Primitives.

Arguments Primitives {_} {_} Action {_} M {_} {_}.
