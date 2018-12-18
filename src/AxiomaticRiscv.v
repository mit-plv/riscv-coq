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

Section Axiomatic.

  Context {W: Words}.
  Context {RFF: RegisterFileFunctions Register word}.
  Context {Action: Type}.
  Context {mem: map.map word byte}.

  Local Notation RiscvMachineL := (RiscvMachine Register Action).

  Context {M: Type -> Type}.
  Context {MM: Monad M}.
  Context {RVM: RiscvProgram M word}.
  Context {RVS: @RiscvState M word _ _ RVM}.

  Class AxiomaticRiscv :=  mkAxiomaticRiscv {

    (* Abstract predicate specifying when a monadic computation satisfies a
       postcondition when run on given initial machine *)
    mcomp_sat: forall {A: Type}, M A -> RiscvMachineL -> (A -> RiscvMachineL -> Prop) -> Prop;

    go_getRegister: forall (initialL: RiscvMachineL) (x: Register)
                             (post: word -> RiscvMachineL -> Prop),
        valid_register x ->
        post (getReg initialL.(getRegs) x) initialL ->
        mcomp_sat (getRegister x) initialL post;

    go_getRegister0: forall (initialL: RiscvMachineL) (post: word -> RiscvMachineL -> Prop),
        post (word.of_Z 0) initialL ->
        mcomp_sat (getRegister Register0) initialL post;

    go_setRegister0: forall initialL v (post: unit -> RiscvMachineL -> Prop),
      post tt initialL ->
      mcomp_sat (setRegister Register0 v) initialL post;

    go_setRegister: forall initialL x v (post: unit -> RiscvMachineL -> Prop),
      valid_register x ->
      post tt (setRegs initialL (setReg initialL.(getRegs) x v)) ->
      mcomp_sat (setRegister x v) initialL post;

    go_loadWord: forall initialL addr (v: w32) (post: w32 -> RiscvMachineL -> Prop),
        Memory.loadWord initialL.(getMem) addr = Some v ->
        post v initialL ->
        mcomp_sat (Program.loadWord (RiscvProgram := RVM) addr) initialL post;

    go_storeWord: forall initialL addr v m' (post: unit -> RiscvMachineL -> Prop),
        Memory.storeWord initialL.(getMem) addr v = Some m' ->
        post tt (withMem m' initialL) ->
        mcomp_sat (Program.storeWord addr v) initialL post;

    go_getPC: forall initialL (post: word -> RiscvMachineL -> Prop),
        post initialL.(getPc) initialL ->
        mcomp_sat getPC initialL post;

    go_setPC: forall initialL v (post: unit -> RiscvMachineL -> Prop),
        post tt (withNextPc v initialL) ->
        mcomp_sat (setPC v) initialL post;

    go_step: forall initialL (post: unit -> RiscvMachineL -> Prop),
        post tt (withNextPc (word.add initialL.(getNextPc) (word.of_Z 4))
                            (withPc (word.add initialL.(getPc) (word.of_Z 4))
                                    initialL)) ->
        mcomp_sat step initialL post;
  }.

End Axiomatic.

Arguments AxiomaticRiscv {_} {_} Action {_} M {_} {_}.
