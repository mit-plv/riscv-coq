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
    mcomp_sat: M unit -> RiscvMachineL -> (RiscvMachineL -> Prop) -> Prop;

    (* Note: These lemmas could be simplified by not wrapping each operation inside
       a Bind, but then the postcondition would have to take a return value as an
       additional input, and before applying these lemmas in the compiler correctness
       proof (where we always have a Bind), we'd have to split up the Bind *)

    go_getRegister: forall (initialL: RiscvMachineL) (x: Register) post (f: word -> M unit),
      valid_register x ->
      mcomp_sat (f (getReg initialL.(getRegs) x)) initialL post ->
      mcomp_sat (Bind (getRegister x) f) initialL post;

    go_getRegister0: forall (initialL: RiscvMachineL) post (f: word -> M unit),
      mcomp_sat (f (ZToReg 0)) initialL post ->
      mcomp_sat (Bind (getRegister Register0) f) initialL post;

    go_setRegister0: forall initialL v post (f: unit -> M unit),
      mcomp_sat (f tt) initialL post ->
      mcomp_sat (Bind (setRegister Register0 v) f) initialL post;

    go_setRegister: forall initialL x v post (f: unit -> M unit),
      valid_register x ->
      mcomp_sat (f tt) (setRegs initialL (setReg initialL.(getRegs) x v)) post ->
      mcomp_sat (Bind (setRegister x v) f) initialL post;

    go_loadWord: forall initialL addr (v: w32) (f: w32 -> M unit) (post: RiscvMachineL -> Prop),
        Memory.loadWord initialL.(getMem) addr = Some v ->
        mcomp_sat (f v) initialL post ->
        mcomp_sat (Bind (Program.loadWord addr) f) initialL post;

    go_storeWord: forall initialL addr v m' post (f: unit -> M unit),
        Memory.storeWord initialL.(getMem) addr v = Some m' ->
        mcomp_sat (f tt) (withMem m' initialL) post ->
        mcomp_sat (Bind (Program.storeWord addr v) f) initialL post;

    go_getPC: forall initialL f (post: RiscvMachineL -> Prop),
        mcomp_sat (f initialL.(getPc)) initialL post ->
        mcomp_sat (Bind getPC f) initialL post;

    go_setPC: forall initialL v post (f: unit -> M unit),
        mcomp_sat (f tt) (setNextPc initialL v) post ->
        mcomp_sat (Bind (setPC v) f) initialL post;

    go_step: forall initialL (post: RiscvMachineL -> Prop),
        post (withNextPc (word.add initialL.(getNextPc) (word.of_Z 4))
                         (withPc initialL.(getNextPc) initialL)) ->
        mcomp_sat step initialL post;

  }.

End Axiomatic.

Arguments AxiomaticRiscv {_} {_} Action {_} M {_} {_}.
