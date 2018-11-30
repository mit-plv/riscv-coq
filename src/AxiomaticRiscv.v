Require Import Coq.Lists.List.
Require Import Coq.ZArith.BinInt.
Require Import riscv.util.Monads.
Require Import riscv.Utility.
Require Import riscv.Decode.
Require Import riscv.Memory.
Require Import riscv.Program.
Require Import riscv.RiscvMachine.
Require Import riscv.util.BitWidths.


(* Note: Register 0 is not considered valid because it cannot be written *)
Definition valid_register(r: Register): Prop := (0 < r < 32)%Z.

Section Axiomatic.

  Context {t: Set}.
  Context {MW: MachineWidth t}.
  Context {RFF: RegisterFileFunctions Register t}.
  Context {MF: MemoryFunctions t}.
  Context {Action: Set}.

  Local Notation RiscvMachineL := (RiscvMachine Register t Action).

  Context {M: Type -> Type}.
  Context {MM: Monad M}.
  Context {RVM: RiscvProgram M t}.
  Context {RVS: @RiscvState M t _ _ RVM}.

  Class AxiomaticRiscv :=  mkAxiomaticRiscv {

    (* Abstract predicate specifying when a monadic computation satisfies a
       postcondition when run on given initial machine *)
    mcomp_sat: M unit -> RiscvMachineL -> (RiscvMachineL -> Prop) -> Prop;

    (* Note: These lemmas could be simplified by not wrapping each operation inside
       a Bind, but then the postcondition would have to take a return value as an
       additional input, and before applying these lemmas in the compiler correctness
       proof (where we always have a Bind), we'd have to split up the Bind *)

    go_getRegister: forall (initialL: RiscvMachineL) (x: Register) post (f: t -> M unit),
      valid_register x ->
      mcomp_sat (f (getReg initialL.(getRegs) x)) initialL post ->
      mcomp_sat (Bind (getRegister x) f) initialL post;

    go_getRegister0: forall (initialL: RiscvMachineL) post (f: t -> M unit),
      mcomp_sat (f (ZToReg 0)) initialL post ->
      mcomp_sat (Bind (getRegister Register0) f) initialL post;

    go_setRegister0: forall initialL v post (f: unit -> M unit),
      mcomp_sat (f tt) initialL post ->
      mcomp_sat (Bind (setRegister Register0 v) f) initialL post;

    go_setRegister: forall initialL x v post (f: unit -> M unit),
      valid_register x ->
      mcomp_sat (f tt) (setRegs initialL (setReg initialL.(getRegs) x v)) post ->
      mcomp_sat (Bind (setRegister x v) f) initialL post;

    go_loadWord: forall initialL addr (f: word 32 -> M unit) (post: RiscvMachineL -> Prop),
        initialL.(isMem) addr = true ->
        mcomp_sat (f (Memory.loadWord initialL.(getMem) addr)) initialL post ->
        mcomp_sat (Bind (Program.loadWord addr) f) initialL post;

    go_storeWord: forall initialL addr v post (f: unit -> M unit),
        initialL.(isMem) addr = true ->
        mcomp_sat (f tt) (withMem (Memory.storeWord initialL.(getMem) addr v) initialL) post ->
        mcomp_sat (Bind (Program.storeWord addr v) f) initialL post;

    (* Physical memory is not that simple!

    go_loadWord: forall initialL addr (f: word 32 -> M unit) (post: RiscvMachineL -> Prop),
        in_range addr 4 0 initialL.(getMem).(memSize) ->
        mcomp_sat (f (Memory.loadWord initialL.(getMem) addr)) initialL post ->
        mcomp_sat (Bind (Program.loadWord addr) f) initialL post;

    go_storeWord: forall initialL addr v post (f: unit -> M unit),
        in_range addr 4 0 initialL.(getMem).(memSize) ->
        mcomp_sat (f tt) (setMem initialL (Memory.storeWord initialL.(getMem) addr v)) post ->
        mcomp_sat (Bind (Program.storeWord addr v) f) initialL post;
    *)

    (* These don't hardcode the implementation of isPhysicalMemAddr, so it's more flexible,
       but harder to use:

    go_loadWord: forall initialL addr (f: word 32 -> M unit) (post: RiscvMachineL -> Prop),
        (forall undefBehavior: M unit,
            mcomp_sat (Bind (isPhysicalMemAddr addr)
                            (fun b => if b
                                      then f (Memory.loadWord initialL.(getMem) addr)
                                      else undefBehavior))
                      initialL post) ->
        mcomp_sat (Bind (Program.loadWord addr) f) initialL post;

    go_storeWord: forall initialL addr v post (f: unit -> M unit),
        (forall undefBehavior: M unit,
            mcomp_sat (Bind (isPhysicalMemAddr addr)
                            (fun b => if b then (f tt) else undefBehavior))
                      (setMem initialL (Memory.storeWord initialL.(getMem) addr v))
                      post) ->
        mcomp_sat (Bind (Program.storeWord addr v) f) initialL post;
    *)

    go_getPC: forall initialL f (post: RiscvMachineL -> Prop),
        mcomp_sat (f initialL.(getPc)) initialL post ->
        mcomp_sat (Bind getPC f) initialL post;

    go_setPC: forall initialL v post (f: unit -> M unit),
        mcomp_sat (f tt) (setNextPc initialL v) post ->
        mcomp_sat (Bind (setPC v) f) initialL post;

    go_step: forall initialL (post: RiscvMachineL -> Prop),
        mcomp_sat
          (Return tt)
          (setNextPc (setPc initialL
                            initialL.(getNextPc))
                     (add initialL.(getNextPc) (ZToReg 4)))
          post ->
        mcomp_sat step initialL post;

  }.

End Axiomatic.

Arguments AxiomaticRiscv t {_} {_} {_} Action M {_} {_}.
