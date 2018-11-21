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
  Context {Event: Set}.

  Local Notation RiscvMachineL := (RiscvMachine Register t Event).

  Context {M: Type -> Type}.
  Context {MM: Monad M}.
  Context {RVM: RiscvProgram M t}.
  Context {RVS: @RiscvState M t _ _ RVM}.

  Class AxiomaticRiscv :=  mkAxiomaticRiscv {

    (* Abstract predicate specifying when a monadic computation satisfies a
       postcondition when run on given initial machine *)
    mcomp_sat: M unit -> RiscvMachineL -> (RiscvMachineL -> Prop) -> Prop;

    go_getRegister: forall (initialL: RiscvMachineL) (x: Register) post (f: t -> M unit),
      valid_register x ->
      mcomp_sat (f (getReg initialL.(getRegs) x)) initialL post ->
      mcomp_sat (Bind (getRegister x) f) initialL post;

    go_getRegister0: forall (initialL: RiscvMachineL) post (f: t -> M unit),
      mcomp_sat (f (ZToReg 0)) initialL post ->
      mcomp_sat (Bind (getRegister Register0) f) initialL post;

    go_setRegister: forall initialL x v post (f: unit -> M unit),
      valid_register x ->
      mcomp_sat (f tt) (setRegs initialL (setReg initialL.(getRegs) x v)) post ->
      mcomp_sat (Bind (setRegister x v) f) initialL post;

(*    do_setRegister0: forall {A: Type} (v: t) (initialL: RiscvMachineL),
          setRegister Register0 v initialL = Return tt initialL;

      do_loadByte: forall {A: Type} (addr: t) (initialL: RiscvMachineL),
          loadByte addr initialL =
          Return (Memory.loadByte initialL.(machine).(machineMem) addr) initialL;

      do_loadHalf: forall {A: Type} (addr: t) (initialL: RiscvMachineL),
          loadHalf addr initialL =
          Return (Memory.loadHalf initialL.(machine).(machineMem) addr) initialL;

      do_loadWord: forall {A: Type} (addr: t) (initialL: RiscvMachineL),
          isMMIOAddr addr = false ->
          loadWord addr initialL =
          Return (Memory.loadWord initialL.(machine).(machineMem) addr) initialL;

      do_MMInput: forall {A: Type} (addr: t) (initialL: RiscvMachineL),
          isMMIOAddr addr = true ->
          loadWord addr initialL =
            (inp <- OStateNDOperations.arbitrary (word 32);
             m <- OStateNDOperations.get;
             OStateNDOperations.put
               (with_log ((EvInput (regToZ_unsigned addr) inp) :: m.(log)) m);;
             Return inp) initialL;

      do_loadDouble: forall {A: Type} (addr: t) (initialL: RiscvMachineL),
          loadDouble addr initialL =
          Return (Memory.loadDouble initialL.(machine).(machineMem) addr) initialL;

      do_storeByte: forall {A: Type} (addr: t) (v: word 8) (initialL: RiscvMachineL),
          storeByte addr v initialL =
          (Return tt) (with_machine
                         (with_machineMem
                            (Memory.storeByte initialL.(machine).(machineMem) addr v)
                            initialL.(machine))
                         initialL);

      do_storeHalf: forall {A: Type} (addr: t) (v: word 16) (initialL: RiscvMachineL),
          storeHalf addr v initialL =
          Return tt (with_machine
                       (with_machineMem
                          (Memory.storeHalf initialL.(machine).(machineMem) addr v)
                          initialL.(machine))
                       initialL);

      do_storeWord: forall {A: Type} (addr: t) (v: word 32) (initialL: RiscvMachineL),
          storeWord addr v initialL =
          Return tt (with_machine
                       (with_machineMem
                          (Memory.storeWord initialL.(machine).(machineMem) addr v)
                          initialL.(machine))
                       initialL);

      do_storeDouble: forall {A: Type} (addr: t) (v: word 64) (initialL: RiscvMachineL),
          storeDouble addr v initialL =
          Return tt (with_machine
                       (with_machineMem
                          (Memory.storeDouble initialL.(machine).(machineMem) addr v)
                          initialL.(machine))
                       initialL);

      do_getPC: forall {A: Type} (initialL: RiscvMachineL),
          getPC initialL =
          Return initialL.(machine).(core).(pc) initialL;

      do_setPC: forall {A: Type} (v: t) (initialL: RiscvMachineL),
          setPC v initialL =
          Return tt (with_machine (with_nextPC v initialL.(machine)) initialL);
*)
  }.

End Axiomatic.

Arguments AxiomaticRiscv t {_} {_} {_} Event M {_} {_}.
