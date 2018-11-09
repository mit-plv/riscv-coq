Require Import Coq.Lists.List.
Require Import Coq.ZArith.BinInt.
Require Import riscv.util.Monads.
Require Import riscv.Utility.
Require Import riscv.Decode.
Require Import riscv.Memory.
Require Import riscv.Program.
Require Import riscv.RiscvMachine.
Require Import riscv.RiscvMachineL.
Require Import riscv.util.BitWidths.


Set Implicit Arguments.

(* Note: Register 0 is not considered valid because it cannot be written *)
Definition valid_register(r: Register): Prop := (0 < r < 32)%Z.

Section AxiomaticRiscv.

  Context {t: Set}.
  Context {MW: MachineWidth t}.
  Context {RF: Type}.
  Context {RFI: RegisterFile RF Register t}.

  Context {Mem: Set}.
  Context {MemIsMem: Memory Mem t}.

  Local Notation RiscvMachineL := (@RiscvMachineL t Mem RF).

  Context {RVM: RiscvProgram (OStateND RiscvMachineL) t}.

  (* assumes generic translate and raiseException functions *)
  Context {RVS: @RiscvState (OStateND RiscvMachineL) t _ _ RVM}.

  Class AxiomaticRiscv :=  mkAxiomaticRiscv {

      do_getRegister0: forall {A: Type},
        getRegister Register0 = Return (ZToReg 0);

      do_getRegister: forall {A: Type} x (initialL: RiscvMachineL),
          valid_register x ->
          getRegister x initialL =
          Return (getReg initialL.(machine).(core).(registers) x) initialL;

      do_setRegister: forall {A: Type} x (v: t) (initialL: RiscvMachineL),
          valid_register x ->
          setRegister x v initialL =
          Return tt (with_machine
                       (with_registers
                          (setReg initialL.(machine).(core).(registers) x v)
                          initialL.(machine))
                       initialL);

      do_setRegister0: forall {A: Type} (v: t) (initialL: RiscvMachineL),
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

      (*
      do_step: forall {A: Type} (f: unit -> OStateND RiscvMachineL A) m,
          step f m =
          (f tt) (with_nextPC (add m.(core).(nextPC) (ZToReg 4)) (with_pc m.(core).(nextPC) m));

      execState_step: forall m,
          step m = (Some tt, with_nextPC (add m.(core).(nextPC) (ZToReg 4)) (with_pc m.(core).(nextPC) m));

      execState_Return: forall {S A} (s: S) (a: A),
          (Return a) s = (Some a, s);
      *)
  }.

End AxiomaticRiscv.
