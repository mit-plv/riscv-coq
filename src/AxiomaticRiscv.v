Require Import Coq.ZArith.BinInt.
Require Import riscv.util.Monads.
Require Import riscv.Utility.
Require Import riscv.Decode.
Require Import riscv.Memory.
Require Import riscv.Program.
Require Import riscv.RiscvMachine.
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

  Local Notation RiscvMachine := (@RiscvMachine t Mem RF).

  Context {RVM: RiscvProgram (OState RiscvMachine) t}.
  
  (* assumes generic translate and raiseException functions *)
  Context {RVS: @RiscvState (OState RiscvMachine) t _ _ RVM}.  

  Class AxiomaticRiscv :=  mkAxiomaticRiscv {
      
      Bind_getRegister0: forall {A: Type} (f: t -> OState RiscvMachine A),
        Bind (getRegister Register0) f = f (ZToReg 0);
      
      Bind_getRegister: forall {A: Type} x (f: t -> OState RiscvMachine A)
                          (initialL: RiscvMachine),
          valid_register x ->
          (Bind (getRegister x) f) initialL =
          (f (getReg initialL.(core).(registers) x)) initialL;

      Bind_setRegister: forall {A: Type} x (v: t)
                          (f: unit -> OState RiscvMachine A) (initialL: RiscvMachine),
          valid_register x ->
          (Bind (setRegister x v) f) initialL =
          (f tt) (with_registers (setReg initialL.(core).(registers) x v) initialL);

      Bind_setRegister0: forall {A: Type} (v: t)
                           (f: unit -> OState RiscvMachine A) (initialL: RiscvMachine),
          (Bind (setRegister Register0 v) f) initialL =
          (f tt) initialL;

      Bind_loadByte: forall {A: Type} (addr: t) (f: word 8 -> OState RiscvMachine A)
                       (initialL: RiscvMachine),
          (Bind (loadByte addr) f) initialL =
          (f (Memory.loadByte initialL.(machineMem) addr)) initialL;

      Bind_loadHalf: forall {A: Type} (addr: t) (f: word 16 -> OState RiscvMachine A)
                       (initialL: RiscvMachine),
          (Bind (loadHalf addr) f) initialL =
          (f (Memory.loadHalf initialL.(machineMem) addr)) initialL;

      Bind_loadWord: forall {A: Type} (addr: t) (f: word 32 -> OState RiscvMachine A)
                       (initialL: RiscvMachine),
          (Bind (loadWord addr) f) initialL =
          (f (Memory.loadWord initialL.(machineMem) addr)) initialL;
      
      Bind_loadDouble: forall {A: Type} (addr: t) (f: word 64 -> OState RiscvMachine A)
                       (initialL: RiscvMachine),
          (Bind (loadDouble addr) f) initialL =
          (f (Memory.loadDouble initialL.(machineMem) addr)) initialL;

      Bind_storeByte: forall {A: Type} (addr: t) (v: word 8)
                        (f: unit -> OState RiscvMachine A) (initialL: RiscvMachine),
          (Bind (storeByte addr v) f) initialL =
          (f tt) (with_machineMem (Memory.storeByte initialL.(machineMem) addr v)
                                            initialL);

      Bind_storeHalf: forall {A: Type} (addr: t) (v: word 16)
                        (f: unit -> OState RiscvMachine A) (initialL: RiscvMachine),
          (Bind (storeHalf addr v) f) initialL =
          (f tt) (with_machineMem (Memory.storeHalf initialL.(machineMem) addr v)
                                            initialL);

      Bind_storeWord: forall {A: Type} (addr: t) (v: word 32)
                        (f: unit -> OState RiscvMachine A) (initialL: RiscvMachine),
          (Bind (storeWord addr v) f) initialL =
          (f tt) (with_machineMem (Memory.storeWord initialL.(machineMem) addr v)
                                            initialL);

      Bind_storeDouble: forall {A: Type} (addr: t) (v: word 64)
                        (f: unit -> OState RiscvMachine A) (initialL: RiscvMachine),
          (Bind (storeDouble addr v) f) initialL =
          (f tt) (with_machineMem (Memory.storeDouble initialL.(machineMem) addr v)
                                            initialL);

      Bind_getPC: forall {A: Type} (f: t -> OState RiscvMachine A) (initialL: RiscvMachine),
          (Bind getPC f) initialL =
          (f initialL.(core).(pc)) initialL;

      Bind_setPC: forall {A: Type} (v: t)
                    (f: unit -> OState RiscvMachine A) (initialL: RiscvMachine),
          (Bind (setPC v) f) initialL =
          (f tt) (with_nextPC v initialL);
      
      Bind_step: forall {A: Type} (f: unit -> OState RiscvMachine A) m,
          (Bind step f) m =
          (f tt) (with_nextPC (add m.(core).(nextPC) (ZToReg 4)) (with_pc m.(core).(nextPC) m));

      execState_step: forall m,
          step m = (Some tt, with_nextPC (add m.(core).(nextPC) (ZToReg 4)) (with_pc m.(core).(nextPC) m));
      
      execState_Return: forall {S A} (s: S) (a: A),
          (Return a) s = (Some a, s);

  }.

End AxiomaticRiscv.
