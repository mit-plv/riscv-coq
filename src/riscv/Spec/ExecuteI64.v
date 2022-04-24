(* Default settings (from HsToCoq.Coq.Preamble) *)

Generalizable All Variables.

Unset Implicit Arguments.
Set Maximal Implicit Insertion.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Coq.Program.Tactics.
Require Coq.Program.Wf.

(* Preamble *)

Require Import Coq.ZArith.BinInt.
Local Open Scope Z.
Require Import riscv.Utility.Utility.
Local Open Scope alu_scope.

(* Converted imports: *)

Require Import Monads.
Require Spec.Decode.
Require Spec.Machine.
Require Spec.VirtualMemory.
Require Utility.Utility.

(* No type declarations to convert. *)

(* Converted value declarations: *)

Definition execute {p : Type -> Type} {t : Type} `{Spec.Machine.RiscvMachine p
                                                                             t}
   : Spec.Decode.InstructionI64 -> p unit :=
  fun arg_0__ =>
    match arg_0__ with
    | Spec.Decode.Lwu rd rs1 oimm12 =>
        Bind (Spec.Machine.getRegister rs1) (fun a =>
                Bind (Spec.VirtualMemory.translate Spec.Machine.Load (ZToReg 4) (a +
                                                    Utility.Utility.fromImm oimm12)) (fun addr =>
                        Bind (Spec.Machine.loadWord Spec.Machine.Execute addr) (fun x =>
                                Spec.Machine.setRegister rd (Utility.Utility.uInt32ToReg x))))
    | Spec.Decode.Ld rd rs1 oimm12 =>
        Bind (Spec.Machine.getRegister rs1) (fun a =>
                Bind (Spec.VirtualMemory.translate Spec.Machine.Load (ZToReg 8) (a +
                                                    Utility.Utility.fromImm oimm12)) (fun addr =>
                        Bind (Spec.Machine.loadDouble Spec.Machine.Execute addr) (fun x =>
                                Spec.Machine.setRegister rd (Utility.Utility.int64ToReg x))))
    | Spec.Decode.Sd rs1 rs2 simm12 =>
        Bind (Spec.Machine.getRegister rs1) (fun a =>
                Bind (Spec.VirtualMemory.translate Spec.Machine.Store (ZToReg 8) (a +
                                                    Utility.Utility.fromImm simm12)) (fun addr =>
                        Bind (Spec.Machine.getRegister rs2) (fun x =>
                                Spec.Machine.storeDouble Spec.Machine.Execute addr (Utility.Utility.regToInt64
                                                                                    x))))
    | Spec.Decode.Addiw rd rs1 imm12 =>
        Bind (Spec.Machine.getRegister rs1) (fun x =>
                Spec.Machine.setRegister rd (Utility.Utility.s32 (x +
                                                                  Utility.Utility.fromImm imm12)))
    | Spec.Decode.Slliw rd rs1 shamt5 =>
        Bind (Spec.Machine.getRegister rs1) (fun x =>
                Spec.Machine.setRegister rd (Utility.Utility.s32 (Utility.Utility.sll x
                                                                  shamt5)))
    | Spec.Decode.Srliw rd rs1 shamt5 =>
        Bind (Spec.Machine.getRegister rs1) (fun x =>
                Spec.Machine.setRegister rd (Utility.Utility.s32 (Utility.Utility.srl
                                                                  (Utility.Utility.u32 x) shamt5)))
    | Spec.Decode.Sraiw rd rs1 shamt5 =>
        Bind (Spec.Machine.getRegister rs1) (fun x =>
                Spec.Machine.setRegister rd (Utility.Utility.s32 (Utility.Utility.sra
                                                                  (Utility.Utility.s32 x) shamt5)))
    | Spec.Decode.Addw rd rs1 rs2 =>
        Bind (Spec.Machine.getRegister rs1) (fun x =>
                Bind (Spec.Machine.getRegister rs2) (fun y =>
                        Spec.Machine.setRegister rd (Utility.Utility.s32 (x + y))))
    | Spec.Decode.Subw rd rs1 rs2 =>
        Bind (Spec.Machine.getRegister rs1) (fun x =>
                Bind (Spec.Machine.getRegister rs2) (fun y =>
                        Spec.Machine.setRegister rd (Utility.Utility.s32 (x - y))))
    | Spec.Decode.Sllw rd rs1 rs2 =>
        Bind (Spec.Machine.getRegister rs1) (fun x =>
                Bind (Spec.Machine.getRegister rs2) (fun y =>
                        Spec.Machine.setRegister rd (Utility.Utility.s32 (Utility.Utility.sll x
                                                                          (Utility.Utility.regToShamt5 y)))))
    | Spec.Decode.Srlw rd rs1 rs2 =>
        Bind (Spec.Machine.getRegister rs1) (fun x =>
                Bind (Spec.Machine.getRegister rs2) (fun y =>
                        Spec.Machine.setRegister rd (Utility.Utility.s32 (Utility.Utility.srl
                                                                          (Utility.Utility.u32 x)
                                                                          (Utility.Utility.regToShamt5 y)))))
    | Spec.Decode.Sraw rd rs1 rs2 =>
        Bind (Spec.Machine.getRegister rs1) (fun x =>
                Bind (Spec.Machine.getRegister rs2) (fun y =>
                        Spec.Machine.setRegister rd (Utility.Utility.s32 (Utility.Utility.sra
                                                                          (Utility.Utility.s32 x)
                                                                          (Utility.Utility.regToShamt5 y)))))
    | inst => Return tt
    end.

(* External variables:
     Bind Return Type ZToReg op_zm__ op_zp__ tt unit Spec.Decode.Addiw
     Spec.Decode.Addw Spec.Decode.InstructionI64 Spec.Decode.Ld Spec.Decode.Lwu
     Spec.Decode.Sd Spec.Decode.Slliw Spec.Decode.Sllw Spec.Decode.Sraiw
     Spec.Decode.Sraw Spec.Decode.Srliw Spec.Decode.Srlw Spec.Decode.Subw
     Spec.Machine.Execute Spec.Machine.Load Spec.Machine.RiscvMachine
     Spec.Machine.Store Spec.Machine.getRegister Spec.Machine.loadDouble
     Spec.Machine.loadWord Spec.Machine.setRegister Spec.Machine.storeDouble
     Spec.VirtualMemory.translate Utility.Utility.fromImm Utility.Utility.int64ToReg
     Utility.Utility.regToInt64 Utility.Utility.regToShamt5 Utility.Utility.s32
     Utility.Utility.sll Utility.Utility.sra Utility.Utility.srl Utility.Utility.u32
     Utility.Utility.uInt32ToReg
*)
