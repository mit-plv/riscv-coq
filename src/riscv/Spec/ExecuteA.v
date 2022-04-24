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
Require Import Utility.
Require Utility.Utility.

(* No type declarations to convert. *)

(* Converted value declarations: *)

Definition execute {p : Type -> Type} {t : Type} `{Spec.Machine.RiscvMachine p
                                                                             t}
   : Spec.Decode.InstructionA -> p unit :=
  fun arg_0__ =>
    match arg_0__ with
    | Spec.Decode.Lr_w rd rs1 aqrl =>
        Bind (Spec.Machine.getRegister rs1) (fun a =>
                Bind (Spec.VirtualMemory.translate Spec.Machine.Load (ZToReg 4) a) (fun addr =>
                        Bind (Spec.Machine.makeReservation addr) (fun _ =>
                                Bind (Spec.Machine.loadWord Spec.Machine.Execute addr) (fun x =>
                                        Spec.Machine.setRegister rd (Utility.Utility.int32ToReg x)))))
    | Spec.Decode.Sc_w rd rs1 rs2 aqrl =>
        Bind (Spec.Machine.getRegister rs1) (fun a =>
                Bind (Spec.VirtualMemory.translate Spec.Machine.Store (ZToReg 4) a) (fun addr =>
                        Bind (Spec.Machine.checkReservation addr) (fun valid =>
                                if valid : bool
                                then Bind (Spec.Machine.getRegister rs2) (fun x =>
                                             Bind (Spec.Machine.storeWord Spec.Machine.Execute addr
                                                                          (Utility.Utility.regToInt32 x)) (fun _ =>
                                                     Spec.Machine.setRegister rd (ZToReg 0)))
                                else Spec.Machine.setRegister rd (ZToReg 1))))
    | Spec.Decode.Amoswap_w rd rs1 rs2 aqrl =>
        Bind (Spec.Machine.getRegister rs1) (fun a =>
                Bind (Spec.VirtualMemory.translate Spec.Machine.Store (ZToReg 4) a) (fun addr =>
                        Bind (Spec.Machine.loadWord Spec.Machine.Execute addr) (fun x =>
                                Bind (Spec.Machine.getRegister rs2) (fun y =>
                                        Bind (Spec.Machine.setRegister rd (Utility.Utility.int32ToReg x)) (fun _ =>
                                                Spec.Machine.storeWord Spec.Machine.Execute addr
                                                                       (Utility.Utility.regToInt32 y))))))
    | Spec.Decode.Amoadd_w rd rs1 rs2 aqrl =>
        Bind (Spec.Machine.getRegister rs1) (fun a =>
                Bind (Spec.VirtualMemory.translate Spec.Machine.Store (ZToReg 4) a) (fun addr =>
                        Bind (Spec.Machine.loadWord Spec.Machine.Execute addr) (fun x =>
                                Bind (Spec.Machine.getRegister rs2) (fun y =>
                                        Bind (Spec.Machine.setRegister rd (Utility.Utility.int32ToReg x)) (fun _ =>
                                                Spec.Machine.storeWord Spec.Machine.Execute addr
                                                                       (Utility.Utility.regToInt32
                                                                        (Utility.Utility.int32ToReg x + y)))))))
    | Spec.Decode.Amoand_w rd rs1 rs2 aqrl =>
        Bind (Spec.Machine.getRegister rs1) (fun a =>
                Bind (Spec.VirtualMemory.translate Spec.Machine.Store (ZToReg 4) a) (fun addr =>
                        Bind (Spec.Machine.loadWord Spec.Machine.Execute addr) (fun x =>
                                Bind (Spec.Machine.getRegister rs2) (fun y =>
                                        Bind (Spec.Machine.setRegister rd (Utility.Utility.int32ToReg x)) (fun _ =>
                                                Spec.Machine.storeWord Spec.Machine.Execute addr
                                                                       (Utility.Utility.regToInt32 (and
                                                                                                    (Utility.Utility.int32ToReg
                                                                                                     x) y)))))))
    | Spec.Decode.Amoor_w rd rs1 rs2 aqrl =>
        Bind (Spec.Machine.getRegister rs1) (fun a =>
                Bind (Spec.VirtualMemory.translate Spec.Machine.Store (ZToReg 4) a) (fun addr =>
                        Bind (Spec.Machine.loadWord Spec.Machine.Execute addr) (fun x =>
                                Bind (Spec.Machine.getRegister rs2) (fun y =>
                                        Bind (Spec.Machine.setRegister rd (Utility.Utility.int32ToReg x)) (fun _ =>
                                                Spec.Machine.storeWord Spec.Machine.Execute addr
                                                                       (Utility.Utility.regToInt32 (or
                                                                                                    (Utility.Utility.int32ToReg
                                                                                                     x) y)))))))
    | Spec.Decode.Amoxor_w rd rs1 rs2 aqrl =>
        Bind (Spec.Machine.getRegister rs1) (fun a =>
                Bind (Spec.VirtualMemory.translate Spec.Machine.Store (ZToReg 4) a) (fun addr =>
                        Bind (Spec.Machine.loadWord Spec.Machine.Execute addr) (fun x =>
                                Bind (Spec.Machine.getRegister rs2) (fun y =>
                                        Bind (Spec.Machine.setRegister rd (Utility.Utility.int32ToReg x)) (fun _ =>
                                                Spec.Machine.storeWord Spec.Machine.Execute addr
                                                                       (Utility.Utility.regToInt32 (xor
                                                                                                    (Utility.Utility.int32ToReg
                                                                                                     x) y)))))))
    | Spec.Decode.Amomax_w rd rs1 rs2 aqrl =>
        Bind (Spec.Machine.getRegister rs1) (fun a =>
                Bind (Spec.VirtualMemory.translate Spec.Machine.Store (ZToReg 4) a) (fun addr =>
                        Bind (Spec.Machine.loadWord Spec.Machine.Execute addr) (fun x =>
                                Bind (Spec.Machine.getRegister rs2) (fun y =>
                                        Bind (Spec.Machine.setRegister rd (Utility.Utility.int32ToReg x)) (fun _ =>
                                                Spec.Machine.storeWord Spec.Machine.Execute addr (if Utility.Utility.s32
                                                                                                     y <
                                                                                                     Utility.Utility.int32ToReg
                                                                                                     x : bool
                                                                        then x
                                                                        else Utility.Utility.regToInt32 y))))))
    | Spec.Decode.Amomaxu_w rd rs1 rs2 aqrl =>
        Bind (Spec.Machine.getRegister rs1) (fun a =>
                Bind (Spec.VirtualMemory.translate Spec.Machine.Store (ZToReg 4) a) (fun addr =>
                        Bind (Spec.Machine.loadWord Spec.Machine.Execute addr) (fun x =>
                                Bind (Spec.Machine.getRegister rs2) (fun y =>
                                        Bind (Spec.Machine.setRegister rd (Utility.Utility.int32ToReg x)) (fun _ =>
                                                Spec.Machine.storeWord Spec.Machine.Execute addr (if Utility.Utility.ltu
                                                                                                     (Utility.Utility.u32
                                                                                                      y)
                                                                                                     (Utility.Utility.uInt32ToReg
                                                                                                      x) : bool
                                                                        then x
                                                                        else Utility.Utility.regToInt32 y))))))
    | Spec.Decode.Amomin_w rd rs1 rs2 aqrl =>
        Bind (Spec.Machine.getRegister rs1) (fun a =>
                Bind (Spec.VirtualMemory.translate Spec.Machine.Store (ZToReg 4) a) (fun addr =>
                        Bind (Spec.Machine.loadWord Spec.Machine.Execute addr) (fun x =>
                                Bind (Spec.Machine.getRegister rs2) (fun y =>
                                        Bind (Spec.Machine.setRegister rd (Utility.Utility.int32ToReg x)) (fun _ =>
                                                Spec.Machine.storeWord Spec.Machine.Execute addr
                                                                       (if Utility.Utility.int32ToReg x <
                                                                           Utility.Utility.s32 y : bool
                                                                        then x
                                                                        else Utility.Utility.regToInt32 y))))))
    | Spec.Decode.Amominu_w rd rs1 rs2 aqrl =>
        Bind (Spec.Machine.getRegister rs1) (fun a =>
                Bind (Spec.VirtualMemory.translate Spec.Machine.Store (ZToReg 4) a) (fun addr =>
                        Bind (Spec.Machine.loadWord Spec.Machine.Execute addr) (fun x =>
                                Bind (Spec.Machine.getRegister rs2) (fun y =>
                                        Bind (Spec.Machine.setRegister rd (Utility.Utility.int32ToReg x)) (fun _ =>
                                                Spec.Machine.storeWord Spec.Machine.Execute addr (if Utility.Utility.ltu
                                                                                                     (Utility.Utility.uInt32ToReg
                                                                                                      x)
                                                                                                     (Utility.Utility.u32
                                                                                                      y) : bool
                                                                        then x
                                                                        else Utility.Utility.regToInt32 y))))))
    | inst => Return tt
    end.

(* External variables:
     Bind Return Type ZToReg and bool op_zl__ op_zp__ or tt unit xor
     Spec.Decode.Amoadd_w Spec.Decode.Amoand_w Spec.Decode.Amomax_w
     Spec.Decode.Amomaxu_w Spec.Decode.Amomin_w Spec.Decode.Amominu_w
     Spec.Decode.Amoor_w Spec.Decode.Amoswap_w Spec.Decode.Amoxor_w
     Spec.Decode.InstructionA Spec.Decode.Lr_w Spec.Decode.Sc_w Spec.Machine.Execute
     Spec.Machine.Load Spec.Machine.RiscvMachine Spec.Machine.Store
     Spec.Machine.checkReservation Spec.Machine.getRegister Spec.Machine.loadWord
     Spec.Machine.makeReservation Spec.Machine.setRegister Spec.Machine.storeWord
     Spec.VirtualMemory.translate Utility.Utility.int32ToReg Utility.Utility.ltu
     Utility.Utility.regToInt32 Utility.Utility.s32 Utility.Utility.u32
     Utility.Utility.uInt32ToReg
*)
