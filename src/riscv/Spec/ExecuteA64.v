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
   : Spec.Decode.InstructionA64 -> p unit :=
  fun arg_0__ =>
    match arg_0__ with
    | Spec.Decode.Lr_d rd rs1 aqrl =>
        Bind (Spec.Machine.getRegister rs1) (fun a =>
                Bind (Spec.VirtualMemory.translate Spec.Machine.Load (ZToReg 8) a) (fun addr =>
                        Bind (Spec.Machine.makeReservation addr) (fun _ =>
                                Bind (Spec.Machine.loadDouble Spec.Machine.Execute addr) (fun x =>
                                        Spec.Machine.setRegister rd (Utility.Utility.int64ToReg x)))))
    | Spec.Decode.Sc_d rd rs1 rs2 aqrl =>
        Bind (Spec.Machine.getRegister rs1) (fun a =>
                Bind (Spec.VirtualMemory.translate Spec.Machine.Store (ZToReg 8) a) (fun addr =>
                        Bind (Spec.Machine.checkReservation addr) (fun valid =>
                                if valid : bool
                                then Bind (Spec.Machine.getRegister rs2) (fun x =>
                                             Bind (Spec.Machine.storeDouble Spec.Machine.Execute addr
                                                                            (Utility.Utility.regToInt64 x)) (fun _ =>
                                                     Spec.Machine.setRegister rd (ZToReg 0)))
                                else Spec.Machine.setRegister rd (ZToReg 1))))
    | Spec.Decode.Amoswap_d rd rs1 rs2 aqrl =>
        Bind (Spec.Machine.getRegister rs1) (fun a =>
                Bind (Spec.VirtualMemory.translate Spec.Machine.Store (ZToReg 4) a) (fun addr =>
                        Bind (Spec.Machine.loadDouble Spec.Machine.Execute addr) (fun x =>
                                Bind (Spec.Machine.getRegister rs2) (fun y =>
                                        Bind (Spec.Machine.setRegister rd (Utility.Utility.int64ToReg x)) (fun _ =>
                                                Spec.Machine.storeDouble Spec.Machine.Execute addr
                                                                         (Utility.Utility.regToInt64 y))))))
    | Spec.Decode.Amoadd_d rd rs1 rs2 aqrl =>
        Bind (Spec.Machine.getRegister rs1) (fun a =>
                Bind (Spec.VirtualMemory.translate Spec.Machine.Store (ZToReg 4) a) (fun addr =>
                        Bind (Spec.Machine.loadDouble Spec.Machine.Execute addr) (fun x =>
                                Bind (Spec.Machine.getRegister rs2) (fun y =>
                                        Bind (Spec.Machine.setRegister rd (Utility.Utility.int64ToReg x)) (fun _ =>
                                                Spec.Machine.storeDouble Spec.Machine.Execute addr
                                                                         (Utility.Utility.regToInt64
                                                                          (Utility.Utility.int64ToReg x + y)))))))
    | Spec.Decode.Amoand_d rd rs1 rs2 aqrl =>
        Bind (Spec.Machine.getRegister rs1) (fun a =>
                Bind (Spec.VirtualMemory.translate Spec.Machine.Store (ZToReg 4) a) (fun addr =>
                        Bind (Spec.Machine.loadDouble Spec.Machine.Execute addr) (fun x =>
                                Bind (Spec.Machine.getRegister rs2) (fun y =>
                                        Bind (Spec.Machine.setRegister rd (Utility.Utility.int64ToReg x)) (fun _ =>
                                                Spec.Machine.storeDouble Spec.Machine.Execute addr
                                                                         (Utility.Utility.regToInt64 (and
                                                                                                      (Utility.Utility.int64ToReg
                                                                                                       x) y)))))))
    | Spec.Decode.Amoor_d rd rs1 rs2 aqrl =>
        Bind (Spec.Machine.getRegister rs1) (fun a =>
                Bind (Spec.VirtualMemory.translate Spec.Machine.Store (ZToReg 4) a) (fun addr =>
                        Bind (Spec.Machine.loadDouble Spec.Machine.Execute addr) (fun x =>
                                Bind (Spec.Machine.getRegister rs2) (fun y =>
                                        Bind (Spec.Machine.setRegister rd (Utility.Utility.int64ToReg x)) (fun _ =>
                                                Spec.Machine.storeDouble Spec.Machine.Execute addr
                                                                         (Utility.Utility.regToInt64 (or
                                                                                                      (Utility.Utility.int64ToReg
                                                                                                       x) y)))))))
    | Spec.Decode.Amoxor_d rd rs1 rs2 aqrl =>
        Bind (Spec.Machine.getRegister rs1) (fun a =>
                Bind (Spec.VirtualMemory.translate Spec.Machine.Store (ZToReg 4) a) (fun addr =>
                        Bind (Spec.Machine.loadDouble Spec.Machine.Execute addr) (fun x =>
                                Bind (Spec.Machine.getRegister rs2) (fun y =>
                                        Bind (Spec.Machine.setRegister rd (Utility.Utility.int64ToReg x)) (fun _ =>
                                                Spec.Machine.storeDouble Spec.Machine.Execute addr
                                                                         (Utility.Utility.regToInt64 (xor
                                                                                                      (Utility.Utility.int64ToReg
                                                                                                       x) y)))))))
    | Spec.Decode.Amomax_d rd rs1 rs2 aqrl =>
        Bind (Spec.Machine.getRegister rs1) (fun a =>
                Bind (Spec.VirtualMemory.translate Spec.Machine.Store (ZToReg 4) a) (fun addr =>
                        Bind (Spec.Machine.loadDouble Spec.Machine.Execute addr) (fun x =>
                                Bind (Spec.Machine.getRegister rs2) (fun y =>
                                        Bind (Spec.Machine.setRegister rd (Utility.Utility.int64ToReg x)) (fun _ =>
                                                Spec.Machine.storeDouble Spec.Machine.Execute addr (if y <
                                                                                                       Utility.Utility.int64ToReg
                                                                                                       x : bool
                                                                          then x
                                                                          else Utility.Utility.regToInt64 y))))))
    | Spec.Decode.Amomaxu_d rd rs1 rs2 aqrl =>
        Bind (Spec.Machine.getRegister rs1) (fun a =>
                Bind (Spec.VirtualMemory.translate Spec.Machine.Store (ZToReg 4) a) (fun addr =>
                        Bind (Spec.Machine.loadDouble Spec.Machine.Execute addr) (fun x =>
                                Bind (Spec.Machine.getRegister rs2) (fun y =>
                                        Bind (Spec.Machine.setRegister rd (Utility.Utility.int64ToReg x)) (fun _ =>
                                                Spec.Machine.storeDouble Spec.Machine.Execute addr
                                                                         (if Utility.Utility.ltu y
                                                                             (Utility.Utility.uInt64ToReg x) : bool
                                                                          then x
                                                                          else Utility.Utility.regToInt64 y))))))
    | Spec.Decode.Amomin_d rd rs1 rs2 aqrl =>
        Bind (Spec.Machine.getRegister rs1) (fun a =>
                Bind (Spec.VirtualMemory.translate Spec.Machine.Store (ZToReg 4) a) (fun addr =>
                        Bind (Spec.Machine.loadDouble Spec.Machine.Execute addr) (fun x =>
                                Bind (Spec.Machine.getRegister rs2) (fun y =>
                                        Bind (Spec.Machine.setRegister rd (Utility.Utility.int64ToReg x)) (fun _ =>
                                                Spec.Machine.storeDouble Spec.Machine.Execute addr
                                                                         (if Utility.Utility.int64ToReg x < y : bool
                                                                          then x
                                                                          else Utility.Utility.regToInt64 y))))))
    | Spec.Decode.Amominu_d rd rs1 rs2 aqrl =>
        Bind (Spec.Machine.getRegister rs1) (fun a =>
                Bind (Spec.VirtualMemory.translate Spec.Machine.Store (ZToReg 4) a) (fun addr =>
                        Bind (Spec.Machine.loadDouble Spec.Machine.Execute addr) (fun x =>
                                Bind (Spec.Machine.getRegister rs2) (fun y =>
                                        Bind (Spec.Machine.setRegister rd (Utility.Utility.int64ToReg x)) (fun _ =>
                                                Spec.Machine.storeDouble Spec.Machine.Execute addr
                                                                         (if Utility.Utility.ltu
                                                                             (Utility.Utility.uInt64ToReg x) y : bool
                                                                          then x
                                                                          else Utility.Utility.regToInt64 y))))))
    | inst => Return tt
    end.

(* External variables:
     Bind Return Type ZToReg and bool op_zl__ op_zp__ or tt unit xor
     Spec.Decode.Amoadd_d Spec.Decode.Amoand_d Spec.Decode.Amomax_d
     Spec.Decode.Amomaxu_d Spec.Decode.Amomin_d Spec.Decode.Amominu_d
     Spec.Decode.Amoor_d Spec.Decode.Amoswap_d Spec.Decode.Amoxor_d
     Spec.Decode.InstructionA64 Spec.Decode.Lr_d Spec.Decode.Sc_d
     Spec.Machine.Execute Spec.Machine.Load Spec.Machine.RiscvMachine
     Spec.Machine.Store Spec.Machine.checkReservation Spec.Machine.getRegister
     Spec.Machine.loadDouble Spec.Machine.makeReservation Spec.Machine.setRegister
     Spec.Machine.storeDouble Spec.VirtualMemory.translate Utility.Utility.int64ToReg
     Utility.Utility.ltu Utility.Utility.regToInt64 Utility.Utility.uInt64ToReg
*)
