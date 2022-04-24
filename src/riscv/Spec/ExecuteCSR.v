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

Require Import Coq.ZArith.BinInt.
Require Machine.
Require Import Monads.
Require Spec.CSR.
Require Spec.CSRField.
Require Spec.CSRSpec.
Require Spec.Decode.
Require Spec.Machine.
Require Import Utility.
Require Utility.Utility.

(* No type declarations to convert. *)

(* Converted value declarations: *)

Definition checkPermissions {p : Type -> Type} {t : Type}
  `{Spec.Machine.RiscvMachine p t}
   : bool -> Utility.Utility.MachineInt -> p unit :=
  fun isWrite csr =>
    let readOnly := Z.eqb (Utility.Utility.bitSlice csr 10 12) 3 in
    let minMode :=
      Spec.Machine.decodePrivMode (Utility.Utility.bitSlice csr 8 10) in
    Bind Spec.Machine.getPrivMode (fun mode =>
            when (orb (Spec.Machine.PrivMode_ltb mode minMode) (andb readOnly isWrite))
            (Machine.raiseException (ZToReg 0) (ZToReg 2))).

Definition execute {p : Type -> Type} {t : Type} `{Spec.Machine.RiscvMachine p
                                                                             t}
   : Spec.Decode.InstructionCSR -> p unit :=
  fun arg_0__ =>
    match arg_0__ with
    | Spec.Decode.Csrrw rd rs1 csr12 =>
        Bind (checkPermissions true csr12) (fun _ =>
                Bind (Spec.Machine.getRegister rs1) (fun x =>
                        Bind (Spec.CSRSpec.getCSR (Spec.CSR.lookupCSR csr12)) (fun y =>
                                Bind (Spec.CSRSpec.setCSR (Spec.CSR.lookupCSR csr12) x) (fun _ =>
                                        when (negb (Z.eqb rd 0)) (Spec.Machine.setRegister rd y)))))
    | Spec.Decode.Csrrs rd rs1 csr12 =>
        Bind (checkPermissions (negb (Z.eqb rs1 0)) csr12) (fun _ =>
                Bind (Spec.Machine.getRegister rs1) (fun mask =>
                        Bind (Spec.CSRSpec.getCSR (Spec.CSR.lookupCSR csr12)) (fun val =>
                                Bind (when (negb (Z.eqb rs1 0)) (Spec.CSRSpec.setCSR (Spec.CSR.lookupCSR csr12)
                                            (or val mask))) (fun _ => Spec.Machine.setRegister rd val))))
    | Spec.Decode.Csrrc rd rs1 csr12 =>
        Bind (checkPermissions (negb (Z.eqb rs1 0)) csr12) (fun _ =>
                Bind (Spec.Machine.getRegister rs1) (fun mask =>
                        Bind (Spec.CSRSpec.getCSR (Spec.CSR.lookupCSR csr12)) (fun val =>
                                Bind (when (negb (Z.eqb rs1 0)) (Spec.CSRSpec.setCSR (Spec.CSR.lookupCSR csr12)
                                            (and val (lnot mask)))) (fun _ => Spec.Machine.setRegister rd val))))
    | Spec.Decode.Csrrwi rd zimm csr12 =>
        Bind (checkPermissions true csr12) (fun _ =>
                Bind (Spec.CSRSpec.getCSR (Spec.CSR.lookupCSR csr12)) (fun val =>
                        Bind (Spec.CSRSpec.setCSR (Spec.CSR.lookupCSR csr12)
                                                  ((ZToReg : Utility.Utility.MachineInt -> t) zimm)) (fun _ =>
                                when (negb (Z.eqb rd 0)) (Spec.Machine.setRegister rd val))))
    | Spec.Decode.Csrrsi rd zimm csr12 =>
        Bind (checkPermissions (negb (Z.eqb zimm 0)) csr12) (fun _ =>
                Bind (Spec.CSRSpec.getCSR (Spec.CSR.lookupCSR csr12)) (fun val =>
                        Bind (when (negb (Z.eqb zimm 0)) (Spec.CSRSpec.setCSR (Spec.CSR.lookupCSR csr12)
                                    (or val ((ZToReg : Utility.Utility.MachineInt -> t) zimm)))) (fun _ =>
                                Spec.Machine.setRegister rd val)))
    | Spec.Decode.Csrrci rd zimm csr12 =>
        Bind (checkPermissions (negb (Z.eqb zimm 0)) csr12) (fun _ =>
                Bind (Spec.CSRSpec.getCSR (Spec.CSR.lookupCSR csr12)) (fun val =>
                        Bind (when (negb (Z.eqb zimm 0)) (Spec.CSRSpec.setCSR (Spec.CSR.lookupCSR csr12)
                                    (and val (lnot ((ZToReg : Utility.Utility.MachineInt -> t) zimm))))) (fun _ =>
                                Spec.Machine.setRegister rd val)))
    | Spec.Decode.Ecall =>
        Bind Spec.Machine.getPrivMode (fun mode =>
                match mode with
                | Spec.Machine.User => Machine.raiseException (ZToReg 0) (ZToReg 8)
                | Spec.Machine.Supervisor => Machine.raiseException (ZToReg 0) (ZToReg 9)
                | Spec.Machine.Machine => Machine.raiseException (ZToReg 0) (ZToReg 11)
                end)
    | Spec.Decode.Ebreak => Machine.raiseException (ZToReg 0) (ZToReg 3)
    | Spec.Decode.Mret =>
        Bind Spec.Machine.getPrivMode (fun priv =>
                Bind (when (Spec.Machine.PrivMode_ltb priv Spec.Machine.Machine)
                           (Machine.raiseException (ZToReg 0) (ZToReg 2))) (fun _ =>
                        Bind (Spec.Machine.getCSRField Spec.CSRField.MPP) (fun mpp =>
                                Bind (Spec.Machine.setCSRField Spec.CSRField.MPP (Spec.Machine.encodePrivMode
                                                                Spec.Machine.User)) (fun _ =>
                                        Bind (Spec.Machine.setPrivMode (Spec.Machine.decodePrivMode mpp)) (fun _ =>
                                                Bind (Spec.Machine.getCSRField Spec.CSRField.MPIE) (fun mpie =>
                                                        Bind (Spec.Machine.setCSRField Spec.CSRField.MPIE 1) (fun _ =>
                                                                Bind (Spec.Machine.setCSRField Spec.CSRField.MIE mpie)
                                                                     (fun _ =>
                                                                        Bind (Spec.Machine.getCSRField
                                                                              Spec.CSRField.MEPC) (fun mepc =>
                                                                                Spec.Machine.setPC
                                                                                ((ZToReg : Utility.Utility.MachineInt ->
                                                                                  t) mepc))))))))))
    | Spec.Decode.Sret =>
        Bind Spec.Machine.getPrivMode (fun priv =>
                Bind (when (Spec.Machine.PrivMode_ltb priv Spec.Machine.Supervisor)
                           (Machine.raiseException (ZToReg 0) (ZToReg 2))) (fun _ =>
                        Bind (Spec.Machine.getCSRField Spec.CSRField.TSR) (fun tsr =>
                                Bind (when (andb (Z.eqb tsr 1) (Spec.Machine.PrivMode_eqb priv
                                                                                          Spec.Machine.Supervisor))
                                           (Machine.raiseException (ZToReg 0) (ZToReg 2))) (fun _ =>
                                        Bind (Spec.Machine.getCSRField Spec.CSRField.SPP) (fun spp =>
                                                Bind (Spec.Machine.setCSRField Spec.CSRField.SPP
                                                                               (Spec.Machine.encodePrivMode
                                                                                Spec.Machine.User)) (fun _ =>
                                                        Bind (Spec.Machine.setPrivMode (Spec.Machine.decodePrivMode
                                                                                        spp)) (fun _ =>
                                                                Bind (Spec.Machine.getCSRField Spec.CSRField.SPIE)
                                                                     (fun spie =>
                                                                        Bind (Spec.Machine.setCSRField
                                                                              Spec.CSRField.SPIE 1) (fun _ =>
                                                                                Bind (Spec.Machine.setCSRField
                                                                                      Spec.CSRField.SIE spie) (fun _ =>
                                                                                        Bind (Spec.Machine.getCSRField
                                                                                              Spec.CSRField.SEPC)
                                                                                             (fun sepc =>
                                                                                                Spec.Machine.setPC
                                                                                                ((ZToReg : Utility.Utility.MachineInt ->
                                                                                                  t) sepc))))))))))))
    | Spec.Decode.Wfi =>
        Bind Spec.Machine.getPrivMode (fun mode =>
                Bind (Spec.Machine.getCSRField Spec.CSRField.TW) (fun tw =>
                        when (andb (Spec.Machine.PrivMode_eqb mode Spec.Machine.Supervisor) (Z.eqb tw
                                                                                                   1))
                        (Machine.raiseException (ZToReg 0) (ZToReg 2))))
    | Spec.Decode.Sfence_vma vaddr asid =>
        Bind Spec.Machine.getPrivMode (fun priv =>
                Bind (Spec.Machine.getCSRField Spec.CSRField.TVM) (fun tvm =>
                        Bind (when (andb (Spec.Machine.PrivMode_eqb priv Spec.Machine.Supervisor) (Z.eqb
                                          tvm 1)) (Machine.raiseException (ZToReg 0) (ZToReg 2))) (fun _ =>
                                Spec.Machine.flushTLB)))
    | inst => Return tt
    end.

(* External variables:
     Bind Return Type Z.eqb ZToReg and andb bool lnot negb or orb true tt unit when
     Machine.raiseException Spec.CSR.lookupCSR Spec.CSRField.MEPC Spec.CSRField.MIE
     Spec.CSRField.MPIE Spec.CSRField.MPP Spec.CSRField.SEPC Spec.CSRField.SIE
     Spec.CSRField.SPIE Spec.CSRField.SPP Spec.CSRField.TSR Spec.CSRField.TVM
     Spec.CSRField.TW Spec.CSRSpec.getCSR Spec.CSRSpec.setCSR Spec.Decode.Csrrc
     Spec.Decode.Csrrci Spec.Decode.Csrrs Spec.Decode.Csrrsi Spec.Decode.Csrrw
     Spec.Decode.Csrrwi Spec.Decode.Ebreak Spec.Decode.Ecall
     Spec.Decode.InstructionCSR Spec.Decode.Mret Spec.Decode.Sfence_vma
     Spec.Decode.Sret Spec.Decode.Wfi Spec.Machine.Machine Spec.Machine.PrivMode_eqb
     Spec.Machine.PrivMode_ltb Spec.Machine.RiscvMachine Spec.Machine.Supervisor
     Spec.Machine.User Spec.Machine.decodePrivMode Spec.Machine.encodePrivMode
     Spec.Machine.flushTLB Spec.Machine.getCSRField Spec.Machine.getPrivMode
     Spec.Machine.getRegister Spec.Machine.setCSRField Spec.Machine.setPC
     Spec.Machine.setPrivMode Spec.Machine.setRegister Utility.Utility.MachineInt
     Utility.Utility.bitSlice
*)
