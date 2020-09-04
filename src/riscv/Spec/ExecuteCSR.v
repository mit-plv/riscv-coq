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
Require Spec.CSR.
Require Spec.CSRField.
Require Spec.CSRSpec.
Require Spec.Decode.
Require Spec.Machine.
Require Import Utility.
Require Utility.Utility.

(* No type declarations to convert. *)

(* Converted value declarations: *)

Definition checkPermissions :=
  fun isWrite csr =>
    let readOnly :=
      reg_eqb (Utility.Utility.bitSlice csr (ZToReg 10) (ZToReg 12)) (ZToReg 3) in
    let minMode :=
      Spec.Machine.decodePrivMode (Utility.Utility.bitSlice csr (ZToReg 8) (ZToReg
                                                                            10)) in
    Bind Spec.Machine.getPrivMode (fun mode =>
            when (orb (mode < minMode) (andb readOnly isWrite)) (Spec.Machine.raiseException
                                                                 (ZToReg 0) (ZToReg 2))).

Definition execute {p} {t} `{(Spec.Machine.RiscvMachine p t)}
   : Spec.Decode.InstructionCSR -> p unit :=
  fun arg_0__ =>
    match arg_0__ with
    | Spec.Decode.Csrrw rd rs1 csr12 =>
        Bind (checkPermissions true csr12) (fun _ =>
                Bind (Spec.Machine.getRegister rs1) (fun x =>
                        Bind (Spec.CSRSpec.getCSR (Spec.CSR.lookupCSR csr12)) (fun y =>
                                Bind (Spec.CSRSpec.setCSR (Spec.CSR.lookupCSR csr12) x) (fun _ =>
                                        when (rd /= ZToReg 0) (Spec.Machine.setRegister rd
                                              ((id : Utility.Utility.MachineInt -> t) y))))))
    | Spec.Decode.Csrrs rd rs1 csr12 =>
        Bind (checkPermissions (rs1 /= ZToReg 0) csr12) (fun _ =>
                Bind (Spec.Machine.getRegister rs1) (fun mask =>
                        Bind (Spec.CSRSpec.getCSR (Spec.CSR.lookupCSR csr12)) (fun val =>
                                Bind (when (rs1 /= ZToReg 0) (Spec.CSRSpec.setCSR (Spec.CSR.lookupCSR csr12) (or
                                                                                                              ((id : Utility.Utility.MachineInt ->
                                                                                                                t) val)
                                                                                                              mask)))
                                     (fun _ =>
                                        Spec.Machine.setRegister rd ((id : Utility.Utility.MachineInt -> t) val)))))
    | Spec.Decode.Csrrc rd rs1 csr12 =>
        Bind (checkPermissions (rs1 /= ZToReg 0) csr12) (fun _ =>
                Bind (Spec.Machine.getRegister rs1) (fun mask =>
                        Bind (Spec.CSRSpec.getCSR (Spec.CSR.lookupCSR csr12)) (fun val =>
                                Bind (when (rs1 /= ZToReg 0) (Spec.CSRSpec.setCSR (Spec.CSR.lookupCSR csr12)
                                            (and ((id : Utility.Utility.MachineInt -> t) val) (lnot mask)))) (fun _ =>
                                        Spec.Machine.setRegister rd ((id : Utility.Utility.MachineInt -> t) val)))))
    | Spec.Decode.Csrrwi rd zimm csr12 =>
        Bind (checkPermissions true csr12) (fun _ =>
                Bind (Spec.CSRSpec.getCSR (Spec.CSR.lookupCSR csr12)) (fun val =>
                        Bind (Spec.CSRSpec.setCSR (Spec.CSR.lookupCSR csr12)
                                                  ((id : Utility.Utility.MachineInt -> t) zimm)) (fun _ =>
                                when (rd /= ZToReg 0) (Spec.Machine.setRegister rd
                                      ((id : Utility.Utility.MachineInt -> t) val)))))
    | Spec.Decode.Csrrsi rd zimm csr12 =>
        Bind (checkPermissions (zimm /= ZToReg 0) csr12) (fun _ =>
                Bind (Spec.CSRSpec.getCSR (Spec.CSR.lookupCSR csr12)) (fun val =>
                        Bind (when (zimm /= ZToReg 0) (Spec.CSRSpec.setCSR (Spec.CSR.lookupCSR csr12)
                                    (or ((id : Utility.Utility.MachineInt -> t) val)
                                        ((id : Utility.Utility.MachineInt -> t) zimm)))) (fun _ =>
                                Spec.Machine.setRegister rd ((id : Utility.Utility.MachineInt -> t) val))))
    | Spec.Decode.Csrrci rd zimm csr12 =>
        Bind (checkPermissions (zimm /= ZToReg 0) csr12) (fun _ =>
                Bind (Spec.CSRSpec.getCSR (Spec.CSR.lookupCSR csr12)) (fun val =>
                        Bind (when (zimm /= ZToReg 0) (Spec.CSRSpec.setCSR (Spec.CSR.lookupCSR csr12)
                                    (and ((id : Utility.Utility.MachineInt -> t) val) (lnot
                                          ((id : Utility.Utility.MachineInt -> t) zimm))))) (fun _ =>
                                Spec.Machine.setRegister rd ((id : Utility.Utility.MachineInt -> t) val))))
    | Spec.Decode.Ecall =>
        Bind Spec.Machine.getPrivMode (fun mode =>
                match mode with
                | Spec.Machine.User => Spec.Machine.raiseException (ZToReg 0) (ZToReg 8)
                | Spec.Machine.Supervisor => Spec.Machine.raiseException (ZToReg 0) (ZToReg 9)
                | Spec.Machine.Machine => Spec.Machine.raiseException (ZToReg 0) (ZToReg 11)
                end)
    | Spec.Decode.Ebreak => Spec.Machine.raiseException (ZToReg 0) (ZToReg 3)
    | Spec.Decode.Mret =>
        Bind Spec.Machine.getPrivMode (fun priv =>
                Bind (when (priv < Spec.Machine.Machine) (Spec.Machine.raiseException (ZToReg 0)
                            (ZToReg 2))) (fun _ =>
                        Bind (Spec.Machine.getCSRField Spec.CSRField.MPP) (fun mpp =>
                                Bind (Spec.Machine.setCSRField Spec.CSRField.MPP (Spec.Machine.encodePrivMode
                                                                Spec.Machine.User)) (fun _ =>
                                        Bind (Spec.Machine.setPrivMode (Spec.Machine.decodePrivMode mpp)) (fun _ =>
                                                Bind (Spec.Machine.getCSRField Spec.CSRField.MPIE) (fun mpie =>
                                                        Bind (Spec.Machine.setCSRField Spec.CSRField.MPIE (ZToReg 1))
                                                             (fun _ =>
                                                                Bind (Spec.Machine.setCSRField Spec.CSRField.MIE mpie)
                                                                     (fun _ =>
                                                                        Bind (Spec.Machine.getCSRField
                                                                              Spec.CSRField.MEPC) (fun mepc =>
                                                                                Spec.Machine.setPC
                                                                                ((id : Utility.Utility.MachineInt -> t)
                                                                                 mepc))))))))))
    | Spec.Decode.Sret =>
        Bind Spec.Machine.getPrivMode (fun priv =>
                Bind (when (priv < Spec.Machine.Supervisor) (Spec.Machine.raiseException (ZToReg
                                                                                          0) (ZToReg 2))) (fun _ =>
                        Bind (Spec.Machine.getCSRField Spec.CSRField.TSR) (fun tsr =>
                                Bind (when (andb (reg_eqb tsr (ZToReg 1)) (Spec.Machine.PrivMode_beq priv
                                                                                                     Spec.Machine.Supervisor))
                                           (Spec.Machine.raiseException (ZToReg 0) (ZToReg 2))) (fun _ =>
                                        Bind (Spec.Machine.getCSRField Spec.CSRField.SPP) (fun spp =>
                                                Bind (Spec.Machine.setCSRField Spec.CSRField.SPP
                                                                               (Spec.Machine.encodePrivMode
                                                                                Spec.Machine.User)) (fun _ =>
                                                        Bind (Spec.Machine.setPrivMode (Spec.Machine.decodePrivMode
                                                                                        spp)) (fun _ =>
                                                                Bind (Spec.Machine.getCSRField Spec.CSRField.SPIE)
                                                                     (fun spie =>
                                                                        Bind (Spec.Machine.setCSRField
                                                                              Spec.CSRField.SPIE (ZToReg 1)) (fun _ =>
                                                                                Bind (Spec.Machine.setCSRField
                                                                                      Spec.CSRField.SIE spie) (fun _ =>
                                                                                        Bind (Spec.Machine.getCSRField
                                                                                              Spec.CSRField.SEPC)
                                                                                             (fun sepc =>
                                                                                                Spec.Machine.setPC
                                                                                                ((id : Utility.Utility.MachineInt ->
                                                                                                  t) sepc))))))))))))
    | Spec.Decode.Wfi =>
        Bind Spec.Machine.getPrivMode (fun mode =>
                Bind (Spec.Machine.getCSRField Spec.CSRField.TW) (fun tw =>
                        when (andb (Spec.Machine.PrivMode_beq mode Spec.Machine.Supervisor) (reg_eqb tw
                                                                                                     (ZToReg 1)))
                        (Spec.Machine.raiseException (ZToReg 0) (ZToReg 2))))
    | Spec.Decode.Sfence_vma vaddr asid =>
        Bind Spec.Machine.getPrivMode (fun priv =>
                Bind (Spec.Machine.getCSRField Spec.CSRField.TVM) (fun tvm =>
                        Bind (when (andb (Spec.Machine.PrivMode_beq priv Spec.Machine.Supervisor)
                                         (reg_eqb tvm (ZToReg 1))) (Spec.Machine.raiseException (ZToReg 0) (ZToReg 2)))
                             (fun _ => Spec.Machine.flushTLB)))
    | inst => Return tt
    end.

(* External variables:
     Bind Return ZToReg and andb id lnot op_zl__ op_zsze__ or orb reg_eqb true tt
     unit when Spec.CSR.lookupCSR Spec.CSRField.MEPC Spec.CSRField.MIE
     Spec.CSRField.MPIE Spec.CSRField.MPP Spec.CSRField.SEPC Spec.CSRField.SIE
     Spec.CSRField.SPIE Spec.CSRField.SPP Spec.CSRField.TSR Spec.CSRField.TVM
     Spec.CSRField.TW Spec.CSRSpec.getCSR Spec.CSRSpec.setCSR Spec.Decode.Csrrc
     Spec.Decode.Csrrci Spec.Decode.Csrrs Spec.Decode.Csrrsi Spec.Decode.Csrrw
     Spec.Decode.Csrrwi Spec.Decode.Ebreak Spec.Decode.Ecall
     Spec.Decode.InstructionCSR Spec.Decode.Mret Spec.Decode.Sfence_vma
     Spec.Decode.Sret Spec.Decode.Wfi Spec.Machine.Machine Spec.Machine.PrivMode_beq
     Spec.Machine.RiscvMachine Spec.Machine.Supervisor Spec.Machine.User
     Spec.Machine.decodePrivMode Spec.Machine.encodePrivMode Spec.Machine.flushTLB
     Spec.Machine.getCSRField Spec.Machine.getPrivMode Spec.Machine.getRegister
     Spec.Machine.raiseException Spec.Machine.setCSRField Spec.Machine.setPC
     Spec.Machine.setPrivMode Spec.Machine.setRegister Utility.Utility.MachineInt
     Utility.Utility.bitSlice
*)
