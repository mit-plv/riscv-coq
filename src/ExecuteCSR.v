(* Default settings (from HsToCoq.Coq.Preamble) *)

Generalizable All Variables.

Unset Implicit Arguments.
Set Maximal Implicit Insertion.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Coq.Program.Tactics.
Require Coq.Program.Wf.

(* Preamble *)

Require Import Utility.
Local Open Scope alu_scope.

(* Converted imports: *)

Require CSR.
Require CSRField.
Require CSRSpec.
Require Import Coq.ZArith.BinInt.
Require Decode.
Require GHC.Num.
Require Import Monads.
Require Import Program.
Require Import Utility.
Import GHC.Num.Notations.

(* No type declarations to convert. *)
(* Converted value declarations: *)

Definition execute {p} {t} `{(RiscvState p t)}
   : Decode.InstructionCSR -> p unit :=
  fun arg_0__ =>
    match arg_0__ with
    | Decode.Csrrw rd rs1 csr12 =>
        Bind (getRegister rs1) (fun x =>
                Bind (when (rd /= zero) (Bind (CSRSpec.getCSR (CSR.lookupCSR csr12)) (fun y =>
                                                 setRegister rd ((id : Z -> t) y)))) (fun _ =>
                        CSRSpec.setCSR (CSR.lookupCSR csr12) x))
    | Decode.Csrrs rd rs1 csr12 =>
        Bind (getRegister rs1) (fun mask =>
                Bind (CSRSpec.getCSR (CSR.lookupCSR csr12)) (fun val =>
                        Bind (setRegister rd ((id : Z -> t) val)) (fun _ =>
                                when (rs1 /= zero) (CSRSpec.setCSR (CSR.lookupCSR csr12) (or val ((id : t -> Z)
                                                                                              mask))))))
    | Decode.Csrrc rd rs1 csr12 =>
        Bind (getRegister rs1) (fun mask =>
                Bind (CSRSpec.getCSR (CSR.lookupCSR csr12)) (fun val =>
                        Bind (setRegister rd ((id : Z -> t) val)) (fun _ =>
                                when (rs1 /= zero) (CSRSpec.setCSR (CSR.lookupCSR csr12) (and val ((id : t -> Z)
                                                                                               mask))))))
    | Decode.Csrrwi rd zimm csr12 =>
        Bind (when (rd /= zero) (Bind (CSRSpec.getCSR (CSR.lookupCSR csr12)) (fun val =>
                                         setRegister rd ((id : Z -> t) val)))) (fun _ =>
                CSRSpec.setCSR (CSR.lookupCSR csr12) zimm)
    | Decode.Csrrsi rd zimm csr12 =>
        Bind (CSRSpec.getCSR (CSR.lookupCSR csr12)) (fun val =>
                Bind (setRegister rd ((id : Z -> t) val)) (fun _ =>
                        when (zimm /= zero) (CSRSpec.setCSR (CSR.lookupCSR csr12) (or val zimm))))
    | Decode.Csrrci rd zimm csr12 =>
        Bind (CSRSpec.getCSR (CSR.lookupCSR csr12)) (fun val =>
                Bind (setRegister rd ((id : Z -> t) val)) (fun _ =>
                        when (zimm /= zero) (CSRSpec.setCSR (CSR.lookupCSR csr12) (and val (lnot
                                                                                        zimm)))))
    | Decode.Ecall => raiseException zero #11
    | Decode.Ebreak => raiseException zero #3
    | Decode.Mret =>
        Bind (getCSRField CSRField.MEPC) (fun mepc => setPC ((id : Z -> t) mepc))
    | inst => Return tt
    end.

(* Unbound variables:
     Bind Return RiscvState Z and getCSRField getRegister id lnot op_zsze__ or
     raiseException setPC setRegister tt unit when zero CSR.lookupCSR CSRField.MEPC
     CSRSpec.getCSR CSRSpec.setCSR Decode.Csrrc Decode.Csrrci Decode.Csrrs
     Decode.Csrrsi Decode.Csrrw Decode.Csrrwi Decode.Ebreak Decode.Ecall
     Decode.InstructionCSR Decode.Mret GHC.Num.fromInteger
*)
