Require Import Coq.ZArith.BinInt.
Local Open Scope Z.
Require Import riscv.Utility.Utility.
Local Open Scope alu_scope.
Require Import Monads.
Require Import Spec.CSR.
Require Spec.CSRGetSet.
Require Import Spec.Machine.

Definition setCSR {p} {t} `{RiscvMachine p t} (c : CSR) (v : t) : p unit :=
  CSRGetSet.setCSR c (regToZ_unsigned v).

Definition getCSR {p} {t} `{Spec.Machine.RiscvMachine p t} (c : CSR) : p t :=
  Bind (CSRGetSet.getCSR c) (fun r => Return (ZToReg r)).
