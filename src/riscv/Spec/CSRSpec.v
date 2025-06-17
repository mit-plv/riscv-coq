Require Import Coq.ZArith.BinInt.
Local Open Scope Z.
Require Import riscv.Utility.Utility.
Local Open Scope alu_scope.
From riscv Require Import Monads.
From riscv Require Import Spec.CSR.
From riscv Require Spec.CSRGetSet.
From riscv Require Import Spec.Machine.

Definition setCSR {p} {t} `{RiscvMachine p t} (c : CSR) (v : t) : p unit :=
  CSRGetSet.setCSR c (regToZ_unsigned v).

Definition getCSR {p} {t} `{Spec.Machine.RiscvMachine p t} (c : CSR) : p t :=
  Bind (CSRGetSet.getCSR c) (fun r => Return (ZToReg r)).
