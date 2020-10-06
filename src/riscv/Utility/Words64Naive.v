Require Import Coq.ZArith.BinInt.
Require Import coqutil.Z.Lia.
Require Import coqutil.Word.Naive.
Require Import coqutil.Word.Properties.
Require Import riscv.Utility.Utility.

Local Open Scope Z_scope.

Existing Instance Naive.word.

Instance Words64Naive: Words := {|
  word := word64;
  width_cases := or_intror eq_refl;
|}.
