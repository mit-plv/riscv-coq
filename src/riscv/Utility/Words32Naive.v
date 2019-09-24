Require Import Coq.ZArith.BinInt.
Require Import coqutil.Z.Lia.
Require Import coqutil.Word.Naive.
Require Import coqutil.Word.Properties.
Require Import riscv.Utility.Utility.

Open Scope Z_scope.

Existing Instance Naive.word.

Instance Words32Naive: Words := {|
  byte := word8;
  word := word32;
  width_cases := or_introl eq_refl;
|}.
