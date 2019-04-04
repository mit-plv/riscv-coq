Require Import Coq.ZArith.BinInt.
Require Import coqutil.Z.Lia.
Require Import coqutil.Word.Naive.
Require Import coqutil.Word.Properties.
Require Import riscv.Utility.Utility.

Open Scope Z_scope.

Instance word64: word.word 64 := Naive.word 64 eq_refl.
Instance word64ok: word.ok word64 := Naive.ok 64 eq_refl.

Instance word8: word.word 8 := Naive.word 8 eq_refl.
Instance word8ok: word.ok word8 := Naive.ok 8 eq_refl.

Instance Words64Naive: Words := {|
  byte := word8;
  word := word64;
  width_cases := or_intror eq_refl;
|}.
