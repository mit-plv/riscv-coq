Require Import Coq.ZArith.BinInt.
Require Import coqutil.Z.Lia.
Require Import coqutil.Word.Naive.
Require Import coqutil.Word.Properties.
Require Import riscv.Utility.Utility.

Open Scope Z_scope.

Instance word32: word.word 32 := Naive.word 32 eq_refl.
Instance word32ok: word.ok word32 := Naive.ok 32 eq_refl.

Instance word8: word.word 8 := Naive.word 8 eq_refl.
Instance word8ok: word.ok word8 := Naive.ok 8 eq_refl.

Instance Words32Naive: Words := {|
  byte := word8;
  word := word32;
  width_cases := or_introl eq_refl;
|}.
