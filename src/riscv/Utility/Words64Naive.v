Require Import Coq.ZArith.BinInt.
Require Import coqutil.Z.Lia.
Require Import coqutil.Word.Naive.
Require Import coqutil.Word.Properties.
Require Import coqutil.Word.Bitwidth.

Local Open Scope Z_scope.

#[global] Instance word: word.word 64 := Naive.word 64.

#[global] Instance Words64Naive: Bitwidth 64 := {|
  width_cases := or_intror eq_refl;
|}.
