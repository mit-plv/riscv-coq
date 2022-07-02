Require Import Coq.ZArith.BinInt.
Require Import coqutil.Z.Lia.
Require Import coqutil.Word.Properties.
Require Import coqutil.Word.Bitwidth.
Require Import coqutil.Word.Naive.

Local Open Scope Z_scope.

#[global] Instance word: word.word 32 := Naive.word 32.

#[global] Instance Words32Naive: Bitwidth 32 := {|
  width_cases := or_introl eq_refl;
|}.
