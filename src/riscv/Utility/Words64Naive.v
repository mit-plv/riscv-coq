Require Import Coq.ZArith.BinInt.
Require Import coqutil.Word.Bitwidth.

#[global] Instance Words64Naive: Bitwidth 64 := {|
  width_cases := or_intror eq_refl;
|}.
