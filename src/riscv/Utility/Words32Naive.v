Require Import Coq.ZArith.BinInt.
Require Import coqutil.Word.Bitwidth.

#[global] Instance Words32Naive: Bitwidth 32 := {|
  width_cases := or_introl eq_refl;
|}.
