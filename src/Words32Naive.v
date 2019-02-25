Require Import Coq.ZArith.BinInt.
Require Import Coq.micromega.Lia.
Require Import coqutil.Word.Naive.
Require Import coqutil.Word.Properties.
Require Import riscv.Utility.

Open Scope Z_scope.

Lemma bound32: 0 < 32. lia. Qed.
Instance word32: word.word 32 := Naive.word 32 bound32.
Instance word32ok: word.ok word32 := Naive.ok 32 bound32.

Lemma bound8: 0 < 8. lia. Qed.
Instance word8: word.word 8 := Naive.word 8 bound8.
Instance word8ok: word.ok word8 := Naive.ok 8 bound8.

Instance Words32Naive: Words := {|
  byte := word8;
  word := word32;
  width_cases := or_introl eq_refl;
|}.
