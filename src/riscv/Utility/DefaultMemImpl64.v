Require Import Coq.ZArith.ZArith.
Require Import coqutil.Word.Bitwidth.
Require Import coqutil.Map.Interface.
Require coqutil.Map.SortedListWord.

#[global] Instance Mem: map.map (bits 64) Byte.byte := SortedListWord.map 64 Byte.byte.
#[global] Instance MemOk: map.ok Mem := SortedListWord.ok 64 Byte.byte.
