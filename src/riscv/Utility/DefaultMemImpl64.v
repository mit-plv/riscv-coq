Require Import Coq.ZArith.ZArith.
Require Import coqutil.Z.Lia.
Require Import coqutil.Word.Interface coqutil.Word.Properties coqutil.Word.Naive.
Require Import coqutil.Map.Interface.
Require Import riscv.Utility.Words64Naive.
Require coqutil.Map.SortedList coqutil.Map.SortedListWord.


Instance params: SortedList.parameters := {|
  SortedList.parameters.key := word64;
  SortedList.parameters.value := Byte.byte;
  SortedList.parameters.ltb := word.ltu;
|}.

Instance Mem: map.map word64 Byte.byte := SortedList.map params _.
Instance MemOk: map.ok Mem := SortedList.map_ok.
