Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Require Import coqutil.Word.Interface coqutil.Word.Properties coqutil.Word.Naive.
Require Import coqutil.Map.Interface.
Require Import riscv.Words32Naive.
Require coqutil.Map.SortedList.

Instance params: SortedList.parameters := {|
  SortedList.parameters.key := word32;
  SortedList.parameters.value := word8;
  SortedList.parameters.ltb := word.ltu;
|}.

Instance strictorder: SortedList.parameters.strict_order SortedList.parameters.ltb.
constructor; simpl; intros; rewrite? Z.ltb_nlt in *; rewrite? Z.ltb_lt in *; try lia.
apply (@word.unsigned_inj 32 word32 word32ok). (* TODO can we make this work without @ ? *)
(* TODO how can we normalize this so that lia will recognize the terms as being the same? *)
match goal with
| H: ~ ?x < ?y |- ?x' = ?y' => change x' with x; change y' with y
end.
lia.
Qed.

Instance Mem: map.map word32 word8 := SortedList.map params strictorder.
Instance MemOk: map.ok Mem := SortedList.map_ok.
