(* import List before bbv.Word, otherwise Word.combine gets shadowed and huge type class
   inference failure messages will appear *)
Require Import Coq.Lists.List.
Require Import Coq.omega.Omega.
Require Import bbv.Word.
Require Import Coq.ZArith.BinInt.
Require Import riscv.Utility.
Require Import riscv.util.Monads.
Require Import riscv.Memory.
Import ListNotations.


Section Memory.

  Definition mem := list (word 8).
  Definition mem_size(m: mem): nat := length m.

  Definition read_byte(m: mem)(a: nat): word 8 := nth a m $0.
  Definition write_byte(m: mem)(a: nat)(v: word 8): mem :=
    (firstn a m) ++ [v] ++ (skipn (S a) m).

  Definition read_half(m: mem)(a: nat): word 16 :=
    let v0 := read_byte m a in let v1 := read_byte m (a + 1) in combine v0 v1.
  Definition read_word(m: mem)(a: nat): word 32 :=
    let v0 := read_half m a in let v1 := read_half m (a + 2) in combine v0 v1.
  Definition read_double(m: mem)(a: nat): word 64 :=
    let v0 := read_word m a in let v1 := read_word m (a + 4) in combine v0 v1.

  Definition lobits(sz: nat)(w: word (sz + sz)): word sz := split1 sz sz w.
  Definition hibits(sz: nat)(w: word (sz + sz)): word sz := split2 sz sz w.

  Definition write_half(m: mem)(a: nat)(v: word 16): mem :=
    let m := write_byte m a (lobits 8 v) in write_byte m (a + 1) (hibits 8 v).
  Definition write_word(m: mem)(a: nat)(v: word 32): mem :=
    let m := write_half m a (lobits 16 v) in write_half m (a + 2) (hibits 16 v).
  Definition write_double(m: mem)(a: nat)(v: word 64): mem :=
    let m := write_word m a (lobits 32 v) in write_word m (a + 4) (hibits 32 v).

  Fixpoint const_mem(default: word 8)(size: nat): mem :=
    match size with
    | O => []
    | S n => default :: (const_mem default n)
    end.

  Definition zero_mem: nat -> mem := const_mem $0.

End Memory.

Arguments mem : clear implicits.


Instance mem_is_Memory(w: nat): Memory mem (nat) := {|
  loadByte    := read_byte;
  loadHalf    := read_half;
  loadWord    := read_word;
  loadDouble  := read_double;
  storeByte   := write_byte;
  storeHalf   := write_half;
  storeWord   := write_word;
  storeDouble := write_double;
|}.

Lemma write_read_byte_eq: forall m a1 a2 v,
    a1 < mem_size m ->
    a2 = a1 ->
    read_byte (write_byte m a1 v) a2 = v.
Proof.
  intros. subst. unfold write_byte, read_byte, mem_size in *.
  pose proof (@firstn_length_le _ m a1).
  rewrite app_nth2 by omega.
  rewrite H0 by omega.
  replace (a1 - a1) with 0 by omega.
  reflexivity.
Qed.

Lemma write_read_byte_ne: forall m a1 a2 v,
    a1 < mem_size m ->
    a2 < mem_size m ->
    a2 <> a1 ->
    read_byte (write_byte m a1 v) a2 = read_byte m a2.
Proof.
  intros. unfold write_byte, read_byte, mem_size in *.
  pose proof (@firstn_length_le _ m a1).
  pose proof (@firstn_length_le _ m a2).
  assert (a2 < a1 \/ a1 < a2 < length m) as P by omega.
  destruct P as [P | P].
  - rewrite app_nth1 by omega.
    clear H2 H3.
    generalize dependent m. generalize dependent a1.
    induction a2; intros.
    + destruct a1; [omega|simpl]. destruct m; reflexivity.
    + destruct a1; [omega|simpl]. destruct m.
      * simpl in H; omega.
      * simpl in *. apply IHa2; omega.
  - rewrite app_nth2 by omega.
    rewrite app_nth2 by (simpl; omega).
    rewrite H2 by omega.
    replace (a2 - a1 - length [v]) with (a2 - (S a1)) by (simpl; omega).
    clear H2 H3.
    generalize dependent m. generalize dependent a1.
    induction a2; intros.
    + omega.
    + replace (S a2 - S a1) with (a2 - a1) by omega.
      destruct a1.
      * replace (a2 - 0) with a2 by omega. destruct m; [simpl in *; omega|reflexivity].
      * destruct m; [simpl in *; omega|].
        change (skipn (S (S a1)) (w :: m)) with (skipn (S a1) m).
        change (nth (S a2) (w :: m)) with (nth a2 m).
        apply IHa2; simpl in *; try omega.
Qed.

Lemma write_read_half_eq: forall m a1 a2 v,
    a1 + 1 < mem_size m ->
    a2 = a1 ->
    read_half (write_half m a1 v) a2 = v.
Proof.
  intros. subst. unfold write_half, read_half in *.
Admitted.
(*
  rewrite (write_read_byte_eq (write_byte m a1 (lobits 8 v))). (a1 + 1) _ (hibits 8 v)).
  assert (a ^+ $1 <> a) as Q by apply wplus_one_neq.
  rewrite (write_read_byte_diff _ a (a ^+ $1) _ (hibits 8 v) Q).
  rewrite write_read_byte.
  apply (combine_split 8 8).
Qed.
*)