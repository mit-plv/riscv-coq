(* import List before bbv.Word, otherwise Word.combine gets shadowed and huge type class
   inference failure messages will appear *)
Require Import Coq.Lists.List.
Require Import Coq.omega.Omega.
Require Import bbv.Word.
Require Import Coq.ZArith.BinInt.
Require Import riscv.Utility.
Require Import riscv.util.Monads.
Require Import riscv.Memory.

Local Open Scope Z_scope.

Section Memory.

  Context {w: nat}. (* bit width of memory addresses *)

  Definition mem := word w -> word 8.

  Definition read_byte(m: mem)(a: word w): word 8 := m a.
  Definition read_half(m: mem)(a: word w): word 16 :=
    let v0 := read_byte m a in let v1 := read_byte m (a ^+ $1) in combine v0 v1.
  Definition read_word(m: mem)(a: word w): word 32 :=
    let v0 := read_half m a in let v1 := read_half m (a ^+ $2) in combine v0 v1.
  Definition read_double(m: mem)(a: word w): word 64 :=
    let v0 := read_word m a in let v1 := read_word m (a ^+ $4) in combine v0 v1.

  Definition lobits(sz: nat)(w: word (sz + sz)): word sz := split1 sz sz w.
  Definition hibits(sz: nat)(w: word (sz + sz)): word sz := split2 sz sz w.

  Definition write_byte(m: mem)(a: word w)(v: word 8): mem :=
    fun a' => if weq a' a then v else m a'.
  Definition write_half(m: mem)(a: word w)(v: word 16): mem :=
    let m := write_byte m a (lobits 8 v) in write_byte m (a ^+ $1) (hibits 8 v).
  Definition write_word(m: mem)(a: word w)(v: word 32): mem :=
    let m := write_half m a (lobits 16 v) in write_half m (a ^+ $2) (hibits 16 v).
  Definition write_double(m: mem)(a: word w)(v: word 64): mem :=
    let m := write_word m a (lobits 32 v) in write_word m (a ^+ $4) (hibits 32 v).

  Definition const_mem(default: word 8): mem := fun a => default.

  Definition zero_mem: mem := const_mem $0.

End Memory.

Arguments mem : clear implicits.


Instance mem_is_Memory(w: nat): Memory (mem w) (word w) := {|
  loadByte    := read_byte;
  loadHalf    := read_half;
  loadWord    := read_word;
  loadDouble  := read_double;
  storeByte   := write_byte;
  storeHalf   := write_half;
  storeWord   := write_word;
  storeDouble := write_double;
|}.

Lemma write_read_byte_eq: forall sz m (a1 a2: word sz) v,
    a2 = a1 ->
    read_byte (write_byte m a1 v) a2 = v.
Proof.
  intros. subst. unfold write_byte, read_byte in *.
  simpl.
  rewrite (rewrite_weq eq_refl). reflexivity.
Qed.

Lemma write_read_byte_ne: forall sz m (a1 a2: word sz) v,
    a2 <> a1 ->
    read_byte (write_byte m a1 v) a2 = read_byte m a2.
Proof.
  intros. unfold read_byte, write_byte in *.
  destruct (weq a2 a1); congruence.
Qed.

Local Ltac solve_eq write_read_eq write_read_ne :=
  intros; subst;
  (* note the order: we only unfold one layer *)
  unfold write_half, read_half, write_word, read_word, write_double, read_double in *;
  repeat match goal with
  | |- context [read_byte (write_byte ?m ?a1 ?v) ?a2] =>
    rewrite (write_read_eq _ m a1 a2 v) by reflexivity
  | |- context [read_byte (write_byte ?m ?a1 ?v) ?a2] =>
    rewrite (write_read_ne _ m a1 a2 v) by
        (pose proof @wplus_one_neq; congruence)
  end;
  match goal with
  | |- context [lobits ?half_sz _] => apply (combine_split half_sz half_sz)
  end.

Lemma write_read_half_eq: forall sz m (a1 a2: word (S sz)) v,
    a2 = a1 ->
    read_half (write_half m a1 v) a2 = v.
Proof.
  solve_eq write_read_byte_eq write_read_byte_ne.
Qed.

Lemma write_read_half_ne: forall sz m (a1 a2: word sz) v,
    (wordToZ a1) mod 2 = 0 ->
    (wordToZ a2) mod 2 = 0 ->
    a2 <> a1 ->
    read_half (write_half m a1 v) a2 = read_half m a2.
Proof.
  intros. subst. unfold write_half, read_half in *.
  pose proof wplus_cancel.
  match goal with
  | |- context [read_byte (write_byte ?m ?a1 ?v) ?a2] =>
    rewrite (write_read_byte_ne _ m a1 a2 v) (*by congruence*)
  end.
  admit.
  intro. subst.
  (* Search wordToZ wplus. *)
  (* annoying *)
Admitted.

Lemma write_read_half_eq': forall sz m (a1 a2: word (S sz)) v,
    a2 = a1 ->
    read_half (write_half m a1 v) a2 = v.
Proof.
  intros. subst. unfold write_half, read_half in *.
  repeat match goal with
  | |- context [read_byte (write_byte ?m ?a1 ?v) ?a2] =>
    rewrite (write_read_byte_eq _ m a1 a2 v) by reflexivity
  | |- context [read_byte (write_byte ?m ?a1 ?v) ?a2] =>
    rewrite (write_read_byte_ne _ m a1 a2 v) by
        (pose proof @wplus_one_neq; congruence)
  end.
  match goal with
  | |- context [lobits ?half_sz _] => apply (combine_split half_sz half_sz)
  end.
Qed.
