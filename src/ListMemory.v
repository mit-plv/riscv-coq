(* import List before bbv.Word, otherwise Word.combine gets shadowed and huge type class
   inference failure messages will appear *)
Require Import Coq.Lists.List.
Require Import Coq.omega.Omega.
Require Import bbv.Word.
Require Import Coq.ZArith.BinInt.
Require Import riscv.Utility.
Require Import riscv.util.Monads.
Require Import riscv.Memory.
Require riscv.ListMemoryNatAddr.


Section Memory.

  Context {w: nat}. (* bit width of memory addresses *)

  Definition mem := ListMemoryNatAddr.mem.
  Definition mem_size: mem -> nat := ListMemoryNatAddr.mem_size.

  Definition read_byte(m: mem)(a: word w): word 8 :=
    ListMemoryNatAddr.read_byte m (wordToNat a).

  Definition read_half(m: mem)(a: word w): word 16 :=
    ListMemoryNatAddr.read_half m (wordToNat a).

  Definition read_word(m: mem)(a: word w): word 32 :=
    ListMemoryNatAddr.read_word m (wordToNat a).

  Definition read_double(m: mem)(a: word w): word 64 :=
    ListMemoryNatAddr.read_double m (wordToNat a).

  Definition write_byte(m: mem)(a: word w)(v: word 8): mem :=
    ListMemoryNatAddr.write_byte m (wordToNat a) v.

  Definition write_half(m: mem)(a: word w)(v: word 16): mem :=
    ListMemoryNatAddr.write_half m (wordToNat a) v.

  Definition write_word(m: mem)(a: word w)(v: word 32): mem :=
    ListMemoryNatAddr.write_word m (wordToNat a) v.

  Definition write_double(m: mem)(a: word w)(v: word 64): mem :=
    ListMemoryNatAddr.write_double m (wordToNat a) v.

  Definition const_mem(default: word 8)(max_addr: nat): mem :=
    ListMemoryNatAddr.const_mem default (S max_addr).

  Definition zero_mem: nat -> mem := const_mem $0.

  Definition valid_addr(m: mem)(alignment: nat)(addr: word w): Prop :=
    wordToNat addr + alignment <= mem_size m /\
    (wordToNat addr) mod alignment = 0.

End Memory.

Instance mem_is_Memory(w: nat): Memory mem (word w) := {|
  loadByte    := read_byte;
  loadHalf    := read_half;
  loadWord    := read_word;
  loadDouble  := read_double;
  storeByte   := write_byte;
  storeHalf   := write_half;
  storeWord   := write_word;
  storeDouble := write_double;
|}.

Lemma write_read_byte_eq: forall w m (a1 a2: word w) v,
    valid_addr m 1 a1 ->
    a2 = a1 ->
    read_byte (write_byte m a1 v) a2 = v.
Proof.
  intros. destruct H.
  unfold mem_size, ListMemoryNatAddr.mem_size in *.
  unfold ListMemoryNatAddr.mem_size in *.
  apply ListMemoryNatAddr.write_read_byte_eq.
  - simpl.
    unfold ListMemoryNatAddr.mem_size.
    omega.
  - f_equal. assumption.
Qed.

Lemma write_read_byte_ne: forall w m (a1 a2: word w) v,
    valid_addr m 1 a1 ->
    valid_addr m 1 a2 ->
    a2 <> a1 ->
    read_byte (write_byte m a1 v) a2 = read_byte m a2.
Proof.
  intros.
  destruct H, H0.
  unfold mem_size, ListMemoryNatAddr.mem_size in *.
  apply ListMemoryNatAddr.write_read_byte_ne; simpl; unfold ListMemoryNatAddr.mem_size.
  - omega.
  - omega.
  - apply (wordToNat_neq1 H1).
Qed.

Lemma write_byte_preserves_mem_size: forall w m (a: word w) v,
    valid_addr m 1 a ->
    mem_size (write_byte m a v) = mem_size m.
Proof.
  intros. destruct H.
  unfold mem_size, write_byte in *.
  apply ListMemoryNatAddr.write_byte_preserves_mem_size.
  omega.
Qed.

Lemma write_read_half_eq: forall w m (a1 a2: word w) v,
    valid_addr m 2 a1 ->
    a2 = a1 ->
    read_half (write_half m a1 v) a2 = v.
Proof.
  intros. destruct H, H0.
  unfold mem_size, ListMemoryNatAddr.mem_size in *.
  apply ListMemoryNatAddr.write_read_half_eq; try reflexivity.
  unfold ListMemoryNatAddr.mem_size.
  omega.
Qed.

Lemma write_read_half_ne: forall w m (a1 a2: word w) v,
    valid_addr m 2 a1 ->
    valid_addr m 2 a2 ->
    a2 <> a1 ->
    read_half (write_half m a1 v) a2 = read_half m a2.
Proof.
  intros. destruct H. destruct H0.
  unfold mem_size, ListMemoryNatAddr.mem_size in *. simpl in H, H0.
  apply ListMemoryNatAddr.write_read_half_ne.
  - simpl.
    unfold ListMemoryNatAddr.mem_size. omega.
  - assumption.
  - simpl.
    unfold ListMemoryNatAddr.mem_size. omega.
  - assumption.
  - apply (wordToNat_neq1 H1).
Qed.

(*
Lemma write_half_preserves_mem_end: forall w m (a: word w) v,
    wlt (a ^+ 1) (mem_end m) ->
    mem_end (write_half m a v) = mem_end m.
Proof.

Qed.

Lemma write_read_word_eq: forall w m (a1 a2: word w) v,
    a1 ^+ 4 <= mem_end m ->
    a1 mod 4 = 0 ->
    a2 = a1 ->
    read_word (write_word m a1 v) a2 = v.
Proof.

Qed.

Lemma write_read_word_ne: forall w m (a1 a2: word w) v,
    a1 ^+ 4 <= mem_end m ->
    a1 mod 4 = 0 ->
    a2 ^+ 4 <= mem_end m ->
    a2 mod 4 = 0 ->
    a2 <> a1 ->
    read_word (write_word m a1 v) a2 = read_word m a2.
Proof.

Qed.

Lemma write_word_preserves_mem_end: forall w m (a: word w) v,
    a ^+ 4 <= mem_end m ->
    mem_end (write_word m a v) = mem_end m.
Proof.

Qed.

Lemma write_read_double_eq: forall w m (a1 a2: word w) v,
    a1 ^+ 8 <= mem_end m ->
    a1 mod 8 = 0 ->
    a2 = a1 ->
    read_double (write_double m a1 v) a2 = v.
Proof.

Qed.

Lemma write_read_double_ne: forall w m (a1 a2: word w) v,
    a1 ^+ 8 <= mem_end m ->
    a1 mod 8 = 0 ->
    a2 ^+ 8 <= mem_end m ->
    a2 mod 8 = 0 ->
    a2 <> a1 ->
    read_double (write_double m a1 v) a2 = read_double m a2.
Proof.

Qed.

Lemma write_double_preserves_mem_end: forall w m (a: word w) v,
    a ^+ 8 <= mem_end m ->
    mem_end (write_double m a v) = mem_end m.
Proof.

Qed.
*)