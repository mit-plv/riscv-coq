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

Local Ltac wrap L :=
  intros;
  repeat match goal with
         | H: valid_addr _ _ _ |- _ => destruct H
         end;
  unfold mem_size, ListMemoryNatAddr.mem_size in *;
  apply L;
  unfold ListMemoryNatAddr.mem_size;
  try apply wordToNat_neq1;
  (congruence || omega || idtac).    

Lemma write_read_byte_eq: forall w m (a1 a2: word w) v,
    valid_addr m 1 a1 ->
    a2 = a1 ->
    read_byte (write_byte m a1 v) a2 = v.
Proof. wrap ListMemoryNatAddr.write_read_byte_eq. Qed.

Lemma write_read_byte_ne: forall w m (a1 a2: word w) v,
    valid_addr m 1 a1 ->
    valid_addr m 1 a2 ->
    a2 <> a1 ->
    read_byte (write_byte m a1 v) a2 = read_byte m a2.
Proof. wrap ListMemoryNatAddr.write_read_byte_ne. Qed.

Lemma write_byte_preserves_mem_size: forall w m (a: word w) v,
    valid_addr m 1 a ->
    mem_size (write_byte m a v) = mem_size m.
Proof. wrap ListMemoryNatAddr.write_byte_preserves_mem_size. Qed.

Lemma write_read_half_eq: forall w m (a1 a2: word w) v,
    valid_addr m 2 a1 ->
    a2 = a1 ->
    read_half (write_half m a1 v) a2 = v.
Proof. wrap ListMemoryNatAddr.write_read_half_eq. Qed.

Lemma write_read_half_ne: forall w m (a1 a2: word w) v,
    valid_addr m 2 a1 ->
    valid_addr m 2 a2 ->
    a2 <> a1 ->
    read_half (write_half m a1 v) a2 = read_half m a2.
Proof. wrap ListMemoryNatAddr.write_read_half_ne. Qed.

Lemma write_half_preserves_mem_size: forall w m (a: word w) v,
    valid_addr m 2 a ->
    mem_size (write_half m a v) = mem_size m.
Proof. wrap ListMemoryNatAddr.write_half_preserves_mem_size. Qed.

Lemma write_read_word_eq: forall w m (a1 a2: word w) v,
    valid_addr m 4 a1 ->
    a2 = a1 ->
    read_word (write_word m a1 v) a2 = v.
Proof. wrap ListMemoryNatAddr.write_read_word_eq. Qed.

Lemma write_read_word_ne: forall w m (a1 a2: word w) v,
    valid_addr m 4 a1 ->
    valid_addr m 4 a2 ->
    a2 <> a1 ->
    read_word (write_word m a1 v) a2 = read_word m a2.
Proof. wrap ListMemoryNatAddr.write_read_word_ne. Qed.

Lemma write_word_preserves_mem_size: forall w m (a: word w) v,
    valid_addr m 4 a ->
    mem_size (write_word m a v) = mem_size m.
Proof. wrap ListMemoryNatAddr.write_word_preserves_mem_size. Qed.

Lemma write_read_double_eq: forall w m (a1 a2: word w) v,
    valid_addr m 8 a1 ->
    a2 = a1 ->
    read_double (write_double m a1 v) a2 = v.
Proof. wrap ListMemoryNatAddr.write_read_double_eq. Qed.

Lemma write_read_double_ne: forall w m (a1 a2: word w) v,
    valid_addr m 8 a1 ->
    valid_addr m 8 a2 ->
    a2 <> a1 ->
    read_double (write_double m a1 v) a2 = read_double m a2.
Proof. wrap ListMemoryNatAddr.write_read_double_ne. Qed.

Lemma write_double_preserves_mem_size: forall w m (a: word w) v,
    valid_addr m 8 a ->
    mem_size (write_double m a v) = mem_size m.
Proof. wrap ListMemoryNatAddr.write_double_preserves_mem_size. Qed.
