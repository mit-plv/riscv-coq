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

Lemma mem_size_write_byte_non_zero: forall m a v,
    ListMemoryNatAddr.mem_size (ListMemoryNatAddr.write_byte m a v) > 0.
Proof.
  intros.
  unfold ListMemoryNatAddr.write_byte. unfold ListMemoryNatAddr.mem_size.
  rewrite? app_length. simpl. omega.
Qed.

Lemma mem_size_write_half_non_zero: forall m a v,
    ListMemoryNatAddr.mem_size (ListMemoryNatAddr.write_half m a v) > 0.
Proof.
  intros.
  unfold ListMemoryNatAddr.write_half. unfold ListMemoryNatAddr.mem_size.
  unfold ListMemoryNatAddr.write_byte.
  rewrite? app_length. simpl. omega.
Qed.

Lemma mem_size_write_word_non_zero: forall m a v,
    ListMemoryNatAddr.mem_size (ListMemoryNatAddr.write_word m a v) > 0.
Proof.
  intros.
  unfold ListMemoryNatAddr.write_word. unfold ListMemoryNatAddr.mem_size.
  unfold ListMemoryNatAddr.write_half. unfold ListMemoryNatAddr.mem_size.
  unfold ListMemoryNatAddr.write_byte.
  rewrite? app_length. simpl. omega.
Qed.

Lemma mem_size_write_double_non_zero: forall m a v,
    ListMemoryNatAddr.mem_size (ListMemoryNatAddr.write_double m a v) > 0.
Proof.
  intros.
  unfold ListMemoryNatAddr.write_double. unfold ListMemoryNatAddr.mem_size.
  unfold ListMemoryNatAddr.write_word. unfold ListMemoryNatAddr.mem_size.
  unfold ListMemoryNatAddr.write_half. unfold ListMemoryNatAddr.mem_size.
  unfold ListMemoryNatAddr.write_byte.
  rewrite? app_length. simpl. omega.
Qed.

Section Memory.

  Context {w: nat}. (* bit width of memory addresses *)

  Definition mem := { m: ListMemoryNatAddr.mem | ListMemoryNatAddr.mem_size m > 0 }.
  Definition max_addr(m: mem): word w :=
    natToWord w (pred (ListMemoryNatAddr.mem_size (proj1_sig m))).

  Definition read_byte(m: mem)(a: word w): word 8 :=
    ListMemoryNatAddr.read_byte (proj1_sig m) (wordToNat a).

  Definition read_half(m: mem)(a: word w): word 16 :=
    ListMemoryNatAddr.read_half (proj1_sig m) (wordToNat a).

  Definition read_word(m: mem)(a: word w): word 32 :=
    ListMemoryNatAddr.read_word (proj1_sig m) (wordToNat a).

  Definition read_double(m: mem)(a: word w): word 64 :=
    ListMemoryNatAddr.read_double (proj1_sig m) (wordToNat a).

  Definition write_byte(m: mem)(a: word w)(v: word 8): mem.
    refine (exist _ (ListMemoryNatAddr.write_byte (proj1_sig m) (wordToNat a) v) _).
    apply mem_size_write_byte_non_zero.
  Defined.

  Definition write_half(m: mem)(a: word w)(v: word 16): mem.
    refine (exist _ (ListMemoryNatAddr.write_half (proj1_sig m) (wordToNat a) v) _).
    apply mem_size_write_half_non_zero.
  Defined.

  Definition write_word(m: mem)(a: word w)(v: word 32): mem.
    refine (exist _ (ListMemoryNatAddr.write_word (proj1_sig m) (wordToNat a) v) _).
    apply mem_size_write_word_non_zero.
  Defined.

  Definition write_double(m: mem)(a: word w)(v: word 64): mem.
    refine (exist _ (ListMemoryNatAddr.write_double (proj1_sig m) (wordToNat a) v) _).
    apply mem_size_write_double_non_zero.
  Defined.

  Definition const_mem(default: word 8)(max_addr: nat): mem.
    refine (exist _ (ListMemoryNatAddr.const_mem default (S max_addr)) _).
    simpl. apply gt_Sn_O.
  Defined.

  Definition zero_mem: nat -> mem := const_mem $0.

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
    (a1 <= (max_addr m))%word ->
    a2 = a1 ->
    read_byte (write_byte m a1 v) a2 = v.
Proof.
  intros.
  unfold max_addr, ListMemoryNatAddr.mem_size in *.
  destruct m as [m P]. simpl in *. unfold ListMemoryNatAddr.mem_size in *.
  apply ListMemoryNatAddr.write_read_byte_eq.
  - simpl.
    destruct m; simpl in *; [omega|]. unfold ListMemoryNatAddr.mem_size.
    apply le_lt_n_Sm.
    apply le_word_le_nat.
    assumption.
  - f_equal. assumption.
Qed.

Lemma write_read_byte_ne: forall w m (a1 a2: word w) v,
    (a1 <= (max_addr m))%word ->
    (a2 <= (max_addr m))%word ->
    a2 <> a1 ->
    read_byte (write_byte m a1 v) a2 = read_byte m a2.
Proof.
  intros.
  unfold max_addr, ListMemoryNatAddr.mem_size in *.
  destruct m as [m P]. simpl in *. unfold ListMemoryNatAddr.mem_size in *.
  destruct m; simpl in *; [omega|].
  apply ListMemoryNatAddr.write_read_byte_ne; simpl; unfold ListMemoryNatAddr.mem_size.
  - apply le_lt_n_Sm.
    apply le_word_le_nat.
    assumption.
  - apply le_lt_n_Sm.
    apply le_word_le_nat.
    assumption.
  - intro C. apply wordToNat_inj in C. contradiction.
Qed.

Lemma write_byte_preserves_max_addr: forall w m (a: word w) v,
    (a <= (max_addr m))%word ->
    @max_addr w (write_byte m a v) = @max_addr w m.
Proof.
  intros.
  unfold max_addr, write_byte in *.
  do 2 f_equal.
  apply ListMemoryNatAddr.write_byte_preserves_mem_size.
  destruct m as [m P]. simpl in *. unfold ListMemoryNatAddr.mem_size in *.
  destruct m; simpl in *; [omega|].
  apply le_lt_n_Sm.
  apply le_word_le_nat.
  assumption.
Qed.

Lemma write_read_half_eq: forall w m (a1 a2: word w) v,
    (a1 <= max_addr m ^- $1)%word ->
    a2 = a1 ->
    read_half (write_half m a1 v) a2 = v.
Proof.
  intros.
  destruct m as [m P]. unfold ListMemoryNatAddr.mem_size in *.
  apply ListMemoryNatAddr.write_read_half_eq.
  - simpl.
    destruct m; simpl in *; [omega|]. unfold ListMemoryNatAddr.mem_size.
    apply le_lt_n_Sm.
    unfold max_addr, ListMemoryNatAddr.mem_size in H.
    simpl in H.
    unfold wminus in H.
    (* minus is a bad idea because bigger minuses might run below 0 *)
Abort.

Lemma write_read_half_eq: forall w m (a1 a2: word w) v,
    (a1 ^+ $1 <= max_addr m)%word ->
    a1 ^% $2 = $0 ->
    a2 = a1 ->
    read_half (write_half m a1 v) a2 = v.
Proof.
  intros.
  destruct m as [m P]. unfold ListMemoryNatAddr.mem_size in *.
  apply ListMemoryNatAddr.write_read_half_eq.
  - simpl.
    destruct m; simpl in *; [omega|]. unfold ListMemoryNatAddr.mem_size.
    apply le_lt_n_Sm.
    unfold max_addr, ListMemoryNatAddr.mem_size in H.
    simpl in H.
    (* if a1=max_addr, the ^+ $1 in H overflows and the lemma doesn't hold,
       unless we add and use mod hypotheses *)
    unfold wmod in H0.
Abort.

Definition valid_addr{w}(m: mem)(alignment: nat)(addr: word w): Prop :=
  wordToNat addr + alignment <= length (proj1_sig m) /\
  (wordToNat addr) mod alignment = 0.

Lemma write_read_half_eq: forall w m (a1 a2: word w) v,
    valid_addr m 2 a1 ->
    a2 = a1 ->
    read_half (write_half m a1 v) a2 = v.
Proof.
  intros. destruct H.
  destruct m as [m P]. unfold ListMemoryNatAddr.mem_size in *. simpl in H.
  apply ListMemoryNatAddr.write_read_half_eq.
  - simpl.
    unfold ListMemoryNatAddr.mem_size. omega.
  - f_equal. assumption.
Qed.  

Lemma write_read_half_ne: forall w m (a1 a2: word w) v,
    valid_addr m 2 a1 ->
    valid_addr m 2 a2 ->
    a2 <> a1 ->
    read_half (write_half m a1 v) a2 = read_half m a2.
Proof.
  intros. destruct H. destruct H0.
  destruct m as [m P]. unfold ListMemoryNatAddr.mem_size in *. simpl in H, H0.
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