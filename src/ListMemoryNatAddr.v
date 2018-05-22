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

  Definition write_byte'(m: mem)(a: nat)(v: word 8): mem :=
    (firstn a m) ++ [v] ++ (skipn (S a) m).

  (* fix for the case when a is out of bounds to make sure length is always preserved:
     allows for _preserves_mem_size lemmas with no hypotheses, and ensures things which
     should not work because out of bounds writes-then-reads don't work *)
  Definition write_byte(m: mem)(a: nat)(v: word 8): mem :=
    firstn (length m) (write_byte' m a v).
  
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

  Lemma const_mem_mem_size: forall default size,
      mem_size (const_mem default size) = size.
  Proof.
    intros. unfold mem_size. induction size; simpl; auto.
  Qed.

  Definition zero_mem: nat -> mem := const_mem $0.

End Memory.


Lemma write_read_byte_eq': forall m a1 a2 v,
    a1 < mem_size m ->
    a2 = a1 ->
    read_byte (write_byte' m a1 v) a2 = v.
Proof.
  intros. subst. unfold write_byte', read_byte, mem_size in *.
  pose proof (@firstn_length_le _ m a1).
  rewrite app_nth2 by omega.
  rewrite H0 by omega.
  replace (a1 - a1) with 0 by omega.
  reflexivity.
Qed.

Lemma write_read_byte_ne': forall m a1 a2 v,
    a1 < mem_size m ->
    a2 < mem_size m ->
    a2 <> a1 ->
    read_byte (write_byte' m a1 v) a2 = read_byte m a2.
Proof.
  intros. unfold write_byte', read_byte, mem_size in *.
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

Lemma skipn_length_le: forall A n (l: list A),
    n <= length l ->
    length (skipn n l) = length l - n.
Proof.
  induction n; intros.
  - simpl. omega.
  - simpl. destruct l; [simpl in *; omega|].
    simpl in *.
    apply IHn; omega.
Qed.

Lemma write_byte_preserves_mem_size': forall m a v,
    a < mem_size m ->
    mem_size (write_byte' m a v) = mem_size m.
Proof.
  intros. unfold mem_size, write_byte' in *.
  repeat rewrite app_length.
  rewrite firstn_length_le by omega.
  rewrite skipn_length_le by omega.
  simpl.
  omega.
Qed.

Lemma write_read_byte_eq: forall m a1 a2 v,
    a1 < mem_size m ->
    a2 = a1 ->
    read_byte (write_byte m a1 v) a2 = v.
Proof.
  intros. unfold write_byte in *.
  erewrite <- write_byte_preserves_mem_size' by eassumption.
  unfold mem_size.
  rewrite firstn_all.
  apply write_read_byte_eq'; assumption.
Qed.

Lemma write_read_byte_ne: forall m a1 a2 v,
    a1 < mem_size m ->
    a2 < mem_size m ->
    a2 <> a1 ->
    read_byte (write_byte m a1 v) a2 = read_byte m a2.
Proof.
  intros. unfold write_byte in *.
  erewrite <- write_byte_preserves_mem_size'; [|exact H].
  unfold mem_size.
  rewrite firstn_all.
  apply write_read_byte_ne'; assumption.
Qed.

Lemma write_byte_preserves_mem_size: forall m a v,
    mem_size (write_byte m a v) = mem_size m.
Proof.
  intros. unfold write_byte.
  assert (a < mem_size m \/ a >= mem_size m) as C by omega. destruct C as [H | H].
  - pose proof write_byte_preserves_mem_size' as P.
    specialize P with (1 := H).
    unfold mem_size in *.
    rewrite <- (P v) at 1.
    rewrite firstn_all.
    apply P.
  - unfold mem_size in *.
    apply firstn_length_le.
    unfold write_byte'.
    rewrite? app_length.
    rewrite firstn_length.
    pose proof (Nat.min_spec a (length m)).
    omega.
Qed.

Lemma write_read_half_eq: forall m a1 a2 v,
    a1 + 1 < mem_size m ->
    a2 = a1 ->
    read_half (write_half m a1 v) a2 = v.
Proof.
  intros. subst. unfold write_half, read_half in *.
  pose proof H.
  rewrite (write_read_byte_eq _ (a1 + 1) (a1 + 1)); try reflexivity.
  - rewrite write_read_byte_ne; try omega.
    + rewrite write_read_byte_eq; try reflexivity; try omega.
      apply (combine_split 8 8).
    + rewrite write_byte_preserves_mem_size; omega.
    + rewrite write_byte_preserves_mem_size; omega.
  - rewrite write_byte_preserves_mem_size; omega.
Qed.

Lemma write_read_half_ne: forall m a1 a2 v,
    a1 + 1 < mem_size m ->
    a1 mod 2 = 0 ->
    a2 + 1 < mem_size m ->
    a2 mod 2 = 0 ->
    a2 <> a1 ->
    read_half (write_half m a1 v) a2 = read_half m a2.
Proof.
  intros. unfold write_half, read_half in *.
  f_equal.
  - rewrite write_read_byte_ne.
    + apply write_read_byte_ne; omega.
    + rewrite write_byte_preserves_mem_size; omega.
    + rewrite write_byte_preserves_mem_size; omega.
    + intro. subst. rewrite Nat.add_mod in H2; try omega.
      rewrite H0 in H2.
      simpl in H2.
      discriminate.
  - rewrite write_read_byte_ne.
    + apply write_read_byte_ne; try omega.
      intro. subst. rewrite Nat.add_mod in H0; try omega.
      rewrite H2 in H0.
      simpl in H0.
      discriminate.
    + rewrite write_byte_preserves_mem_size; omega.
    + rewrite write_byte_preserves_mem_size; omega.
    + omega.
Qed.

Lemma add_mod_r: forall a m,
    m <> 0 ->
    (a + m) mod m = a mod m.
Proof.
  intros.
  rewrite Nat.add_mod by assumption.
  rewrite Nat.mod_same by assumption.
  rewrite Nat.add_0_r.
  apply Nat.mod_mod.
  assumption.
Qed.

Lemma weaken_alignment: forall n al,
    n mod (al * 2) = 0 ->
    al <> 0 ->
    n mod al = 0.
Proof.
  intros.
  pose proof H.
  apply Nat.mod_divides in H; try omega.
  destruct H as [n' H]. subst.
  rewrite <- Nat.mul_assoc.
  rewrite Nat.mul_mod by omega.
  rewrite Nat.mod_same by assumption.
  apply Nat.mod_0_l.
  assumption.
Qed.  

Lemma write_half_preserves_mem_size: forall m a v,
    mem_size (write_half m a v) = mem_size m.
Proof.
  intros. unfold write_half, mem_size in *.
  repeat rewrite write_byte_preserves_mem_size; unfold mem_size; omega.
Qed.

Lemma diviBy4_implies_diviBy2: forall n,
    n mod 4 = 0 ->
    n mod 2 = 0.
Proof.
  intros.
  apply weaken_alignment; [assumption | omega].
Qed.  

Lemma write_read_word_eq: forall m a1 a2 v,
    a1 + 4 <= mem_size m ->
    a1 mod 4 = 0 ->
    a2 = a1 ->
    read_word (write_word m a1 v) a2 = v.
Proof.
  intros. subst. unfold write_word, read_word in *.
  pose proof H.
  rewrite (write_read_half_eq _ (a1 + 2) (a1 + 2)); try reflexivity.
  - rewrite write_read_half_ne; try omega.
    + rewrite write_read_half_eq; try reflexivity; try omega.
      apply (combine_split 16 16).
    + rewrite write_half_preserves_mem_size; omega.
    + apply diviBy4_implies_diviBy2 in H0. rewrite Nat.add_mod by omega.
      rewrite H0.
      reflexivity.
    + rewrite write_half_preserves_mem_size; omega.
    + apply diviBy4_implies_diviBy2. assumption.
  - rewrite write_half_preserves_mem_size; omega.
Qed.

Lemma write_read_word_ne: forall m a1 a2 v,
    a1 + 4 <= mem_size m ->
    a1 mod 4 = 0 ->
    a2 + 4 <= mem_size m ->
    a2 mod 4 = 0 ->
    a2 <> a1 ->
    read_word (write_word m a1 v) a2 = read_word m a2.
Proof.
  intros. unfold write_word, read_word in *.
  pose proof (diviBy4_implies_diviBy2 _ H0).
  pose proof (diviBy4_implies_diviBy2 _ H2).
  f_equal.
  - rewrite write_read_half_ne.
    + apply write_read_half_ne; omega.
    + rewrite write_half_preserves_mem_size; omega.
    + rewrite Nat.add_mod by omega.
      rewrite H4.
      reflexivity.
    + rewrite write_half_preserves_mem_size; omega.
    + assumption.
    + intro. subst. rewrite Nat.add_mod in H2; try omega.
      rewrite H0 in H2.
      simpl in H2.
      discriminate.
  - rewrite write_read_half_ne.
    + apply write_read_half_ne; try omega.
      * rewrite add_mod_r; omega.
      * intro. subst. rewrite Nat.add_mod in H0; try omega.
        rewrite H2 in H0.
        simpl in H0.
        discriminate.
    + rewrite write_half_preserves_mem_size; omega.
    + rewrite add_mod_r; omega.
    + rewrite write_half_preserves_mem_size; omega.
    + rewrite add_mod_r; omega.
    + omega.
Qed.


Lemma write_word_preserves_mem_size: forall m a v,
    mem_size (write_word m a v) = mem_size m.
Proof.
  intros. unfold write_word, mem_size in *.
  repeat rewrite write_half_preserves_mem_size; unfold mem_size; omega.
Qed.

Lemma diviBy8_implies_diviBy4: forall n,
    n mod 8 = 0 ->
    n mod 4 = 0.
Proof.
  intros.
  apply weaken_alignment; [assumption | omega].
Qed.  

Lemma write_read_double_eq: forall m a1 a2 v,
    a1 + 8 <= mem_size m ->
    a1 mod 8 = 0 ->
    a2 = a1 ->
    read_double (write_double m a1 v) a2 = v.
Proof.
  intros. subst. unfold write_double, read_double in *.
  pose proof H.
  rewrite (write_read_word_eq _ (a1 + 4) (a1 + 4)); try reflexivity.
  - rewrite write_read_word_ne; try omega.
    + rewrite write_read_word_eq; try reflexivity; try omega.
      * apply (combine_split 32 32).
      * apply diviBy8_implies_diviBy4. assumption.
    + rewrite write_word_preserves_mem_size; omega.
    + apply diviBy8_implies_diviBy4 in H0. rewrite Nat.add_mod by omega.
      rewrite H0.
      reflexivity.
    + rewrite write_word_preserves_mem_size; omega.
    + apply diviBy8_implies_diviBy4. assumption.
  - rewrite write_word_preserves_mem_size; omega.
  - rewrite add_mod_r by omega.
    apply diviBy8_implies_diviBy4. assumption.
Qed.

Lemma write_read_double_ne: forall m a1 a2 v,
    a1 + 8 <= mem_size m ->
    a1 mod 8 = 0 ->
    a2 + 8 <= mem_size m ->
    a2 mod 8 = 0 ->
    a2 <> a1 ->
    read_double (write_double m a1 v) a2 = read_double m a2.
Proof.
  intros. unfold write_double, read_double in *.
  pose proof (diviBy8_implies_diviBy4 _ H0).
  pose proof (diviBy8_implies_diviBy4 _ H2).
  f_equal.
  - rewrite write_read_word_ne.
    + apply write_read_word_ne; omega.
    + rewrite write_word_preserves_mem_size; omega.
    + rewrite Nat.add_mod by omega.
      rewrite H4.
      reflexivity.
    + rewrite write_word_preserves_mem_size; omega.
    + assumption.
    + intro. subst. rewrite Nat.add_mod in H2; try omega.
      rewrite H0 in H2.
      simpl in H2.
      discriminate.
  - rewrite write_read_word_ne.
    + apply write_read_word_ne; try omega.
      * rewrite add_mod_r; omega.
      * intro. subst. rewrite Nat.add_mod in H0; try omega.
        rewrite H2 in H0.
        simpl in H0.
        discriminate.
    + rewrite write_word_preserves_mem_size; omega.
    + rewrite add_mod_r; omega.
    + rewrite write_word_preserves_mem_size; omega.
    + rewrite add_mod_r; omega.
    + omega.
Qed.

Lemma write_double_preserves_mem_size: forall m a v,
    mem_size (write_double m a v) = mem_size m.
Proof.
  intros. unfold write_double, mem_size in *.
  repeat rewrite write_word_preserves_mem_size; unfold mem_size; omega.
Qed.
