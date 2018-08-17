Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Require Import riscv.Utility.
Require Import riscv.util.Monads.
Require Import riscv.Memory.
Import ListNotations.
Local Open Scope Z_scope.


Section Memory.

  Definition mem := list (word 8).
  Definition mem_size(m: mem): Z := Zlength m.

  Definition read_byte(m: mem)(a: Z): word 8 := Znth m a (ZToWord _ 0).

  Definition write_byte'(m: mem)(a: Z)(v: word 8): mem :=
    (Zfirstn a m) ++ [v] ++ (Zskipn (a + 1) m).

  (* fix for the case when a is out of bounds to make sure length is always preserved:
     allows for _preserves_mem_size lemmas with no hypotheses, and ensures things which
     should not work because out of bounds writes-then-reads don't work *)
  Definition write_byte(m: mem)(a: Z)(v: word 8): mem :=
    firstn (length m) (write_byte' m a v).
  
  Definition read_half(m: mem)(a: Z): word 16 :=
    let v0 := read_byte m a in let v1 := read_byte m (a + 1) in wappend v1 v0.
  Definition read_word(m: mem)(a: Z): word 32 :=
    let v0 := read_half m a in let v1 := read_half m (a + 2) in wappend v1 v0.
  Definition read_double(m: mem)(a: Z): word 64 :=
    let v0 := read_word m a in let v1 := read_word m (a + 4) in wappend v1 v0.

  Definition write_half(m: mem)(a: Z)(v: word 16): mem :=
    let m := write_byte m a (lobits 8 v) in write_byte m (a + 1) (hibits 8 v).
  Definition write_word(m: mem)(a: Z)(v: word 32): mem :=
    let m := write_half m a (lobits 16 v) in write_half m (a + 2) (hibits 16 v).
  Definition write_double(m: mem)(a: Z)(v: word 64): mem :=
    let m := write_word m a (lobits 32 v) in write_word m (a + 4) (hibits 32 v).

  Definition const_mem(default: word 8)(size: Z): mem :=
    map_range (fun _: Z => default) size.

  Lemma const_mem_mem_size: forall default size,
      0 <= size ->
      mem_size (const_mem default size) = size.
  Proof.
    intros. unfold mem_size, const_mem. apply Zlength_map_range. assumption.
  Qed.

  Definition zero_mem: Z -> mem := const_mem (ZToWord 8 0).

End Memory.

Ltac omega' := zify; rewrite Z2Nat.id in *; omega.

Lemma write_read_byte_eq': forall m a1 a2 v,
    0 <= a1 < mem_size m ->
    a2 = a1 ->
    read_byte (write_byte' m a1 v) a2 = v.
Proof.
  intros. subst. unfold write_byte', read_byte, mem_size in *.
  unfold Zfirstn, Zskipn, Znth, Zlength in *.
  pose proof (@firstn_length_le _ m (Z.to_nat a1)).
  rewrite app_nth2 by omega'.
  rewrite H0 by omega'.
  replace (Z.to_nat a1 - Z.to_nat a1)%nat with 0%nat by omega.
  reflexivity.
Qed.

Lemma Z_bounds_to_nat_bound: forall (a: Z) (n: nat),
    0 <= a < Z.of_nat n ->
    (Z.to_nat a < n)%nat.
Proof.
  intros. omega'.
Qed.

Lemma Z_ne_to_nat_ne: forall (a b: Z),
    0 <= a ->
    0 <= b ->
    a <> b ->
    Z.to_nat a <> Z.to_nat b.
Proof.
  intros. intro. apply H1. apply Z2Nat.inj; assumption.
Qed.

Lemma write_read_byte_ne': forall m a1 a2 v,
    0 <= a1 < mem_size m ->
    0 <= a2 < mem_size m ->
    a2 <> a1 ->
    read_byte (write_byte' m a1 v) a2 = read_byte m a2.
Proof.
  intros. unfold write_byte', read_byte, mem_size in *.
  pose proof (@firstn_length_le _ m (Z.to_nat a1)).
  pose proof (@firstn_length_le _ m (Z.to_nat a2)).
  unfold Znth, Zfirstn, Zskipn, Zlength in *.
  rewrite Z2Nat.inj_add by omega.
  apply Z_ne_to_nat_ne in H1; [|omega..].
  apply Z_bounds_to_nat_bound in H.
  apply Z_bounds_to_nat_bound in H0.
  remember (Z.to_nat a1) as a1'. clear Heqa1' a1. rename a1' into a1.
  remember (Z.to_nat a2) as a2'. clear Heqa2' a2. rename a2' into a2.
  replace (a1 + Z.to_nat 1)%nat with (S a1) by omega'.
  assert (a2 < a1 \/ a1 < a2 < length m)%nat as P by omega.
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
    replace (a2 - a1 - length [v])%nat with (a2 - (S a1))%nat by (simpl; omega).
    clear H2 H3.
    generalize dependent m. generalize dependent a1.
    induction a2; intros.
    + omega.
    + replace (S a2 - S a1)%nat with (a2 - a1)%nat by omega.
      destruct a1.
      * replace (a2 - 0)%nat with a2 by omega. destruct m; [simpl in *; omega|reflexivity].
      * destruct m; [simpl in *; omega|].
        change (skipn (S (S a1)) (w :: m)) with (skipn (S a1) m).
        change (nth (S a2) (w :: m)) with (nth a2 m).
        apply IHa2; simpl in *; try omega.
Qed.

Lemma skipn_length_le: forall A n (l: list A),
    (n <= length l)%nat ->
    length (skipn n l) = (length l - n)%nat.
Proof.
  induction n; intros.
  - simpl. omega.
  - simpl. destruct l; [simpl in *; omega|].
    simpl in *.
    apply IHn; omega.
Qed.

Lemma write_byte_preserves_mem_size': forall m a v,
    0 <= a < mem_size m ->
    mem_size (write_byte' m a v) = mem_size m.
Proof.
  intros. unfold mem_size, write_byte' in *.
  unfold Zlength, Zfirstn, Zskipn in *.
  repeat rewrite app_length.
  rewrite firstn_length_le by omega'.
  rewrite skipn_length_le by omega'.
  simpl.
  omega'.
Qed.

Lemma firstn_all_write_byte': forall m a1 v,
    0 <= a1 < mem_size m ->
    firstn (length m) (write_byte' m a1 v) = write_byte' m a1 v.
Proof.
  intros.
  replace (length m) with (length (write_byte' m a1 v)).
  - rewrite firstn_all. reflexivity.
  - pose proof (write_byte_preserves_mem_size' m a1 v H) as P.
    unfold mem_size, Zlength in *.
    apply Nat2Z.inj in P.
    assumption.
Qed.

Lemma write_read_byte_eq: forall m a1 a2 v,
    0 <= a1 < mem_size m ->
    a2 = a1 ->
    read_byte (write_byte m a1 v) a2 = v.
Proof.
  intros. unfold write_byte in *.
  erewrite <- write_read_byte_eq' by eassumption.
  rewrite firstn_all_write_byte' by assumption.
  reflexivity.
Qed.

Lemma write_read_byte_ne: forall m a1 a2 v,
    0 <= a1 < mem_size m ->
    0 <= a2 < mem_size m ->
    a2 <> a1 ->
    read_byte (write_byte m a1 v) a2 = read_byte m a2.
Proof.
  intros. unfold write_byte in *.
  rewrite <- (write_read_byte_ne' m a1 a2 v);
    rewrite? firstn_all_write_byte' by assumption;
    rewrite? write_byte_preserves_mem_size' by assumption;
    [reflexivity | eassumption ..].
Qed.

Lemma Z2Nat_nonpos: forall (a: Z),
    a <= 0 ->
    Z.to_nat a = 0%nat.
Proof.
  intros.
  destruct a.
  - reflexivity.
  - lia.
  - apply Z2Nat.inj_neg.
Qed.

Lemma write_byte_preserves_mem_size: forall m a v,
    mem_size (write_byte m a v) = mem_size m.
Proof.
  intros. unfold write_byte.
  assert (a < 0 \/ 0 <= a < mem_size m \/ a >= mem_size m) as C by omega.
  destruct C as [H | [H | H]].
  - unfold write_byte', Zfirstn, Zskipn.
    rewrite! Z2Nat_nonpos by omega.
    simpl.
    unfold mem_size, Zlength in *.
    apply Znat.inj_eq.
    apply firstn_length_le.
    simpl.
    repeat constructor.
  - pose proof write_byte_preserves_mem_size' as P.
    specialize P with (1 := H).
    unfold mem_size, Zlength in *.
    rewrite <- (P v) at 1.
    rewrite firstn_all_write_byte' by assumption.
    reflexivity.
  - unfold mem_size, Zlength in *.
    apply Znat.inj_eq.
    apply firstn_length_le.
    unfold write_byte', Zfirstn, Zskipn.
    rewrite? app_length.
    rewrite firstn_length.
    omega'.
Qed.

Lemma write_read_half_eq: forall m a1 a2 v,
    0 <= a1 ->
    a1 + 1 < mem_size m ->
    a2 = a1 ->
    read_half (write_half m a1 v) a2 = v.
Proof.
  intros. subst. unfold write_half, read_half in *.
  pose proof H.
  rewrite (write_read_byte_eq _ (a1 + 1) (a1 + 1)); try reflexivity.
  - rewrite write_read_byte_ne; try omega.
    + rewrite write_read_byte_eq; try reflexivity; try omega.
      apply (wappend_split 8 8); omega.
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
    0 <= a1 ->
    0 <= a2 ->
    read_half (write_half m a1 v) a2 = read_half m a2.
Proof.
  intros. unfold write_half, read_half in *.
  f_equal.
  - rewrite write_read_byte_ne.
    + apply write_read_byte_ne; try omega.
      intro. subst. rewrite Z.add_mod in H0; try omega.
      rewrite H2 in H0.
      simpl in H0.
      discriminate.
    + rewrite write_byte_preserves_mem_size; omega.
    + rewrite write_byte_preserves_mem_size; omega.
    + omega.
  - rewrite write_read_byte_ne.
    + apply write_read_byte_ne; omega.
    + rewrite write_byte_preserves_mem_size; omega.
    + rewrite write_byte_preserves_mem_size; omega.
    + intro. subst. rewrite Z.add_mod in H2; try omega.
      rewrite H0 in H2.
      simpl in H2.
      discriminate.
Qed.

Lemma add_mod_r: forall a m,
    m <> 0 ->
    (a + m) mod m = a mod m.
Proof.
  intros.
  rewrite Z.add_mod by assumption.
  rewrite Z.mod_same by assumption.
  rewrite Z.add_0_r.
  apply Z.mod_mod.
  assumption.
Qed.

Lemma weaken_alignment: forall n al,
    n mod (al * 2) = 0 ->
    al <> 0 ->
    n mod al = 0.
Proof.
  intros.
  pose proof H.
  apply Z.mod_divide in H; try omega.
  destruct H as [n' H]. subst.
  replace (n' * (al * 2)) with (n' * 2 * al) by ring.
  apply Z.mod_mul.
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
    0 <= a1 ->
    read_word (write_word m a1 v) a2 = v.
Proof.
  intros. subst. unfold write_word, read_word in *.
  pose proof H.
  rewrite (write_read_half_eq _ (a1 + 2) (a1 + 2)); try reflexivity; try omega.
  - rewrite write_read_half_ne; try omega.
    + rewrite write_read_half_eq; try reflexivity; try omega.
      apply (wappend_split 16 16); omega.
    + rewrite write_half_preserves_mem_size; omega.
    + apply diviBy4_implies_diviBy2 in H0. rewrite Z.add_mod by omega.
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
    0 <= a1 ->
    0 <= a2 ->
    read_word (write_word m a1 v) a2 = read_word m a2.
Proof.
  intros. unfold write_word, read_word in *.
  rename H4 into H6, H5 into H7.
  pose proof (diviBy4_implies_diviBy2 _ H0).
  pose proof (diviBy4_implies_diviBy2 _ H2).
  f_equal.
  - rewrite write_read_half_ne.
    + apply write_read_half_ne; try omega.
      * rewrite add_mod_r; omega.
      * intro. subst. rewrite Z.add_mod in H0; try omega.
        rewrite H2 in H0.
        simpl in H0.
        discriminate.
    + rewrite write_half_preserves_mem_size; omega.
    + rewrite add_mod_r; omega.
    + rewrite write_half_preserves_mem_size; omega.
    + rewrite add_mod_r; omega.
    + omega.
    + omega.
    + omega.
  - rewrite write_read_half_ne.
    + apply write_read_half_ne; omega.
    + rewrite write_half_preserves_mem_size; omega.
    + rewrite Z.add_mod by omega.
      rewrite H4.
      reflexivity.
    + rewrite write_half_preserves_mem_size; omega.
    + assumption.
    + intro. subst. rewrite Z.add_mod in H2; try omega.
      rewrite H0 in H2.
      simpl in H2.
      discriminate.
    + omega.
    + assumption.
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
    0 <= a1 ->
    read_double (write_double m a1 v) a2 = v.
Proof.
  intros. subst. unfold write_double, read_double in *.
  pose proof H.
  rewrite (write_read_word_eq _ (a1 + 4) (a1 + 4)); try reflexivity; try omega.
  - rewrite write_read_word_ne; try omega.
    + rewrite write_read_word_eq; try reflexivity; try omega.
      * apply (wappend_split 32 32); omega.
      * apply diviBy8_implies_diviBy4. assumption.
    + rewrite write_word_preserves_mem_size; omega.
    + apply diviBy8_implies_diviBy4 in H0. rewrite Z.add_mod by omega.
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
    0 <= a1 ->
    0 <= a2 ->
    read_double (write_double m a1 v) a2 = read_double m a2.
Proof.
  intros. unfold write_double, read_double in *.
  rename H4 into H6, H5 into H7.
  pose proof (diviBy8_implies_diviBy4 _ H0).
  pose proof (diviBy8_implies_diviBy4 _ H2).
  f_equal.
  - rewrite write_read_word_ne.
    + apply write_read_word_ne; try omega.
      * rewrite add_mod_r; omega.
      * intro. subst. rewrite Z.add_mod in H0; try omega.
        rewrite H2 in H0.
        simpl in H0.
        discriminate.
    + rewrite write_word_preserves_mem_size; omega.
    + rewrite add_mod_r; omega.
    + rewrite write_word_preserves_mem_size; omega.
    + rewrite add_mod_r; omega.
    + omega.
    + omega.
    + omega.
  - rewrite write_read_word_ne.
    + apply write_read_word_ne; omega.
    + rewrite write_word_preserves_mem_size; omega.
    + rewrite Z.add_mod by omega.
      rewrite H4.
      reflexivity.
    + rewrite write_word_preserves_mem_size; omega.
    + assumption.
    + intro. subst. rewrite Z.add_mod in H2; try omega.
      rewrite H0 in H2.
      simpl in H2.
      discriminate.
    + omega.
    + omega.
Qed.

Lemma write_double_preserves_mem_size: forall m a v,
    mem_size (write_double m a v) = mem_size m.
Proof.
  intros. unfold write_double, mem_size in *.
  repeat rewrite write_word_preserves_mem_size; unfold mem_size; omega.
Qed.
