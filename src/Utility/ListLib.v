Require Import Coq.Lists.List Coq.ZArith.ZArith coqutil.Z.Lia coqutil.Z.Lia.

Open Scope Z_scope.


Definition Znth_error{A: Type}(l: list A)(i: Z): option A :=
  match i with
  | Zneg _ => None
  | _ => nth_error l (Z.to_nat i)
  end.

(*
Definition Znth{T: Type}(l: list T)(i: Z)(default: T): T :=
  match Znth_error l i with
  | Some x => x
  | None => default
  end.
*)
Definition Znth{T: Type}(l: list T)(i: Z)(default: T): T := nth (Z.to_nat i) l default.

Definition Zfirstn{T: Type}(n: Z)(l: list T): list T := firstn (Z.to_nat n) l.

Definition Zskipn{T: Type}(n: Z)(l: list T): list T := skipn (Z.to_nat n) l.

Lemma list_elementwise_same: forall A (l1 l2: list A),
    (forall i, nth_error l1 i = nth_error l2 i) ->
    l1 = l2.
Proof.
  induction l1; intros.
  - specialize (H O). simpl in H. destruct l2; congruence.
  - pose proof H as G.
    specialize (H O). simpl in H. destruct l2; inversion H. subst. f_equal.
    apply IHl1. intro i. apply (G (S i)).
Qed.

Lemma list_elementwise_same_Z: forall A (l1 l2: list A),
    (forall i, 0 <= i -> Znth_error l1 i = Znth_error l2 i) ->
    l1 = l2.
Proof.
  intros. apply list_elementwise_same.
  intro i. specialize (H (Z.of_nat i)).
  unfold Znth_error in *.
  destruct (Z.of_nat i) eqn: E;
    try blia;
    apply Z2Nat.inj_iff in E; try blia;
      rewrite Nat2Z.id in E;
      subst i;
      apply H;
      blia.
Qed.

Lemma list_elementwise_same': forall (A : Type) (l1 l2 : list A),
    (forall i e, nth_error l1 i = Some e <-> nth_error l2 i = Some e) ->
    l1 = l2.
Proof.
  intros.
  apply list_elementwise_same.
  intro i.
  destruct (nth_error l1 i) as [e1|] eqn: E1.
  - edestruct H as [A1 A2]. specialize (A1 E1). congruence.
  - destruct (nth_error l2 i) as [e2|] eqn: E2; [|reflexivity].
    edestruct H as [A1 A2]. specialize (A2 E2). congruence.
Qed.

Lemma list_elementwise_same_Z': forall (A : Type) (l1 l2 : list A),
    (forall i e, Znth_error l1 i = Some e <-> Znth_error l2 i = Some e) ->
    l1 = l2.
Proof.
  intros.
  apply list_elementwise_same_Z.
  intro i.
  destruct (Znth_error l1 i) as [e1|] eqn: E1.
  - edestruct H as [A1 A2]. specialize (A1 E1). congruence.
  - destruct (Znth_error l2 i) as [e2|] eqn: E2; [|reflexivity].
    edestruct H as [A1 A2]. specialize (A2 E2). congruence.
Qed.

Lemma map_nth_error': forall (A B : Type) (f : A -> B) (n : nat) (l : list A) (b : B),
     nth_error (map f l) n = Some b ->
     exists a, nth_error l n = Some a /\ f a = b.
Proof.
  induction n; intros.
  - destruct l; simpl in *; try discriminate. inversion H; subst. eauto.
  - destruct l; simpl in *; try discriminate. apply IHn. assumption.
Qed.

Lemma map_Znth_error': forall (A B : Type) (f : A -> B) (n : Z) (l : list A) (b : B),
     Znth_error (map f l) n = Some b ->
     exists a, Znth_error l n = Some a /\ f a = b.
Proof.
  intros.
  unfold Znth_error in *.
  destruct n; try discriminate; apply map_nth_error'; assumption.
Qed.

Lemma map_Zlength: forall (A B : Type) (f : A -> B) (l : list A),
    Zlength (map f l) = Zlength l.
Proof.
  intros. rewrite? Zlength_correct. rewrite map_length. reflexivity.
Qed.

Definition map_nat_range{R: Type}(f: nat -> R): nat -> nat -> list R :=
  fix rec(start count: nat) :=
    match count with
    | O => nil
    | S count' => f start :: rec (S start) count'
    end.

Definition map_range{R: Type}(f: Z -> R)(count: Z): list R :=
  map_nat_range (fun i => f (Z.of_nat i)) 0 (Z.to_nat count).

Definition fold_left_index{A B: Type}(f: Z -> A -> B -> A)(l: list B)(i0: Z)(a0: A): A :=
  snd (fold_left (fun p b => (fst p + 1, f (fst p) (snd p) b)) l (i0, a0)).

Lemma map_nat_range_cons: forall {R: Type} (f: nat -> R) (count start: nat),
    map_nat_range f start (S count) = f start :: map_nat_range f (S start) count.
Proof.
  intros. reflexivity.
Qed.

Lemma length_map_nat_range{R: Type}: forall (f: nat -> R) (count start: nat),
    length (map_nat_range f start count) = count.
Proof.
  induction count; intros; simpl; congruence.
Qed.

Lemma Zlength_map_range{R: Type}: forall (f: Z -> R) (count: Z),
    0 <= count ->
    Zlength (map_range f count) = count.
Proof.
  intros. unfold map_range. rewrite Zlength_correct.
  rewrite length_map_nat_range.
  apply Z2Nat.id.
  assumption.
Qed.

Lemma nth_error_map_nat_range{R: Type}: forall (f: nat -> R) (count start i: nat),
    (start <= i < start + count)%nat ->
    nth_error (map_nat_range f start count) (i - start) = Some (f i).
Proof.
  induction count; intros.
  - exfalso. blia.
  - simpl. assert (start = i \/ start < i)%nat as C by blia. destruct C as [C | C].
    + subst. rewrite Nat.sub_diag. reflexivity.
    + destruct i; [exfalso;blia|].
      replace (S i - start)%nat with (S (i - start)) by blia.
      simpl.
      specialize (IHcount (S start) (S i)).
      rewrite Nat.sub_succ in IHcount.
      apply IHcount.
      blia.
Qed.

Lemma Znth_error_map_range{R: Type}: forall (f: Z -> R) (count i: Z),
    0 <= i < count ->
    Znth_error (map_range f count) i = Some (f i).
Proof.
  intros. unfold Znth_error, map_range.
  pose proof (@nth_error_map_nat_range R) as P.
  specialize P with (start := O).
  setoid_rewrite Nat.sub_0_r in P.
  destruct i.
  - rewrite P.
    + reflexivity.
    + split; [blia|].
      apply Z2Nat.inj_lt; blia.
  - rewrite P.
    + f_equal. f_equal. apply Z2Nat.id. blia.
    + split; [blia|].
      rewrite Nat.add_0_l.
      apply Z2Nat.inj_lt; blia.
  - exfalso. destruct H as [H _].
    unfold Z.le in H. simpl in H. congruence.
Qed.

(* TODO is there a more principled approach for lemmas of this kind? *)
Lemma Znth_error_Some: forall (A : Type) (l : list A) (n : Z),
    Znth_error l n <> None <-> 0 <= n < Zlength l.
Proof using .
  intros. unfold Znth_error. rewrite Zlength_correct.
  pose proof (nth_error_Some l (Z.to_nat n)) as P.
  split; intros.
  - apply proj1 in P.
    destruct n; try contradiction; (split; [blia|]); (apply Z2Nat.inj_lt; [blia|blia|]);
      rewrite? Nat2Z.id; apply P; assumption.
  - apply proj2 in P.
    destruct n; try blia; apply P; apply Nat2Z.inj_lt; rewrite? Z2Nat.id; blia.
Qed.

Lemma Znth_error_ge_None: forall {A : Type} (l : list A) (n : Z),
    Zlength l <= n -> Znth_error l n = None.
Proof.
  unfold Znth_error. intros. rewrite Zlength_correct in *.
  destruct n; try reflexivity; apply nth_error_None;
    apply Nat2Z.inj_le; rewrite? Z2Nat.id; blia.
Qed.

Lemma Zlength_nonneg: forall {A: Type} (l: list A), 0 <= Zlength l.
Proof.
  intros. rewrite Zlength_correct. blia.
Qed.

Lemma map_Znth_error: forall {A B : Type} (f : A -> B) (n : Z) (l : list A) {d : A},
    Znth_error l n = Some d -> Znth_error (map f l) n = Some (f d).
Proof.
  intros.
  unfold Znth_error in *.
  destruct n; try discriminate; erewrite map_nth_error; eauto.
Qed.

(* destruct list length without destructing the cons to avoid unwanted simpls *)
Lemma destruct_list_length: forall A (l: list A),
    l = nil \/ 0 < Zlength l.
Proof.
  intros. rewrite Zlength_correct. destruct l; cbv; auto.
Qed.

Lemma Zlength_cons: forall {A: Type} (a: A) (l: list A),
    Zlength (a :: l) = Zlength l + 1.
Proof.
  intros.
  simpl.
  rewrite? Zlength_correct.
  change (length (a :: l)) with (S (length l)).
  rewrite Nat2Z.inj_succ.
  reflexivity.
Qed.

Lemma Zlength_nil: forall {A: Type}, Zlength (@nil A) = 0.
Proof.
  intros. reflexivity.
Qed.

Lemma Zlength_app: forall {A: Type} (l1 l2: list A),
    Zlength (l1 ++ l2) = Zlength l1 + Zlength l2.
Proof.
  intros.
  simpl.
  rewrite? Zlength_correct.
  rewrite app_length.
  blia.
Qed.

Lemma Znth_error_head: forall {A: Type} (l: list A) (a: A),
    Znth_error (a :: l) 0 = Some a.
Proof.
  intros. reflexivity.
Qed.

Lemma Znth_error_tail: forall {A: Type} (l: list A) (a: A) (i: Z),
    0 < i ->
    Znth_error (a :: l) i = Znth_error l (i - 1).
Proof.
  intros.
  unfold Znth_error.
  assert (i = 1 \/ 1 < i) as C by blia. destruct C as [C | C].
  - subst. reflexivity.
  - destruct i eqn: E; try blia.
    destruct (Z.pos p - 1) eqn: F; try blia.
    replace (Z.pos p) with (Z.succ (Z.pos p0)) by blia.
    rewrite Z2Nat.inj_succ by blia.
    reflexivity.
Qed.

Lemma Znth_error_nil: forall {A: Type} (i: Z),
    Znth_error (@nil A) i = None.
Proof.
  intros. unfold Znth_error.
  destruct i; try reflexivity.
  destruct (Z.to_nat (Z.pos p)); reflexivity.
Qed.

Hint Rewrite
     @Zlength_nil @Zlength_cons
     @Znth_error_head @Znth_error_tail @Znth_error_nil
  using blia
  : rew_Zlist.
