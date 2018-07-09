Require Import Coq.Lists.List.
Require Import bbv.Word.
Require Import Coq.omega.Omega.
Require Import Coq.micromega.Lia.
Require Import riscv.util.div_mod_to_quot_rem.
Require Import riscv.util.Tactics.
Require Import riscv.Utility.


Local Open Scope Z_scope.

Section ValidAddr.

Context {t: Set}.
Context {MW: MachineWidth t}.

Definition valid_addr(addr: t)(alignment size: Z): Prop :=
  regToZ_unsigned addr + alignment <= size /\ (regToZ_unsigned addr) mod alignment = 0.

(* Note: alignment refers to addr, not to the range *)
Definition in_range(addr: t)(alignment start size: Z): Prop :=
  start <= regToZ_unsigned addr /\
  regToZ_unsigned addr + alignment <= start + size /\
  regToZ_unsigned addr mod alignment = 0.

Definition not_in_range(addr: t)(alignment start size: Z): Prop :=
  regToZ_unsigned addr + alignment <= start \/ start + size <= regToZ_unsigned addr.

Definition valid_addr'(addr: t)(alignment size: Z): Prop :=
  in_range addr alignment 0 size.

Lemma valid_addr_alt: forall (addr: t) alignment size,
    valid_addr addr alignment size <-> valid_addr' addr alignment size.
Proof.
  intros. unfold valid_addr, valid_addr', in_range.
  pose proof (regToZ_unsigned_bounds addr).
  intuition omega.
Qed.

End ValidAddr.

Class Memory(m t: Set)`{MachineWidth t} := mkMemory {
  memSize: m -> Z;

  loadByte   : m -> t -> word  8;
  loadHalf   : m -> t -> word 16;
  loadWord   : m -> t -> word 32;
  loadDouble : m -> t -> word 64;
  storeByte  : m -> t -> word  8 -> m;
  storeHalf  : m -> t -> word 16 -> m;
  storeWord  : m -> t -> word 32 -> m;
  storeDouble: m -> t -> word 64 -> m;

  memSize_bound: forall m,
    memSize m <= 2^XLEN;

  memSize_mod8: forall m,
    memSize m mod 8 = 0;
  
  loadStoreByte_eq: forall m (a1 a2: t) v,
    valid_addr a1 1 (memSize m) ->
    a2 = a1 ->
    loadByte (storeByte m a1 v) a2 = v;

  loadStoreByte_ne: forall m (a1 a2: t) v,
    valid_addr a1 1 (memSize m) ->
    valid_addr a2 1 (memSize m) ->
    a2 <> a1 ->
    loadByte (storeByte m a1 v) a2 = loadByte m a2;

  storeByte_preserves_memSize: forall m (a: t) v,
    memSize (storeByte m a v) = memSize m;

  loadStoreHalf_eq: forall m (a1 a2: t) v,
    valid_addr a1 2 (memSize m) ->
    a2 = a1 ->
    loadHalf (storeHalf m a1 v) a2 = v;

  loadStoreHalf_ne: forall m (a1 a2: t) v,
    valid_addr a1 2 (memSize m) ->
    valid_addr a2 2 (memSize m) ->
    a2 <> a1 ->
    loadHalf (storeHalf m a1 v) a2 = loadHalf m a2;

  storeHalf_preserves_memSize: forall m (a: t) v,
    memSize (storeHalf m a v) = memSize m;

  loadStoreWord_eq: forall m (a1 a2: t) v,
    valid_addr a1 4 (memSize m) ->
    a2 = a1 ->
    loadWord (storeWord m a1 v) a2 = v;

  loadStoreWord_ne: forall m (a1 a2: t) v,
    valid_addr a1 4 (memSize m) ->
    valid_addr a2 4 (memSize m) ->
    a2 <> a1 ->
    loadWord (storeWord m a1 v) a2 = loadWord m a2;

  storeWord_preserves_memSize: forall m (a: t) v,
    memSize (storeWord m a v) = memSize m;

  loadStoreDouble_eq: forall m (a1 a2: t) v,
    valid_addr a1 8 (memSize m) ->
    a2 = a1 ->
    loadDouble (storeDouble m a1 v) a2 = v;

  loadStoreDouble_ne: forall m (a1 a2: t) v,
    valid_addr a1 8 (memSize m) ->
    valid_addr a2 8 (memSize m) ->
    a2 <> a1 ->
    loadDouble (storeDouble m a1 v) a2 = loadDouble m a2;

  storeDouble_preserves_memSize: forall m (a: t) v,
    memSize (storeDouble m a v) = memSize m;

  loadHalf_spec: forall m a,
    valid_addr a 2 (memSize m) ->
    loadHalf m a = combine (loadByte m a) (loadByte m (add a one));

  loadWord_spec: forall m a,
    valid_addr a 4 (memSize m) ->
    loadWord m a = combine (loadHalf m a) (loadHalf m (add a two));

  loadDouble_spec: forall m a,
    valid_addr a 8 (memSize m) ->
    loadDouble m a = combine (loadWord m a) (loadWord m (add a four));

  (* Note: No storeHalf_spec, storeWord_spec, storeDouble_spec, because we don't
     want to compare memories with = (too restrictive for implementors), nor start
     using a custom equivalence (too complicated).
     Also, it shouldn't be needed, because at the end you only need to know what
     you get back when you do a load, and you can split a load into the unit on
     which the store was done. *)
}.

Lemma valid_addr_8_4: forall {t: Set} {MW: MachineWidth t} (addr: t) size,
    valid_addr addr 8 size ->
    valid_addr addr 4 size.
Proof.
  intros. unfold valid_addr in *.
  intuition (try omega).
  div_mod_to_quot_rem.
  nia.
Qed.

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

Lemma map_nth_error': forall (A B : Type) (f : A -> B) (n : nat) (l : list A) (b : B),
     nth_error (map f l) n = Some b ->
     exists a, nth_error l n = Some a /\ f a = b.
Proof.
  induction n; intros.
  - destruct l; simpl in *; try discriminate. inversion H; subst. eauto.
  - destruct l; simpl in *; try discriminate. apply IHn. assumption.
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

Definition Znth_error{A: Type}(l: list A)(i: Z): option A :=
  match i with
  | Zneg _ => None
  | _ => nth_error l (Z.to_nat i)
  end.

Definition Zlength{T: Type}(l: list T): Z := Z.of_nat (length l).

Lemma length_map_nat_range{R: Type}: forall (f: nat -> R) (count start: nat),
    length (map_nat_range f start count) = count.
Proof.
  induction count; intros; simpl; congruence.
Qed.

Lemma Zlength_map_range{R: Type}: forall (f: Z -> R) (count: Z),
    0 <= count ->
    Zlength (map_range f count) = count.
Proof.
  intros. unfold map_range, Zlength.
  rewrite length_map_nat_range.
  apply Z2Nat.id.
  assumption.
Qed.

Lemma nth_error_map_nat_range{R: Type}: forall (f: nat -> R) (count start i: nat),
    (start <= i < start + count)%nat ->
    nth_error (map_nat_range f start count) (i - start) = Some (f i).
Proof.
  induction count; intros.
  - exfalso. omega.
  - simpl. assert (start = i \/ start < i)%nat as C by omega. destruct C as [C | C].
    + subst. rewrite Nat.sub_diag. reflexivity.
    + destruct i; [exfalso;omega|].
      replace (S i - start)%nat with (S (i - start)) by omega.
      simpl.
      specialize (IHcount (S start) (S i)).
      rewrite Nat.sub_succ in IHcount.
      apply IHcount.
      omega.
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
    + split; [omega|].
      apply Z2Nat.inj_lt; omega.
  - rewrite P.
    + f_equal. f_equal. apply Z2Nat.id. omega.
    + split; [omega|].
      rewrite Nat.add_0_l.
      apply Z2Nat.inj_lt; omega.
  - exfalso. destruct H as [H _].
    unfold Z.le in H. simpl in H. congruence.
Qed.    

Ltac demod :=  
  repeat match goal with
         | H: _ mod _ = 0 |- _ => apply Nat.mod_divides in H; [destruct H | congruence]
         end.

(* destruct list length without destructing the cons to avoid unwanted simpls *)
Lemma destruct_list_length: forall A (l: list A),
    l = nil /\ length l = O \/ length l = S (pred (length l)).
Proof.
  intros. destruct l; simpl; auto.
Qed.

Ltac destruct_list_length :=
  match goal with
  | _: context [length ?L] |- _ =>
       is_var L;
       destruct (destruct_list_length _ L) as [ [ ? ? ] | ? ]; [ subst L | ]
  end.

Ltac womega_pre :=
  match goal with
  | |- ~ (@eq (word _) _ _) => apply wordToNat_neq2
  | |-   (@eq (word _) _ _) => apply wordToNat_eq2
  end.

Ltac womega := womega_pre; omega.

(*
Hint Rewrite
     Nat.succ_inj_wd
     Nat.mul_0_r
     Nat.add_0_r 
     mod_add_r
     mul_div_exact
using omega
: nats.
 *)

Ltac pose_mem_proofs :=
  repeat match goal with
         | m: _ |- _ => unique pose proof (memSize_bound m)
         | m: _ |- _ => unique pose proof (memSize_mod8 m)
         | H: valid_addr _ 8 _ |- _ => unique pose proof (valid_addr_8_4 _ _ H)
         end.

Ltac word_nat_rewrites :=
  rewrite? wordToNat_wplus';
  rewrite? wordToNat_natToWord_idempotent' by omega.

Ltac mem_simpl :=
  pose_mem_proofs;
  unfold valid_addr in *;
  try womega_pre;
  repeat (
      autorewrite with nats in *;
      rewrite? storeWord_preserves_memSize in *;
      rewrite? loadDouble_spec by mem_simpl;
      rewrite? loadStoreWord_ne by mem_simpl;
      rewrite? loadStoreWord_eq by mem_simpl;
      subst;
      auto;
      word_nat_rewrites
    );
  try solve [repeat ((try omega); f_equal)].


Section MemoryHelpers.

  Context {Mem: Set}.
  Context {t: Set}.
  Context {MW: MachineWidth t}.
  Context {MM: Memory Mem t}.
  Hypothesis pow2_sz_4: 4 < 2 ^ XLEN.

  Add Ring tring: (@regRing t MW).

  Lemma regToZ_unsigned_one: regToZ_unsigned one = 1.
  Proof.
    intros. rewrite <- ZToReg_morphism.(morph1).
    apply regToZ_ZToReg_unsigned. omega.
  Qed.

  Lemma regToZ_unsigned_two: regToZ_unsigned two = 2.
  Proof.
    intros. unfold two. rewrite add_def_unsigned.
    rewrite regToZ_unsigned_one.
    apply regToZ_ZToReg_unsigned. omega.
  Qed.
  
  Lemma regToZ_unsigned_four: regToZ_unsigned four = 4.
  Proof.
    intros. unfold four. rewrite add_def_unsigned.
    rewrite regToZ_unsigned_two.
    apply regToZ_ZToReg_unsigned. omega.
  Qed.

  Lemma loadWord_storeDouble_ne: forall m (a1 a2: t) v,
      valid_addr a1 8 (memSize m) ->
      valid_addr a2 4 (memSize m) ->
      a2 <> a1 ->
      a2 <> add a1 four ->
      loadWord (storeDouble m a1 v) a2 = loadWord m a2.
  Proof.
    intros.
    pose proof (memSize_bound m) as B.
    pose proof loadStoreDouble_ne as P.
    specialize P with (1 := H).
    Search (_ mod 2)%Z.
    destruct (ZLib.mod2_cases (regToZ_unsigned a2 / 4)) as [C | C].
    - specialize (P a2 v).
      assert (valid_addr a2 8 (memSize m)) as V. {
        unfold valid_addr in *.
        destruct H, H0.
        assert (regToZ_unsigned a2 mod 8 = 0). {
          apply Z.mod_divide; try congruence.
          change 8 with (2 * 4).
          replace (regToZ_unsigned a2) with (regToZ_unsigned a2 / 4 * 4).
          - apply Z.mul_divide_mono_r.
            apply Z.mod_divide; congruence.
          - apply ZLib.div_mul_undo; congruence.
        }
        split; try assumption.
        pose proof (memSize_mod8 m).
        div_mod_to_quot_rem. omega.
      }
      specialize (P V).
      rewrite loadDouble_spec in P
        by (rewrite storeDouble_preserves_memSize; assumption).
      specialize (P H1).
      rewrite loadDouble_spec in P by assumption.
      pose proof combine_inj as Q.
      specialize (Q 32%nat 32%nat _ _ _ _ P).
      destruct Q as [Q _]. assumption.
    - specialize (P (sub a2 four) v).
      pose proof (regToZ_unsigned_bounds a2).
      assert (regToZ_unsigned a2 = 0 \/
              regToZ_unsigned a2 = 1 \/
              regToZ_unsigned a2 = 2 \/
              regToZ_unsigned a2 = 3 \/
              4 <= regToZ_unsigned a2) as D by omega.
      destruct D as [D | [D | [D | [D | D]]]];
        [ (rewrite D in C; simpl in C; discriminate) .. | ].
      pose proof (loadDouble_spec              m       (sub a2 four)) as Sp1.
      pose proof (loadDouble_spec (storeDouble m a1 v) (sub a2 four)) as Sp2.
      unfold valid_addr in *.
      destruct H, H0.
      rewrite storeDouble_preserves_memSize in Sp2.
      replace (regToZ_unsigned  (sub a2 four)) with (regToZ_unsigned a2 - 4) in *.
      + assert ((regToZ_unsigned a2 - 4) mod 8 = 0) as X. {
          clear Sp1 Sp2 P.
          div_mod_to_quot_rem. nia.
        }
        assert (regToZ_unsigned a2 - 4 + 8 <= memSize m) as A by omega.
        specialize (P (conj A X)).
        rewrite Sp1 in P by (split; assumption). clear Sp1.
        rewrite Sp2 in P by (split; assumption). clear Sp2.
        assert (sub a2 four <> a1) as Ne. {
          clear -H2.
          intro. subst. apply H2.
          ring.
        }
        specialize (P Ne).
        pose proof combine_inj as Q.
        specialize (Q 32%nat 32%nat _ _ _ _ P).
        destruct Q as [_ Q].
        ring_simplify (add (sub a2 four) four) in Q.
        assumption.
      + rewrite sub_def_unsigned.
        rewrite regToZ_unsigned_four.
        rewrite regToZ_ZToReg_unsigned; omega.
  Qed.

  Lemma loadWord_storeDouble_ne': forall (m : Mem) (a1 a2 : t) (v : word 64),
      in_range a1 8 0 (memSize m) ->
      in_range a2 4 0 (memSize m) ->
      (* a2 (4 bytes big) is not in the 8-byte range starting at a1 *)
      not_in_range a2 4 (regToZ_unsigned a1) 8 ->
      loadWord (storeDouble m a1 v) a2 = loadWord m a2.
  Proof.
    intros.
    pose proof (memSize_bound m).
    apply loadWord_storeDouble_ne;
    unfold in_range, not_in_range, valid_addr in *;
    simpl in *;
    intuition (subst; try omega);
    rewrite @add_def_unsigned in *;
    rewrite @regToZ_unsigned_four in *;
    rewrite @regToZ_ZToReg_unsigned in * by omega;
    omega.
  Qed.

  Definition store_byte_list(l: list (word 8))(a: t)(m: Mem): Mem :=
    fold_left_index (fun i m w => storeByte m (add a (ZToReg i)) w) l 0 m.
  
  Definition load_byte_list(m: Mem)(start: t)(count: Z): list (word 8) :=
    map_range (fun i => loadByte m (add start (ZToReg i))) count.

  Definition store_half_list(l: list (word 16))(a: t)(m: Mem): Mem :=
    fold_left_index (fun i m w => storeHalf m (add a (ZToReg (2 * i))) w) l 0 m.

  Definition load_half_list(m: Mem)(start: t)(count: Z): list (word 16) :=
    map_range (fun i => loadHalf m (add start (ZToReg (2 * i)))) count.

  Definition store_word_list(l: list (word 32))(a: t)(m: Mem): Mem :=
    fold_left_index (fun i m w => storeWord m (add a (ZToReg (4 * i))) w) l 0 m.

  Definition load_word_list(m: Mem)(start: t)(count: Z): list (word 32) :=
    map_range (fun i => loadWord m (add start (ZToReg (4 * i)))) count.

  Definition store_double_list(l: list (word 64))(a: t)(m: Mem): Mem :=
    fold_left_index (fun i m w => storeDouble m (add a (ZToReg (4 * i))) w) l 0 m.

  Definition load_double_list(m: Mem)(start: t)(count: Z): list (word 64) :=
    map_range (fun i => loadDouble m (add start (ZToReg (8 * i)))) count.

  Lemma Znth_error_load_word_list: forall m l i offset,
      0 <= i < l ->
      Znth_error (load_word_list m offset l) i =
      Some (loadWord m (add offset (ZToReg (4 * i)))).
  Proof.
    intros. unfold load_word_list.
    rewrite Znth_error_map_range by assumption.
    reflexivity.
  Qed.

  Lemma Zlength_load_word_list: forall m l offset,
      0 <= l ->
      Zlength (load_word_list m offset l) = l.
  Proof.
    intros. unfold load_word_list.
    apply Zlength_map_range.
    assumption.
  Qed.

  Local Arguments Z.mul: simpl never.

  Lemma fold_left_index_cons': forall T R (a: T) (l: list T) (f: Z -> R -> T -> R) (i: Z) (r: R),
      fold_left_index f (a :: l) i r = fold_left_index f l (i + 1) (f i r a).
  Proof.
    intros. reflexivity.
  Qed.

  Lemma fold_left_index_shift: forall T R (l: list T) (f: Z -> R -> T -> R) (i d: Z) (r: R),
      fold_left_index f l (i + d) r = fold_left_index (fun j => f (j + d)) l i r.
  Proof.
    induction l; intros.
    - reflexivity.
    - unfold fold_left_index in *. simpl in *.
      replace (i + d + 1) with (i + 1 + d) by omega.
      apply IHl.
  Qed.

  Lemma fold_left_index_cons: forall T R (a: T) (l: list T) (f: Z -> R -> T -> R) (i: Z) (r: R),
      fold_left_index f (a :: l) i r =
      fold_left_index (fun i => f (i + 1)) l i (f i r a).
  Proof.
    intros. rewrite fold_left_index_cons'. apply fold_left_index_shift.
  Qed.

  Lemma fold_left_ext: forall A B (f1 f2: A -> B -> A) (l: list B) (a0: A),
      (forall a b, f1 a b = f2 a b) ->
      fold_left f1 l a0 = fold_left f2 l a0.
  Proof.
    induction l; intros.
    - reflexivity.
    - simpl. rewrite H. apply IHl. assumption.
  Qed.
  
  Lemma store_word_list_cons: forall w l a m,
      store_word_list (w :: l) a m = store_word_list l (add a four) (storeWord m a w).
  Proof.
    intros. unfold store_word_list. rewrite fold_left_index_cons.
    rewrite Z.mul_0_r.
    rewrite ZToReg_morphism.(morph0).
    ring_simplify (add a zero).
    unfold fold_left_index.
    f_equal.
    apply fold_left_ext.
    intros. do 2 f_equal.
    rewrite! add_def_unsigned.
    rewrite! regToZ_unsigned_four.
    rewrite! ZToReg_morphism.(morph_mul).
    rewrite! ZToReg_morphism.(morph_add).
    rewrite! ZToReg_regToZ_unsigned.
    rewrite! ZToReg_morphism.(morph1).
    ring.
  Qed.

  Lemma store_word_list_preserves_memSize_aux: forall ll (m: Mem) a l,
      length l = ll ->
      memSize (store_word_list l a m) = memSize m.
  Proof.
    induction ll; intros; subst; destruct l; simpl in *; try reflexivity; try congruence.
    inversion H; subst.
    rewrite store_word_list_cons.
    rewrite IHll by reflexivity.
    apply storeWord_preserves_memSize.
  Qed.

  Lemma store_word_list_preserves_memSize: forall (m: Mem) l a,
      memSize (store_word_list l a m) = memSize m.
  Proof.
    intros. eapply store_word_list_preserves_memSize_aux. reflexivity.
  Qed.
 
  Lemma loadWord_before_store_word_list: forall l (m: Mem) (a1 a2: t),
      regToZ_unsigned a1 + 4 <= regToZ_unsigned a2 ->
      regToZ_unsigned a2 + 4 * (Zlength l) <= (memSize m) ->
      valid_addr a1 4 (memSize m) ->
      valid_addr a2 4 (memSize m) ->
      loadWord (store_word_list l a2 m) a1 = loadWord m a1.
  Proof.
    induction l; intros; unfold store_word_list in *; simpl in *; try reflexivity.
    mem_simpl.
    destruct_list_length; simpl in *.
    - mem_simpl.
    - rewrite IHl; mem_simpl.
  Qed.

  Proof.
    induction l; intros; simpl in *; try congruence.
    mem_simpl.
    destruct_list_length; simpl in *.
    - mem_simpl.
    - rewrite IHl; mem_simpl.
  Qed.

  Lemma loadWord_after_store_word_list: forall l (m: Mem) (a1 a2: t),
      regToZ_unsigned a2 + 4 * (length l) <= regToZ_unsigned a1 ->
      valid_addr a1 4 (memSize m) ->
      valid_addr a2 4 (memSize m) ->
      loadWord (store_word_list l a2 m) a1 = loadWord m a1.
  Proof.
    induction l; intros; simpl in *; try congruence.
    mem_simpl.
    destruct_list_length; simpl in *.
    - mem_simpl.
    - rewrite IHl; mem_simpl.
  Qed.

  Lemma loadWord_outside_store_word_list: forall l (m: Mem) a1 a2,
      not_in_range a1 4 (regToZ_unsigned a2) (4 * Zlength l) ->
      regToZ_unsigned a2 + 4 * Zlength l <= memSize m ->
      valid_addr a1 4 (memSize m) ->
      valid_addr a2 4 (memSize m) ->
      loadWord (store_word_list l a2 m) a1 = loadWord m a1.
  Proof.
    intros. unfold not_in_range in *. destruct H.
    - apply loadWord_before_store_word_list; mem_simpl.
    - apply loadWord_after_store_word_list; mem_simpl.
  Qed.

  Local Arguments Nat.div: simpl never.
  Local Arguments nth: simpl never.

  Lemma wminus_diag: forall sz (w: t),
      w ^- w = $0.
  Proof.
    intros. unfold wminus. apply wminus_inv.
  Qed.

  Lemma loadWord_inside_store_word_list_aux: forall l (m: Mem) i offset,
      i < length l ->
      regToZ_unsigned offset + 4 * length l <= memSize m ->
      valid_addr offset 4 (memSize m) ->
      loadWord (store_word_list l offset m) $(regToZ_unsigned offset + 4 * i) = nth i l $0.
  Proof.
    induction l; intros; unfold in_range in *; simpl in *; mem_simpl.
    destruct_list_length; simpl in *.
    - assert (i = 0) by omega. mem_simpl.
    - destruct i.
      + rewrite loadWord_before_store_word_list; mem_simpl.
      + change (nth (S i) (a :: l) $ (0)) with (nth i l $ (0)).
        specialize (IHl (storeWord m offset a) i (offset ^+ $4)).
        rewrite <- IHl; mem_simpl.
  Qed.
  
  Lemma loadWord_inside_store_word_list: forall l (m: Mem) addr offset,
      in_range addr 4 regToZ_unsigned offset (4 * length l) ->
      regToZ_unsigned offset + 4 * length l <= memSize m ->
      valid_addr offset 4 (memSize m) ->
      loadWord (store_word_list l offset m) addr = nth (regToZ_unsigned  (addr ^- offset) / 4) l $0.
  Proof.
    intros. unfold in_range in *.
    rewrite <- (loadWord_inside_store_word_list_aux l m (regToZ_unsigned  (addr ^- offset) / 4) offset);
      try assumption.
    (* TODO this should be in mem_simpl too *)
    - repeat f_equal. rewrite wminus_minus' by omega.
      rewrite mul_div_exact; mem_simpl.
      rewrite sub_mod_0; omega.
    - rewrite wminus_minus' by omega.
      pose proof (Nat.mul_lt_mono_pos_l 4) as P.
      apply P; try omega. clear P.
      rewrite mul_div_exact; mem_simpl.
      rewrite sub_mod_0; omega.
  Qed.
  
  Lemma loadDouble_before_store_word_list: forall l (m: Mem) (a1 a2: t),
      regToZ_unsigned a1 + 8 <= regToZ_unsigned a2 ->
      regToZ_unsigned a2 + 4 * (length l) <= (memSize m) ->
      valid_addr a1 8 (memSize m) ->
      valid_addr a2 4 (memSize m) ->
      loadDouble (store_word_list l a2 m) a1  = loadDouble m a1.
  Proof.
    induction l; intros; simpl in *; try congruence.
    mem_simpl.
    destruct_list_length; simpl in *.
    - mem_simpl.
    - rewrite IHl; mem_simpl.
  Qed.

  Lemma loadDouble_after_store_word_list: forall l (m: Mem) (a1 a2: t),
      regToZ_unsigned a2 + 4 * (length l) <= regToZ_unsigned a1 ->
      valid_addr a1 8 (memSize m) ->
      valid_addr a2 4 (memSize m) ->
      loadDouble (store_word_list l a2 m) a1  = loadDouble m a1.
  Proof.
    induction l; intros; simpl in *; try congruence.
    mem_simpl.
    destruct_list_length; simpl in *.
    - mem_simpl.
    - rewrite IHl; mem_simpl.
  Qed.

  Lemma loadDouble_outside_store_word_list: forall l (m: Mem) a1 a2,
      not_in_range a1 8 regToZ_unsigned a2 (4 * length l) ->
      regToZ_unsigned a2 + 4 * length l <= memSize m ->
      valid_addr a1 8 (memSize m) ->
      valid_addr a2 4 (memSize m) ->
      loadDouble (store_word_list l a2 m) a1 = loadDouble m a1.
  Proof.
    intros. unfold not_in_range in *. destruct H.
    - apply loadDouble_before_store_word_list; mem_simpl.
    - apply loadDouble_after_store_word_list; mem_simpl.
  Qed.

  Local Arguments Nat.modulo: simpl never.

  Lemma load_store_word_list_eq: forall l (m: Mem) ll a1 a2,
      a2 = a1 ->
      ll = length l ->
      regToZ_unsigned a1 mod 4 = 0 ->
      regToZ_unsigned a1 + 4 * (length l) <= memSize m ->
      load_word_list (store_word_list l a1 m) a2 ll = l.
  Proof.
    induction l; intros; subst; simpl in *; try congruence.
    mem_simpl.
    destruct_list_length; simpl in *.
    - mem_simpl.
    - rewrite loadWord_before_store_word_list; mem_simpl.
      rewrite IHl; mem_simpl.
  Qed.

End MemoryHelpers.
