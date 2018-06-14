Require Import Coq.Lists.List.
Require Import bbv.Word.
Require Import Coq.omega.Omega.
Require Import riscv.util.Tactics.

Definition valid_addr{w: nat}(addr: word w)(alignment size: nat): Prop :=
  wordToNat addr + alignment <= size /\ (wordToNat addr) mod alignment = 0.

(* Note: alignment refers to addr, not to the range *)
Definition in_range{w: nat}(addr: word w)(alignment start size: nat): Prop :=
  start <= wordToNat addr /\
  wordToNat addr + alignment <= start + size /\
  wordToNat addr mod alignment = 0.

Definition not_in_range{w: nat}(addr: word w)(alignment start size: nat): Prop :=
  wordToNat addr + alignment <= start \/ start + size <= wordToNat addr.

Definition valid_addr'{w: nat}(addr: word w)(alignment size: nat): Prop :=
  in_range addr alignment 0 size.

Lemma valid_addr_alt: forall w (addr: word w) alignment size,
    valid_addr addr alignment size <-> valid_addr' addr alignment size.
Proof.
  intros. unfold valid_addr, valid_addr', in_range.
  intuition omega.
Qed.


Class Memory(m: Set)(w: nat) := mkMemory {
  memSize: m -> nat;

  loadByte   : m -> (word w) -> word  8;
  loadHalf   : m -> (word w) -> word 16;
  loadWord   : m -> (word w) -> word 32;
  loadDouble : m -> (word w) -> word 64;
  storeByte  : m -> (word w) -> word  8 -> m;
  storeHalf  : m -> (word w) -> word 16 -> m;
  storeWord  : m -> (word w) -> word 32 -> m;
  storeDouble: m -> (word w) -> word 64 -> m;

  memSize_bound: forall m,
    memSize m <= 2^w;

  memSize_mod8: forall m,
    memSize m mod 8 = 0;
  
  loadStoreByte_eq: forall m (a1 a2: word w) v,
    valid_addr a1 1 (memSize m) ->
    a2 = a1 ->
    loadByte (storeByte m a1 v) a2 = v;

  loadStoreByte_ne: forall m (a1 a2: word w) v,
    valid_addr a1 1 (memSize m) ->
    valid_addr a2 1 (memSize m) ->
    a2 <> a1 ->
    loadByte (storeByte m a1 v) a2 = loadByte m a2;

  storeByte_preserves_memSize: forall m (a: word w) v,
    memSize (storeByte m a v) = memSize m;

  loadStoreHalf_eq: forall m (a1 a2: word w) v,
    valid_addr a1 2 (memSize m) ->
    a2 = a1 ->
    loadHalf (storeHalf m a1 v) a2 = v;

  loadStoreHalf_ne: forall m (a1 a2: word w) v,
    valid_addr a1 2 (memSize m) ->
    valid_addr a2 2 (memSize m) ->
    a2 <> a1 ->
    loadHalf (storeHalf m a1 v) a2 = loadHalf m a2;

  storeHalf_preserves_memSize: forall m (a: word w) v,
    memSize (storeHalf m a v) = memSize m;

  loadStoreWord_eq: forall m (a1 a2: word w) v,
    valid_addr a1 4 (memSize m) ->
    a2 = a1 ->
    loadWord (storeWord m a1 v) a2 = v;

  loadStoreWord_ne: forall m (a1 a2: word w) v,
    valid_addr a1 4 (memSize m) ->
    valid_addr a2 4 (memSize m) ->
    a2 <> a1 ->
    loadWord (storeWord m a1 v) a2 = loadWord m a2;

  storeWord_preserves_memSize: forall m (a: word w) v,
    memSize (storeWord m a v) = memSize m;

  loadStoreDouble_eq: forall m (a1 a2: word w) v,
    valid_addr a1 8 (memSize m) ->
    a2 = a1 ->
    loadDouble (storeDouble m a1 v) a2 = v;

  loadStoreDouble_ne: forall m (a1 a2: word w) v,
    valid_addr a1 8 (memSize m) ->
    valid_addr a2 8 (memSize m) ->
    a2 <> a1 ->
    loadDouble (storeDouble m a1 v) a2 = loadDouble m a2;

  storeDouble_preserves_memSize: forall m (a: word w) v,
    memSize (storeDouble m a v) = memSize m;

  loadHalf_spec: forall m a,
    valid_addr a 2 (memSize m) ->
    loadHalf m a = combine (loadByte m a) (loadByte m (a ^+ $1));

  loadWord_spec: forall m a,
    valid_addr a 4 (memSize m) ->
    loadWord m a = combine (loadHalf m a) (loadHalf m (a ^+ $2));

  loadDouble_spec: forall m a,
    valid_addr a 8 (memSize m) ->
    loadDouble m a = combine (loadWord m a) (loadWord m (a ^+ $4));

  (* Note: No storeHalf_spec, storeWord_spec, storeDouble_spec, because we don't
     want to compare memories with = (too restrictive for implementors), nor start
     using a custom equivalence (too complicated).
     Also, it shouldn't be needed, because at the end you only need to know what
     you get back when you do a load, and you can split a load into the unit on
     which the store was done. *)
}.

Lemma list_elementwise_same: forall A (l1 l2: list A),
    (forall i, nth_error l1 i = nth_error l2 i) ->
    l1 = l2.
Proof.
  induction l1; intros.
  - specialize (H 0). simpl in H. destruct l2; congruence.
  - pose proof H as G.
    specialize (H 0). simpl in H. destruct l2; inversion H. subst. f_equal.
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

Ltac demod :=  
  repeat match goal with
         | H: _ mod _ = 0 |- _ => apply Nat.mod_divides in H; [destruct H | congruence]
         end.

(* destruct list length without destructing the cons to avoid unwanted simpls *)
Lemma destruct_list_length: forall A (l: list A),
    l = nil /\ length l = 0 \/ length l = S (pred (length l)).
Proof.
  intros. destruct l; simpl; auto.
Qed.

Ltac destruct_list_length :=
  match goal with
  | _: context [length ?L] |- _ =>
       is_var L;
       destruct (destruct_list_length _ L) as [ [ ? ? ] | ? ]; [ subst L | ]
  end.

Local Arguments Nat.modulo: simpl never.

Ltac womega :=
  match goal with
  | |- ~ (@eq (word _) _ _) => apply wordToNat_neq2
  | |-   (@eq (word _) _ _) => apply wordToNat_eq2
  end;
  omega.

Hint Rewrite
     Nat.succ_inj_wd
     mod_add_r
using omega
: nats.

Hint Rewrite
     @storeWord_preserves_memSize
     @loadStoreWord_ne
     @loadStoreWord_eq
  using (unfold valid_addr in *; (auto || womega || omega))
: mem_rew.

Ltac pose_mem_proofs :=
  repeat match goal with
         | m: _ |- _ => unique pose proof (memSize_bound m)
         | m: _ |- _ => unique pose proof (memSize_mod8 m)
         end.

Ltac word_nat_rewrites :=
  rewrite? wordToNat_wplus';
  rewrite? wordToNat_natToWord_idempotent' by omega.

Ltac mem_simpl :=
  pose_mem_proofs;
  unfold valid_addr in *;
  repeat (
      autorewrite with nats mem_rew in *;
      subst;
      auto;
      word_nat_rewrites
    );
  try omega.

Section MemoryHelpers.

  Context {sz: nat}.
  Context {Mem: Set}.
  Context {MM: Memory Mem sz}.
  Hypothesis pow2_sz_4: 4 < pow2 sz.

  Lemma loadWord_storeDouble_ne: forall m (a1 a2: word sz) v,
      valid_addr a1 8 (memSize m) ->
      valid_addr a2 4 (memSize m) ->
      a2 <> a1 ->
      a2 <> a1 ^+ $4 ->
      loadWord (storeDouble m a1 v) a2 = loadWord m a2.
  Proof.
    intros.
    pose proof (memSize_bound m) as B.
    pose proof loadStoreDouble_ne as P.
    specialize P with (1 := H).
    destruct (mod2_cases (#a2 / 4)) as [C | C].
    - specialize (P a2 v).
      assert (valid_addr a2 8 (memSize m)) as V. {
        unfold valid_addr in *.
        destruct H, H0.
        assert (#a2 mod 8 = 0). {
          apply Nat.mod_divide; try congruence.
          change 8 with (2 * 4).
          replace #a2 with (#a2 / 4 * 4).
          - apply Nat.mul_divide_mono_r.
            apply Nat.mod_divide; try congruence.
          - apply div_mul_undo; congruence.
        }
        split; try assumption.
        pose proof (memSize_mod8 m).
        demod. omega.
      }
      specialize (P V).
      rewrite loadDouble_spec in P
        by (rewrite storeDouble_preserves_memSize; assumption).
      specialize (P H1).
      rewrite loadDouble_spec in P by assumption.
      pose proof combine_inj as Q.
      specialize (Q 32 32 _ _ _ _ P).
      destruct Q as [Q _]. assumption.
    - specialize (P (a2 ^- $4) v).
      assert (#a2 = 0 \/ #a2 = 1 \/ #a2 = 2 \/ #a2 = 3 \/ 4 <= #a2) as D by omega.
      destruct D as [D | [D | [D | [D | D]]]];
        [ (rewrite D in C; simpl in C; discriminate) .. | ].
      pose proof (loadDouble_spec              m       (a2 ^- $ (4))) as Sp1.
      pose proof (loadDouble_spec (storeDouble m a1 v) (a2 ^- $ (4))) as Sp2.
      unfold valid_addr in *.
      destruct H, H0.
      rewrite storeDouble_preserves_memSize in Sp2.
      replace (# (a2 ^- $4)) with (#a2 - 4) in *.
      + assert ((#a2 - 4) mod 8 = 0) as X. {
          clear Sp1 Sp2.
          apply Nat.mod_divide; try congruence.
          change 8 with (2 * 4).
          assert (((#a2 - 4) / 4) mod 2 = 0) as F. {
            apply Nat.mod_divides in H4; [ | congruence].
            destruct H4 as [k Y]. rewrite Y in C|-*.
            destruct k; [omega|].
            replace (4 * S k - 4) with (4 * k) by omega.
            rewrite mul_div_undo in * by congruence.
            apply Smod2_1. assumption.
          }
          replace (#a2 - 4) with ((#a2 - 4) / 4 * 4).
          - apply Nat.mul_divide_mono_r.
            apply Nat.mod_divide; congruence.
          - apply div_mul_undo; try congruence.
            clear -H4 D. demod. rename H into Y. rewrite Y.
            rewrite Nat.mod_eq in * by congruence.
            destruct x; [omega|].
            replace (4 * S x - 4) with (4 * x) by omega.
            rewrite mul_div_undo in * by congruence.
            omega.
        }
        assert (#a2 - 4 + 8 <= memSize m) as A by omega.
        specialize (P (conj A X)).
        rewrite Sp1 in P by (split; assumption). clear Sp1.
        rewrite Sp2 in P by (split; assumption). clear Sp2.
        assert (a2 ^- $4 <> a1) as Ne. {
          clear -H2.
          intro. subst. apply H2.
          symmetry. apply wminus_wplus_undo.
        }
        specialize (P Ne).
        pose proof combine_inj as Q.
        specialize (Q 32 32 _ _ _ _ P).
        destruct Q as [_ Q].
        rewrite wminus_wplus_undo in Q.
        assumption.
      + rewrite wminus_minus.
        * rewrite wordToNat_natToWord_idempotent'; [reflexivity|omega].
        * apply wordToNat_le2.
          rewrite wordToNat_natToWord_idempotent'; omega.
  Qed.

  Lemma loadWord_storeDouble_ne': forall (m : Mem) (a1 a2 : word sz) (v : word 64),
      in_range a1 8 0 (memSize m) ->
      in_range a2 4 0 (memSize m) ->
      not_in_range a2 4 #a1 8 -> (* a2 (4 bytes big) is not in the 8-byte range starting at a1 *)
      loadWord (storeDouble m a1 v) a2 = loadWord m a2.
  Proof.
    intros.
    pose proof (memSize_bound m).
    apply loadWord_storeDouble_ne;
    unfold in_range, not_in_range, valid_addr in *;
    simpl in *;
    intuition (subst; try omega);
    rewrite (wordToNat_wplus' a1 $4) in H6;
    rewrite wordToNat_natToWord_idempotent' in *;
    try omega. 
  Qed.

  Fixpoint store_byte_list(l: list (word 8))(a: word sz)(m: Mem): Mem :=
    match l with
    | nil => m
    | cons w l' => let m' := storeByte m a w in store_byte_list l' (a ^+ $1) m'
    end.

  Fixpoint load_byte_list(m: Mem)(start: word sz)(count: nat): list (word 8) :=
    match count with
    | S c => loadByte m start :: load_byte_list m (start ^+ $1) c
    | O => nil
    end.

  Fixpoint store_half_list(l: list (word 16))(a: word sz)(m: Mem): Mem :=
    match l with
    | nil => m
    | cons w l' => let m' := storeHalf m a w in store_half_list l' (a ^+ $2) m'
    end.

  Fixpoint load_half_list(m: Mem)(start: word sz)(count: nat): list (word 16) :=
    match count with
    | S c => loadHalf m start :: load_half_list m (start ^+ $2) c
    | O => nil
    end.

  Fixpoint store_word_list(l: list (word 32))(a: word sz)(m: Mem): Mem :=
    match l with
    | nil => m
    | cons w l' => let m' := storeWord m a w in store_word_list l' (a ^+ $4) m'
    end.

  Fixpoint load_word_list(m: Mem)(start: word sz)(count: nat): list (word 32) :=
    match count with
    | S c => loadWord m start :: load_word_list m (start ^+ $4) c
    | O => nil
    end.

  Fixpoint store_double_list(l: list (word 64))(a: word sz)(m: Mem): Mem :=
    match l with
    | nil => m
    | cons w l' => let m' := storeDouble m a w in store_double_list l' (a ^+ $8) m'
    end.

  Fixpoint load_double_list(m: Mem)(start: word sz)(count: nat): list (word 64) :=
    match count with
    | S c => loadDouble m start :: load_double_list m (start ^+ $8) c
    | O => nil
    end.

  Local Arguments mult: simpl never.

  Lemma nth_error_load_word_list: forall m (l: nat) i offset,
      i < l ->
      nth_error (load_word_list m offset l) i =
      Some (loadWord m (offset ^+ $ (4 * i))).
  Proof.
    induction l; intros; simpl.
    - exfalso. omega.
    - destruct i; simpl.
      + change (4 * 0) with 0. rewrite wplus_comm. rewrite wplus_unit.
        reflexivity.
      + replace (offset ^+ $(4 * S i)) with ((offset ^+ $4) ^+ $(4 * i)).
        * apply IHl. omega.
        * rewrite <- wplus_assoc. f_equal. rewrite <- natToWord_plus.
          f_equal. omega.
  Qed.

  Lemma length_load_word_list: forall m l offset,
      length (load_word_list m offset l) = l.
  Proof.
    induction l; intros.
    - reflexivity.
    - simpl. f_equal. apply IHl.
  Qed.

  Local Arguments mult: simpl never.

  Lemma store_word_list_preserves_memSize_aux: forall ll (m: Mem) a l,
      length l = ll ->
      memSize (store_word_list l a m) = memSize m.
  Proof.
    induction ll; intros; subst; destruct l; simpl in *; try congruence.
    inversion H; subst.
    rewrite IHll by reflexivity.
    apply storeWord_preserves_memSize.
  Qed.

  Lemma store_word_list_preserves_memSize: forall (m: Mem) l a,
      memSize (store_word_list l a m) = memSize m.
  Proof.
    intros. eapply store_word_list_preserves_memSize_aux. reflexivity.
  Qed.
 
  Lemma loadWord_before_store_word_list: forall l (m: Mem) (a1 a2: word sz),
      #a1 + 4 <= #a2 ->
      #a2 + 4 * (length l) <= (memSize m) ->
      valid_addr a1 4 (memSize m) ->
      valid_addr a2 4 (memSize m) ->
      loadWord (store_word_list l a2 m) a1  = loadWord m a1.
  Proof.
    induction l; intros; simpl in *; try congruence.
    mem_simpl.
    destruct_list_length; simpl in *.
    - mem_simpl.
    - rewrite IHl; mem_simpl.
  Qed.

  Local Arguments Nat.modulo: simpl never.

  Lemma load_store_word_list_eq: forall l (m: Mem) ll a1 a2,
      a2 = a1 ->
      ll = length l ->
      #a1 mod 4 = 0 ->
      #a1 + 4 * (length l) <= memSize m ->
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
