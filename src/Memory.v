Require Import Coq.Lists.List.
Require Import bbv.Word.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Require Import riscv.util.nat_div_mod_to_quot_rem.
Require Import riscv.util.Tactics.
Require Import riscv.Utility.

Import Word.ArithmeticNotations.
Import Word.ConversionNotations.
Local Open Scope word_scope.

Section ValidAddr.

Context {t: Set}.
Context {MW: MachineWidth t}.

Definition valid_addr(addr: t)(alignment size: nat): Prop :=
  regToNat addr + alignment <= size /\ (regToNat addr) mod alignment = 0.

(* Note: alignment refers to addr, not to the range *)
Definition in_range(addr: t)(alignment start size: nat): Prop :=
  start <= regToNat addr /\
  regToNat addr + alignment <= start + size /\
  regToNat addr mod alignment = 0.

Definition not_in_range(addr: t)(alignment start size: nat): Prop :=
  regToNat addr + alignment <= start \/ start + size <= regToNat addr.

Definition valid_addr'(addr: t)(alignment size: nat): Prop :=
  in_range addr alignment 0 size.

Lemma valid_addr_alt: forall (addr: t) alignment size,
    valid_addr addr alignment size <-> valid_addr' addr alignment size.
Proof.
  intros. unfold valid_addr, valid_addr', in_range.
  intuition omega.
Qed.

End ValidAddr.

Class Memory(m t: Set)`{MachineWidth t} := mkMemory {
  memSize: m -> nat;

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
  nat_div_mod_to_quot_rem.
  nia.
Qed.

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

Lemma mod_0_r: forall (m: nat),
    m mod 0 = 0.
Proof.
  intros. reflexivity.
Qed.

Lemma sub_mod_0: forall (a b m: nat),
    a mod m = 0 ->
    b mod m = 0 ->
    (a - b) mod m = 0.
Proof.
  intros. assert (m = 0 \/ m <> 0) as C by omega. destruct C as [C | C].
  - subst. apply mod_0_r.
  - assert (a - b = 0 \/ b < a) as D by omega. destruct D as [D | D].
    + rewrite D. apply Nat.mod_0_l. assumption.
    + apply Nat2Z.inj. simpl.
      rewrite Zdiv.mod_Zmod by assumption.
      rewrite Nat2Z.inj_sub by omega.
      rewrite Zdiv.Zminus_mod.
      rewrite <-! Zdiv.mod_Zmod by assumption.
      rewrite H. rewrite H0.
      apply Z.mod_0_l.
      omega.
Qed.      

Lemma wminus_minus': forall (sz : nat) (a b : word sz),
    #b <= #a ->
    #(a ^- b) = #a - #b.
Proof.
  intros. apply wminus_minus.
  unfold wlt. intro C.
  apply Nlt_out in C.
  rewrite! wordToN_to_nat in *.
  omega.
Qed.

Ltac womega_pre :=
  match goal with
  | |- ~ (@eq (word _) _ _) => apply wordToNat_neq2
  | |-   (@eq (word _) _ _) => apply wordToNat_eq2
  end.

Ltac womega := womega_pre; omega.

Lemma mul_div_exact: forall (a b: nat),
    b <> 0 ->
    a mod b = 0 ->
    b * (a / b) = a.
Proof.
  intros. edestruct Nat.div_exact as [_ P]; [eassumption|].
  specialize (P H0). symmetry. exact P.
Qed.

Hint Rewrite
     Nat.succ_inj_wd
     Nat.mul_0_r
     Nat.add_0_r 
     mod_add_r
     mul_div_exact
using omega
: nats.

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
  Hypothesis pow2_sz_4: 4 < pow2 XLEN.

  Add Ring tring: (@regRing t MW).

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
    destruct (mod2_cases (regToNat a2 / 4)) as [C | C].
    - specialize (P a2 v).
      assert (valid_addr a2 8 (memSize m)) as V. {
        unfold valid_addr in *.
        destruct H, H0.
        assert (regToNat a2 mod 8 = 0). {
          apply Nat.mod_divide; try congruence.
          change 8 with (2 * 4).
          replace (regToNat a2) with (regToNat a2 / 4 * 4).
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
    - specialize (P (sub a2 four) v).
      assert (regToNat a2 = 0 \/ regToNat a2 = 1 \/ regToNat a2 = 2 \/ regToNat a2 = 3 \/ 4 <= regToNat a2) as D by omega.
      destruct D as [D | [D | [D | [D | D]]]];
        [ (rewrite D in C; simpl in C; discriminate) .. | ].
      pose proof (loadDouble_spec              m       (sub a2 four)) as Sp1.
      pose proof (loadDouble_spec (storeDouble m a1 v) (sub a2 four)) as Sp2.
      unfold valid_addr in *.
      destruct H, H0.
      rewrite storeDouble_preserves_memSize in Sp2.
      replace (regToNat  (sub a2 four)) with (regToNat a2 - 4) in *.
      + assert ((regToNat a2 - 4) mod 8 = 0) as X. {
          clear Sp1 Sp2.
          apply Nat.mod_divide; try congruence.
          change 8 with (2 * 4).
          assert (((regToNat a2 - 4) / 4) mod 2 = 0) as F. {
            apply Nat.mod_divides in H4; [ | congruence].
            destruct H4 as [k Y]. rewrite Y in C|-*.
            destruct k; [omega|].
            replace (4 * S k - 4) with (4 * k) by omega.
            rewrite mul_div_undo in * by congruence.
            apply Smod2_1. assumption.
          }
          replace (regToNat a2 - 4) with ((regToNat a2 - 4) / 4 * 4).
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
        assert (regToNat a2 - 4 + 8 <= memSize m) as A by omega.
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
        specialize (Q 32 32 _ _ _ _ P).
        destruct Q as [_ Q].
        ring_simplify (add (sub a2 four) four) in Q.
        assumption.
      + Check natToReg_semimorph.  rewrite wminus_minus.
        * rewrite wordToNat_natToWord_idempotent'; [reflexivity|omega].
        * apply wordToNat_le2.
          rewrite wordToNat_natToWord_idempotent'; omega.
  Qed.

  Lemma loadWord_storeDouble_ne': forall (m : Mem) (a1 a2 : t) (v : word 64),
      in_range a1 8 0 (memSize m) ->
      in_range a2 4 0 (memSize m) ->
      not_in_range a2 4 regToNat a1 8 -> (* a2 (4 bytes big) is not in the 8-byte range starting at a1 *)
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

  Fixpoint store_byte_list(l: list (word 8))(a: t)(m: Mem): Mem :=
    match l with
    | nil => m
    | cons w l' => let m' := storeByte m a w in store_byte_list l' (a ^+ $1) m'
    end.

  Fixpoint load_byte_list(m: Mem)(start: t)(count: nat): list (word 8) :=
    match count with
    | S c => loadByte m start :: load_byte_list m (start ^+ $1) c
    | O => nil
    end.

  Fixpoint store_half_list(l: list (word 16))(a: t)(m: Mem): Mem :=
    match l with
    | nil => m
    | cons w l' => let m' := storeHalf m a w in store_half_list l' (a ^+ $2) m'
    end.

  Fixpoint load_half_list(m: Mem)(start: t)(count: nat): list (word 16) :=
    match count with
    | S c => loadHalf m start :: load_half_list m (start ^+ $2) c
    | O => nil
    end.

  Fixpoint store_word_list(l: list (word 32))(a: t)(m: Mem): Mem :=
    match l with
    | nil => m
    | cons w l' => let m' := storeWord m a w in store_word_list l' (a ^+ $4) m'
    end.

  Fixpoint load_word_list(m: Mem)(start: t)(count: nat): list (word 32) :=
    match count with
    | S c => loadWord m start :: load_word_list m (start ^+ $4) c
    | O => nil
    end.

  Fixpoint store_double_list(l: list (word 64))(a: t)(m: Mem): Mem :=
    match l with
    | nil => m
    | cons w l' => let m' := storeDouble m a w in store_double_list l' (a ^+ $8) m'
    end.

  Fixpoint load_double_list(m: Mem)(start: t)(count: nat): list (word 64) :=
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
 
  Lemma loadWord_before_store_word_list: forall l (m: Mem) (a1 a2: t),
      regToNat a1 + 4 <= regToNat a2 ->
      regToNat a2 + 4 * (length l) <= (memSize m) ->
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

  Lemma loadWord_after_store_word_list: forall l (m: Mem) (a1 a2: t),
      regToNat a2 + 4 * (length l) <= regToNat a1 ->
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
      not_in_range a1 4 regToNat a2 (4 * length l) ->
      regToNat a2 + 4 * length l <= memSize m ->
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
      regToNat offset + 4 * length l <= memSize m ->
      valid_addr offset 4 (memSize m) ->
      loadWord (store_word_list l offset m) $(regToNat offset + 4 * i) = nth i l $0.
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
      in_range addr 4 regToNat offset (4 * length l) ->
      regToNat offset + 4 * length l <= memSize m ->
      valid_addr offset 4 (memSize m) ->
      loadWord (store_word_list l offset m) addr = nth (regToNat  (addr ^- offset) / 4) l $0.
  Proof.
    intros. unfold in_range in *.
    rewrite <- (loadWord_inside_store_word_list_aux l m (regToNat  (addr ^- offset) / 4) offset);
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
      regToNat a1 + 8 <= regToNat a2 ->
      regToNat a2 + 4 * (length l) <= (memSize m) ->
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
      regToNat a2 + 4 * (length l) <= regToNat a1 ->
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
      not_in_range a1 8 regToNat a2 (4 * length l) ->
      regToNat a2 + 4 * length l <= memSize m ->
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
      regToNat a1 mod 4 = 0 ->
      regToNat a1 + 4 * (length l) <= memSize m ->
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
