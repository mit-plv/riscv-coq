Require Import bbv.Word.
Require Import Coq.omega.Omega.

Definition valid_addr{w: nat}(addr: word w)(alignment size: nat): Prop :=
  wordToNat addr + alignment <= size /\ (wordToNat addr) mod alignment = 0.

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

Lemma mod2_cases: forall (n: nat), n mod 2 = 0 \/ n mod 2 = 1.
Proof.
  intros.
  assert (n mod 2 < 2). {
    apply Nat.mod_upper_bound. congruence.
  }
  omega.
Qed.

Lemma div_mul_undo: forall a b,
    b <> 0 ->
    a mod b = 0 ->
    a / b * b = a.
Proof.
  intros.
  pose proof Nat.div_mul_cancel_l as A. specialize (A a 1 b).
  replace (b * 1) with b in A by omega.
  rewrite Nat.div_1_r in A.
  rewrite mult_comm.
  rewrite <- Nat.divide_div_mul_exact; try assumption.
  - apply A; congruence.
  - apply Nat.mod_divide; assumption.
Qed.

Ltac demod :=  
  repeat match goal with
         | H: _ mod _ = 0 |- _ => apply Nat.mod_divides in H; [destruct H | congruence]
         end.

Section MemoryHelpers.

  Context {sz: nat}.
  Context {Mem: Set}.
  Context {MM: Memory Mem sz}.

  Lemma loadWord_storeDouble_ne: forall m (a1 a2: word sz) v,
      valid_addr a1 8 (memSize m) ->
      valid_addr a2 4 (memSize m) ->
      a2 <> a1 ->
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
        assert (#a2 mod 8 = 0). {
          apply Nat.mod_divide; try congruence.
          change 8 with (2 * 4).
          replace #a2 with (#a2 / 4 * 4).
          - apply Nat.mul_divide_mono_r.
            apply Nat.mod_divide; try congruence.
          - apply div_mul_undo; intuition.
        }
        intuition.
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
          replace (#a2 - 4) with ((#a2 - 4) / 4 * 4).
          - apply Nat.mul_divide_mono_r.
            apply Nat.mod_divide; try congruence.
            admit.
          - apply div_mul_undo. admit.
            admit.
        }
        assert (#a2 - 4 + 8 <= memSize m) as A. {
          admit.
        }
        specialize (P (conj A X)).
        rewrite Sp1 in P by (split; assumption). clear Sp1.
        rewrite Sp2 in P by (split; assumption). clear Sp2.
        assert (a2 ^- $4 <> a1) as Ne. {
          admit.
        }
        specialize (P Ne).
        pose proof combine_inj as Q.
        specialize (Q 32 32 _ _ _ _ P).
        destruct Q as [_ Q].
        replace (a2 ^- $ (4) ^+ $ (4)) with a2 in Q by admit.
        assumption.
      + rewrite wminus_minus.
        * rewrite wordToNat_natToWord_idempotent'; [reflexivity|omega].
        * apply wordToNat_le2.
          rewrite wordToNat_natToWord_idempotent'; omega.
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

End MemoryHelpers.
