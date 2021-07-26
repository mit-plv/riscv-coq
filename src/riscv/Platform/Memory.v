Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import coqutil.Word.Interface.
Require Import coqutil.Word.Properties.
Require Import coqutil.Word.Bitwidth.
Require Import coqutil.Datatypes.HList.
Require Import coqutil.Datatypes.PrimitivePair.
Require Import coqutil.Map.Interface.
Require Import coqutil.Map.Properties.
Require Import coqutil.Tactics.Tactics.
Require Import coqutil.sanity.
Require Import coqutil.Z.Lia.
Require Import coqutil.Byte.

Local Open Scope Z_scope.


Section MemAccess.
  Context {width} {word: word width} {mem: map.map word byte}.

  Definition footprint(a: word)(sz: nat): tuple word sz :=
    tuple.unfoldn (fun w => word.add w (word.of_Z 1)) sz a.

  Definition load_bytes(sz: nat)(m: mem)(addr: word): option (tuple byte sz) :=
    map.getmany_of_tuple m (footprint addr sz).

  Definition unchecked_store_bytes(sz: nat)(m: mem)(a: word)(bs: tuple byte sz): mem :=
    map.putmany_of_tuple (footprint a sz) bs m.

  Definition store_bytes(sz: nat)(m: mem)(a: word)(v: tuple byte sz): option mem :=
    match load_bytes sz m a with
    | Some _ => Some (unchecked_store_bytes sz m a v)
    | None => None (* some addresses were invalid *)
    end.

  Definition unchecked_store_byte_list(a: word)(l: list byte)(m: mem): mem :=
    unchecked_store_bytes (length l) m a (tuple.of_list l).

  Lemma unchecked_store_byte_list_cons: forall a x (l: list byte) m,
      unchecked_store_byte_list a (x :: l) m =
      map.put (unchecked_store_byte_list (word.add a (word.of_Z 1)) l m) a x.
  Proof.
    intros. reflexivity.
  Qed.

  Lemma lift_option_match{A B: Type}: forall (x: option A) (f: A -> B) (a: A),
      match x with
      | Some y => f y
      | None => f a
      end =
      f (match x with
         | Some y => y
         | None => a
         end).
  Proof. intros. destruct x; reflexivity. Qed.

  Lemma store_bytes_preserves_domain{wordOk: word.ok word}{memOk: map.ok mem}: forall n m a v m',
      store_bytes n m a v = Some m' ->
      map.same_domain m m'.
  Proof.
    unfold store_bytes, load_bytes.
    induction n; intros.
    - simpl in *.
      change (unchecked_store_bytes 0 m a v) with m in H.
      inversion H. apply map.same_domain_refl.
    - destruct (map.getmany_of_tuple m (footprint a (S n))) eqn: E; [|discriminate].
      inversion H. subst m'. clear H.
      unfold map.getmany_of_tuple in *.
      simpl in *.
      destruct (map.get m a) eqn: E'; [|discriminate].
      destruct_one_match_hyp; [|discriminate].
      inversion E. subst t. clear E.
      unfold unchecked_store_bytes in *. simpl.
      destruct v as [v vs].
      eapply map.same_domain_trans.
      + eapply IHn. unfold map.getmany_of_tuple. rewrite E0. reflexivity.
      + eapply map.same_domain_put_r.
        * eapply map.same_domain_refl.
        * rewrite map.putmany_of_tuple_to_putmany.
          rewrite map.get_putmany_dec.
          rewrite E'.
          rewrite lift_option_match.
          reflexivity.
  Qed.

End MemAccess.


Require Import riscv.Utility.Utility.

Section MemAccess2.
  Context {width} {word: word width} {mem: map.map word byte}.

  Definition loadByte:   mem -> word -> option w8  := load_bytes 1.
  Definition loadHalf:   mem -> word -> option w16 := load_bytes 2.
  Definition loadWord:   mem -> word -> option w32 := load_bytes 4.
  Definition loadDouble: mem -> word -> option w64 := load_bytes 8.

  Definition storeByte  : mem -> word -> w8  -> option mem := store_bytes 1.
  Definition storeHalf  : mem -> word -> w16 -> option mem := store_bytes 2.
  Definition storeWord  : mem -> word -> w32 -> option mem := store_bytes 4.
  Definition storeDouble: mem -> word -> w64 -> option mem := store_bytes 8.
End MemAccess2.


Local Unset Universe Polymorphism.

Section MemoryHelpers.
  Context {width} {word: word width} {word_ok: word.ok word}.
  Add Ring wring: (@word.ring_theory width word word_ok).

  Goal forall (a: word), word.add a (word.of_Z 0) = a. intros. ring. Qed.

  Lemma regToZ_unsigned_add: forall (a b: word),
      0 <= word.unsigned a + word.unsigned b < 2 ^ width ->
      word.unsigned (word.add a b) = word.unsigned a + word.unsigned b.
  Proof.
    intros.
    rewrite word.unsigned_add.
    apply Z.mod_small. assumption.
  Qed.

  Lemma regToZ_unsigned_add_l: forall (a: Z) (b: word),
      0 <= a ->
      0 <= a + word.unsigned b < 2 ^ width ->
      word.unsigned (word.add (word.of_Z a) b) = a + word.unsigned b.
  Proof.
    intros.
    rewrite word.unsigned_add.
    rewrite word.unsigned_of_Z.
    pose proof (word.unsigned_range b).
    unfold word.wrap.
    rewrite (Z.mod_small a) by blia.
    rewrite Z.mod_small by assumption.
    reflexivity.
  Qed.

  Lemma regToZ_unsigned_add_r: forall (a: word) (b: Z),
      0 <= b ->
      0 <= word.unsigned a + b < 2 ^ width ->
      word.unsigned (word.add a (word.of_Z b)) = word.unsigned a + b.
  Proof.
    intros.
    rewrite word.unsigned_add.
    rewrite word.unsigned_of_Z.
    pose proof (word.unsigned_range a).
    unfold word.wrap.
    rewrite (Z.mod_small b) by blia.
    rewrite Z.mod_small by assumption.
    reflexivity.
  Qed.
End MemoryHelpers.
