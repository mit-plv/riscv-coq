Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import coqutil.Word.Interface.
Require Import coqutil.Word.Properties.
Require Import coqutil.Datatypes.HList.
Require Import coqutil.Datatypes.PrimitivePair.
Require Import coqutil.Map.Interface.
Require Import coqutil.Tactics.Tactics.
Require Import coqutil.sanity.

Local Open Scope Z_scope.


Section MemAccess.
  Context {byte: word 8} {width: Z} {word: word width} {mem: map.map word byte}.

  Local Notation "' x <- a ; f" :=
    (match (a: option _) with
     | x => f
     | _ => None
     end)
      (right associativity, at level 70, x pattern).

  Fixpoint load(n: nat)(m: mem)(addr: word){struct n}: option (tuple byte n) :=
      match n with
      | O => Some tt
      | S n =>
        'Some b <- map.get m addr;
        'Some bs <- load n m (word.add addr (word.of_Z 1));
        Some (pair.mk b bs)
      end.

  Fixpoint unchecked_store(n: nat)(m: mem)(a: word): tuple byte n -> mem :=
    match n with
    | O => fun bs => m
    | S n => fun bs =>
         unchecked_store n (map.put m a (pair._1 bs)) (word.add a (word.of_Z 1)) (pair._2 bs)
    end.

  Definition store(n: nat)(m: mem)(a: word)(v: tuple byte n): option mem :=
    'Some _ <- load n m a; (* <- checks that all addresses are valid *)
    Some (unchecked_store n m a v).

  Fixpoint unchecked_store_byte_tuple_list{n: nat}(a: word)(l: list (tuple byte n))(m: mem): mem :=
    match l with
    | w :: rest => unchecked_store_byte_tuple_list
                     (word.add a (word.of_Z (Z.of_nat n))) rest (unchecked_store n m a w)
    | nil => m
    end.

End MemAccess.


Require Import riscv.Utility.

Section MemAccess2.
  Context {W: Words} {mem: map.map word byte}.

  Definition loadByte:   mem -> word -> option w8  := load 1.
  Definition loadHalf:   mem -> word -> option w16 := load 2.
  Definition loadWord:   mem -> word -> option w32 := load 4.
  Definition loadDouble: mem -> word -> option w64 := load 8.

  Definition storeByte  : mem -> word -> w8  -> option mem := store 1.
  Definition storeHalf  : mem -> word -> w16 -> option mem := store 2.
  Definition storeWord  : mem -> word -> w32 -> option mem := store 4.
  Definition storeDouble: mem -> word -> w64 -> option mem := store 8.
End MemAccess2.


Local Unset Universe Polymorphism.

Section MemoryHelpers.
  Context {W: Words}.
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
    rewrite (Z.mod_small a) by omega.
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
    rewrite (Z.mod_small b) by omega.
    rewrite Z.mod_small by assumption.
    reflexivity.
  Qed.
End MemoryHelpers.
