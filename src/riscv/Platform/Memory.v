Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import coqutil.Word.Interface.
Require Import coqutil.Word.Properties.
Require Import coqutil.Word.Bitwidth.
Require Import coqutil.Datatypes.HList.
Require Import coqutil.Datatypes.PrimitivePair.
Require Import coqutil.Map.Interface.
Require Import coqutil.Map.Properties.
Require Import coqutil.Map.Memory.
Require Import coqutil.Map.SeparationMemory.
Require Import coqutil.Tactics.Tactics.
Require Import coqutil.sanity.
Require Import coqutil.Z.Lia.
Require Import coqutil.Byte.
Require Import riscv.Utility.Utility.

Notation load_bytes sz (* : nat, value *) := (fun m addr =>
  match load_Z m addr sz with
  | Some z => Some (tuple.of_list (LittleEndianList.le_split sz z))
  | None => None
  end) (only parsing).

Definition store_bytes
  {width} {word: word width} {mem: map.map word byte}
  (sz: nat)(m: mem)(a: word)(v: tuple byte sz): option mem :=
  store_bytes m a (tuple.to_list v).

Section MemAccess2.
  Context {width} {word: word width} {mem: map.map word byte}.
  Implicit Types m : mem.

  Definition loadByte:   mem -> word -> option w8 := load_bytes 1.
  Definition loadHalf:   mem -> word -> option w16 := load_bytes 2.
  Definition loadWord:   mem -> word -> option w32 := load_bytes 4.
  Definition loadDouble: mem -> word -> option w64 := load_bytes 8.

  Definition storeByte  : mem -> word -> w8  -> option mem := store_bytes 1.
  Definition storeHalf  : mem -> word -> w16 -> option mem := store_bytes 2.
  Definition storeWord  : mem -> word -> w32 -> option mem := store_bytes 4.
  Definition storeDouble: mem -> word -> w64 -> option mem := store_bytes 8.
End MemAccess2.

Lemma store_bytes_preserves_domain
  {width} {word: word width} {mem: map.map word byte}
  {wordOk: word.ok word}{memOk: map.ok mem}: forall n m a v m',
    store_bytes n m a v = Some m' :> option mem ->
    map.same_domain m m'.
Proof. intros; eapply same_domain_store_bytes; eauto. Qed.

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
