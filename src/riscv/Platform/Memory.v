Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import coqutil.Word.Bitwidth.
Require Import coqutil.Map.Interface.
Require Import coqutil.Map.Properties.
Require Import coqutil.Map.Memory.
Require Import coqutil.Word.LittleEndianList.
Require Import coqutil.Map.SeparationMemory.
Require Import coqutil.Tactics.Tactics.
Require Import coqutil.sanity.
Require Import coqutil.Z.Lia.
Require Import coqutil.Byte.
Require Import riscv.Utility.Utility.

Notation load_bytes sz (* : nat, value *) := (fun m addr =>
  match load_Z m addr sz with
  | Some z => Some (bits.of_Z (8 * Z.of_nat sz) z)
  | None => None
  end) (only parsing).

Definition store_bytes
  {width} {mem: map.map (bits width) byte}
  (sz: nat)(m: mem)(a: bits width)(v: bits (8 * Z.of_nat sz)): option mem :=
  store_Z m a sz (Zmod.unsigned v).

Section MemAccess2.
  Context {width: Z}.
  Local Notation word := (bits width).
  Context {mem: map.map word byte}.
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
  {width} {BW: Bitwidth width} {mem: map.map (bits width) byte}
  {memOk: map.ok mem}: forall n m a v m',
    store_bytes n m a v = Some m' :> option mem ->
    map.same_domain m m'.
Proof. intros; eapply (same_domain_store_bytes width_pos); eauto. Qed.

Section MemoryHelpers.
  Context {width} {BW: Bitwidth width}.
  Local Notation word := (bits width).

  Lemma regToZ_unsigned_add: forall (a b: word),
      0 <= Zmod.unsigned a + Zmod.unsigned b < 2 ^ width ->
      Zmod.unsigned (Zmod.add a b) = Zmod.unsigned a + Zmod.unsigned b.
  Proof.
    intros.
    rewrite Zmod.unsigned_add.
    apply Z.mod_small. assumption.
  Qed.

  Lemma regToZ_unsigned_add_l: forall (a: Z) (b: word),
      0 <= a ->
      0 <= a + Zmod.unsigned b < 2 ^ width ->
      Zmod.unsigned (Zmod.add (bits.of_Z _ a) b) = a + Zmod.unsigned b.
  Proof.
    intros.
    rewrite Zmod.unsigned_add.
    pose proof (bits.unsigned_range b width_nonneg).
    rewrite bits.unsigned_of_Z_small by lia.
    rewrite Z.mod_small by assumption.
    reflexivity.
  Qed.

  Lemma regToZ_unsigned_add_r: forall (a: word) (b: Z),
      0 <= b ->
      0 <= Zmod.unsigned a + b < 2 ^ width ->
      Zmod.unsigned (Zmod.add a (bits.of_Z _ b)) = Zmod.unsigned a + b.
  Proof.
    intros.
    rewrite Zmod.unsigned_add.
    pose proof (bits.unsigned_range a width_nonneg).
    rewrite bits.unsigned_of_Z_small by lia.
    rewrite Z.mod_small by assumption.
    reflexivity.
  Qed.
End MemoryHelpers.

Lemma le_split_unsigned_of_Z: forall n z,
    LittleEndianList.le_split n (Zmod.unsigned (bits.of_Z (8 * Z.of_nat n) z)) =
    LittleEndianList.le_split n z.
Proof.
  intros. rewrite bits.unsigned_of_Z, Z.mul_comm. symmetry. apply LittleEndianList.le_split_mod.
Qed.

Lemma unsigned_of_Z_le_combine: forall n bs,
    length bs = n ->
    Zmod.unsigned (bits.of_Z (8 * Z.of_nat n) (LittleEndianList.le_combine bs)) =
    LittleEndianList.le_combine bs.
Proof.
  intros. subst. apply bits.unsigned_of_Z_small, LittleEndianList.le_combine_bound.
Qed.
