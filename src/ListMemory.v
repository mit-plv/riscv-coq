Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import riscv.Utility.
Require Import riscv.util.Monads.
Require Import riscv.Memory.
Require Import riscv.util.Tactics.
Require riscv.ListMemoryZAddr.


Local Open Scope Z_scope.

Definition align(alignment: Z)(n: Z): Z := alignment * (n / alignment).

Lemma align_lt: forall a n,
    0 < a ->
    align a n <= n.
Proof.
  intros. unfold align.
  apply Z.mul_div_le.
  assumption.
Qed.

Lemma align8_lt: forall n, align 8 n <= n.
Proof.
  intros. apply align_lt. omega.
Qed.

Lemma align_eq: forall a n,
    0 < a  ->
    n mod a = 0 ->
    align a n = n.
Proof.
  intros. unfold align. symmetry. apply Z.div_exact; omega.
Qed.

Lemma align8_eq: forall n,
    n mod 8 = 0 ->
    align 8 n = n.
Proof.
  intros. apply align_eq; omega.
Qed.


Definition mem := ListMemoryZAddr.mem.

Section Memory.

  Context {mword: Set}.
  Context {MW: MachineWidth mword}.

  Definition mem_size(m: mem): Z :=
    align 8 (Z.min (2 ^ XLEN) (ListMemoryZAddr.mem_size m)).

  Definition read_byte(m: mem)(a: mword): word 8 :=
    ListMemoryZAddr.read_byte m (regToZ_unsigned a).

  Definition read_half(m: mem)(a: mword): word 16 :=
    ListMemoryZAddr.read_half m (regToZ_unsigned a).

  Definition read_word(m: mem)(a: mword): word 32 :=
    ListMemoryZAddr.read_word m (regToZ_unsigned a).

  Definition read_double(m: mem)(a: mword): word 64 :=
    ListMemoryZAddr.read_double m (regToZ_unsigned a).

  Definition write_byte(m: mem)(a: mword)(v: word 8): mem :=
    ListMemoryZAddr.write_byte m (regToZ_unsigned a) v.

  Definition write_half(m: mem)(a: mword)(v: word 16): mem :=
    ListMemoryZAddr.write_half m (regToZ_unsigned a) v.

  Definition write_word(m: mem)(a: mword)(v: word 32): mem :=
    ListMemoryZAddr.write_word m (regToZ_unsigned a) v.

  Definition write_double(m: mem)(a: mword)(v: word 64): mem :=
    ListMemoryZAddr.write_double m (regToZ_unsigned a) v.

  Definition const_mem(default: word 8)(size: Z): mem :=
    ListMemoryZAddr.const_mem default size.

  Definition zero_mem: Z -> mem := const_mem (ZToWord 8 0).

  (* Since mem_size is a bit fancy, we better prove that it's possible to create memory of any
     desired size (as long as it's a multiple of 8 and not bigger than the biggest address) *)
  Lemma const_mem_mem_size: forall size default,
      size mod 8 = 0 ->
      0 <= size <= 2 ^ XLEN ->
      mem_size (const_mem default size) = size.
  Proof.
    intros. unfold mem_size, const_mem. rewrite ListMemoryZAddr.const_mem_mem_size by omega.
    replace (Z.min (2 ^ XLEN) size) with size by momega.
    apply align8_eq. assumption.
  Qed.

End Memory.

Ltac pose_bounds :=
  repeat match goal with
         | _: context [align 8 ?x] |- _=> unique pose proof (align8_lt x)
         | |- context [align 8 ?x]     => unique pose proof (align8_lt x)
         | w: _ |- _ => unique pose proof (regToZ_unsigned_bounds w)
         end.

Local Ltac wrap L :=
  intros;
  repeat match goal with
         | H: valid_addr _ _ _ |- _ => destruct H
         end;
  unfold mem_size, ListMemoryZAddr.mem_size in *;
  first [do 2 f_equal; apply L | apply L];
  unfold ListMemoryZAddr.mem_size;
  pose_bounds;
  try apply ne_regToZ_unsigned;
  (congruence || momega || idtac).

Instance mem_is_Memory(mword: Set){MW: MachineWidth mword}: Memory mem mword := 
{|
  memSize     := mem_size;
  loadByte    := read_byte;
  loadHalf    := read_half;
  loadWord    := read_word;
  loadDouble  := read_double;
  storeByte   := write_byte;
  storeHalf   := write_half;
  storeWord   := write_word;
  storeDouble := write_double;
|}.
- intros. unfold mem_size. pose_bounds. momega.
- intros. unfold mem_size, align. rewrite Z.mul_comm. apply Z.mod_mul. congruence.
- wrap ListMemoryZAddr.write_read_byte_eq.
- wrap ListMemoryZAddr.write_read_byte_ne.
- wrap ListMemoryZAddr.write_byte_preserves_mem_size.
- wrap ListMemoryZAddr.write_read_half_eq.
- wrap ListMemoryZAddr.write_read_half_ne.
- wrap ListMemoryZAddr.write_half_preserves_mem_size.
- wrap ListMemoryZAddr.write_read_word_eq.
- wrap ListMemoryZAddr.write_read_word_ne.
- wrap ListMemoryZAddr.write_word_preserves_mem_size.
- wrap ListMemoryZAddr.write_read_double_eq.
- wrap ListMemoryZAddr.write_read_double_ne.
- wrap ListMemoryZAddr.write_double_preserves_mem_size.
- intros. unfold valid_addr, mem_size, read_byte in *. pose_bounds.
  rewrite regToZ_unsigned_add_r by momega. reflexivity.
- intros. unfold valid_addr, mem_size, read_half in *. pose_bounds.
  rewrite regToZ_unsigned_add_r by momega. reflexivity.
- intros. unfold valid_addr, mem_size, read_word in *. pose_bounds.
  rewrite regToZ_unsigned_add_r by momega. reflexivity.
Defined.
