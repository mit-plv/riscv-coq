(* import List before bbv.Word, otherwise Word.combine gets shadowed and huge type class
   inference failure messages will appear *)
Require Import Coq.Lists.List.
Require Import bbv.Word.
Require Import Coq.ZArith.ZArith.
Require Import riscv.Utility.
Require Import riscv.util.Monads.
Require Import riscv.Memory.
Require Import riscv.util.Tactics.
Require riscv.ListMemoryZAddr.
Import Word.ArithmeticNotations.
Import Word.ConversionNotations.
Local Open Scope word_scope.

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


(* bitwidth w is ignored on RHS, but we still want to carry it in the type *)
Definition mem(w: nat) := ListMemoryZAddr.mem.

Section Memory.

  Context {w: nat}. (* bit width of memory addresses *)

  Definition mem_size(m: mem w): Z :=
    align 8 (Z.min (2 ^ Z.of_nat w) (ListMemoryZAddr.mem_size m)).

  Definition read_byte(m: mem w)(a: word w): word 8 :=
    ListMemoryZAddr.read_byte m (uwordToZ a).

  Definition read_half(m: mem w)(a: word w): word 16 :=
    ListMemoryZAddr.read_half m (uwordToZ a).

  Definition read_word(m: mem w)(a: word w): word 32 :=
    ListMemoryZAddr.read_word m (uwordToZ a).

  Definition read_double(m: mem w)(a: word w): word 64 :=
    ListMemoryZAddr.read_double m (uwordToZ a).

  Definition write_byte(m: mem w)(a: word w)(v: word 8): mem w :=
    ListMemoryZAddr.write_byte m (uwordToZ a) v.

  Definition write_half(m: mem w)(a: word w)(v: word 16): mem w :=
    ListMemoryZAddr.write_half m (uwordToZ a) v.

  Definition write_word(m: mem w)(a: word w)(v: word 32): mem w :=
    ListMemoryZAddr.write_word m (uwordToZ a) v.

  Definition write_double(m: mem w)(a: word w)(v: word 64): mem w :=
    ListMemoryZAddr.write_double m (uwordToZ a) v.

  Definition const_mem(default: word 8)(size: Z): mem w :=
    ListMemoryZAddr.const_mem default size.

  Definition zero_mem: Z -> mem w := const_mem $0.

  (* Since mem_size is a bit fancy, we better prove that it's possible to create memory of any
     desired size (as long as it's a multiple of 8 and not bigger than the biggest address) *)
  Lemma const_mem_mem_size: forall size default,
      size mod 8 = 0 ->
      0 <= size <= 2 ^ Z.of_nat w ->
      mem_size (const_mem default size) = size.
  Proof.
    intros. unfold mem_size, const_mem. rewrite ListMemoryZAddr.const_mem_mem_size by omega.
    replace (Z.min (2 ^ Z.of_nat w) size) with size by momega.
    apply align8_eq. assumption.
  Qed.

End Memory.

Ltac pose_align8_lt :=
  repeat match goal with
         | _: context [align 8 ?x] |- _=> unique pose proof (align8_lt x)
         | |- context [align 8 ?x]     => unique pose proof (align8_lt x)
         end.

Definition TODO{T: Type}: T. Admitted.

Local Ltac wrap L :=
  intros;
  repeat match goal with
         | H: valid_addr _ _ _ |- _ => destruct H
         end;
  unfold mem_size, ListMemoryZAddr.mem_size in *;
  first [do 2 f_equal; apply L | apply L];
  unfold ListMemoryZAddr.mem_size;
  pose_align8_lt;
  try apply wordToNat_neq1;
  (congruence || momega || apply TODO).

Instance mem_is_Memory(w: nat){MW: MachineWidth (word w)}(E: Z.of_nat w = XLEN)
: Memory (mem w) (word w) := 
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
- intros. unfold mem_size. pose_align8_lt.
  rewrite E in *.
  momega.
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
- apply TODO.
- apply TODO.
- apply TODO.
(*
- unfold read_byte.
  intros. unfold valid_addr, mem_size in *. pose_align8_lt. rewrite uwordToZ_wplus'' by momega. reflexivity.
- unfold read_half.
  intros. unfold valid_addr, mem_size in *. pose_align8_lt. rewrite uwordToZ_wplus'' by momega. reflexivity.
- unfold read_word.
  intros. unfold valid_addr, mem_size in *. pose_align8_lt. rewrite uwordToZ_wplus'' by momega. reflexivity.
*)
Defined.

Require Import riscv.MachineWidth32.

Instance mem32_is_Memory: Memory (mem 32) (word 32) := mem_is_Memory _ eq_refl.
