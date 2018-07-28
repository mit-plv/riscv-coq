(* import List before bbv.Word, otherwise Word.combine gets shadowed and huge type class
   inference failure messages will appear *)
Require Import Coq.Lists.List.
Require Import Coq.omega.Omega.
Require Import bbv.Word.
Require Import Coq.ZArith.BinInt.
Require Import riscv.Utility.
Require Import riscv.util.Monads.
Require Import riscv.Memory.
Require Import riscv.util.Tactics.
Require riscv.ListMemoryNatAddr.
Import Word.ArithmeticNotations.
Import Word.ConversionNotations.
Local Open Scope word_scope.

Definition align(alignment: nat)(n: nat): nat := alignment * (n / alignment).

Lemma align_lt: forall a n,
    a <> 0 ->
    align a n <= n.
Proof.
  intros. unfold align.
  apply Nat.mul_div_le.
  assumption.
Qed.

Lemma align8_lt: forall n, align 8 n <= n.
Proof.
  intros. apply align_lt. congruence.
Qed.

Lemma align_eq: forall a n,
    a <> 0 ->
    n mod a = 0 ->
    align a n = n.
Proof.
  intros. unfold align. symmetry. apply Nat.div_exact; assumption.
Qed.

Lemma align8_eq: forall n,
    n mod 8 = 0 ->
    align 8 n = n.
Proof.
  intros. apply align_eq; congruence.
Qed.
  

(* bitwidth w is ignored on RHS, but we still want to carry it in the type *)
Definition mem(w: nat) := ListMemoryNatAddr.mem.

Section Memory.

  Context {w: nat}. (* bit width of memory addresses *)

  Definition mem_size(m: mem w): nat := align 8 (min (pow2 w) (ListMemoryNatAddr.mem_size m)).

  Definition read_byte(m: mem w)(a: word w): word 8 :=
    ListMemoryNatAddr.read_byte m (wordToNat a).

  Definition read_half(m: mem w)(a: word w): word 16 :=
    ListMemoryNatAddr.read_half m (wordToNat a).

  Definition read_word(m: mem w)(a: word w): word 32 :=
    ListMemoryNatAddr.read_word m (wordToNat a).

  Definition read_double(m: mem w)(a: word w): word 64 :=
    ListMemoryNatAddr.read_double m (wordToNat a).

  Definition write_byte(m: mem w)(a: word w)(v: word 8): mem w :=
    ListMemoryNatAddr.write_byte m (wordToNat a) v.

  Definition write_half(m: mem w)(a: word w)(v: word 16): mem w :=
    ListMemoryNatAddr.write_half m (wordToNat a) v.

  Definition write_word(m: mem w)(a: word w)(v: word 32): mem w :=
    ListMemoryNatAddr.write_word m (wordToNat a) v.

  Definition write_double(m: mem w)(a: word w)(v: word 64): mem w :=
    ListMemoryNatAddr.write_double m (wordToNat a) v.

  Definition const_mem(default: word 8)(size: nat): mem w :=
    ListMemoryNatAddr.const_mem default size.

  Definition zero_mem: nat -> mem w := const_mem $0.

  (* Since mem_size is a bit fancy, we better prove that it's possible to create memory of any
     desired size (as long as it's a multiple of 8 and not bigger than the biggest address) *)
  Lemma const_mem_mem_size: forall size default,
      size mod 8 = 0 ->
      size <= pow2 w ->
      mem_size (const_mem default size) = size.
  Proof.
    intros. unfold mem_size. rewrite ListMemoryNatAddr.const_mem_mem_size.
    replace (Init.Nat.min (pow2 w) size) with size by momega.
    apply align8_eq.
    assumption.
  Qed.
            
End Memory.

Lemma wordToNat_wplus'': forall sz (a: word sz) (b: nat),
    #a + b < pow2 sz -> #(a ^+ $b) = #a + b.
Proof.
  intros. rewrite wordToNat_wplus';
  rewrite wordToNat_natToWord_2; omega.
Qed.

Ltac pose_align8_lt :=
  repeat match goal with
         | _: context [align 8 ?x] |- _=> unique pose proof (align8_lt x)
         | |- context [align 8 ?x]     => unique pose proof (align8_lt x)
         end.

Local Ltac wrap L :=
  intros;
  repeat match goal with
         | H: valid_addr _ _ _ |- _ => destruct H
         end;
  unfold mem_size, ListMemoryNatAddr.mem_size in *;
  first [do 2 f_equal; apply L | apply L];
  unfold ListMemoryNatAddr.mem_size;
  pose_align8_lt;
  try apply wordToNat_neq1;
  (congruence || momega || idtac).    


Instance mem_is_Memory(w: nat): Memory (mem w) w := {|
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
- intros. unfold mem_size. pose_align8_lt. momega.
- intros. unfold mem_size, align. rewrite Nat.mul_comm. apply Nat.mod_mul. congruence.
- wrap ListMemoryNatAddr.write_read_byte_eq.
- wrap ListMemoryNatAddr.write_read_byte_ne.
- wrap ListMemoryNatAddr.write_byte_preserves_mem_size.
- wrap ListMemoryNatAddr.write_read_half_eq.
- wrap ListMemoryNatAddr.write_read_half_ne.
- wrap ListMemoryNatAddr.write_half_preserves_mem_size.
- wrap ListMemoryNatAddr.write_read_word_eq.
- wrap ListMemoryNatAddr.write_read_word_ne.
- wrap ListMemoryNatAddr.write_word_preserves_mem_size.
- wrap ListMemoryNatAddr.write_read_double_eq.
- wrap ListMemoryNatAddr.write_read_double_ne.
- wrap ListMemoryNatAddr.write_double_preserves_mem_size.
- unfold read_byte.
  intros. unfold valid_addr, mem_size in *. pose_align8_lt. rewrite wordToNat_wplus'' by momega. reflexivity.
- unfold read_half.
  intros. unfold valid_addr, mem_size in *. pose_align8_lt. rewrite wordToNat_wplus'' by momega. reflexivity.
- unfold read_word.
  intros. unfold valid_addr, mem_size in *. pose_align8_lt. rewrite wordToNat_wplus'' by momega. reflexivity.
Defined.
