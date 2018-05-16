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

(* bitwidth w is ignored on RHS, but we still want to carry it in the type *)
Definition mem(w: nat) := ListMemoryNatAddr.mem.

Section Memory.

  Context {w: nat}. (* bit width of memory addresses *)

  Definition mem_size(m: mem w): nat := min (pow2 w) (ListMemoryNatAddr.mem_size m).

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

  Definition const_mem(default: word 8)(max_addr: nat): mem w :=
    ListMemoryNatAddr.const_mem default (S max_addr).

  Definition zero_mem: nat -> mem w := const_mem $0.

End Memory.

Local Ltac wrap L :=
  intros;
  repeat match goal with
         | H: valid_addr _ _ _ |- _ => destruct H
         end;
  unfold mem_size, ListMemoryNatAddr.mem_size in *;
  first [f_equal; apply L | apply L];
  unfold ListMemoryNatAddr.mem_size;
  try apply wordToNat_neq1;
  (congruence || momega || idtac).    

Definition TODO{T: Type}: T. Admitted.

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
- intros. unfold mem_size. momega.
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
- intros. unfold read_half. unfold ListMemoryNatAddr.read_half.
  unfold read_byte.
  unfold valid_addr, mem_size in *.
  apply TODO. (* we need word lemmas not yet in Word.v *)
- apply TODO.
- apply TODO.
Defined.
