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

Definition mem(w: nat) :=
  { m: ListMemoryNatAddr.mem
  | ListMemoryNatAddr.mem_size m <= pow2 w /\ ListMemoryNatAddr.mem_size m mod 8 = 0 }.

Section Memory.

  Context {w: nat}. (* bit width of memory addresses *)

  Definition mem_size(m: mem w): nat := ListMemoryNatAddr.mem_size (proj1_sig m).

  Definition read_byte(m: mem w)(a: word w): word 8 :=
    ListMemoryNatAddr.read_byte (proj1_sig m) (wordToNat a).

  Definition read_half(m: mem w)(a: word w): word 16 :=
    ListMemoryNatAddr.read_half (proj1_sig m) (wordToNat a).

  Definition read_word(m: mem w)(a: word w): word 32 :=
    ListMemoryNatAddr.read_word (proj1_sig m) (wordToNat a).

  Definition read_double(m: mem w)(a: word w): word 64 :=
    ListMemoryNatAddr.read_double (proj1_sig m) (wordToNat a).

  Definition write_byte(m: mem w)(a: word w)(v: word 8): mem w.
    refine (exist _ (ListMemoryNatAddr.write_byte (proj1_sig m) (wordToNat a) v) _).
    destruct m. cbn [proj1_sig].
    rewrite ListMemoryNatAddr.write_byte_preserves_mem_size.
    assumption.
  Defined.
  
  Definition write_half(m: mem w)(a: word w)(v: word 16): mem w.
    refine (exist _ (ListMemoryNatAddr.write_half (proj1_sig m) (wordToNat a) v) _).
    destruct m. cbn [proj1_sig].
    rewrite ListMemoryNatAddr.write_half_preserves_mem_size.
    assumption.
  Defined.

  Definition write_word(m: mem w)(a: word w)(v: word 32): mem w.
    refine (exist _ (ListMemoryNatAddr.write_word (proj1_sig m) (wordToNat a) v) _).
    destruct m. cbn [proj1_sig].
    rewrite ListMemoryNatAddr.write_word_preserves_mem_size.
    assumption.
  Defined.

  Definition write_double(m: mem w)(a: word w)(v: word 64): mem w.
    refine (exist _ (ListMemoryNatAddr.write_double (proj1_sig m) (wordToNat a) v) _).
    destruct m. cbn [proj1_sig].
    rewrite ListMemoryNatAddr.write_double_preserves_mem_size.
    assumption.
  Defined.

  Definition const_mem(default: word 8)(size: nat):
    if ((size mod 8 =? 0) && (size <? pow2 w))%bool then mem w else unit.
    match goal with
    | |- if ?c then _ else _ => destruct c eqn: E; [|exact tt]
    end.
    rewrite Bool.andb_true_iff in E. destruct E as [E1 E2].
    refine (exist _ (ListMemoryNatAddr.const_mem default size) _).
  Abort.    

End Memory.
