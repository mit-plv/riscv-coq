(* import List before bbv.Word, otherwise Word.combine gets shadowed and huge type class
   inference failure messages will appear *)
Require Import Coq.Lists.List.
Require Import bbv.Word.
Require Import Coq.ZArith.ZArith.
Require Import riscv.Utility.
Require Import riscv.util.Monads.
Import Word.ArithmeticNotations.
Import Word.ConversionNotations.
Local Open Scope word_scope.

(* TODO remove option here, making it very simple,
   and only use option based memory in compiler *)
Class Memory(m: Set)(a: Set) := mkMemory {
  loadByte : m -> a -> option (word 8);
  loadHalf : m -> a -> option (word 16);
  loadWord : m -> a -> option (word 32);
  loadDouble : m -> a -> option (word 64);
  storeByte : m -> a -> word 8 -> option m;
  storeHalf : m -> a -> word 16 -> option m;
  storeWord : m -> a -> word 32 -> option m;
  storeDouble : m -> a -> word 64 -> option m;
}.

(* memory addresses are represented using Z because word does not restrict them enough,
   there are always invalid memory addresses, which are represented by returning None,
   so we prefer Z, also because that's more "high-level computation" related, where we
   use Z, rather than "store state" related, where we use word *)

Local Open Scope Z_scope.

Section Memory.

  Variable w: nat. (* bit width of memory words *)

  Definition mem := Z -> option (word w).

  Definition read_mem(x: Z)(m: mem): option (word w) := m x.

  Definition write_mem(x: Z)(v: word w)(m: mem): option mem :=
    match m x with
    | Some old_value => Some (fun y => if Z.eqb x y then Some v else m y)
    | None => None
    end.

  Definition no_mem: mem := fun x => None.

  Definition const_mem(size: Z)(default: word w): mem :=
    fun x => if ZArith_dec.Z_lt_dec x size then Some default else None.

  Definition zero_mem(size: Z): mem := const_mem size $0.

  Definition counter_mem(size: Z): mem :=
    fun x => if ZArith_dec.Z_lt_dec x size then Some (ZToWord w x) else None.

End Memory.

Arguments read_mem {_} _.
Arguments write_mem {_} _ _.

Definition read_byte(m: mem 8)(a: Z): option (word 8) := read_mem a m.
Definition read_half(m: mem 8)(a: Z): option (word 16) :=
  v0 <- read_byte m a; v1 <- read_byte m (a + 1); Return (combine v0 v1).
Definition read_word(m: mem 8)(a: Z): option (word 32) :=
  v0 <- read_half m a; v1 <- read_half m (a + 2); Return (combine v0 v1).
Definition read_double(m: mem 8)(a: Z): option (word 64) :=
  v0 <- read_word m a; v1 <- read_word m (a + 4); Return (combine v0 v1).

Definition lobits(sz: nat)(w: word (sz + sz)): word sz := split1 sz sz w.
Definition hibits(sz: nat)(w: word (sz + sz)): word sz := split2 sz sz w.

Definition write_byte(m: mem 8)(a: Z)(v: word 8): option (mem 8) := write_mem a v m.
Definition write_half(m: mem 8)(a: Z)(v: word 16): option (mem 8) :=
  m <- write_byte m a (lobits 8 v); write_byte m (a + 1) (hibits 8 v).
Definition write_word(m: mem 8)(a: Z)(v: word 32): option (mem 8) :=
  m <- write_half m a (lobits 16 v); write_half m (a + 2) (hibits 16 v).
Definition write_double(m: mem 8)(a: Z)(v: word 64): option (mem 8) :=
  m <- write_word m a (lobits 32 v); write_word m (a + 4) (hibits 32 v).


Definition wrapLoad{aw sz: nat}(f: mem 8 -> Z -> option (word sz))
  (m: mem 8)(a: word aw): option (word sz) := f m (uwordToZ a).

Definition wrapStore{aw sz: nat}(f: mem 8 -> Z -> word sz -> option (mem 8))
  (m: mem 8)(a: word aw)(v: word sz): option (mem 8) := f m (uwordToZ a) v.

Instance mem_is_Memory(aw: nat): Memory (mem 8) (word aw) := {|
  loadByte   := wrapLoad read_byte;
  loadHalf   := wrapLoad read_half;
  loadWord   := wrapLoad read_word;
  loadDouble := wrapLoad read_double;
  storeByte   := wrapStore write_byte;
  storeHalf   := wrapStore write_half;
  storeWord   := wrapStore write_word;
  storeDouble := wrapStore write_double;
|}.


Section store_retrieve.

  Context {sz: nat}.

  Fixpoint storeWords(l: list (word 32))(a: word sz)(m: mem 8): option (mem 8) :=
    match l with
    | nil => Some m
    | cons w l' =>
        match storeWord m a w with
        | Some m' => storeWords l' (a ^+ $4) m'
        | None => None
        end
    end.

  Fixpoint mem_to_word_list(m: mem 8)(start: Z)(count: nat): list (option (word 32)) :=
    match count with
    | S c => read_word m start :: mem_to_word_list m (start + 4) c
    | O => nil
    end.

  Lemma write_read_byte: forall m m' a v ,
    write_byte m a v = Some m' ->
    read_byte m' a = Some v.
  Proof.
    intros. unfold write_byte, read_byte, read_mem, write_mem in *.
    destruct (m a) eqn: E; [|discriminate].
    inversion H. clear H. subst.
  Admitted.

  Lemma write_read_byte_diff: forall a1 a2 m m' v o,
    a2 <> a1 ->
    read_byte m a1 = o ->
    write_byte m a2 v = Some m' ->
    read_byte m' a1 = o.
  Proof.
    intros. unfold read_byte, write_byte, read_mem, write_mem in *.
    destruct (m a2) eqn: E; [|discriminate].
    inversion H1.
  Admitted.

  Lemma write_read_half: forall m m' a v ,
    write_half m a v = Some m' ->
    read_half m' a = Some v.
  Proof.
    intros. unfold write_half, read_half in *. simpl in *.
    match goal with
    | H: match ?x with _ => _ end = Some _ |- _ => destruct x eqn: E; [|discriminate]
    end.
    pose proof H as H'.
    apply write_read_byte in H'. rewrite H'.
    pose proof E as E'.
    apply write_read_byte in E'.
    assert (a + 1 <> a) as Q by omega.
    pose proof (write_read_byte_diff a _ m0 m' _ _ Q E' H) as P.
    rewrite P.
    f_equal.
    unfold lobits, hibits.
    apply combine_split.
  Qed.

  Lemma write_read_word: forall m m' a v ,
    write_word m a v = Some m' ->
    read_word m' a = Some v.
  Admitted.

  Lemma store_retrieve_word_list: forall l a m m',
    storeWords l a m = Some m' ->
    mem_to_word_list m' (uwordToZ a) (length l) = map Some l.
  Proof.
    induction l; intros; simpl in *; try reflexivity.
    destruct (wrapStore write_word m a0 a) eqn: F; [|discriminate].
    specialize IHl with (1 := H).
    assert (uwordToZ (a0 ^+ $4) = uwordToZ a0 + 4) as E by admit.
    rewrite E in IHl.
    rewrite IHl.
    f_equal.
    unfold wrapStore in F.
  Abort.

End store_retrieve.
