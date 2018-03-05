(* import List before bbv.Word, otherwise Word.combine gets shadowed and huge type class
   inference failure messages will appear *)
Require Import Coq.Lists.List.
Require Import bbv.Word.
Require Import Coq.ZArith.BinInt.
Require Import riscv.util.Decidable.
Require Import riscv.Utility.
Require Import riscv.util.Monad.

Class Memory(m: Set)(a: Set) := mkMemory {
  loadByte : m -> a -> option Int8;
  loadHalf : m -> a -> option Int16;
  loadWord : m -> a -> option Int32;
  loadDouble : m -> a -> option Int64;
  storeByte : m -> a -> Int8 -> option m;
  storeHalf : m -> a -> Int16 -> option m;
  storeWord : m -> a -> Int32 -> option m;
  storeDouble : m -> a -> Int64 -> option m;
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
    | Some old_value => Some (fun y => if dec (x = y) then Some v else m y)
    | None => None
    end.

  Definition no_mem: mem := fun x => None.

  Definition zero_mem(size: Z): mem := fun x => if dec (x < size) then Some $0 else None.

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
  m <- write_byte m a (lobits 8 v); write_byte m a (hibits 8 v).
Definition write_word(m: mem 8)(a: Z)(v: word 32): option (mem 8) :=
  m <- write_half m a (lobits 16 v); write_half m a (hibits 16 v).
Definition write_double(m: mem 8)(a: Z)(v: word 64): option (mem 8) :=
  m <- write_word m a (lobits 32 v); write_word m a (hibits 32 v).


Definition uwordToZ{sz: nat}(w: word sz): Z := Z.of_N (wordToN w).

Definition wrapLoad{aw sz: nat}(f: mem 8 -> Z -> option (word sz))
  (m: mem 8)(a: word aw): option (SignedWord sz) :=
  match (f m (uwordToZ a)) with
  | Some x => Some (mkSignedWord x)
  | None => None
  end.

Definition wrapStore{aw sz: nat}(f: mem 8 -> Z -> word sz -> option (mem 8))
  (m: mem 8)(a: word aw)(v: SignedWord sz): option (mem 8) :=
  match v with
  | mkSignedWord w => f m (uwordToZ a) w
  end.

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
