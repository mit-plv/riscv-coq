Require Import bbv.Word.

Class Memory(m: Set)(a: Set) := mkMemory {
  loadByte   : m -> a -> word  8;
  loadHalf   : m -> a -> word 16;
  loadWord   : m -> a -> word 32;
  loadDouble : m -> a -> word 64;
  storeByte  : m -> a -> word  8 -> m;
  storeHalf  : m -> a -> word 16 -> m;
  storeWord  : m -> a -> word 32 -> m;
  storeDouble: m -> a -> word 64 -> m;
}.

Section MemoryHelpers.

  Context {sz: nat}.
  Context {Mem: Set}.
  Context {MM: Memory Mem (word sz)}.

  Fixpoint store_byte_list(l: list (word 8))(a: word sz)(m: Mem): Mem :=
    match l with
    | nil => m
    | cons w l' => let m' := storeByte m a w in store_byte_list l' (a ^+ $1) m'
    end.

  Fixpoint load_byte_list(m: Mem)(start: word sz)(count: nat): list (word 8) :=
    match count with
    | S c => loadByte m start :: load_byte_list m (start ^+ $1) c
    | O => nil
    end.

  Fixpoint store_half_list(l: list (word 16))(a: word sz)(m: Mem): Mem :=
    match l with
    | nil => m
    | cons w l' => let m' := storeHalf m a w in store_half_list l' (a ^+ $2) m'
    end.

  Fixpoint load_half_list(m: Mem)(start: word sz)(count: nat): list (word 16) :=
    match count with
    | S c => loadHalf m start :: load_half_list m (start ^+ $2) c
    | O => nil
    end.

  Fixpoint store_word_list(l: list (word 32))(a: word sz)(m: Mem): Mem :=
    match l with
    | nil => m
    | cons w l' => let m' := storeWord m a w in store_word_list l' (a ^+ $4) m'
    end.

  Fixpoint load_word_list(m: Mem)(start: word sz)(count: nat): list (word 32) :=
    match count with
    | S c => loadWord m start :: load_word_list m (start ^+ $4) c
    | O => nil
    end.

  Fixpoint store_double_list(l: list (word 64))(a: word sz)(m: Mem): Mem :=
    match l with
    | nil => m
    | cons w l' => let m' := storeDouble m a w in store_double_list l' (a ^+ $8) m'
    end.

  Fixpoint load_double_list(m: Mem)(start: word sz)(count: nat): list (word 64) :=
    match count with
    | S c => loadDouble m start :: load_double_list m (start ^+ $8) c
    | O => nil
    end.

End MemoryHelpers.
