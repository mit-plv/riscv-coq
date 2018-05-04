Require Import bbv.Word.
Require Import Coq.omega.Omega.

Definition valid_addr{w: nat}(addr: word w)(alignment size: nat): Prop :=
  wordToNat addr + alignment <= size /\ (wordToNat addr) mod alignment = 0.

Class Memory(m: Set)(w: nat) := mkMemory {
  memSize: m -> nat;

  loadByte   : m -> (word w) -> word  8;
  loadHalf   : m -> (word w) -> word 16;
  loadWord   : m -> (word w) -> word 32;
  loadDouble : m -> (word w) -> word 64;
  storeByte  : m -> (word w) -> word  8 -> m;
  storeHalf  : m -> (word w) -> word 16 -> m;
  storeWord  : m -> (word w) -> word 32 -> m;
  storeDouble: m -> (word w) -> word 64 -> m;

  loadStoreByte_eq: forall m (a1 a2: word w) v,
    valid_addr a1 1 (memSize m) ->
    a2 = a1 ->
    loadByte (storeByte m a1 v) a2 = v;

  loadStoreByte_ne: forall m (a1 a2: word w) v,
    valid_addr a1 1 (memSize m) ->
    valid_addr a2 1 (memSize m) ->
    a2 <> a1 ->
    loadByte (storeByte m a1 v) a2 = loadByte m a2;

  storeByte_preserves_memSize: forall m (a: word w) v,
    memSize (storeByte m a v) = memSize m;

  loadStoreHalf_eq: forall m (a1 a2: word w) v,
    valid_addr a1 2 (memSize m) ->
    a2 = a1 ->
    loadHalf (storeHalf m a1 v) a2 = v;

  loadStoreHalf_ne: forall m (a1 a2: word w) v,
    valid_addr a1 2 (memSize m) ->
    valid_addr a2 2 (memSize m) ->
    a2 <> a1 ->
    loadHalf (storeHalf m a1 v) a2 = loadHalf m a2;

  storeHalf_preserves_memSize: forall m (a: word w) v,
    memSize (storeHalf m a v) = memSize m;

  loadStoreWord_eq: forall m (a1 a2: word w) v,
    valid_addr a1 4 (memSize m) ->
    a2 = a1 ->
    loadWord (storeWord m a1 v) a2 = v;

  loadStoreWord_ne: forall m (a1 a2: word w) v,
    valid_addr a1 4 (memSize m) ->
    valid_addr a2 4 (memSize m) ->
    a2 <> a1 ->
    loadWord (storeWord m a1 v) a2 = loadWord m a2;

  storeWord_preserves_memSize: forall m (a: word w) v,
    memSize (storeWord m a v) = memSize m;

  loadStoreDouble_eq: forall m (a1 a2: word w) v,
    valid_addr a1 8 (memSize m) ->
    a2 = a1 ->
    loadDouble (storeDouble m a1 v) a2 = v;

  loadStoreDouble_ne: forall m (a1 a2: word w) v,
    valid_addr a1 8 (memSize m) ->
    valid_addr a2 8 (memSize m) ->
    a2 <> a1 ->
    loadDouble (storeDouble m a1 v) a2 = loadDouble m a2;

  storeDouble_preserves_memSize: forall m (a: word w) v,
    memSize (storeDouble m a v) = memSize m;

}.

Section MemoryHelpers.

  Context {sz: nat}.
  Context {Mem: Set}.
  Context {MM: Memory Mem sz}.

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
