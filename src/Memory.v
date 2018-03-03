Require Import bbv.Word.
Require Import Coq.ZArith.BinInt.
Require Import riscv.util.Decidable.
Require Import Coq.Lists.List.
Require Import riscv.Utility.

Class Memory(m: Set)(a: Set) := mkMemory {
  loadByte : m -> a -> option Word8;
  loadHalf : m -> a -> option Word16;
  loadWord : m -> a -> option Word32;
  loadDouble : m -> a -> option Word64;
  storeByte : m -> a -> option Word8 -> m;
  storeHalf : m -> a -> option Word16 -> m;
  storeWord : m -> a -> option Word32 -> m;
  storeDouble : m -> a -> option Word64 -> m;
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

End Memory.

Arguments read_mem {_} _.
Arguments write_mem {_} _ _.
