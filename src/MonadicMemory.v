Require Import riscv.Memory.
Require Import riscv.Utility.
Require Import riscv.util.Monads.

Class MonadicMemory(m: Type -> Type)(a: Type) := mkMonadicMemory {
  loadByte   : a -> m (word  8);
  loadHalf   : a -> m (word 16);
  loadWord   : a -> m (word 32);
  loadDouble : a -> m (word 64);
  storeByte  : a -> word  8 -> m unit;
  storeHalf  : a -> word 16 -> m unit;
  storeWord  : a -> word 32 -> m unit;
  storeDouble: a -> word 64 -> m unit;
}.

Definition wrapLoadO{M R: Type}{t: Type}{MW: MachineWidth t}{MM: Memory M t}(f: M -> t -> R)
  : t -> OState M R :=
  fun a => m <- get; Return (f m a).

Definition wrapStoreO{M R: Type}{t: Type}{MW: MachineWidth t}{MM: Memory M t}(f: M -> t -> R -> M)
  : t -> R -> OState M unit :=
  fun a v => m <- get; put (f m a v).

Instance OStateMemory(M: Type)(t: Type){MW: MachineWidth t}{MM: Memory M t}
  : MonadicMemory (OState M) t :=
{|
  loadByte := wrapLoadO Memory.loadByte;
  loadHalf := wrapLoadO Memory.loadHalf;
  loadWord := wrapLoadO Memory.loadWord;
  loadDouble := wrapLoadO Memory.loadDouble;
  storeByte := wrapStoreO Memory.storeByte;
  storeHalf := wrapStoreO Memory.storeHalf;
  storeWord := wrapStoreO Memory.storeWord;
  storeDouble := wrapStoreO Memory.storeDouble;
|}.

(*
Definition wrapLoad{M A R: Type}{MM: Memory M A}(f: M -> A -> R): A -> State M R :=
  fun a => m <- StateM.get; Return (f m a).

Definition wrapStore{M A R: Type}{MM: Memory M A}(f: M -> A -> R -> M): A -> R -> State M unit :=
  fun a v => m <- StateM.get; StateM.put (f m a v).

Instance StateMemory(M A: Type){MM: Memory M A}: MonadicMemory (State M) A := {|
  loadByte := wrapLoad Memory.loadByte;
  loadHalf := wrapLoad Memory.loadHalf;
  loadWord := wrapLoad Memory.loadWord;
  loadDouble := wrapLoad Memory.loadDouble;
  storeByte := wrapStore Memory.storeByte;
  storeHalf := wrapStore Memory.storeHalf;
  storeWord := wrapStore Memory.storeWord;
  storeDouble := wrapStore Memory.storeDouble;
|}.
*)
