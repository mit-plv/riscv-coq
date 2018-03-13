Require Import Coq.Lists.List.
Import ListNotations.
Require Import bbv.Word.
Require Import riscv.Memory.
Require Import riscv.MonadicMemory.
Require Import riscv.util.Monads.

Inductive TraceEvent{a: Set}: Set :=
| Trace_loadByte   : a -> word  8 -> TraceEvent
| Trace_loadHalf   : a -> word 16 -> TraceEvent
| Trace_loadWord   : a -> word 32 -> TraceEvent
| Trace_loadDouble : a -> word 64 -> TraceEvent
| Trace_storeByte  : a -> word  8 -> TraceEvent
| Trace_storeHalf  : a -> word 16 -> TraceEvent
| Trace_storeWord  : a -> word 32 -> TraceEvent
| Trace_storeDouble: a -> word 64 -> TraceEvent.

Arguments TraceEvent: clear implicits.

Definition LoggingMemory(m a: Set) := (m * list (TraceEvent a))%type.

Definition log{M A: Set}(m: LoggingMemory M A)(e: TraceEvent A): LoggingMemory M A :=
  (fst m, snd m ++ [e]).

Definition myInst M A: Monad (State (LoggingMemory M A)) := State_Monad _.

Existing Instance myInst.

Instance StateLoggingMemory_is_MonadicMemory(M A: Set){MM: Memory M A}:
  MonadicMemory (State (LoggingMemory M A)) A :=
{|
  loadByte a :=
     m <- StateM.get;
     let r := Memory.loadByte (fst m) a in
     StateM.put (log m (Trace_loadByte a r));;
     Return r;
  loadHalf a :=
     m <- StateM.get;
     let r := Memory.loadHalf (fst m) a in
     StateM.put (log m (Trace_loadHalf a r));;
     Return r;
  loadWord a :=
     m <- StateM.get;
     let r := Memory.loadWord (fst m) a in
     StateM.put (log m (Trace_loadWord a r));;
     Return r;
  loadDouble a :=
     m <- StateM.get;
     let r := Memory.loadDouble (fst m) a in
     StateM.put (log m (Trace_loadDouble a r));;
     Return r;
  storeByte a v :=
     m <- StateM.get;
     let m' := Memory.storeByte (fst m) a v in
     StateM.put (log (m', snd m) (Trace_storeByte a v));
  storeHalf a v :=
     m <- StateM.get;
     let m' := Memory.storeHalf (fst m) a v in
     StateM.put (log (m', snd m) (Trace_storeHalf a v));
  storeWord a v :=
     m <- StateM.get;
     let m' := Memory.storeWord (fst m) a v in
     StateM.put (log (m', snd m) (Trace_storeWord a v));
  storeDouble a v :=
     m <- StateM.get;
     let m' := Memory.storeDouble (fst m) a v in
     StateM.put (log (m', snd m) (Trace_storeDouble a v));
|}.
