Require Import Coq.Logic.FunctionalExtensionality.
Require Export riscv.util.Monad.
Require Export riscv.util.MonadPlus.

Definition State(S A: Type) := S -> (A * S).

Instance State_Monad(S: Type): Monad (State S) := {|
  Bind := fun {A B: Type} (m: State S A) (f: A -> State S B) =>
            fun (s: S) => let (a, s') := m s in f a s' ;
  Return := fun {A: Type} (a: A) =>
              fun (s: S) => (a, s)
|}.
- intros. reflexivity.
- intros. extensionality s. destruct (m s). reflexivity.
- intros. extensionality s. destruct (m s). reflexivity.
Defined.

Definition get{S: Type}: State S S := fun (s: S) => (s, s).
Definition gets{S A: Type}(f: S -> A): State S A := fun (s: S) => (f s, s).
Definition put{S: Type}(s: S): State S unit := fun _ => (tt, s).


(* Evaluate state computation with given initial state, discard final state, return final answer *)
Definition evalState{S A: Type}(m: State S A)(initial: S): A := fst (m initial).

(* Evaluate state computation with given initial state, discard final answer, return final state *)
Definition execState{S A: Type}(m: State S A)(initial: S): S := snd (m initial).


Definition OAState(S A: Type) := S -> option (A * S).

Instance OAState_Monad(S: Type): Monad (OAState S) := {|
  Bind := fun {A B: Type} (m: OAState S A) (f: A -> OAState S B) =>
            fun (s: S) => match m s with
            | Some (a, s') => f a s'
            | None => None
            end;
  Return := fun {A: Type} (a: A) =>
              fun (s: S) => Some (a, s)
|}.
- intros. reflexivity.
- intros. extensionality s. destruct (m s); [|reflexivity]. destruct p. reflexivity.
- intros. extensionality s. destruct (m s); [|reflexivity]. destruct p. reflexivity.
Defined.

Instance State_MonadPlus(S: Type): MonadPlus (OAState S) := {|
  mzero A s := @None (A * S);
  mplus A m1 m2 s := match m1 s with
    | Some p => Some p
    | None => m2 s
    end;
|}.
- intros. reflexivity.
- intros. simpl. extensionality s. destruct (v s); [|reflexivity]. destruct p. reflexivity.
- intros. extensionality s. destruct (m1 s); reflexivity.
Defined.
