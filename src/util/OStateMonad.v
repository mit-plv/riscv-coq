Require Import Coq.Logic.FunctionalExtensionality.
Require Export riscv.util.Monad.
Require Export riscv.util.MonadPlus.

Definition OState(S A: Type) := S -> option (A * S).

Instance OState_Monad(S: Type): Monad (OState S) := {|
  Bind := fun {A B: Type} (m: OState S A) (f: A -> OState S B) =>
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

Instance OState_MonadPlus(S: Type): MonadPlus (OState S) := {|
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

Definition get{S: Type}: OState S S := fun (s: S) => Some (s, s).
Definition gets{S A: Type}(f: S -> A): OState S A := fun (s: S) => Some (f s, s).
Definition put{S: Type}(s: S): OState S unit := fun _ => Some (tt, s).
