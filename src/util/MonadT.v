Require Import Coq.Lists.List. Import ListNotations.


Class Monad(M: Type -> Type) := mkMonad {
  Bind: forall {A B}, M A -> (A -> M B) -> M B;
  Return: forall {A}, A -> M A;
  MonadEq: forall {A}, M A -> M A -> Prop;

  left_identity: forall {A B} (a: A) (f: A -> M B),
    MonadEq (Bind (Return a) f) (f a);
  right_identity: forall {A} (m: M A),
    MonadEq (Bind m Return) m;
  associativity: forall {A B C} (m: M A) (f: A -> M B) (g: B -> M C),
    MonadEq (Bind (Bind m f) g) (Bind m (fun x => Bind (f x) g))
}.


Notation "x <- m1 ; m2" := (Bind m1 (fun x => m2))
  (right associativity, at level 60) : monad_scope.
Notation "m1 ;; m2" := (Bind m1 (fun _ => m2))
  (right associativity, at level 60) : monad_scope.

Open Scope monad_scope.

Definition TODO{A: Type}: A. Admitted.


Instance option_Monad: Monad option := {|
  Bind := fun {A B: Type} (o: option A) (f: A -> option B) => match o with
            | Some x => f x
            | None => None
            end;
  Return := fun {A: Type} (a: A) => Some a;
  MonadEq := fun {A: Type} => @eq (option A);
|}.
Proof.
  - intros. reflexivity.
  - intros. destruct m; reflexivity.
  - intros. destruct m; reflexivity.
Defined.

Definition optionT(M: Type -> Type)(A: Type) := M (option A).

Instance OptionT_is_Monad(M: Type -> Type){MM: Monad M}: Monad (optionT M) := {|
  Bind{A}{B}(m: M (option A))(f: A -> M (option B)) :=
    Bind m (fun (o: option A) =>
              match o with
              | Some a => f a
              | None => Return None
              end);
  Return{A}(a: A) := Return (Some a);
  MonadEq{A} := @MonadEq M MM (option A);
|}.
Proof.
  all: intros.
  - apply (left_identity (Some a) (fun o =>
                                     match o with
                                     | Some a => f a
                                     | None => Return None
                                       end)).
  - pose proof (@right_identity M MM (option A) m).
    (* probably will need refl/sym/trans of MonadEq *)
Admitted.

Module OptionMonad.
  Definition success{A: Type}: A -> option A := Some.
  Definition failure{A: Type}: option A := None.
  Definition recover{A: Type}(oa: option A)(default: A): A :=
    match oa with
    | Some a => a
    | None => default
    end.
End OptionMonad.


Definition State(S A: Type) := S -> (A * S).

Instance State_Monad(S: Type): Monad (State S) := {|
  Bind := fun {A B: Type} (m: State S A) (f: A -> State S B) =>
              fun (s: S) => let (a, s') := m s in f a s' ;
  Return := fun {A: Type} (a: A) =>
                fun (s: S) => (a, s);
  MonadEq := fun {A: Type} (m1 m2: State S A) =>
                 forall s, m1 s = m2 s;
|}.
Proof.
  - intros. reflexivity.
  - intros. destruct (m s). reflexivity.
  - intros. destruct (m s). reflexivity.
Defined.

Definition StateT(S: Type)(M: Type -> Type)(A: Type) := S -> M (A * S)%type.

Instance StateT_is_Monad(M: Type -> Type){MM: Monad M}(S: Type): Monad (StateT S M) := {|
  Bind{A B: Type}(m: StateT S M A)(f: A -> StateT S M B) :=
    fun (s: S) => Bind (m s) (fun '(a, s) => f a s);
  Return{A: Type}(a: A) :=
    fun (s: S) => Return (a, s);
  MonadEq{A: Type}(m1 m2: StateT S M A) := forall (s: S), MonadEq (m1 s) (m2 s);
|}.
Admitted.

Module StateMonad.
  Definition get{S: Type}: State S S := fun (s: S) => (s, s).
  Definition gets{S A: Type}(f: S -> A): State S A := fun (s: S) => (f s, s).
  Definition put{S: Type}(s: S): State S unit := fun _ => (tt, s).
End StateMonad.


Definition NonDet(A: Type) := A -> Prop.

Module NonDetMonad.

  Definition flatMapSet{A B: Type}(aset: A -> Prop)(f: A -> (B -> Prop)): B -> Prop :=
    fun b => exists a, aset a /\ f a b.

  Definition mapSet{A B: Type}(aset: A -> Prop)(f: A -> B): B -> Prop :=
    fun b => exists a, aset a /\ f a = b.

  Definition bigUnion{B: Type}(sets: (B -> Prop) -> Prop): B -> Prop :=
    fun b => exists set, sets set /\ set b.

  Definition flatMapSet'{A B: Type}(aset: A -> Prop)(f: A -> (B -> Prop)): B -> Prop :=
    bigUnion (mapSet aset f).

  Definition setEq{A: Type}(set1 set2: A -> Prop): Prop :=
    forall a, set1 a <-> set2 a.

  Definition singletonSet{A: Type}(a: A): A -> Prop := eq a.

  Definition arbitrary(A: Type): NonDet A := fun a => True.

End NonDetMonad.

Instance NonDet_Monad: Monad NonDet := {|
  Bind := @NonDetMonad.flatMapSet;
  Return := @NonDetMonad.singletonSet;
  MonadEq := @NonDetMonad.setEq;
|}.
Proof.
  all:
    cbv [NonDetMonad.flatMapSet NonDet NonDetMonad.setEq NonDetMonad.singletonSet];
    intros; try split; intros;
    repeat match goal with
           | p: _ * _  |- _ => destruct p
           | H: _ /\ _ |- _ => destruct H
           | E: exists y, _ |- _ => destruct E
           end;
    subst;
    eauto.
Defined.


Module Test.

  Import NonDetMonad. Import OptionMonad. Import StateMonad.

  Definition Riscv(S: Type): Type -> Type :=
    StateT S (optionT NonDet).
  Eval cbv in Riscv.

End Test.
