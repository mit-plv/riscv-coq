Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Logic.PropExtensionality.
Require Import Coq.Lists.List.

Class Monad(M: Type -> Type) := mkMonad {
  Bind: forall {A B}, M A -> (A -> M B) -> M B;
  Return: forall {A}, A -> M A;

  left_identity: forall {A B} (a: A) (f: A -> M B),
    Bind (Return a) f = f a;
  right_identity: forall {A} (m: M A),
    Bind m Return = m;
  associativity: forall {A B C} (m: M A) (f: A -> M B) (g: B -> M C),
    Bind (Bind m f) g = Bind m (fun x => Bind (f x) g)
}.

Definition when{M: Type -> Type}{MM: Monad M}(a: bool)(b: M unit): M unit :=
  if a then b else Return tt.

Create HintDb unf_monad_ops.

Ltac prove_monad_law :=
  repeat match goal with
         | |- _ => intro
         | |- _ => apply functional_extensionality
         | |- _ => apply propositional_extensionality; split; intros
         | H: exists x, _ |- _ => destruct H
         | H: _ /\ _ |- _ => destruct H
         | p: _ * _ |- _ => destruct p
         | |- context [ let (_, _) := ?p in _ ] => let E := fresh "E" in destruct p eqn: E
         | H: Some _ = Some _ |- _ => inversion H; clear H; subst
         | H: (_, _) = (_, _) |- _ => inversion H; clear H; subst
         | |- _ => discriminate
         | |- _ => progress (autounfold with unf_monad_ops in *; subst; simpl in *)
         | |- _ => solve [eauto 10]
         | H: _ \/ _ |- _ => destruct H
         | o: option _ |- _ => destruct o
         end.

Instance option_Monad: Monad option := {|
  Bind := fun {A B: Type} (o: option A) (f: A -> option B) => match o with
          | Some x => f x
          | None => None
          end;
  Return := fun {A: Type} (a: A) => Some a
|}.
all: prove_monad_law.
Defined.


Definition NonDet(A: Type): Type := A -> Prop.

Instance NonDet_Monad: Monad NonDet := {|
  Bind{A B}(m: NonDet A)(f: A -> NonDet B) :=
    fun (b: B) => exists a, m a /\ f a b;
  Return{A} := eq;
|}.
all: prove_monad_law.
Defined.


Definition State(S A: Type) := S -> (A * S).

Instance State_Monad(S: Type): Monad (State S) := {|
  Bind := fun {A B: Type} (m: State S A) (f: A -> State S B) =>
            fun (s: S) => let (a, s') := m s in f a s' ;
  Return := fun {A: Type} (a: A) =>
              fun (s: S) => (a, s)
|}.
all: prove_monad_law.
Defined.

Module StateOperations.
  Definition get{S: Type}: State S S := fun (s: S) => (s, s).
  Definition gets{S A: Type}(f: S -> A): State S A := fun (s: S) => (f s, s).
  Definition put{S: Type}(s: S): State S unit := fun _ => (tt, s).
End StateOperations.


Definition OState(S A: Type) := S -> (option A) * S.

Instance OState_Monad(S: Type): Monad (OState S) := {|
  Bind := fun {A B: Type} (m: OState S A) (f: A -> OState S B) =>
            fun (s: S) => match m s with
            | (Some a, s') => f a s'
            | (None, s') => (None, s')
            end;
  Return := fun {A: Type} (a: A) =>
              fun (s: S) => (Some a, s)
|}.
all: prove_monad_law.
Defined.

Module OStateOperations.

  Definition get{S: Type}: OState S S := fun (s: S) => (Some s, s).

  Definition put{S: Type}(s: S): OState S unit := fun _ => (Some tt, s).

  Definition fail_hard{S A: Type}: OState S A :=
    fun (s: S) => (None, s).

  Hint Unfold get put fail_hard : unf_monad_ops.

  Lemma Bind_get{S A: Type}: forall (f: S -> OState S A) (s: S),
      Bind get f s = f s s.
  Proof. prove_monad_law. Qed.

  Lemma Bind_put{S A: Type}: forall (f: unit -> OState S A) (s0 s1: S),
      Bind (put s1) f s0 = f tt s1.
  Proof. prove_monad_law. Qed.

  (* provides the link between "S -> option A * S" and "S -> (S -> Prop) -> Prop" *)
  Definition computation_satisfies{S: Type}(m: OState S unit)(s: S)(post: S -> Prop): Prop :=
    exists s', m s = (Some tt, s') /\ post s'.

  (* provides the link between "S -> option A * S" and "S -> (A -> S -> Prop) -> Prop" *)
  Definition computation_with_answer_satisfies
             {S A: Type}(m: OState S A)(s: S)(post: A -> S -> Prop): Prop :=
    exists a s', m s = (Some a, s') /\ post a s'.

  Lemma computation_with_answer_satisfies_Return{S A: Type}: forall (a: A) (initial: S) post,
      computation_with_answer_satisfies (Return a) initial post ->
      post a initial.
  Proof.
    unfold computation_with_answer_satisfies.
    intros. simpl in *.
    destruct H as (? & ? & ? & ?).
    inversion H. subst. assumption.
  Qed.

  Lemma computation_with_answer_satisfies_Bind{S A B: Type}:
    forall (m: OState S A) (f: A -> OState S B) (initial: S) post,
      computation_with_answer_satisfies (Bind m f) initial post ->
      (exists mid, computation_with_answer_satisfies m initial mid
                   /\ forall a s, mid a s -> computation_with_answer_satisfies (f a) s post).
  Proof.
    unfold computation_with_answer_satisfies.
    intros. simpl in *.
    eexists.
    split.
    - intros. destruct (m initial).
      destruct o. 2: { destruct H as (? & ? & ? & ?). discriminate. }
      do 2 eexists; split; [reflexivity|].
      exact H.
    - simpl. intros. assumption.
  Qed.

  Lemma computation_with_answer_satisfies_get{S: Type}: forall (initial: S) post,
      computation_with_answer_satisfies get initial post ->
      post initial initial.
  Proof.
    unfold computation_with_answer_satisfies, get.
    intros. destruct H as (? & ? & ? & ?).
    inversion H. subst. assumption.
  Qed.

  Lemma computation_with_answer_satisfies_put{S: Type}: forall (initial new: S) post,
      computation_with_answer_satisfies (put new) initial post ->
      post tt new.
  Proof.
    unfold computation_with_answer_satisfies, put.
    intros. destruct H as (? & ? & ? & ?).
    inversion H. subst. assumption.
  Qed.

  Lemma computation_with_answer_satisfies_fail_hard{S A: Type}:
    forall (initial: S) (post: A -> S -> Prop),
      computation_with_answer_satisfies fail_hard initial post ->
      False.
  Proof.
    unfold computation_with_answer_satisfies, fail_hard.
    intros. destruct H as (? & ? & ? & ?). discriminate.
  Qed.

  Ltac simpl_computation_with_answer_satisfies :=
    match goal with
    | H: computation_with_answer_satisfies (Return _) _ _ |- _ =>
      apply computation_with_answer_satisfies_Return in H
    | H: computation_with_answer_satisfies (Bind _ _) _ _ |- _ =>
      apply computation_with_answer_satisfies_Bind in H
    | H: computation_with_answer_satisfies get _ _ |- _ =>
      apply computation_with_answer_satisfies_get in H
    | H: computation_with_answer_satisfies (put _) _ _ |- _ =>
      apply computation_with_answer_satisfies_put in H
    | H: computation_with_answer_satisfies fail_hard _ _ |- _ =>
      apply computation_with_answer_satisfies_fail_hard in H; contradiction
    end.

End OStateOperations.


(* We can think of it as "S -> ((A * S) -> Prop)", i.e. a function returning
   a unique set of all possible outcomes. *)
Definition StateND(S A: Type) := S -> (A * S) -> Prop.

Instance StateND_Monad(S: Type): Monad (StateND S) := {|
  Bind{A B}(m: StateND S A)(f : A -> StateND S B) :=
    fun (s1 : S) bs3 => exists a s2, m s1 (a, s2) /\ f a s2 bs3;
  Return{A}(a : A) :=
    fun (s : S) '(a', s') => a' = a /\ s' = s;
|}.
all: prove_monad_law.
Defined.

Module StateNDOperations.

  Definition get{S: Type}: StateND S S :=
    fun (s: S) (ss: (S * S)) => ss = (s, s).

  Definition put{S: Type}(new_s: S): StateND S unit :=
    fun (s: S) (us: (unit * S)) => us = (tt, new_s).

  Definition unspecified_behavior{S A: Type}: StateND S A :=
    fun (s: S) (a_s: (A * S)) => True. (* everything's possible *)

  Definition arbitrary{S: Type}(A: Type): StateND S A :=
    fun (s: S) (a_s: (A * S)) => exists a, a_s = (a, s).

  Hint Unfold get put unspecified_behavior arbitrary : unf_monad_ops.

  Lemma Bind_get{S A: Type}: forall (f: S -> StateND S A) (s: S),
      Bind get f s = f s s.
  Proof. prove_monad_law. Qed.

  Lemma Bind_put{S A: Type}: forall (f: unit -> StateND S A) (s0 s1: S),
      Bind (put s1) f s0 = f tt s1.
  Proof. prove_monad_law. Qed.

  (* provides the link between "S -> (A * S) -> Prop" and "S -> (S -> Prop) -> Prop" *)
  Definition computation_satisfies{S: Type}(m: StateND S unit)(s: S)(post: S -> Prop): Prop :=
    forall (o: (unit * S)), m s o -> exists s', o = (tt, s') /\ post s'.

  (* provides the link between "S -> (A * S) -> Prop" and "S -> (A -> S -> Prop) -> Prop" *)
  Definition computation_with_answer_satisfies
             {S A: Type}(m: StateND S A)(s: S)(post: A -> S -> Prop): Prop :=
    forall (o: (A * S)), m s o -> exists a s', o = (a, s') /\ post a s'.

End StateNDOperations.


(* option is for failure, Prop is for non-determinism.
   We can think of it as "S -> (option (A * S) -> Prop)", i.e. a function returning
   a unique set of all possible outcomes. *)
Definition OStateND(S A: Type) := S -> option (A * S) -> Prop.

Instance OStateND_Monad(S: Type): Monad (OStateND S) := {|
  Bind{A B}(m: OStateND S A)(f : A -> OStateND S B) :=
    fun (s : S) (obs: option (B * S)) =>
      (m s None /\ obs = None) \/
      (exists a s', m s (Some (a, s')) /\ f a s' obs);
  Return{A}(a : A) :=
    fun (s : S) (oas: option (A * S)) => oas = Some (a, s);
|}.
all: prove_monad_law.
Defined.

Module OStateNDOperations.

  Definition get{S: Type}: OStateND S S :=
    fun (s: S) (oss: option (S * S)) => oss = Some (s, s).

  Definition put{S: Type}(new_s: S): OStateND S unit :=
    fun (s: S) (ous: option (unit * S)) => ous = Some (tt, new_s).

  Definition fail_hard{S A: Type}: OStateND S A :=
    fun (s: S) (oas: option (A * S)) => oas = None.

  Definition arbitrary{S: Type}(A: Type): OStateND S A :=
    fun (s: S) (oas: option (A * S)) => exists a, oas = Some (a, s).

  Hint Unfold get put fail_hard arbitrary : unf_monad_ops.

  Lemma Bind_get{S A: Type}: forall (f: S -> OStateND S A) (s: S),
      Bind get f s = f s s.
  Proof. prove_monad_law. Qed.

  Lemma Bind_put{S A: Type}: forall (f: unit -> OStateND S A) (s0 s1: S),
      Bind (put s1) f s0 = f tt s1.
  Proof. prove_monad_law. Qed.

  (* provides the link between "S -> option (A * S) -> Prop" and "S -> (S -> Prop) -> Prop" *)
  Definition computation_satisfies{S: Type}(m: OStateND S unit)(s: S)(post: S -> Prop): Prop :=
    forall (o: option (unit * S)), m s o -> exists s', o = Some (tt, s') /\ post s'.

  (* provides the link between "S -> option (A * S) -> Prop" and "S -> (A -> S -> Prop) -> Prop" *)
  Definition computation_with_answer_satisfies
             {S A: Type}(m: OStateND S A)(s: S)(post: A -> S -> Prop): Prop :=
    forall (o: option (A * S)), m s o -> exists a s', o = Some (a, s') /\ post a s'.

  Lemma computation_with_answer_satisfies_Return{S A: Type}: forall (a: A) (initial: S) post,
      computation_with_answer_satisfies (Return a) initial post ->
      post a initial.
  Proof.
    unfold computation_with_answer_satisfies.
    intros. simpl in *.
    edestruct H as (? & ? & ? & ?); [reflexivity|].
    inversion H0. subst. assumption.
  Qed.

  Lemma computation_with_answer_satisfies_Bind{S A B: Type}:
    forall (m: OStateND S A) (f: A -> OStateND S B) (initial: S) post,
      computation_with_answer_satisfies (Bind m f) initial post ->
      (exists mid, computation_with_answer_satisfies m initial mid
                   /\ forall a s, mid a s -> computation_with_answer_satisfies (f a) s post).
  Proof.
    unfold computation_with_answer_satisfies.
    intros. simpl in *.
    eexists.
    split.
    - intros. destruct o as [(? & ?) |]. 1: do 2 eexists; split; [reflexivity|].
      2: { edestruct (H None) as (? & ? & ? & ?); [auto|discriminate]. }
      exact H0.
    - simpl. intros. specialize (H o). eapply H. right. eauto.
  Qed.

  Lemma computation_with_answer_satisfies_get{S: Type}: forall (initial: S) post,
      computation_with_answer_satisfies get initial post ->
      post initial initial.
  Proof.
    unfold computation_with_answer_satisfies, get.
    intros. specialize (H _ eq_refl). destruct H as (? & ? & ? & ?).
    inversion H. subst. assumption.
  Qed.

  Lemma computation_with_answer_satisfies_put{S: Type}: forall (initial new: S) post,
      computation_with_answer_satisfies (put new) initial post ->
      post tt new.
  Proof.
    unfold computation_with_answer_satisfies, put.
    intros. specialize (H _ eq_refl). destruct H as (? & ? & ? & ?).
    inversion H. subst. assumption.
  Qed.

  Lemma computation_with_answer_satisfies_arbitrary{S A: Type}: forall (initial: S) post,
      computation_with_answer_satisfies (arbitrary A) initial post ->
      forall (a: A), post a initial.
  Proof.
    unfold computation_with_answer_satisfies, arbitrary.
    intros. specialize (H (Some (a, initial))). destruct H as (? & ? & ? & ?).
    - eexists. reflexivity.
    - inversion H. subst. assumption.
  Qed.

  Lemma computation_with_answer_satisfies_fail_hard{S A: Type}:
    forall (initial: S) (post: A -> S -> Prop),
      computation_with_answer_satisfies fail_hard initial post ->
      False.
  Proof.
    unfold computation_with_answer_satisfies, fail_hard.
    intros. specialize (H _ eq_refl). destruct H as (? & ? & ? & ?). discriminate.
  Qed.

  Ltac simpl_computation_with_answer_satisfies :=
    match goal with
    | H: computation_with_answer_satisfies (Return _) _ _ |- _ =>
      apply computation_with_answer_satisfies_Return in H
    | H: computation_with_answer_satisfies (Bind _ _) _ _ |- _ =>
      apply computation_with_answer_satisfies_Bind in H
    | H: computation_with_answer_satisfies get _ _ |- _ =>
      apply computation_with_answer_satisfies_get in H
    | H: computation_with_answer_satisfies (put _) _ _ |- _ =>
      apply computation_with_answer_satisfies_put in H
    | H: computation_with_answer_satisfies (arbitrary _) _ _ |- _ =>
      specialize @computation_with_answer_satisfies_arbitrary with (1 := H);
      clear H
    | H: computation_with_answer_satisfies fail_hard _ _ |- _ =>
      apply computation_with_answer_satisfies_fail_hard in H; contradiction
    end.

End OStateNDOperations.

Inductive Outcome(A: Type): Type :=
| Success(a: A)
| Exception (* recoverable *)
| HardFailure (* non-recoverable *).

Class ErrorStateMonad(StM: Type -> Type -> Type) := {
  get{S: Type}: StM S S;
  put{S: Type}(s: S): StM S unit;
  throw{S A: Type}: StM S A;
  failHard{S A: Type}: StM S A;
  (* not sure if needed here
  evalState{S A: Type}(m: StM S A): Outcome A;
  execState{S A: Type}(m: StM S A): Outcome S;
  *)
}.
