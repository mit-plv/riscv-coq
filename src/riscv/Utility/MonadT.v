Require Import Coq.Lists.List.

Class Monad(M: Type -> Type) := mkMonad {
  Bind: forall {A B}, M A -> (A -> M B) -> M B;
  Return: forall {A}, A -> M A;

  (* Let's see whether we really need them (maybe in FlatToRiscv)
  left_identity: forall {A B} (a: A) (f: A -> M B),
    Bind (Return a) f === f a;
  right_identity: forall {A} (m: M A),
    Bind m Return === m;
  associativity: forall {A B C} (m: M A) (f: A -> M B) (g: B -> M C),
    Bind (Bind m f) g === Bind m (fun x => Bind (f x) g)
  *)
}.

Notation "x <- m1 ; m2" := (Bind m1 (fun x => m2))
  (right associativity, at level 60) : monad_scope.
Notation "m1 ;; m2" := (Bind m1 (fun _ => m2))
  (right associativity, at level 60) : monad_scope.

Open Scope monad_scope.

#[global] Instance option_Monad: Monad option := {|
  Bind := fun {A B: Type} (o: option A) (f: A -> option B) => match o with
            | Some x => f x
            | None => None
            end;
  Return := fun {A: Type} (a: A) => Some a;
|}.

(*
The proper way to do monad transformers would be this:

Record optionT(M: Type -> Type)(A: Type): Type := {
  runOptionT: M (option A)
}.

Build_optionT
     : forall (M : Type -> Type) (A : Type), M (option A) -> optionT M A
runOptionT
     : forall (M : Type -> Type) (A : Type), optionT M A -> M (option A)

but how is this really different from just creating an alias like below?
*)

(* wrong direction: *)
Definition optionT(M: Type -> Type)(A: Type) := M (option A).
Definition runOptionT{M : Type -> Type}{A : Type}: optionT M A -> M (option A) := id.

Definition listT(M: Type -> Type)(A: Type) := M (list A).
Definition runListT{M : Type -> Type}{A : Type}: listT M A -> M (list A) := id.

(* if we do it in the correct direction, runOptionT is not just id any more:
Definition optionT(M: Type -> Type)(A: Type) := option (M A).
Definition runOptionT{M : Type -> Type}{A : Type}: optionT M A -> M (option A).
Abort.

monadic calculation contains intermediate values of suspicious structure

[ None;  (Some 1) ] must not be (optionT list nat)

[ Some _; Some _; ]
[ None ]
are ok


if we consider however
listT option nat

[ None; Some 1 ] is ok

*)

(*Eval cbv in (optionT list nat).*)


#[global] Instance OptionT_Monad(M: Type -> Type){MM: Monad M}: Monad (optionT M) := {|
  Bind{A}{B}(m: M (option A))(f: A -> M (option B)) :=
    Bind m (fun (o: option A) =>
              match o with
              | Some a => f a
              | None => Return None
              end);
  Return{A}(a: A) := Return (Some a);
|}.

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

#[global] Instance State_Monad(S: Type): Monad (State S) := {|
  Bind := fun {A B: Type} (m: State S A) (f: A -> State S B) =>
              fun (s: S) => let (a, s') := m s in f a s' ;
  Return := fun {A: Type} (a: A) =>
                fun (s: S) => (a, s);
|}.

Definition StateT(S: Type)(M: Type -> Type)(A: Type) := S -> M (A * S)%type.

#[global] Instance StateT_Monad(M: Type -> Type){MM: Monad M}(S: Type): Monad (StateT S M) := {|
  Bind{A B: Type}(m: StateT S M A)(f: A -> StateT S M B) :=
    fun (s: S) => Bind (m s) (fun '(a, s) => f a s);
  Return{A: Type}(a: A) :=
    fun (s: S) => Return (a, s);
|}.

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

  Definition fmap{M: Type -> Type}{MM: Monad M}{A B: Type}(ma: M A)(f: A -> B): M B :=
    Bind ma (fun (a: A) => Return (f a)).

  Definition foo0{A: Type} := @mapSet (A -> Prop) A.
  (* Eval cbv in @foo0. *)
  (*
  Definition bar{A: Type}(M: Type -> Type)(mla: M (list A)
*)

  Definition bar{A: Type}(M: Type -> Type){MM: Monad M}(mla: M (list A)): list (M A).
  Abort. (*maybe too strong and therefore impossible *)
(*
    refine (cons _ nil).
    apply (fmap (A := list A)).
    apply mla.
    refine (List.map _ _).
*)

  Definition foo{A: Type}(M: Type -> Type){MM: Monad M}(m: list (M (list A))): list (M A).
    (* would be possible if we had bar.
       not possible because deciding whether we return nil or cons requires to
       enter the monad m to inspect it, but once we entered, we'll have to return an M
  refine (fold_left (fun (ma : M A) (mla: M (list A)) => _) m _).

  Definition foo{A: Type}(M: Type -> Type)(m: NonDet (M (NonDet A))): NonDet (M A).
    unfold NonDet in *.
*)
  Abort.

  Definition bigUnion{B: Type}(sets: (B -> Prop) -> Prop): B -> Prop :=
    fun b => exists set, sets set /\ set b.

  Definition flatMapSet'{A B: Type}(aset: A -> Prop)(f: A -> (B -> Prop)): B -> Prop :=
    bigUnion (mapSet aset f).

  Definition setEq{A: Type}(set1 set2: A -> Prop): Prop :=
    forall a, set1 a <-> set2 a.

  Definition singletonSet{A: Type}(a: A): A -> Prop := eq a.

  Definition arbitrary(A: Type): NonDet A := fun a => True.

End NonDetMonad.

#[global] Instance NonDet_Monad: Monad NonDet := {|
  Bind := @NonDetMonad.flatMapSet;
  Return := @NonDetMonad.singletonSet;
|}.

Definition NonDetT(M: Type -> Type)(A: Type) := NonDet (M A).

Goal forall (M: Type -> Type) (A: Type), NonDet (M A) = (M A -> Prop).
  intros. reflexivity. Qed.

#[global] Instance NonDetT_Monad(M: Type -> Type){MM: Monad M}: Monad (NonDetT M). refine ({|
  Bind{A B}(m: NonDet (M A))(f: A -> NonDet (M B)) := _;
  Return := _
|}).
unfold NonDet in *.
destruct MM.
apply f.
Abort.

Definition OState(S: Type): Type -> Type := optionT (StateT S option).

Goal forall S A,
    OState S A = (S -> option (option A * S)).
Proof. intros. reflexivity. Qed.

Definition OStateND(S: Type): Type -> Type := optionT (StateT S (optionT NonDet)).

Goal forall S A,
    OStateND S A = (S -> option (option A * S) -> Prop).
Proof. intros. reflexivity. Qed.
(*
  option around A is for recoverable failure,
  option around (option A * S) means hard failure.

before we wanted this:
Definition OStateND(S A: Type) := S -> (S -> option A -> Prop) -> Prop.

 *)
Definition OrigOState(S A: Type) := S -> option A * S.
Definition OStateND'(S A: Type) := S -> (option A * S -> Prop) -> Prop.

(* double NonDet *)
Definition DNonDetT(M: Type -> Type)(A: Type) := M (A -> Prop) -> Prop.
Goal forall S A, DNonDetT (OrigOState S) A = OStateND' S A.
  intros.
  cbv.
Abort. (* doesn't hold *)

Definition deterministic{S A: Type}(m: OState S A): OStateND S A := fun s => eq (m s).
(* this is return of NonDet *)

Module OldVersions.

  (* turns recoverable failure into hard failure *)
  Definition nothrow{S A}(m: OStateND S A): S -> option (A * S) -> Prop :=
    fun s oas => match oas with
                 | Some (a, s') => m s (Some (Some a, s'))
               | None => m s None \/ exists s', m s (Some (None, s'))
                 end.

  Definition ignoreAns{S A}(m: S -> option (A * S) -> Prop): S -> (S -> Prop) -> Prop.
  Abort.


  Section RunsTo.

    Variable State: Type.
    (* the option represents hard unacceptable failure, the Prop represents non-determinism *)
    Variable step: State -> (option State) -> Prop.

    Inductive runsTo(initial: State)(P: State -> Prop): Prop :=
    | runsToDone:
        P initial ->
        runsTo initial P
    | runsToStep:
        (forall omid, step initial omid -> exists mid, omid = Some mid /\ runsTo mid P) ->
        runsTo initial P.

    (*Check runsTo_ind.  bad! *)
  End RunsTo.

End OldVersions.


Module DeterministicByAccident.

  Parameter State: Type.
  Parameter step: OStateND State unit.

  Inductive runsTo(initial: State)(P: State -> Prop): Prop :=
    | runsToDone:
        P initial ->
        runsTo initial P
    | runsToStep: forall mid,
        (forall omid, step initial omid -> omid = Some (Some tt, mid)) ->
        runsTo mid P ->
        runsTo initial P.
End DeterministicByAccident.

Module MoreOld.

  Parameter State: Type.
  Parameter step: OStateND State unit.

  Inductive runsTo(initial: State)(P: State -> Prop): Prop :=
    | runsToDone:
        P initial ->
        runsTo initial P
    | runsToStep:
        (* shouldn't repeat here! *)
        (forall omid, step initial omid -> exists mid, omid = Some (Some tt, mid)) ->
        (forall mid, step initial (Some (Some tt, mid)) -> runsTo mid P) ->
        runsTo initial P.

End MoreOld.


Section RunsTo.

  Variable State: Type.
  Variable step: OStateND State unit.

  Inductive runsTo(initial: State)(P: State -> Prop): Prop :=
    | runsToDone:
        P initial ->
        runsTo initial P
    | runsToStep:
        (forall omid,
            step initial omid ->
            exists mid, omid = Some (Some tt, mid) /\ runsTo mid P) ->
        runsTo initial P.

  Hint Constructors runsTo.

  (* Print runsTo_ind. bad (not a fixpoint) *)

  Lemma runsTo_induct: forall (R : State -> (State -> Prop) -> Prop),
      (forall (initial : State) (P : State -> Prop), P initial -> R initial P) ->
      (forall (initial : State) (P : State -> Prop),
          (forall (omid : option (option unit * State)),
              step initial omid ->
              exists mid, omid = Some (Some tt, mid) /\ runsTo mid P /\ R mid P) ->
         R initial P) ->
      forall (initial : State) (P : State -> Prop), runsTo initial P -> R initial P.
  Proof.
    intros R Base Step.
    fix IH 3; intros. destruct H.
    - apply Base. assumption.
    - apply Step. intros.
      specialize (H omid H0).
      destruct H as (mid & ? & Rmid).
      subst omid.
      eexists. split; [reflexivity|].
      split; [assumption|].
      apply IH. apply Rmid.
  Qed.

  Lemma runsTo_trans: forall initial P,
      runsTo initial P ->
      forall Q,
        (forall middle, P middle -> runsTo middle Q) ->
        runsTo initial Q.
  Proof.
    pose proof (runsTo_induct (fun initial P =>
      forall Q, runsTo initial P ->
                (forall middle, P middle -> runsTo middle Q) ->
                runsTo initial Q)) as Ind.
    simpl in Ind.
    intros initial P R1 Q R2.
    specialize Ind with (P := P) (Q := Q) (3 := R1) (4 := R1) (5 := R2).
    apply Ind.
    - clear. intros. eauto.
    - clear. intros initial P IH Q R1 R2.
      apply runsToStep.
      intros omid St.
      specialize (IH omid St).
      destruct IH as (mid & ? & R3 & R4).
      subst omid.
      eexists; split; [reflexivity|].
      eauto.
  Qed.

  Lemma runsTo_weaken: forall (P Q : State -> Prop) initial,
    runsTo initial P ->
    (forall final, P final -> Q final) ->
    runsTo initial Q.
  Proof.
    intros. eapply runsTo_trans; [eassumption|].
    intros final Pf. apply runsToDone. auto.
  Qed.

End RunsTo.

(* Print Assumptions runsTo_weaken. *)
