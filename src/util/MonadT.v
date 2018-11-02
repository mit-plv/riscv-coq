Require Import Coq.Setoids.Setoid.


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


Module OptionMonad.

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

End OptionMonad.


Module StateMonad.

  Definition State(S A: Type) := S -> (A * S).

  Definition get{S: Type}: State S S := fun (s: S) => (s, s).
  Definition gets{S A: Type}(f: S -> A): State S A := fun (s: S) => (f s, s).
  Definition put{S: Type}(s: S): State S unit := fun _ => (tt, s).

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

  Definition StateT(M: Type -> Type)(S A: Type) := S -> M (A * S)%type.
  (* wrong:
  Definition StateT(M: Type -> Type)(S A: Type) := M (State S A).
  *)

  Instance StateT_is_Monad(M: Type -> Type){MM: Monad M}(S: Type): Monad (StateT M S) := {|
    Bind{A B: Type}(m: StateT M S A)(f: A -> StateT M S B) :=
      fun (s: S) => Bind (m s) (fun '(a, s) => f a s);
    Return{A: Type}(a: A) :=
      fun (s: S) => Return (a, s);
    MonadEq{A: Type}(m1 m2: StateT M S A) := forall (s: S), MonadEq (m1 s) (m2 s);
  |}.
  Admitted.

End StateMonad.


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

  Definition NonDet(A: Type) := A -> Prop.

  Definition arbitrary(A: Type): NonDet A := fun a => True.

  Ltac t :=
    cbv [flatMapSet NonDet setEq singletonSet];
    intros; try split; intros;
    repeat match goal with
           | p: _ * _  |- _ => destruct p
           | H: _ /\ _ |- _ => destruct H
           | E: exists y, _ |- _ => destruct E
           | H: context [match ?x with _ => _ end] |- _ =>
             let E := fresh "E" in destruct x eqn: E
           | |- context [match ?x with _ => _ end] =>
             let E := fresh "E" in destruct x eqn: E
           | H: Some _ = Some _ |- _ => inversion H; subst
           | _ => discriminate
           | |- _ /\ _ => split; eauto
(*           | |- exists _, _ => eexists*)
           end;
    subst;
    eauto.

  Instance NonDet_Monad: Monad NonDet := {|
    Bind := @flatMapSet;
    Return := @singletonSet;
    MonadEq := @setEq;
  |}.
  Proof. all:  t. Defined.

(* existing monad outside (like haskell's ListT and optionT *)
(*
  Definition NonDetT(M: Type -> Type)(A: Type) := M (NonDet A).

  Instance NonDetT_option_is_Monad: Monad (NonDetT option) := {|
    Bind{A B: Type}(m: option (A -> Prop))(f: A -> option (B -> Prop)) :=
      _;
    Return{A: Type}(a: A) := Return (eq a);
    MonadEq{A: Type}(m1 m2: NonDetT option A) := _;
  |}.
  all: unfold NonDetT, NonDet in *.
  {
    refine (Bind m (fun aset => _ )).

  Instance NonDetT_is_Monad(M: Type -> Type){MM: Monad M}: Monad (NonDetT M) := {|
    Bind{A B: Type}(m: M (A -> Prop))(f: A -> M (B -> Prop)) :=
      _;
    Return{A: Type}(a: A) := Return (eq a);
    MonadEq{A: Type}(m1 m2: NonDetT M A) := _;
  |}.
  all: unfold NonDetT, NonDet in *.
  {
    refine (Bind m (fun aset => _ )).
(*
    set (y := (fun (a: A) => aset a /\ f a
    set (x := (@flatMapSet A (M (B -> Prop)) aset)).

    refine (Return (@flatMapSet A B aset (fun a => _))).


    refine (Bind m (fun aset => _ )).
    refine (Return (@flatMapSet A B aset (fun a => _))).

    set (x := (@flatMapSet A B aset)).

  refine (Bind m (fun aset => (Bind _ (fun (b: (B -> Prop) -> Prop) => Return (bigUnion b))))).
  refine (Return (fun bset => exists a, aset a /\ _)).

  admit.

    m >>= k  = ListT $ do
        a <- runListT m
        b <- mapM (runListT . k) a
        return (concat b)

  refine (Bind m (fun aset => exists (a: A), _)).
*)
*)

(* existing monad inside *)
  Definition NonDetT(M: Type -> Type)(A: Type) := M A -> Prop.

  Instance NonDetT_option_is_Monad: Monad (NonDetT option) := {|
    Bind{A B: Type}(m: option A -> Prop)(f: A -> option B -> Prop) :=
      fun ob =>
            exists oa, m oa /\ match oa with
                               | Some a => f a ob
                               | None => ob = None
                               end;
    Return{A: Type}(a: A) := fun oa => oa = Some a;
    MonadEq{A: Type}(m1 m2: NonDetT option A) :=
      forall oa, m1 oa <-> m2 oa;
  |}.
  Proof.
    all: t; try (eexists; split; [eassumption|]; t).
    - exists None. eauto.
    - eexists. split.
      + eexists. split; [eassumption|]. simpl. eassumption.
      + simpl. assumption.
    - eexists. split.
      + eexists. split; [eassumption|]. simpl. eassumption.
      + simpl. reflexivity.
    - eexists. split.
      + eexists. split; [eassumption|]. simpl. reflexivity.
      + simpl. reflexivity.
  Defined.

(*
  Instance NonDetT_is_Monad(M: Type -> Type){MM: Monad M}: Monad (NonDetT M) := {|
    Bind{A B: Type}(m: M A -> Prop)(f: A -> M B -> Prop) :=
      _;
    Return{A: Type}(a: A) := MonadEq (Return a);
    MonadEq{A: Type}(m1 m2: NonDetT M A) := _;
  |}.
all: unfold NonDet in *.

{
  refine (fun mb => _).
  refine (exists (ma: M A), m ma /\ @MonadEq M MM B (@Bind M MM _ _ ma f) mb).
  refine (Bind m (fun a => _)). unfold NonDet.
  intro mb.

unfold
  pose proof (@MonadEq M MM ).

  apply (@MonadEq M MM A m1 m2).

apply (MonadEq (Return a)).

End NonDetMonad.
*)

Class MonadTrans(T: (Type -> Type) -> (Type -> Type)) := mkMonadTrans {
  lift{M: Type -> Type}{MM: Monad M}{A: Type}: M A -> T M A;
  transformed_monad{M: Type -> Type}{MM: Monad M}: Monad (T M);
  lift_return{M: Type -> Type}{MM: Monad M}{A: Type}:
    forall a: A, lift (Return a) = Return a;
  lift_bind{M: Type -> Type}{MM: Monad M}{A B: Type}:
    forall (m: M A) (f: A -> M B), lift (Bind m f) = Bind (lift m) (fun x => lift (f x));
}.

(* Promote a function to a monad. *)
Definition liftM{M: Type -> Type}{MM: Monad M}{A B: Type}(f: A -> B): M A -> M B :=
  fun m => x <- m; Return (f x).

Instance optionT_is_MonadTrans: MonadTrans OptionMonad.optionT := {|
  lift M MM A := liftM Some;
  transformed_monad := OptionMonad.OptionT_is_Monad;
|}.
Admitted.
(*
- intros. unfold liftM. simpl. rewrite left_identity. reflexivity.
- intros. unfold liftM. simpl. rewrite? associativity. f_equal. extensionality a.
  rewrite left_identity. reflexivity.
Defined.
*)
End NonDetMonad.