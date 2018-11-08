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


Notation "x <- m1 ; m2" := (Bind m1 (fun x => m2))
  (right associativity, at level 60) : monad_scope.
Notation "m1 ;; m2" := (Bind m1 (fun _ => m2))
  (right associativity, at level 60) : monad_scope.

Open Scope monad_scope.

Instance option_Monad: Monad option := {|
  Bind := fun {A B: Type} (o: option A) (f: A -> option B) => match o with
          | Some x => f x
          | None => None
          end;
  Return := fun {A: Type} (a: A) => Some a
|}.
- intros. reflexivity.
- intros. destruct m; reflexivity.
- intros. destruct m; reflexivity.
Defined.


(* Monad which also supports failure (mzero) and choice (mplus), typically used to chose
   the first successful one *)
Class MonadPlus(M: Type -> Type){MM: Monad M} := mkMonadPlus {
  mzero: forall {A}, M A;
  mplus: forall {A}, M A -> M A -> M A;

  mzero_left: forall {A} (f: A -> M A), Bind mzero f = mzero;
  mzero_right: forall {A B} (v: M A), Bind v (fun (_: A) => @mzero B) = @mzero B;
  mplus_assoc: forall {A} (m1 m2 m3: M A), mplus m1 (mplus m2 m3) = mplus (mplus m1 m2) m3;
}.

Definition msum{A}{M: Type -> Type}{MM: Monad M}{MP: MonadPlus M}: list (M A) -> M A :=
  fold_right mplus mzero.


Instance OptionMonadPlus: MonadPlus option := {|
  mzero := @None;
  mplus A m1 m2 := match m1 with
                   | Some x => m1
                   | None => m2
                   end;
|}.
- intros. reflexivity.
- intros. destruct v; reflexivity.
- intros. destruct m1; reflexivity.
Defined.


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

Module StateM.
Definition get{S: Type}: State S S := fun (s: S) => (s, s).
Definition gets{S A: Type}(f: S -> A): State S A := fun (s: S) => (f s, s).
Definition put{S: Type}(s: S): State S unit := fun _ => (tt, s).
End StateM.

(*
Inductive StateOutcome(S A: Type) :=
| Success: S -> A -> StateOutcome S A
| Break: S -> StateOutcome S A
| Unhandled: StateOutcome S A.

Definition OState(S A: Type) := S -> StateOutcome S A.

Instance OState_Monad(S: Type): Monad (OState S) := {|
  Bind := fun {A B: Type} (m: OState S A) (f: A -> OState S B) =>
            fun (s: S) => match m s with
              | Success _ _ s' a => f a s'
              | Break _ _ s' => Break S B s'
              | Unhandled _ _ => Unhandled S B
              end;
  Return := fun {A: Type} (a: A) =>
              fun (s: S) => Success S A s a
|}.
- intros. reflexivity.
- intros. extensionality s. destruct (m s); reflexivity.
- intros. extensionality s. destruct (m s); reflexivity.
Defined.

Instance OState_MonadPlus(S: Type): MonadPlus (OState S) := {|
  mzero A s := Unhandled S A;
  mplus A m1 m2 s := match m1 s with
    | Success _ _ s' a => Success _ _ s' a
    | Break _ _ s' => Break _ _ s'
    | Unhandled _ _ => m2 s
    end
|}.
- intros. reflexivity.
- intros. Close Scope monad_scope.
  unfold Bind, OState_Monad.
  extensionality s. destruct (v s); try reflexivity.
  (* Note: does not hold: If after break, we find out that actually it's unhandled,
     it's still break, because after break, nothing more is run. *)
Abort.

Definition get{S: Type}: OState S S := fun (s: S) => Some (s, s).
Definition gets{S A: Type}(f: S -> A): OState S A := fun (s: S) => Some (f s, s).
Definition put{S: Type}(s: S): OState S unit := fun _ => Some (tt, s).

*)



(* Note: This one is not what we want either, because it throws away all the state
   on endCycle/raiseException:

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
 *)


(* Note: This one is not what we want because in "mplus m1 m2", if m1 throws an exception,
   m2 is run, instead of keeping m1's exception.
   The problem is that "None" can mean both "unhandled, please try next" or
   "handled, but exception"
*)
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
- intros. reflexivity.
- intros. extensionality s. destruct (m s). destruct o; reflexivity.
- intros. extensionality s. destruct (m s). destruct o; reflexivity.
Defined.

Definition OStateND(S A: Type) := S -> (S -> A -> Prop) -> Prop.

Definition TODO{A: Type}: A. Admitted.

Instance OStateND_Monad(S: Type): Monad (OStateND S) := {|
  Bind{A B}(m: OStateND S A)(f : A -> OStateND S B) :=
    fun (s : S) (post : S -> B -> Prop) =>
      exists mid : S -> A -> Prop,
        m s mid /\ (forall s' a, mid s' a -> f a s' post);
  Return{A}(a : A) :=
    fun (s : S) (post : S -> A -> Prop) => post s a;
|}.
- intros.
  extensionality s. extensionality post.
  apply propositional_extensionality. split; intro H.
  + destruct H as (mid & midsa & H). auto.
  + exists (fun s a => f a s post). split; [assumption|]. auto.
- intros.
  extensionality s. extensionality post.
  apply propositional_extensionality. split; intro H.
  + destruct H as (mid & msmid & H).
    replace post with mid; [assumption|].
    (* doesn't hold because Return allows state to change as long as it still satisfies
       post *)

Admitted.


Definition OOStateND(S A: Type) := S -> (S -> option A -> Prop) -> Prop.

Instance OOStateND_Monad(S: Type): Monad (OOStateND S) := {|
  Bind := fun (A B : Type) (m : OOStateND S A) (f : A -> OOStateND S B)
              (s : S) (post : S -> option B -> Prop) =>
            exists mid : S -> option A -> Prop,
              m s mid /\
              (forall (s' : S) (oa : option A),
                  mid s' oa -> oa = None /\ post s' None \/
                                            (exists a : A, oa = Some a /\ f a s' post));
  Return := fun (A : Type) (a : A) (s : S) (post : S -> option A -> Prop) => post s (Some a);
|}.
- intros. extensionality s. extensionality post. apply propositional_extensionality.
  split; intro.
  + destruct H as (mid & H1 & H2).
    specialize (H2 _ _ H1). destruct H2 as [(? & ?) | (? & ? & ?)].
    * discriminate.
    * inversion H. subst. assumption.
  + apply TODO.
- apply TODO.
- intros. extensionality s. extensionality post.
  apply propositional_extensionality. split; intro.
  + destruct H as (midB & (midA & HA & HB) & Hpost).
    exists midA. split; [exact HA|].
    intros s' oa Hma.
    specialize HB with (1 := Hma).
    destruct HB as [[? ?] | [a [Eq HB]]]; [left|right]; subst oa.
    * specialize Hpost with (1 := H0).
      destruct Hpost as [[_ X] | [b [? ?]]]; [auto | discriminate].
    * exists a. split; [reflexivity|].
      exists midB. split; [assumption|].
      intros s'' ob Hmb.
      apply Hpost.
      assumption.
  + destruct H as (midA & Hma & H).
    evar (PSome: Prop).
    exists (fun s ob => match ob with | None => post s None | Some _ => PSome end).
    (*exists (fun s ob => exists o, ob = Some o /\ PSome).*)
    split.
    * exists midA. split; [exact Hma|].
      intros s' oa HA.
      specialize H with (1 := HA).
      destruct H as [H | [a [Eq [midB [F H]]]]]; [left; assumption|right].
      subst oa.
      exists a; split; [reflexivity|].
      apply TODO.
    * apply TODO.
Grab Existential Variables.
apply True.
Defined.

(*
Instance OStateND_Monad(S: Type): Monad (OStateND S) := {|
  Bind := fun {A B: Type} (m: OStateND S A) (f: A -> OStateND S B) => _;
  Return := fun {A: Type} (a: A) => _;
|}.
{
cbv [OStateND] in *.
refine(fun s post => _ ).
refine  (exists (mid: S -> option A -> Prop), m s mid /\ forall s' oa, mid s' oa -> (
Logic.or (oa = None /\ post s' None) (exists a, oa = Some a /\ f a s' post)
      )).
}
{
  cbv [OStateND] in *.
  refine (fun s post => post s (Some a)).
}
all: apply TODO.
Defined.
*)

(*
Definition OStateND(S A: Type) := S -> (option A) * S -> Prop.

Instance OStateND_Monad(S: Type): Monad (OStateND S) := {|
  Bind := fun {A B: Type} (m: OStateND S A) (f: A -> OStateND S B) =>
            (fun (s: S) => exists (oas: option A * S), m s oas /\ match oas with
            | (Some a, s') => f a s'
            | (None, s') => eq (None, s')
            end);
  Return := fun {A: Type} (a: A) =>
              fun (s: S) => (Some a, s)
|}.
- intros. reflexivity.
- intros. extensionality s. destruct (m s). destruct o; reflexivity.
- intros. extensionality s. destruct (m s). destruct o; reflexivity.
Defined.
*)

(* TODO if we want to use MonadPlus, we'd have to define a custom equivalence on
   the state monad which only considers A, but not S *)
Axiom OStateEq_to_eq: forall {S A: Type} (s1 s2: S) (a1 a2: option A),
  a1 = a2 -> (a1, s1) = (a2, s2).

Instance OState_MonadPlus(S: Type): MonadPlus (OState S) := {|
  mzero A s := (@None A, s);
  mplus A m1 m2 s := match m1 s with
    | (Some a, s') => (Some a, s')
    | (None, s') => m2 s
    end;
|}.
- intros. reflexivity.
- intros. simpl. extensionality s. destruct (v s).
  destruct o; apply OStateEq_to_eq; reflexivity.
- intros. simpl. extensionality s. destruct (m1 s). destruct o; reflexivity.
Defined.

Definition get{S: Type}: OState S S := fun (s: S) => (Some s, s).
Definition gets{S A: Type}(f: S -> A): OState S A := fun (s: S) => (Some (f s), s).
Definition put{S: Type}(s: S): OState S unit := fun _ => (Some tt, s).

Definition execState{S A: Type}(m: OState S A)(initial: S): S :=
  snd (m initial).

(* T for transformer, corresponds to Haskell's MaybeT: *)
Definition optionT(M: Type -> Type)(A: Type) := M (option A).

Instance OptionT_is_Monad(M: Type -> Type){MM: Monad M}: Monad (optionT M) := {|
  Bind{A}{B}(m: M (option A))(f: A -> M (option B)) :=
    Bind m (fun (o: option A) =>
      match o with
      | Some a => f a
      | None => Return None
      end);
  Return{A}(a: A) := Return (Some a);
|}.
- intros. rewrite left_identity. reflexivity.
- intros. rewrite <- right_identity. f_equal. extensionality o. destruct o; reflexivity.
- intros. rewrite associativity. f_equal. extensionality o. destruct o.
  + reflexivity.
  + rewrite left_identity. reflexivity.
Defined.

Lemma discard_left: forall {M : Type -> Type} {MM : Monad M} {A B : Type} (m: M A) (b: B),
  Bind m (fun _  => Return b) = Return b.
Proof.
  intros. (* Note: This does not hold for the state monad! *)
Admitted.

Definition OpSt(S: Type): Type -> Type := optionT (State S).

Definition OpSt_Monad(S: Type): Monad (OpSt S).
  unfold OpSt. apply OptionT_is_Monad. apply State_Monad.
Defined.

Goal forall (S: Type), False. intro S. set (b := @Bind (OpSt S) (OpSt_Monad S)).
Abort.

Instance optionT_is_MonadPlus(M: Type -> Type){MM: Monad M}: MonadPlus (optionT M) := {|
  mzero A := Return None : M (option A);
  mplus A m1 m2 := @Bind _ _ (option A) _ m1 (fun (o1: option A) => match o1 with
    | Some a1 => Return (Some a1)
    | None => m2
    end) : M (option A);
|}.
- intros. simpl. rewrite left_identity. reflexivity.
- intros. simpl.
  transitivity (Bind v (fun o : option A => Return (@None B))).
  + f_equal. extensionality o. destruct o; reflexivity.
  + apply discard_left.
- intros.
  rewrite associativity. f_equal. extensionality o1. destruct o1.
  + rewrite left_identity. reflexivity.
  + reflexivity.
Defined.

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

Instance optionT_is_MonadTrans: MonadTrans optionT := {|
  lift M MM A := liftM Some;
  transformed_monad := OptionT_is_Monad;
|}.
- intros. unfold liftM. simpl. rewrite left_identity. reflexivity.
- intros. unfold liftM. simpl. rewrite? associativity. f_equal. extensionality a.
  rewrite left_identity. reflexivity.
Defined.
