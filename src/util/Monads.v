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

Definition bind_option{A B: Type}(oa: option A)(f: A -> option B): option B :=
  match oa with
  | Some a => f a
  | None => None
  end.

Lemma bind_option_assoc{A B C: Type}: forall (f: A -> option B) (g: B -> option C)
                                             (oa: option A),
    bind_option (bind_option oa f) g = bind_option oa (fun a => bind_option (f a) g).
Proof.
  intros.
  destruct oa; reflexivity.
Qed.

Definition set(A: Type): Type := A -> Prop.

Definition contains{A: Type}(s: set A)(a: A) := s a.

Notation "a '\in' s" := (contains s a) (at level 50).

Definition union{A: Type}(s1 s2: set A): set A := fun a => a \in s1 \/ a \in s2.

Definition empty_set{A: Type}: set A := fun a => False.

Definition singleton_set{A: Type}(a: A): set A := eq a.

Module WithOption.

  Definition OStateND(S A: Type) := S -> option (set (S * A)).

  Definition folding_step{S A B: Type}(f: A -> OStateND S B):
    S * A -> option (set (S * B)) -> option (set (S * B)) :=
    fun '(s, a) res =>
      bind_option (f a s)
                  (fun newres =>
                     bind_option res
                                 (fun oldres => Some (union newres oldres))).

  (* this combination doesn't work because we can't fold over a set ( -> Prop)
     and arrive in option *)

End WithOption.


Module WithOptionAndList.

  Definition OStateND(S A: Type) := S -> option (list (S * A)).

  Definition folding_step{S A B: Type}(f: A -> OStateND S B):
    S * A -> option (list (S * B)) -> option (list (S * B)) :=
    fun '(s, a) res =>
      bind_option (f a s)
                  (fun newres =>
                     bind_option res
                                 (fun oldres => Some (newres ++ oldres))).

  (*
  Definition folding_step{S A B: Type}(f: A -> OStateND S B):
    S * A -> option (list (S * B)) -> option (list (S * B)) :=
    (fun '(s, a) res =>
       match f a s, res with
       | Some newres, Some oldres => Some (newres ++ oldres)
       | _, _ => None
       end).
  *)

  Instance OStateND_Monad(S: Type): Monad (OStateND S) := {|
    Bind{A B}(m: OStateND S A)(f : A -> OStateND S B) :=
      fun (s : S) => bind_option (m s) (fun l => fold_right (folding_step f)
                                                            (Some nil)
                                                            l);
    Return{A}(a : A) :=
      fun (s : S) => Some (cons (s, a) nil);
  |}.
  - intros.
    extensionality s.
    simpl.
    destruct (f a s); [|reflexivity].
    simpl.
    f_equal.
    apply app_nil_r.
  - intros.
    extensionality s.
    destruct (m s); [|reflexivity].
    clear s m.
    induction l; [reflexivity|].
    simpl in *.
    destruct a as [s a].
    rewrite IHl.
    reflexivity.
  - intros. extensionality s.
    rewrite bind_option_assoc.
    f_equal.
    extensionality l.
    induction l; [reflexivity|].
    destruct a as [s' a].
    simpl.
    destruct (f a s') eqn: E.
    + simpl.
      rewrite bind_option_assoc.
      simpl.

  Abort.
End WithOptionAndList.


(* outer set is for hard failure and different choices of how specific we want to be,
   inner set is for non-determinism *)
Definition OStateND(S A: Type) := S -> set (set (S * A)).

Definition TODO{A: Type}: A. Admitted.

Definition bind_set{A B: Type}(sa: set A)(f: A -> set B): set B :=
  fun b => exists a, a \in sa /\ b \in (f a).

Module SetsLikeList.

  Definition fold_set{A B: Type}(f: B -> set A -> set A)(initial: set A)(sb: set B): set A.
    (* not possible: cannot thread accumulator through appying f to all elements of sb *)
  Admitted.

  Definition folding_step{S A B: Type}(f: A -> OStateND S B):
    S * A -> set (set (S * B)) -> set (set (S * B)) :=
    fun '(s, a) res =>
      bind_set (f a s)
               (fun newres =>
                  bind_set res
                           (fun oldres => singleton_set (union newres oldres))).

  Instance OStateND_Monad(S: Type): Monad (OStateND S) := {|
    Bind{A B}(m: OStateND S A)(f : A -> OStateND S B) :=
      fun (s : S) => bind_set (m s) (fun (mid: set (S * A)) =>
                                       (fold_set (folding_step f)
                                                 (singleton_set empty_set)
                                                 mid));
    Return{A}(a : A) :=
      fun (s : S) => singleton_set (singleton_set (s, a));
  |}.
  Abort.
End SetsLikeList.

(* "bind" for a set which is used to encode "option", i.e. 0 or one value *)
Definition bind_option_set{A B: Type}(sa: set A)(f: A -> set B): set B :=
    fun b => exists a, a \in sa /\ (forall a', a' \in sa -> a' = a) /\ b \in (f a).

Module TryWithoutFoldSet.

  Instance OStateND_Monad(S: Type): Monad (OStateND S) := {|
    Bind{A B}(m: OStateND S A)(f : A -> OStateND S B) :=
      fun (s : S) => bind_option_set (m s)
                                     (fun (mid: set (S * A)) =>
     (* not what we want: bind_set will ignore empty sets returned by bind_option_set *)
                                        bind_set mid (fun '(s', a) =>
                                                        bind_option_set (f a s')
                                                                        (fun sbs =>
                                                                           singleton_set sbs)));
    Return{A}(a : A) :=
      fun (s : S) => singleton_set (singleton_set (s, a));
  |}.
  Abort.

End TryWithoutFoldSet.

(* already in Coq lib
Definition exists_unique{A: Type}(P: A -> Prop): Prop :=
  exists (a: A), P a /\ forall (a': A), P a -> a' = a.
*)

Module NextTry.

  Instance OStateND_Monad(S: Type): Monad (OStateND S) := {|
    Bind{A B}(m: OStateND S A)(f : A -> OStateND S B) :=
      fun (s : S) (post: set (S * B)) =>
        exists! (mid: set (S * A)), mid \in m s /\ (_: Prop);
    Return{A}(a : A) :=
      fun (s : S) => singleton_set (singleton_set (s, a));
  |}.
  pose (forall s' a, (s', a) \in mid -> f a s' = f a s').

    (*
It seems there is no nice way to get the monad laws to hold

If we want right_associativity to hold, we need to make sure Bind & Return
return a unique postcond set.
If we use option to encode this, we can't put a (A -> Prop) inside it,
because we can't fold over an (A -> Prop) and arrive in an option, so
we have to put list in it, but then associativity becomes a fold_right
nightmare, and the fold_right will probably pop up elsewhere too, and it's
inconvenient to use fold_right because it "threads" through the set in a
very particular order just to assert no Nones and to take the union,
this seems cumbersome to reason about.
But if we choose not to use option, but set and then ensure uniqueness,
we have to add many uniqueness conditions (not evern sure if possible),
which is cumbersome as well. *)
  Abort.

End NextTry.




Instance OStateND_Monad(S: Type): Monad (OStateND S) := {|
  Bind{A B}(m: OStateND S A)(f : A -> OStateND S B) :=
    fun (s : S) (post : set (S * B)) =>
      exists mid : set (S * A),
        (* if "f a s'" returns an empty set (i.e. (fun post' => False)),
           then the -> will never hold, which is good *)
        m s mid /\ (forall s' a, (s', a) \in mid <-> f a s' post);
  Return{A}(a : A) :=
    fun (s : S) (post : set (S * A)) =>
      (* with builtin weakening: just "post s a"
         with precision: *)
      forall s' a', (s' = s /\ a' = a) <-> (s', a') \in post;
|}.
- intros.
  extensionality s. extensionality post.
  apply propositional_extensionality.
  split; intro H.
  + destruct H as (mid & H1 & H2). apply H2. apply H1. auto.
  + exists (fun '(s, a) => f a s post). split.
    * intros. split; intros.
      -- destruct H0; subst s' a'. unfold contains. exact H.
      -- unfold contains in H0. (* same confusion as below *)
  (*
  admit.
- intros.
  extensionality s. extensionality post.
  apply propositional_extensionality. split; intro H.
  + destruct H as (mid & msmid & H).
    replace post with mid; [assumption|].
    extensionality s'. extensionality a.
    specialize (H s' a).
    apply propositional_extensionality.
    rewrite H.
    split; intros.
    * specialize (H0 s' a). apply H0. auto.
    * split; intros.
      -- destruct H1; subst. assumption.
      --

If we allow post to be imprecise, right_associativity doesn't hold
(because Return can sneak in an extra state change, and probably it
wont' be possible to find an equivalence under which right_identity
holds, because right_identity looks asymmetric in this setting.

If we require post to be precise, (as in the code above),
we should get something similar to list-based non-determinism, but
it doesn't really look like so. *)

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
