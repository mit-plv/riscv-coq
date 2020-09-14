Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Logic.PropExtensionality.
Require Import riscv.Utility.Monads.

Module free.
  Section WithInterface.
    Context {action : Type} {result : action -> Type}.
    Inductive free {T : Type} : Type :=
    | act (a : action) (_ : result a -> free)
    | ret (x : T).
    Arguments free : clear implicits.

    Fixpoint bind {A B} (mx : free A) (fy : A -> free B) : free B :=
      match mx with
      | act a k => act a (fun x => bind (k x) fy)
      | ret x => fy x
      end.

    (** Monad laws *)
    Definition bind_ret_l {A B} a b : @bind A B (ret a) b = b a := eq_refl.
    Lemma bind_assoc {A B C} (a : free A) (b : A -> free B) (c : B -> free C) :
      bind (bind a b) c = bind a (fun x => bind (b x) c).
    Proof. revert c; revert C; revert b; revert B; induction a;
        cbn [bind]; eauto using f_equal, functional_extensionality. Qed.
    Lemma bind_ret_r {A} (a : free A) : bind a ret = a.
    Proof. induction a;
        cbn [bind]; eauto using f_equal, functional_extensionality. Qed.
    Global Instance Monad_free : Monad free.
    Proof. esplit; eauto using bind_ret_l, bind_assoc, bind_ret_r. Defined.

    Section WithState.
      Context {state}
      (interp_action : forall a : action, state -> (result a -> state -> Prop) -> Prop).
      Section WithOutput.
        Context {output} (post : output -> state -> Prop).
        Definition interp_body interp (a : free output) (s : state) : Prop :=
          match a with
          | ret x => post x s
          | act a k => interp_action a s (fun r => interp (k r))
          end.
        Fixpoint interp_fix a := interp_body interp_fix a.
      End WithOutput.

      Definition interp {output} a s post := @interp_fix output post a s.

      Lemma interp_ret {T} (x : T) m P : interp (ret x) m P = P x m.
      Proof. exact eq_refl. Qed.
      Lemma interp_act {T} a (k : _ -> free T) s post
        : interp (act a k) s post
        = interp_action a s (fun r s => interp (k r) s post).
      Proof. exact eq_refl. Qed.

      Context (interp_action_weaken_post :
        forall a (post1 post2:_->_->Prop), (forall r s, post1 r s -> post2 r s) -> forall s, interp_action a s post1 -> interp_action a s post2).

      Lemma interp_weaken_post {T} (p : free T) s
        (post1 post2:_->_->Prop) (Hpost : forall r s, post1 r s -> post2 r s)
        (Hinterp : interp p s post1) : interp p s post2.
      Proof. revert dependent s; induction p; cbn; firstorder eauto. Qed.

      Lemma interp_bind {A B} s post (a : free A) (b : A -> free B) :
        interp (bind a b) s post <-> interp a s (fun x s => interp (b x) s post).
      Proof.
        revert post; revert b; revert B; revert s; induction a.
        2: { intros. cbn. reflexivity. }
        split; eapply interp_action_weaken_post; intros; eapply H; eauto.
      Qed.

      Lemma interp_bind_ex_mid {A B} m0 post (a : free A) (b : A -> free B) :
        interp (bind a b) m0 post <->
        (exists mid, interp a m0 mid /\ forall x m1, mid x m1 -> interp (b x) m1 post).
      Proof.
        rewrite interp_bind.
        split; [intros ? | intros (?&?&?)].
        { exists (fun x m1 => interp (b x) m1 post); split; eauto. }
        { eauto using interp_weaken_post. }
      Qed.
    End WithState.

    Section WithStateAndAbort.
      Context {state : Type}.
      Context (interpret_action : forall a : action,
                  state ->                       (* initial state *)
                  (result a -> state -> Prop) -> (* postcondition if finished *)
                  (state -> Prop) ->             (* postcondition if aborted *)
                  Prop).
      Section WithOutput.
        Context {output} (postF : output -> state -> Prop) (postA : state -> Prop).
        Definition interpret_body rec (a : free output) (s : state) : Prop :=
          match a with
          | ret x => postF x s
          | act a k => interpret_action a s (fun r => rec (k r)) postA
          end.
        Fixpoint interpret_fix a := interpret_body interpret_fix a.
      End WithOutput.

      Definition interpret {output} a s postF postA := @interpret_fix output postF postA a s.

      Lemma interpret_ret {T} (x : T) m postF postA : interpret (ret x) m postF postA = postF x m.
      Proof. exact eq_refl. Qed.
      Lemma interpret_act {T} a (k : _ -> free T) s postF postA
        : interpret (act a k) s postF postA
        = interpret_action a s (fun r s => interpret (k r) s postF postA) postA.
      Proof. exact eq_refl. Qed.

      Context (interpret_action_weaken_post :
        forall a (postF1 postF2 : _ -> _ -> Prop) (postA1 postA2 : _ -> Prop),
        (forall r s, postF1 r s -> postF2 r s) ->
        (forall s, postA1 s -> postA2 s) ->
        forall s, interpret_action a s postF1 postA1 -> interpret_action a s postF2 postA2).

      Lemma interpret_weaken_post {T} (p : free T) s
            (postF1 postF2 : _ -> _ -> Prop) (postA1 postA2 : _ -> Prop):
        (forall r s, postF1 r s -> postF2 r s) ->
        (forall s, postA1 s -> postA2 s) ->
        interpret p s postF1 postA1 -> interpret p s postF2 postA2.
      Proof.
        revert dependent s; induction p. 2: firstorder eauto.
        cbn. intros. eapply interpret_action_weaken_post.
        - intros. eapply H; try eassumption. exact H3.
        - eassumption.
        - eassumption.
      Qed.

      Lemma interpret_bind {A B} s postF postA (a : free A) (b : A -> free B) :
        interpret (bind a b) s postF postA <->
        interpret a s (fun x s => interpret (b x) s postF postA) postA.
      Proof.
        revert postF; revert postA; revert b; revert B; revert s; induction a.
        2: { intros. cbn. reflexivity. }
        split; intros; eapply interpret_action_weaken_post; intros.
        - eapply H. exact H1.
        - exact H1.
        - eauto.
        - eapply H. exact H1.
        - exact H1.
        - eauto.
      Qed.

      Lemma interpret_bind_ex_mid {A B} m0 postF postA (a : free A) (b : A -> free B) :
        interpret (bind a b) m0 postF postA <->
        (exists mid, interpret a m0 mid postA /\ forall x m1, mid x m1 -> interpret (b x) m1 postF postA).
      Proof.
        rewrite interpret_bind.
        split; [intros ? | intros (?&?&?)].
        { exists (fun x m1 => interpret (b x) m1 postF postA); split; eauto. }
        { eauto using interpret_weaken_post. }
      Qed.
    End WithStateAndAbort.
  End WithInterface.
  Global Arguments free : clear implicits.
End free. Notation free := free.free.
