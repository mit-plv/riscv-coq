(* Some Ltac code and Gallina notations which can be used to translate a goal about integer
   arithmetic into smtlib syntax, so that it can be fed to an SMT solver such as Z3. *)

Require Import Coq.Logic.Classical_Prop.
Require Import Coq.ZArith.BinInt.

Open Scope Z_scope.

Definition marker(P: Prop): Prop := P.

Lemma E: forall A (P: A -> Prop), (exists a: A, ~ P a) <-> ~ forall (a: A), P a.
Proof.                                                                                
  intros. split.
  - intros. destruct H as [a H]. intro. apply H. auto.
  - intro. destruct (classic (exists a : A, ~ P a)) as [C | C]; [assumption|].
    exfalso. apply H. intro. destruct (classic (P a)) as [D | D]; [assumption |].
    exfalso. apply C. exists a. assumption.
Qed.

Lemma K: forall (P Q: Prop), (~ marker (P -> Q)) <-> marker (~ (P -> Q)).
Proof.
  cbv [marker]. intros. reflexivity. 
Qed.

Ltac countZ t :=
  lazymatch t with
  | forall (x: Z), @?t' x =>
    let a := eval cbv beta in (t' 0) in
        let r := countZ a in constr:(S r)
  | _ => constr:(O)
  end.

Ltac repeatN N f :=
  match N with
  | S ?n => f; repeatN n f
  | O => idtac
  end.

Ltac smt :=
  repeat match goal with
         | H: ?T |- _ => match T with
                         | Z => fail 1
                         | _ => revert H
                         end
         end;
  match goal with
  | |- ?P => change (marker P)
  end;
  repeat match goal with
         | H: _ |- _ => revert H
         end;
  match goal with
  | |- ?P => assert (~P); [|admit]
  end;
  match goal with
  | |- ~ ?P => let r := countZ P in repeatN r ltac:(setoid_rewrite <- E)
  end;
  setoid_rewrite K.
    
Notation "'and' A B" := (Logic.and A B) (at level 10, A at level 0, B at level 0).
Notation "'or' A B" := (Logic.or A B) (at level 10, A at level 0, B at level 0).
Notation "+ A B" := (Z.add A B) (at level 10, A at level 0, B at level 0).
Notation "< A B" := (Z.lt A B) (at level 10, A at level 0, B at level 0).
Notation "<= A B" := (Z.le A B) (at level 10, A at level 0, B at level 0).
Notation "- A B" := (Z.sub A B) (at level 10, A at level 0, B at level 0).
Notation "* A B" := (Z.mul A B) (at level 10, A at level 0, B at level 0, format " *  A  B").
Notation "= A B" := (@eq Z A B) (at level 10, A at level 0, B at level 0).
Notation "'not' A" := (not A) (at level 10, A at level 0).
Notation "'(declare-const' a 'Int)' body" := (ex (fun (a: Z) => body))
                                               (at level 10, body at level 10,
                                                format "(declare-const  a  Int) '//' body").
Notation "'(assert' P ')'" := (marker P)
                                (at level 10, P at level 0,
                                 format "(assert  P )").
Notation "- 0 a" := (Z.opp a) (at level 10, a at level 10).
Notation "'or' '(not' A ')' B" := (A -> B) (at level 10, A at level 0, B at level 0,
                                            format "or  (not  A )  B").

Global Set Printing Depth 10000.
