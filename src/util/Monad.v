Require Import Coq.Logic.FunctionalExtensionality.

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
  (right associativity, at level 60).
Notation "m1 ;; m2" := (Bind m1 (fun _ => m2))
  (right associativity, at level 60).

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


(* T for transformer, corresponds to Haskell's MaybeT: *)
Definition optionT(M: Type -> Type)(A: Type) := M (option A).

Instance OptionT_Monad(M: Type -> Type){MM: Monad M}: Monad (optionT M) := {|
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

