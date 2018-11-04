(* monads implemented in terms of fmap & join & return instead of bind & return *)
Require Import Coq.Lists.List.

Class Monad(M: Type -> Type) := mkMonad {
  ret: forall {A}, A -> M A;
  mmap: forall {A B}, (A -> B) -> M A -> M B;
  join: forall {A}, M (M A) -> M A;
}.

Definition bind{M: Type -> Type}{MM: Monad M}{A B: Type}(m: M A)(f: A -> M B): M B :=
  join (mmap f m).

Notation "x <- m1 ; m2" := (bind m1 (fun x => m2))
  (right associativity, at level 60) : monad_scope.
Notation "m1 ;; m2" := (bind m1 (fun _ => m2))
  (right associativity, at level 60) : monad_scope.

Open Scope monad_scope.

Instance identity_monad: Monad (@id Type) := {|
  ret := @id;
  mmap{A B} := @id (A -> B);
  join := @id;
|}.

Record optionT(M: Type -> Type)(A: Type): Type := mkOptionT {
  runOptionT: M (option A)
}.
Arguments mkOptionT {M} {A} (_).
Arguments runOptionT {M} {A} (_).

Definition retOption{A}: A -> option A := Some.

Definition mapOption{A B}(f: A -> B)(oa: option A): option B :=
  match oa with
  | Some a => Some (f a)
  | None => None
  end.

Definition flattenOption{A}(ooa: option (option A)): option A :=
  match ooa with
  | Some (Some a) => Some a
  | _ => None
  end.

Instance OptionT_Monad(M: Type -> Type){MM: Monad M}: Monad (optionT M) := {|
  ret{A}(a: A) := mkOptionT (ret (retOption a));
  mmap{A B}(f: A -> B)(oma: optionT M A) :=
    mkOptionT (mmap (mapOption f)
                    (runOptionT oma));
  join{A}(omoma: (optionT M) ((optionT M) A)) :=
    mkOptionT (join (mmap (fun (ooma: option (optionT M A)) =>
                             match ooma with
                             | Some oma => runOptionT oma
                             | None => ret None
                             end)
                          (runOptionT omoma)));
|}.


Definition retList{A}(a: A): list A := cons a nil.

Definition mapList: forall {A B: Type}, (A -> B) -> list A -> list B := @List.map.

Definition flattenList: forall {A}, list (list A) -> list A := @List.concat.

Record listT(M: Type -> Type)(A: Type): Type := mkListT {
  runListT: M (list A)
}.
Arguments mkListT {M} {A} (_).
Arguments runListT {M} {A} (_).

Instance listT_Monad(M: Type -> Type){MM: Monad M}: Monad (listT M) := {|
  ret{A}(a: A) := mkListT (ret (retList a));
  mmap{A B}(f: A -> B)(nma: listT M A) :=
    mkListT (mmap (mapList f)
                  (runListT nma));
  join{A}(nmnma: (listT M) ((listT M) A)) :=
    mkListT (join (mmap (fun (nnma: list (listT M A)) => _)
                        (runListT nmnma)));
|}.
induction nnma.
- apply (ret nil).
- apply runListT in a.
  refine (l1 <- a; l2 <- IHnnma; ret (l1 ++ l2)).
Defined.


Definition NonDet(A: Type) := A -> Prop.

Definition retNonDet{A}: A -> NonDet A := eq.

Definition mapNonDet{A B}(f: A -> B)(aset: NonDet A): NonDet B :=
  fun b => exists a, aset a /\ f a = b.

Definition flattenNonDet{A}(asetset: NonDet (NonDet A)): NonDet A :=
  fun a => exists aset, asetset aset /\ aset a.

Record NonDetT(M: Type -> Type)(A: Type): Type := mkNonDetT {
  runNonDetT: M (NonDet A)
}.
Arguments mkNonDetT {M} {A} (_).
Arguments runNonDetT {M} {A} (_).

Instance NonDetT_Monad(M: Type -> Type){MM: Monad M}: Monad (NonDetT M) := {|
  ret{A}(a: A) := mkNonDetT (ret (retNonDet a));
  mmap{A B}(f: A -> B)(nma: NonDetT M A) :=
    mkNonDetT (mmap (mapNonDet f)
                    (runNonDetT nma));
  join{A}(nmnma: (NonDetT M) ((NonDetT M) A)) :=
    mkNonDetT (join (mmap (fun (nnma: NonDet (NonDetT M A)) => _)
                          (runNonDetT nmnma)));
|}.

Check (exists (nma: NonDetT M A), nnma nma /\ runNonDetT nma = _).

Abort.
