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

Definition Id: Type -> Type := id.

Instance Id_monad: Monad Id := {|
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
    mkListT (join (mmap (fun nnma =>
                           fold_left
                             (fun (acc: M (list A)) (elem: listT M A) =>
                                l1 <- runListT elem; l2 <- acc; ret (l1 ++ l2))
                             nnma
                             (ret nil))
                        (runListT nmnma)));
|}.

Definition State(S A: Type) := S -> (A * S).

Record StateT(S: Type)(M: Type -> Type)(A: Type): Type := mkStateT {
  runStateT: S -> M (A * S)%type
}.
Arguments mkStateT {S} {M} {A} (_).
Arguments runStateT {S} {M} {A} (_).

Instance StateT_Monad(S: Type)(M: Type -> Type){MM: Monad M}: Monad (StateT S M) := {|
  ret{A}(a: A) := mkStateT (fun s => ret (a, s));
  mmap{A B}(f: A -> B)(sma: StateT S M A) :=
    mkStateT (fun s => mmap (fun '(a, s0) => (f a, s0)) (runStateT sma s));
  join{A}(smsma: (StateT S M) ((StateT S M) A)) :=
    mkStateT (fun s1 => p <- runStateT smsma s1; let '(ssma, s2) := p in runStateT ssma s2);
|}.

Definition get{S: Type}{M: Type -> Type}{MM: Monad M}: StateT S M S :=
  mkStateT (fun (s: S) => ret (s, s)).

Definition put{S: Type}{M: Type -> Type}{MM: Monad M}(s: S): StateT S M unit :=
  mkStateT (fun _ => ret (tt, s)).

(*
Definition OOState(S: Type): Type -> Type := optionT (optionT (StateT S Id)).

Definition runOOState{S A: Type}(m: OOState S A)(s: S): option (option A * S).
  apply runOptionT in m.
  apply runOptionT in m.
  apply (@runStateT S) in m. 2: apply s.
  apply runOptionT in m.
  cbv in m.
*)

Definition OOState(S: Type): Type -> Type := optionT (StateT S (optionT Id)).

Definition runOOState{S A: Type}(m: OOState S A)(s: S): option (option A * S) :=
  runOptionT (runStateT (runOptionT m) s).

Definition OOStateND(S: Type): Type -> Type := listT (OOState S).

Definition runOOStateND{S A: Type}(m: OOStateND S A)(s: S): list (option (option A * S)).
  apply runListT in m.
  apply (@runOOState S (list A)) in m. 2: apply s.
Abort.

(* if we use listT for the nondeterminism, it doesn't help much towards getting transformers,
   because we'd have to put listT at the innermost level *)

Record NonDetT(M: Type -> Type)(A: Type): Type := mkNonDetT {
  runNonDetT: list (M A)
}.
Arguments mkNonDetT {M} {A} (_).
Arguments runNonDetT {M} {A} (_).

Definition flatMapList{A B: Type}(f: A -> list B)(l: list A): list B :=
  List.concat (List.map f l).

Instance NonDetT_Monad(M: Type -> Type){MM: Monad M}: Monad (NonDetT M) := {|
  ret{A}(a: A) := mkNonDetT (cons (ret a) nil);
  mmap{A B}(f: A -> B)(nma: NonDetT M A) :=
    mkNonDetT (List.map (mmap f) (runNonDetT nma));
  join{A}(nmnma: (NonDetT M) ((NonDetT M) A)) :=
    mkNonDetT _;
|}.
(* same problem as earlier: we'd need to know now whether to apply nil or cons,
   to know that we'd have to enter the monad *)
Abort.


(*
will have to do (run1; get) to obtain list of possible new states
*)