(* monads implemented in terms of fmap & join & return instead of bind & return *)
Require Import Coq.Lists.List.

Class Monad(M: Type -> Type) := mkMonad {
  ret: forall {A}, A -> M A;
  mmap: forall {A B}, (A -> B) -> M A -> M B;
  join: forall {A}, M (M A) -> M A;
}.

Definition bind{M: Type -> Type}{MM: Monad M}{A B: Type}(m: M A)(f: A -> M B): M B :=
  join (mmap f m).

Declare Scope monad_scope.

Notation "x <- m1 ; m2" := (bind m1 (fun x => m2))
  (right associativity, at level 60) : monad_scope.
Notation "m1 ;; m2" := (bind m1 (fun _ => m2))
  (right associativity, at level 60) : monad_scope.

Open Scope monad_scope.

Definition Id: Type -> Type := id.

#[global] Instance Id_monad: Monad Id := {|
  ret := @id;
  mmap A B := @id (A -> B);
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

#[global] Instance OptionT_Monad(M: Type -> Type){MM: Monad M}: Monad (optionT M) := {|
  ret A (a: A) := mkOptionT (ret (retOption a));
  mmap A B (f: A -> B)(oma: optionT M A) :=
    mkOptionT (mmap (mapOption f)
                    (runOptionT oma));
  join A (omoma: (optionT M) ((optionT M) A)) :=
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

#[global] Instance listT_Monad(M: Type -> Type){MM: Monad M}: Monad (listT M) := {|
  ret A (a: A) := mkListT (ret (retList a));
  mmap A B (f: A -> B)(nma: listT M A) :=
    mkListT (mmap (mapList f)
                  (runListT nma));
  join A (nmnma: (listT M) ((listT M) A)) :=
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

#[global] Instance StateT_Monad(S: Type)(M: Type -> Type){MM: Monad M}: Monad (StateT S M) := {|
  ret A (a: A) := mkStateT (fun s => ret (a, s));
  mmap A B (f: A -> B)(sma: StateT S M A) :=
    mkStateT (fun s => mmap (fun '(a, s0) => (f a, s0)) (runStateT sma s));
  join A (smsma: (StateT S M) ((StateT S M) A)) :=
    mkStateT (fun s1 => p <- runStateT smsma s1; let '(ssma, s2) := p in runStateT ssma s2);
|}.

Definition get{S: Type}{M: Type -> Type}{MM: Monad M}: StateT S M S :=
  mkStateT (fun (s: S) => ret (s, s)).

Definition put{S: Type}{M: Type -> Type}{MM: Monad M}(s: S): StateT S M unit :=
  mkStateT (fun _ => ret (tt, s)).

(*
These are not very useful because often we'll have to write
"lift (t := optionT)" instead of just "lift" to prevent typeclass
search from looping infinitely, so we prefer to just define lift_xxxT
separately

Class MonadTrans(t: (Type -> Type) -> Type -> Type) := {
  lift: forall {M: Type -> Type} {MM: Monad M} {A: Type}, M A -> t M A;
}.

Instance optionT_MonadTrans: MonadTrans optionT := {
  lift{M}{MM}{A}(m: M A) := mkOptionT (mmap Some m);
}.

Instance stateT_MonadTrans(S: Type): MonadTrans (StateT S) := {
  lift{M}{MM}{A}(m: M A) := mkStateT (fun s => a <- m; ret (a, s));
}.

Instance listT_MonadTrans: MonadTrans listT := {
  lift{M}{MM}{A}(m: M A) := mkListT (mmap (fun a => cons a nil) m);
}.
*)


Definition liftOptionT{M: Type -> Type}{MM: Monad M}{A: Type}(m: M A): optionT M A :=
  mkOptionT (mmap Some m).

Definition liftStateT{S: Type}{M: Type -> Type}{MM: Monad M}{A: Type}(m: M A): StateT S M A :=
  mkStateT (fun s => a <- m; ret (a, s)).

Definition liftListT{M: Type -> Type}{MM: Monad M}{A: Type}(m: M A): listT M A :=
  mkListT (mmap (fun a => cons a nil) m).

(*
   Note: No way of composing
     NonDet A := list A
   and
     State S A := S -> (A * S)
   results in this signature!
*)
Definition NDS(S A: Type): Type := S -> list (A * S).

Record NDStateT(S: Type)(M: Type -> Type)(A: Type): Type := mkNDStateT {
  runNDStateT: S -> M (A * S)%type (* TODO where to put list ?? *)
}.
Arguments mkNDStateT {S} {M} {A} (_).
Arguments runNDStateT {S} {M} {A} (_).

(*
Instance NDStateT_Monad(S: Type)(M: Type -> Type){MM: Monad M}: Monad (NDStateT S M) := {|
  ret{A}(a: A) := mkStateT (fun s => ret (a, s));
  mmap{A B}(f: A -> B)(sma: StateT S M A) :=
    mkStateT (fun s => mmap (fun '(a, s0) => (f a, s0)) (runStateT sma s));
  join{A}(smsma: (StateT S M) ((StateT S M) A)) :=
    mkStateT (fun s1 => p <- runStateT smsma s1; let '(ssma, s2) := p in runStateT ssma s2);
|}.
*)

(* note: no "pick" is needed as argument here *)
#[global] Instance NDS_Monad(S: Type): Monad (NDS S) := {|
  ret A (a: A) :=
    fun s => cons (a, s) nil;
  mmap A B (f: A -> B)(m: NDS S A) :=
    fun s => List.map (fun '(a, s) => (f a, s)) (m s);
  join A (mm: NDS S (NDS S A)) :=
    fun s1 => List.concat (List.map (fun '(m, s2) => m s2) (mm s1));
|}.

(*
Definition NDS(S A: Type): Type := S -> (A * S) -> Prop.

Instance NDS_Monad(S: Type)(pick: forall (A: Type), NDS S A): Monad (NDS S) := {|
  ret{A}(a: A) := fun s1 '(v, s2) => s1 = s2 /\ a = v;
  mmap{A B}(f: A -> B)(m: NDS S A) := fun s1 '(b, s2) => _;
  join{A}(mm: NDS S (NDS S A)) := _;
|}.
*)

Module way1.

  Definition OState(S: Type): Type -> Type := StateT S (optionT Id).

  Definition runOState{S A: Type}(m: OState S A)(s: S): option (A * S) :=
    runOptionT (runStateT m s).

End way1.

Definition OState(S: Type): Type -> Type := optionT (StateT S Id).

Definition runOState{S A: Type}(m: OState S A)(s: S): option A * S :=
  runStateT (runOptionT m) s.

Definition OStateND(S: Type): Type -> Type := optionT (NDS S).

Definition runOStateND{S A: Type}(m: OStateND S A)(s: S): list (option A * S) :=
 runOptionT m s.


Section Test.

  Context {M: Type -> Type}.
  Axiom run1: M unit.
End Test.

(*
Axiom RiscvMachine: Type.
(*Check (@lift optionT _ _ _ _ get).*)
Check (@run1 (OStateND RiscvMachine);; liftListT (liftOptionT get)).
Check (runOStateND (@run1 (OStateND RiscvMachine);; liftListT (liftOptionT get))).

Definition comp1: OStateND (nat * nat) nat :=
  both <- liftListT (liftOptionT get); ret (fst both).

Definition comp20: OStateND (nat * nat) nat.
  refine (liftListT ( _)).
  unfold OState.
  refine (mkOptionT _).
  refine (ret None).
Defined.

Definition comp2: OStateND (nat * nat) nat :=
  liftListT (mkOptionT (ret None)).

Definition comp12: OStateND (nat * nat) nat :=
  c1 <- comp1;
  c2 <- comp2;
  ret (c1 + c2)%nat.

Compute (runOStateND comp12 (12, 23)).

Definition rvRunND(s: RiscvMachine): option (list RiscvMachine) :=
  fst (runOStateND (@run1 (OStateND RiscvMachine);; liftListT (liftOptionT get)) s).
*)

Section RunsTo.

  Variable State: Type.
  Variable step: State -> option (list State).

(* something is wrong: it should be "list (option State)":
  some nondet choices fail, others succeed.
  But maybe the way we compose, the monad already does the collecting for us,
  and only returns Some if all choices succeeded?
 *)

(*
  Inductive runsTo(initial: State)(P: State -> Prop): Prop :=
    | runsToDone:
        P initial ->
        runsTo initial P
    | runsToStep:
        (forall omid,
            step initial omid ->
            exists mids, omid = Some mids /\
                        List.Forall (fun mid => runsTo mid P) mids) ->
        runsTo initial P.
*)
End RunsTo.
