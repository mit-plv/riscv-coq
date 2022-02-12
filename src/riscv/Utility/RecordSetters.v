Require Import Ltac2.Ltac2.
Require Ltac2.Option.
Set Default Proof Mode "Classic".

Ltac2 rec strip_foralls(t: constr) :=
  match Constr.Unsafe.kind t with
  | Constr.Unsafe.Prod b u => let (bs, body) := strip_foralls u in (b :: bs, body)
  | _ => ([], t)
  end.

Ltac2 app_arg_count(t: constr) :=
  match Constr.Unsafe.kind t with
  | Constr.Unsafe.App f args => Array.length args
  | _ => 0
  end.

Ltac2 binder_to_field(qualification: ident list)(b: binder) :=
   Option.get (Env.get (List.append qualification [Option.get (Constr.Binder.name b)])).

Ltac2 field_names(ctor_ref: Std.reference) :=
  let ctor_type := Constr.type (Env.instantiate ctor_ref) in
  let (binders, result) := strip_foralls ctor_type in
  let n_type_args := app_arg_count result in
  let field_name_binders := List.skipn n_type_args binders in
  List.map (binder_to_field (List.removelast (Env.path ctor_ref))) field_name_binders.

Ltac2 constructor_of_record(t: constr) :=
  match Constr.Unsafe.kind t with
  | Constr.Unsafe.Ind ind inst =>
    Std.ConstructRef (Constr.Unsafe.constructor ind 0)
  | _ => Control.throw (Invalid_argument (Some (Message.of_constr t)))
  end.

Ltac2 mkApp(f: constr)(args: constr array) :=
  Constr.Unsafe.make (Constr.Unsafe.App f args).

Ltac2 eta(t: constr) :=
  let (h, args) := match Constr.Unsafe.kind t with
                   | Constr.Unsafe.App h args => (h, args)
                   | _ => (t, Array.empty ())
                   end in
  let ctor := constructor_of_record h in
  let getters := List.map (fun getterRef => mkApp (Env.instantiate getterRef) args)
                          (field_names ctor) in
  constr:(fun x: $t => ltac2:(
    let projections := List.map (fun getter => constr:($getter &x)) getters in
    let res := mkApp (mkApp (Env.instantiate ctor) args) (Array.of_list projections) in
    exact $res)).

Ltac exact_eta :=
  ltac2:(t |- let res := eta (Option.get (Ltac1.to_constr t)) in exact $res).

Ltac eta T := constr:(ltac:(exact_eta T)).

Definition Updater{R E: Type}(getter: R -> E): Type := (E -> E) -> R -> R.
Existing Class Updater.

Ltac updater R getter :=
  let etaR := eta R in
  lazymatch etaR with
  | context[getter] => idtac
  | _ => fail 1 getter "is not a field of" R
  end;
  lazymatch eval pattern getter in etaR with
  | ?updateR _ =>
      let u := eval cbv beta in (fun updateE => updateR (fun r => updateE (getter r))) in
      exact u
  end.

Global Hint Extern 1 (@Updater ?R ?E ?getter) => updater R getter : typeclass_instances.

(* Note: in coq-record-update, the second-to-last argument of `set` is an updater
   of type `E -> E` (a function transforming an old value into a new value),
   and for setting a field, it just passes a constant function that ignores the
   old value.
   This is inconvenient for me because I use rewriting/simplification tactics that
   don't recurse under binders, but I do want them to recurse into new values of set,
   so we need two separate definitions for `set` and `update` *)

Definition update{R E: Type}(getter: R -> E){updater: Updater getter}
  : (E -> E) -> R -> R := updater.

Definition set{R E: Type}(getter: R -> E){updater: Updater getter}(newVal: E): R -> R :=
  updater (fun _ => newVal).

(*
Module RecordSetNotations1.
  Declare Scope record_set.
  Delimit Scope record_set with rs.
  Open Scope rs.
  (* Note: coq-record-update uses level 12, but I prefer level 8:
      https://github.com/tchajed/coq-record-update/issues/14 *)
  Notation "x <| proj ::= f |>" := (update proj f x)
     (at level 8, f at next level, left associativity, format "x <| proj  ::=  f |>")
     : record_set.
  Notation "x <| proj := v |>" := (set proj v x)
     (at level 8, left associativity, format "x <| proj  :=  v |>")
     : record_set.
End RecordSetNotations1.
*)

Module Export RecordSetNotationsOCamlLike.
  Declare Scope record_set.
  Delimit Scope record_set with rs.
  Open Scope rs.

  Declare Custom Entry field_update.
  Notation "proj := v" := (set proj v)
    (in custom field_update at level 1, proj constr at level 99, v constr at level 99)
    : record_set.
  Notation "proj ::= f" := (update proj f)
    (in custom field_update at level 1, proj constr at level 99, f constr at level 99)
    : record_set.

  (* marker function to enable notation printing *)
  Definition apply_update{R: Type}(u: R -> R): R -> R := u.

  Notation "{ x 'with' u }" := (apply_update u x)
     (at level 0, x at level 99, u custom field_update at level 1,
      format "{  x  'with'  u  }") : record_set.
  Notation "{ x 'with' u ; .. ; v ; w }" :=
     (apply_update w (apply_update v .. (apply_update u x) .. ))
     (at level 0, x at level 99, u custom field_update at level 1,
      v custom field_update at level 1, w custom field_update at level 1,
      format "{  x  'with'  u ;  .. ;  v ;  w  }") : record_set.
End RecordSetNotationsOCamlLike.

Module LeftUpdateNotations.
  Declare Scope record_set.
  Delimit Scope record_set with rs.
  Open Scope rs.

  Declare Custom Entry fld_update.
  Notation "proj := v" := (set proj v)
    (in custom fld_update at level 1, proj constr at level 99, v constr at level 99)
    : record_set.
  Notation "proj ::= f" := (update proj f)
    (in custom fld_update at level 1, proj constr at level 99, f constr at level 99)
    : record_set.
  Notation "'{!' u }" := u
     (at level 0, u custom fld_update at level 1,
      format "'{!'  u  }")
    : record_set.
  Notation "'{!' u ; v ; .. ; w } r" := (u (v .. (w r) ..))
     (at level 10, u custom fld_update at level 1, r constr at level 9,
      v custom fld_update at level 1, w custom fld_update at level 1,
      format "'{!'  u ;  v ;  .. ;  w  }  r")
    : record_set.
  (* Doesn't print. If move the r into (fun r => ...) on the rhs, it prints, but as
     soon as a `cbv beta` happens, it doesn't print any more *)
End LeftUpdateNotations.

Module RecordSetterTests.

  Record foo(A: Type)(n: nat) := {
    fieldA: A;
    fieldB: n = n;
    fieldC: bool;
  }.

  Arguments fieldA {_ _}.
  Arguments fieldB {_ _}.
  Arguments fieldC {_ _}.

  Example testFoo(b: bool): foo nat 2 :=
    {| fieldA := 3; fieldB := eq_refl; fieldC := b |}.

  Goal forall b, { testFoo b with fieldC := false } = { testFoo b with fieldC := false }.
  Abort.

  Goal forall b,
      { testFoo b with fieldC := true; fieldC := false; fieldA ::= Nat.add 2 } =
      { testFoo b with fieldA ::= Nat.add 1; fieldC := false; fieldA ::= Nat.add 1 }.
  Proof.
    intros. unfold apply_update. unfold update, set. cbn. reflexivity.
  Qed.
End RecordSetterTests.


Module record.

  Ltac head t :=
    lazymatch t with
    | ?f _ => head f
    | _ => t
    end.

  Ltac apply_set fullRecord partialRecord getter newVal :=
    match partialRecord with
    | ?rest ?fieldVal =>
        let __ := match constr:(Set) with
                  | _ => unify (getter fullRecord) fieldVal
                  end in
        constr:(rest newVal)
    | ?rest ?fieldVal =>
        let r := apply_set fullRecord rest getter newVal in constr:(r fieldVal)
    end.

  (* TODO generalize: ltac that traverses list of updates and unique-ifies them *)
  Ltac simp_step :=
    match goal with
    | |- context[ ?fieldA { ?r with ?fieldB := ?v } ] =>
        progress tryif constr_eq fieldA fieldB
        then change (fieldA { r with fieldB := v }) with v
        else change (fieldA { r with fieldB := v }) with (fieldA r)
    | |- context[ ?fieldA { ?r with ?fieldB ::= ?f } ] =>
        progress tryif constr_eq fieldA fieldB
        then change (fieldA { r with fieldB ::= f }) with (f (fieldA r))
        else change (fieldA { r with fieldB ::= f }) with (fieldA r)
    | |- context[{ ?r with ?field := ?v1; ?field := ?v2 }] =>
        progress change { r with field := v1; field := v2 } with { r with field := v2 }
    | |- context[{ ?r with ?field ::= ?f1; ?field := ?v2 }] =>
        progress change { r with field ::= f1; field := v2 } with { r with field := v2 }
    | |- context[{ ?r with ?field := ?v1; ?field ::= ?f2 }] =>
        progress change { r with field := v1; field ::= f2 }
                 with { r with field := f2 v1 }
    | |- context[{ ?r with ?field ::= ?f1; ?field ::= ?f2 }] =>
        progress change { r with field ::= f1; field ::= f2 }
                 with { r with field := f2 (f1 (field r)) }
    | |- context[{ ?r with ?field := ?v }] =>
        let h := head r in is_constructor h;
        let res := apply_set r r field v in
        progress change { r with field := v } with res
    | |- context[{ ?r with ?field ::= ?f }] =>
        let h := head r in is_constructor h;
        let bare_field := head field in (* <-- strip implicit args/params *)
        let oldval := eval cbn [bare_field] in (field r) in
        let res := apply_set r r field (f oldval) in
        progress change { r with field ::= f } with res

    | H: context[ ?fieldA { ?r with ?fieldB := ?v } ] |- _ =>
        progress tryif constr_eq fieldA fieldB
        then change (fieldA { r with fieldB := v }) with v in H
        else change (fieldA { r with fieldB := v }) with (fieldA r) in H
    | H: context[ ?fieldA { ?r with ?fieldB ::= ?f } ] |- _ =>
        progress tryif constr_eq fieldA fieldB
        then change (fieldA { r with fieldB ::= f }) with (f (fieldA r)) in H
        else change (fieldA { r with fieldB ::= f }) with (fieldA r) in H
    | H: context[{ ?r with ?field := ?v1; ?field := ?v2 }] |- _ =>
        progress change { r with field := v1; field := v2 } with { r with field := v2 } in H
    | H: context[{ ?r with ?field ::= ?f1; ?field := ?v2 }] |- _ =>
        progress change { r with field ::= f1; field := v2 } with { r with field := v2 } in H
    | H: context[{ ?r with ?field := ?v1; ?field ::= ?f2 }] |- _ =>
        progress change { r with field := v1; field ::= f2 }
                 with { r with field := f2 v1 } in H
    | H: context[{ ?r with ?field ::= ?f1; ?field ::= ?f2 }] |- _ =>
        progress change { r with field ::= f1; field ::= f2 }
                 with { r with field := f2 (f1 (field r)) } in H
    | H: context[{ ?r with ?field := ?v }] |- _ =>
        let h := head r in is_constructor h;
        let res := apply_set r r field v in
        progress change { r with field := v } with res in H
    | H: context[{ ?r with ?field ::= ?f }] |- _ =>
        let h := head r in is_constructor h;
        let bare_field := head field in (* <-- strip implicit args/params *)
        let oldval := eval cbn [bare_field] in (field r) in
        let res := apply_set r r field (f oldval) in
        progress change { r with field ::= f } with res in H
    end.

  Ltac simp := repeat simp_step.
End record.
