Require Import Coq.Program.Basics.
Require Import Ltac2.Ltac2.
Require Ltac2.Option.
Require Import Ltac2.Bool.
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

Class Setter{R E: Type}(getter: R -> E): Type := set: (E -> E) -> R -> R.
Arguments set {R E} (getter) {Setter} (fieldUpdater) (r).

(* "getter and field updater": a specialized tuple with fst/snd that no one else uses,
   to avoid confusing tactics *)
Record gafu{R E: Type} := mk_gafu {
  gafu_getter: R -> E;
  gafu_field_updater: E -> E;
}.
Arguments gafu: clear implicits.
Arguments mk_gafu {R E} (gafu_getter gafu_field_updater).

(* partially uncurried set ("tupled set") that works better with notations *)
Definition tset{R E: Type}(t: gafu R E){Setter: Setter (gafu_getter t)}: R -> R :=
  set (gafu_getter t) (gafu_field_updater t).

Ltac setter R getter :=
  let getter := lazymatch getter with
                | gafu_getter (mk_gafu ?g _) => g
                | _ => getter
                end in
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

Global Hint Extern 1 (@Setter ?R ?E ?getter) => setter R getter : typeclass_instances.

(* Note: To update a field with a constant value (rather than by applying an
   updater function to its old value), we could just use the constant function
   `fun _ => newValue`, but then `newValue` would appear under a binder, which
   causes some rewriting/simplification tactics which don't recurse under binders
   to miss opportunities for rewriting/simplification, so we use this explicit
   definition of `const` instead. *)
Definition const{E: Type}(newValue: E): E -> E := fun _ => newValue.

Module Export RecordSetNotations1.
  Declare Scope record_set.
  Delimit Scope record_set with rs.
  Open Scope rs.
  (* Note: coq-record-update uses level 12, but I prefer level 8:
      https://github.com/tchajed/coq-record-update/issues/14 *)
  Notation "x <| proj ::= f |>" := (set proj f x)
     (at level 8, f at level 99, left associativity, format "x <| proj  ::=  f |>")
     : record_set.
  Notation "x <| proj := v |>" := (set proj (const v) x)
     (at level 8, v at level 99, left associativity, format "x <| proj  :=  v |>")
     : record_set.
End RecordSetNotations1.

Module Export RecordSetNotations.
  Declare Scope record_set.
  Delimit Scope record_set with rs.
  Open Scope rs.

  Declare Custom Entry field_update.
  Notation "proj := v" := (mk_gafu proj (const v))
    (in custom field_update at level 1, proj constr at level 99, v constr at level 99,
     format "proj  :=  '/' v")
    : record_set.
  Notation "proj ::= f" := (mk_gafu proj f)
    (in custom field_update at level 1, proj constr at level 99, f constr at level 99,
     format "proj  ::=  '/' f")
    : record_set.

  Notation "'{!' u }" := (tset u)
     (at level 0, u custom field_update at level 1,
      format "'{!'  u  }")
    : record_set.

  Notation "'{!' u ; v ; .. ; w }" :=
     (compose (tset w) .. (compose (tset v) (tset u)) ..)
     (at level 0, u custom field_update at level 1, v custom field_update at level 1,
      w custom field_update at level 1,
      format "'{!'  '[' u ;  '/' v ;  '/' .. ;  '/' w  ']' }")
    : record_set.

  Notation "{ x 'with' u }" := (tset u x)
     (at level 0, x at level 99, u custom field_update at level 1,
      format "{  x  'with'  '[' u ']'  }") : record_set.
  Notation "{ x 'with' u ; .. ; v ; w }" :=
     (tset w (tset v .. (tset u x) .. ))
     (at level 0, x at level 99, u custom field_update at level 1,
      v custom field_update at level 1, w custom field_update at level 1,
      format "{  x  'with'  '[' u ;  '/' .. ;  '/' v ;  '/' w  ']' }") : record_set.
End RecordSetNotations.

Module record.

  (* Is c a bound var with 1-based de Brujin index i? *)
  Ltac2 is_rel(i: int)(c: constr) :=
    match Constr.Unsafe.kind c with
    | Constr.Unsafe.Rel j => Int.equal i j
    | _ => false
    end.

  (* Returns (Some i) if c is of the form (fun xn .. x2 x1 => xi) with (1 <= i <= n),
     None otherwise *)
  Ltac2 lambda_proj_index(c: constr) :=
    let rec test d t :=
      match Constr.Unsafe.kind t with
      | Constr.Unsafe.Lambda x body => test (Int.add d 1) body
      | Constr.Unsafe.Rel i => if Int.le i d then Some i else None
      | _ => None
      end in
    test 0 c.

  (* Returns (Some i) if u is of the form
       (fun r => match r with
                 | constructor params field_N ... field_2 field_1 => field_i
                 end)
     with (1 <= i <= n), None otherwise. *)
  Ltac2 unfolded_getter_proj_index(u: constr) :=
    match Constr.Unsafe.kind u with
    | Constr.Unsafe.Lambda x body =>
        match Constr.Unsafe.kind body with
        | Constr.Unsafe.Case _ _ _ d branches =>
            if is_rel 1 d && Int.equal (Array.length branches) 1 then
              lambda_proj_index (Array.get branches 0)
            else None
        | _ => None
        end
    | _ => None
    end.

  Ltac2 rec strip_n_lambdas(n: int)(c: constr) :=
    if Int.le n 0 then Some c else
      match Constr.Unsafe.kind c with
      | Constr.Unsafe.Lambda x body => strip_n_lambdas (Int.sub n 1) body
      | _ => None
      end.

  (* Returns (Some i) if f is a getter returning the i-th-to-last field of a record,
     None otherwise *)
  Ltac2 getter_proj_index(f: constr) :=
    match Constr.Unsafe.kind f with
    | Constr.Unsafe.App h params =>
        match Constr.Unsafe.kind h with
        | Constr.Unsafe.Constant cst _ =>
            let flags := {
                Std.rBeta := false;
                Std.rMatch := false;
                Std.rFix := false;
                Std.rCofix := false;
                Std.rZeta := false;
                Std.rDelta := false; (* false = delta only on rConst*)
                Std.rConst := [Std.ConstRef cst]
              } in
            let unfolded_h := Std.eval_cbv flags h in
            match strip_n_lambdas (Array.length params) unfolded_h with
            | Some l => unfolded_getter_proj_index l
            | None => None
            end
        | _ => None
        end
    | _ => None
    end.

  Ltac2 rec right_leaning_compose(c1: constr)(c2: constr) :=
    lazy_match! c1 with
    | compose ?f1 ?f2 =>
        right_leaning_compose f1 (right_leaning_compose f2 c2)
    | _ => constr:(compose $c1 $c2)
    end.

  Ltac2 Type exn ::= [ Type_not_preserved (constr, constr, constr, constr) ].

  (* for debugging *)
  Ltac2 preserve_type(c: constr)(f: unit -> constr option) :=
    let t := Constr.type c in
    match f () with
    | Some c' =>
        let t' := Constr.type c' in
        orelse (fun () => unify $t $t'; Some c')
               (fun _ => Control.throw (Type_not_preserved c t c' t'))
    | None => None
    end.

  Ltac2 rec constr_list_to_msg(l: constr list) :=
    match l with
    | [] => Message.of_string " "
    | h :: t => Message.concat (Message.of_string " ") (Message.concat
                 (Message.of_constr h) (constr_list_to_msg t))
    end.

  Ltac2 log_call(name: string)(args: constr list) := (). (*
    Message.print (Message.concat (Message.of_string "(Calling ")
      (Message.concat (Message.of_string name) (constr_list_to_msg args))). *)

  Ltac2 co_msg(co: constr option) :=
    match co with
    | Some c => Message.concat (Message.of_string "Some constr:(") (Message.concat (Message.of_constr c) (Message.of_string ")"))
    | None => Message.of_string "None"
    end.

  Ltac2 log_ret(name: string)(args: constr list)(ret: constr option) := (*
    Message.print (Message.concat (Message.concat (Message.of_string "Return value of ")
      (Message.concat (Message.of_string name) (constr_list_to_msg args)))
           (Message.concat (Message.of_string " is ") (Message.concat (co_msg ret) (Message.of_string ")")))); *)
    ret.

  (* g: getter, u: field updater, c: any constr
     If c is a series of setters setting g to some u_old, replaces u_old by u.
     If c is a series of setters not setting g and ending in a constructor,
     replaces the constructor argument corresponding to g by u.
     If (Some c') is returned, c' is convertible to c, but simpler.
     If None is returned, no simplification could be made, so the caller might
     be able to reuse an existing (tset (mk_gafu g u) c) term rather than
     allocating a new one. *)
  Ltac2 rec push_down_setter(g: constr)(u: constr)(c: constr) :=
    log_call "push_down_setter" [g; u; c];
    let c' := preserve_type c (fun () =>
    lazy_match! c with
    | tset (mk_gafu ?g' ?u') ?r =>
        (* setter applied to setter *)
        if Constr.equal g g' then
          (* setter applied to same setter *)
          lazy_match! u with
          | const _ => Some constr:(tset (mk_gafu $g $u) $r)
          | _ => let u_combined :=
                   lazy_match! u' with
                   | const ?v' => eval cbv beta in (const ($u $v'))
                   | _ => right_leaning_compose u u'
                   end in
                 Some constr:(tset (mk_gafu $g $u_combined) $r)
          end
        else (* setter applied to different setter *)
          match push_down_setter g u r with
          | Some r' => Some constr:(tset (mk_gafu $g' $u') $r')
          | None => None
          end
    | _ => match Constr.Unsafe.kind c with
           | Constr.Unsafe.App h args =>
               if Constr.is_constructor h then
                 (* setter applied to constructor *)
                 match getter_proj_index g with
                 | Some i =>
                     let j := Int.sub (Array.length args) i in
                     let old_field := Array.get args j in
                     let new_field :=
                       lazy_match! u with
                       | const ?v => v
                       | _ => eval cbv beta in ($u $old_field)
                       end in
                     let new_args := Array.copy args in
                     Array.set new_args j new_field;
                     Some (Constr.Unsafe.make (Constr.Unsafe.App h new_args))
                  | None => Control.throw_invalid_argument "g is not a getter"
                  end
               else (* setter applied to non-setter-non-constructor *) None
           | _ => (* setter applied to non-setter-non-constructor *) None
           end
    end) in
    log_ret "push_down_setter" [g; u; c] c'.

  (* g: getter, i: its backwards-index, c: any constr
     If c is a series of setters setting g to some v, returns v.
     If c is a series of setters not setting g and ending in a constructor,
     returns the constructor argument corresponding to g.
     If (Some c') is returned, c' is convertible to c, but simpler.
     If None is returned, no simplification could be made, so the caller might
     be able to reuse an existing (g c) term rather than allocating a new one. *)
  Ltac2 rec lookup_getter(g: constr)(i: int)(c: constr) :=
    log_call "lookup_getter" [g; c];
    let c' :=
    lazy_match! c with
    | tset (mk_gafu ?g' ?u') ?r =>
        (* getter applied to setter *)
        if Constr.equal g g' then
          (* getter applied to same setter *)
          lazy_match! u' with
          | const ?v' => Some v'
          | _ => let w := match lookup_getter g i r with
                          | Some w => w
                          | None => constr:($g $r)
                          end in
                 Some (eval cbv beta in ($u' $w))
          end
        else (* getter applied to different setter *)
          match lookup_getter g i r with
          | Some w => Some w
          | None => Some constr:($g $r)
          end
    | _ => match Constr.Unsafe.kind c with
           | Constr.Unsafe.App h args =>
               if Constr.is_constructor h then (* getter applied to constructor *)
                 Some (Array.get args (Int.sub (Array.length args) i))
               else (* getter applied to non-setter-non-constructor *) None
           | _ => (* getter applied to non-setter-non-constructor *) None
           end
    end in
    log_ret "lookup_getter" [g; c] c'.

  Ltac2 simp_app(f: constr)(a: constr) :=
    log_call "simp_app" [f; a];
    let c' := lazy_match! f with
    | tset (mk_gafu ?g ?u) => push_down_setter g u a
    | _ => match getter_proj_index f with
           | Some i => lookup_getter f i a
           | None => None
           end
    end in
    log_ret "simp_app" [f; a] c'.

  Ltac2 rec simp_term(c: constr) :=
    log_call "simp_term" [c];
    let c' := preserve_type c (fun () =>
    lazy_match! c with
    | ?f ?a =>
        match simp_term f with
        | Some f' =>
            let a' := match simp_term a with
                      | Some a' => a'
                      | None => a
                      end in
            let o := simp_app f' a' in
            match o with
            | Some _ => o
            | None => Some constr:($f' $a')
            end
        | None =>
            match simp_term a with
            | Some a' =>
                let o := simp_app f a' in
                match o with
                | Some _ => o
                | None => Some constr:($f $a')
                end
            | None =>
                (* if nothing was simplifiable, we return None instead of
                   reconstructing an identical constr:($f $a) *)
                simp_app f a
            end
        end
    | _ => None
    end) in
    log_ret "simp_term" [c] c'.

  Ltac2 simp_goal () :=
    match simp_term (Control.goal ()) with
    | Some g => change $g
    | None => Control.backtrack_tactic_failure "no simplification opportunities"
    end.

  Ltac simp_goal := ltac2:(simp_goal ()).

  Ltac simp := simp_goal. (* TODO also in hyps *)
End record.

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

  Goal forall b, fieldA (testFoo b)<|fieldA := 3|> = 3. intros. reflexivity. Qed.

  Goal forall b,
      { testFoo b with fieldC := true; fieldC := false; fieldA ::= Nat.add 2 } =
      { testFoo b with fieldA ::= Nat.add 1; fieldC := false; fieldA ::= Nat.add 1 }.
  Proof.
    intros. unfold tset, gafu_getter, gafu_field_updater. unfold set, const. cbn.
    reflexivity.
  Qed.
  (*  *)
  Check (fun b => {! fieldC := false } (testFoo b)).
  Check (fun b => {! fieldC := false; fieldC := true } (testFoo b)).
  Check (fun b => {! fieldC := false; fieldC := true; fieldA ::= Nat.add 2 } (testFoo b)).

  Goal forall b,
      {! fieldC := false; fieldC := true; fieldA ::= Nat.add 2 } (testFoo b) =
      {! fieldA ::= Nat.add 1; fieldC := true; fieldA ::= Nat.add 1 } (testFoo b).
  Proof.
    intros. unfold tset, gafu_getter, gafu_field_updater. unfold set, const, compose. cbn.
    reflexivity.
  Qed.

  Goal forall r: foo (foo nat 4) 2,
  { r with fieldA ::= {! fieldA ::= Nat.add 1 } }.(fieldA).(fieldA) = S r.(fieldA).(fieldA).
  Proof. intros. reflexivity. Qed.

  (* simplify setter applied to constructor *)
  Goal forall b, { testFoo b with fieldA ::= (Nat.add 12) } = testFoo b.
  Proof.
    unfold testFoo at 1. intros.
    record.simp.
  Abort.

  (* simplify getter applied to setter *)
  Goal forall b, fieldB { testFoo b with fieldA ::= (Nat.add 12) } = eq_refl.
    intros.
    record.simp.
  Abort.

  (* unfold getter applied to constructor *)
  Goal forall b, fieldB (testFoo b) = eq_refl.
  Proof.
    intros. unfold testFoo. record.simp.
  Abort.
End RecordSetterTests.
