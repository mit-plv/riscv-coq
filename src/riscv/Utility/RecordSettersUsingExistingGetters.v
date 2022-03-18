Require Import Coq.Program.Basics.
Require Import Ltac2.Ltac2.
Require Ltac2.Option.
Require Import Ltac2.Bool.
Require Import coqutil.Ltac2Lib.Constr.
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
    let (h, nparams) := match Constr.Unsafe.kind f with
                        | Constr.Unsafe.App h params => (h, Array.length params)
                        | _ => (f, 0)
                        end in
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
        match strip_n_lambdas nparams unfolded_h with
        | Some l => unfolded_getter_proj_index l
        | None => None
        end
    | _ => None
    end.

  Ltac2 t_compose(t1: constr)(t2: constr)(t3: constr)(f: constr)(g: constr) :=
    let args := Array.make 5 t1 in
    Array.set args 1 t2;
    Array.set args 2 t3;
    Array.set args 3 f;
    Array.set args 4 g;
    Constr.Unsafe.make (Constr.Unsafe.App (Env.instantiate reference:(compose)) args).

  (* Note: Since there's no uconstr:(...) in Ltac2 (https://github.com/coq/coq/issues/13977),
     and we don't want to re-typecheck the term each time we create a piece of a term,
     (both for performance reasons and because the terms we're building contain unbound
     variables (dangling deBrujin indices)), we need to use mkApp to build the terms,
     and have to provide all implicit arguments explicitly. *)
  (* f: t2 -> t4, g: t1 -> t2                         f1    f2    g
                                                   t4 <- t3 <- t2 <- t1   *)
  Ltac2 rec right_leaning_compose t1 t2 t4 f g :=
    lazy_match! f with
    | @compose _ ?t3 _ ?f1 ?f2 =>
        right_leaning_compose t1 t3 t4 f1 (right_leaning_compose t1 t2 t3 f2 g)
    | _ => t_compose t1 t2 t4 f g
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

  Ltac2 t_tset(tR: constr)(tE: constr)(p: constr)(s: constr)(r: constr) :=
    let args := Array.make 5 tR in
    Array.set args 1 tE;
    Array.set args 2 p;
    Array.set args 3 s;
    Array.set args 4 r;
    Constr.Unsafe.make (Constr.Unsafe.App (Env.instantiate reference:(tset)) args).

  Ltac2 t_mk_gafu(tR: constr)(tE: constr)(g: constr)(u: constr) :=
    let args := Array.make 4 tR in
    Array.set args 1 tE;
    Array.set args 2 g;
    Array.set args 3 u;
    Constr.Unsafe.make (Constr.Unsafe.App (Env.instantiate reference:(mk_gafu)) args).

  Ltac2 t_const(tE: constr)(v: constr) :=
    let args := Array.make 2 tE in
    Array.set args 1 v;
    Constr.Unsafe.make (Constr.Unsafe.App (Env.instantiate reference:(const)) args).

  (* tR: record type
     tE: element type
     g: getter of type R -> E
     u: field updater of type E -> E
     c: any constr
     If c is a series of setters setting g to some u_old, replaces u_old by u.
     If c is a series of setters not setting g and ending in a constructor,
     replaces the constructor argument corresponding to g by u.
     If (Some c') is returned, c' is convertible to c, but simpler.
     If None is returned, no simplification could be made, so the caller might
     be able to reuse an existing (tset (mk_gafu g u) c) term rather than
     allocating a new one. *)
  Ltac2 rec push_down_setter(tR: constr)(tE: constr)(g: constr)(u: constr)(c: constr) :=
    log_call "push_down_setter" [g; u; c];
    let c' :=
    lazy_match! c with
    | @tset ?tR' ?tE' (mk_gafu ?g' ?u') ?s ?r =>
        (* setter applied to setter *)
        if Constr.equal g g' then
          (* setter applied to same setter *)
          lazy_match! u with
          | const _ => Some (t_tset tR tE (t_mk_gafu tR tE g u) s r)
          | _ => let u_combined :=
                   lazy_match! u' with
                   | const ?v' => t_const tE (simp_app_nonstrict u v')
                   | _ => right_leaning_compose tE tE tE u u'
                   end in
                 Some (t_tset tR tE (t_mk_gafu tR tE g u_combined) s r)
          end
        else (* setter applied to different setter *)
          match push_down_setter tR tE g u r with
          | Some r' => Some (t_tset tR' tE' (t_mk_gafu tR' tE' g' u') s r')
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
                       | _ => simp_app_nonstrict u old_field
                       end in
                     let new_args := Array.copy args in
                     Array.set new_args j new_field;
                     Some (Constr.Unsafe.make (Constr.Unsafe.App h new_args))
                  | None => Control.throw_invalid_argument "g is not a getter"
                  end
               else (* setter applied to non-setter-non-constructor *) None
           | _ => (* setter applied to non-setter-non-constructor *) None
           end
    end in
    log_ret "push_down_setter" [g; u; c] c'

  (* g: getter, i: its backwards-index, c: any constr
     If c is a series of setters setting g to some v, returns v.
     If c is a series of setters not setting g and ending in a constructor,
     returns the constructor argument corresponding to g.
     If (Some c') is returned, c' is convertible to c, but simpler.
     If None is returned, no simplification could be made, so the caller might
     be able to reuse an existing (g c) term rather than allocating a new one. *)
  with lookup_getter(g: constr)(i: int)(c: constr) :=
    log_call "lookup_getter" [g; c];
    let c' :=
    lazy_match! c with
    | tset (mk_gafu ?g' ?u') ?r =>
        (* getter applied to setter *)
        if Constr.equal g g' then
          (* getter applied to same setter *)
          lazy_match! u' with
          | const ?v' => Some v'
          | _ => Some (simp_app_nonstrict u' (lookup_getter_nonstrict g i r))
          end
        else (* getter applied to different setter *)
          Some (lookup_getter_nonstrict g i r)
    | _ => match Constr.Unsafe.kind c with
           | Constr.Unsafe.App h args =>
               if Constr.is_constructor h then (* getter applied to constructor *)
                 Some (Array.get args (Int.sub (Array.length args) i))
               else (* getter applied to non-setter-non-constructor *) None
           | _ => (* getter applied to non-setter-non-constructor *) None
           end
    end in
    log_ret "lookup_getter" [g; c] c'

  with lookup_getter_nonstrict(g: constr)(i: int)(r: constr) :=
    match lookup_getter g i r with
    | Some w => w
    | None => mkApp1 g r
    end

  with simp_app(f: constr)(a: constr) :=
    log_call "simp_app" [f; a];
    let c' := lazy_match! f with
    | @tset ?tR ?tE (mk_gafu ?g ?u) ?s => push_down_setter tR tE g u a
    | compose ?f1 ?f2 => Some (simp_app_nonstrict f1 (simp_app_nonstrict f2 a))
    | fun x => _ => match Constr.Unsafe.kind f with
                    | Constr.Unsafe.Lambda y body => Some (Constr.Unsafe.substnl [a] 0 body)
                    | _ => Control.throw Assertion_failure
                    end
    | _ => match getter_proj_index f with
           | Some i => lookup_getter f i a
           | None => None
           end
    end in
    log_ret "simp_app" [f; a] c'

  with simp_app_nonstrict(f: constr)(a: constr) :=
    match simp_app f a with
    | Some r => r
    | None => mkApp1 f a
    end.

  (* In-place-apply f to all elements of array a for which it returns Some,
     and return true iff at least one returned Some *)
  Ltac2 rec transform_array(f: 't -> 'u option)(i: int)(a: 't array) :=
    if Int.ge i (Array.length a) then false
    else match f (Array.get a i) with
         | Some v => Array.set a i v; transform_array f (Int.add i 1) a; true
         | None => transform_array f (Int.add i 1) a
         end.

  (* Returns (Some c') with c' convertible to c if simplifications were made,
     None otherwise. *)
  Ltac2 rec simp_term(c: constr) :=
    log_call "simp_term" [c];
    let c' :=
    match Constr.Unsafe.kind c with
    | Constr.Unsafe.App _ _ =>
        lazy_match! c with
        | ?f ?a =>
            match simp_term f with
            | Some f' =>
                let a' := simp_term_nonstrict a in
                Some (simp_app_nonstrict f' a')
            | None =>
                match simp_term a with
                | Some a' => Some (simp_app_nonstrict f a')
                | None =>
                    (* if nothing was simplifiable, we return None instead of
                       reconstructing an identical (mkApp f [| a |]) *)
                    simp_app f a
                end
            end
        end
    | Constr.Unsafe.Prod b body =>
        match simp_term (Constr.Binder.type b) with
        | Some t => let b' := Constr.Binder.make (Constr.Binder.name b) t in
                    let body' := simp_term_nonstrict body in
                    Some (Constr.Unsafe.make (Constr.Unsafe.Prod b' body'))
        | None => match simp_term body with
                  | Some body' => Some (Constr.Unsafe.make (Constr.Unsafe.Prod b body'))
                  | None => None
                  end
        end
    | Constr.Unsafe.Lambda x body =>
        match simp_term body with
        | Some body' => Some (Constr.Unsafe.make (Constr.Unsafe.Lambda x body'))
        | None => None
        end
    | Constr.Unsafe.LetIn x rhs body =>
        match simp_term rhs with
        | Some rhs' =>
            let body' := simp_term_nonstrict body in
            Some (Constr.Unsafe.make (Constr.Unsafe.LetIn x rhs' body'))
        | None =>
            match simp_term body with
            | Some body' => Some (Constr.Unsafe.make (Constr.Unsafe.LetIn x rhs body'))
            | None => None
            end
        end
    | Constr.Unsafe.Case c t ci d branches =>
        match simp_term d with
        | Some d' =>
            let branches' := Array.map simp_term_nonstrict branches in
            Some (Constr.Unsafe.make (Constr.Unsafe.Case c t ci d' branches'))
        | None =>
            let branches' := Array.copy branches in
            if transform_array simp_term 0 branches' then
              Some (Constr.Unsafe.make (Constr.Unsafe.Case c t ci d branches'))
            else None
        end
    | _ => None
    end in
    log_ret "simp_term" [c] c'

  (* Always returns a term convertible to the input term, even if no simplifications
     were made *)
  with simp_term_nonstrict(c: constr) :=
    match simp_term c with
    | Some c' => c'
    | None => c
    end.

  Ltac2 Type exn ::=
    [ Initial_term_ill_typed (constr)
    | Returned_term_ill_typed (constr)
    | Type_not_preserved (constr, constr, constr, constr) ].

  Ltac2 simp_term_check(c: constr) :=
    match simp_term c with
    | Some c' =>
        let ct := match Constr.Unsafe.check c with
                  | Val ct => ct
                  | _ => Control.throw (Initial_term_ill_typed c)
                  end in
        let t := orelse (fun () => Constr.type ct)
                        (fun _ => Control.throw (Initial_term_ill_typed ct)) in
        let ct' := match Constr.Unsafe.check c' with
                   | Val ct' => ct'
                   | _ => Control.throw (Returned_term_ill_typed c')
                   end in
        let t' := orelse (fun () => Constr.type ct')
                         (fun _ => Control.throw (Returned_term_ill_typed ct')) in
        if Constr.equal t t' then Some c'
        else Control.throw (Type_not_preserved c t ct' t')
    | None => None
    end.

  Ltac2 simp_hyps_bool_progress () :=
    List.fold_left (fun progr (x, obody, tp) =>
      match simp_term_check tp with
      | Some tp' => change $tp' in $x; true
      | None => progr
      end) (Control.hyps ()) false.

  Ltac2 simp_hyps () :=
    if simp_hyps_bool_progress () then ()
    else Control.backtrack_tactic_failure "no simplification opportunities".

  Ltac2 simp_goal_bool_progress () :=
    match simp_term_check (Control.goal ()) with
    | Some g => change $g; true
    | None => false
    end.

  Ltac2 simp_goal () :=
    if simp_goal_bool_progress () then ()
    else Control.backtrack_tactic_failure "no simplification opportunities".

  Ltac2 simp () :=
    let progr_h := simp_hyps_bool_progress () in
    let progr_g := simp_goal_bool_progress () in
    if progr_h || progr_g then ()
    else Control.backtrack_tactic_failure "no simplification opportunities".

  Ltac simp_hyps := ltac2:(Control.enter simp_hyps).
  Ltac simp_goal := ltac2:(Control.enter simp_goal).
  Ltac simp := ltac2:(Control.enter simp).
End record.

(* syntactic reflexivity *)
Ltac srefl :=
  lazymatch goal with
  | |- ?x = ?y => constr_eq x y; reflexivity
  end.

Module RecordSetterTests.

  Record foo(A: Type)(n: nat) := {
    fieldA: A;
    fieldB: n = n;
    fieldC: bool;
  }.

  Record bar := {
    fieldD: bool;
    fieldE: foo nat 2;
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

  Goal forall f: foo bool 1, fieldA { f with fieldC ::= andb true } = fieldA f.
  Proof. record.simp. intros. srefl. Qed.

  Goal forall b, {| fieldD := true; fieldE := testFoo b |}.(fieldE).(fieldC) = b.
  Proof. record.simp. unfold testFoo. record.simp. intros. srefl. Qed.

  Goal forall b, { testFoo b with fieldA ::= (Nat.add 12) }
                 = {| fieldA := 12 + 3; fieldB := eq_refl; fieldC := b |}.
  Proof. unfold testFoo. record.simp. intros. srefl. Qed.

  Goal compose (compose (Nat.add 1) (Nat.add 2)) (compose (Nat.add 3) (Nat.add 4)) 5 =
         1 + (2 + (3 + (4 + 5))).
  Proof. record.simp. srefl. Qed.

  Goal forall b: bool, { {| fieldD := b; fieldE := testFoo true |}
                         with fieldD ::= (fun old => andb old old) }
                       = {| fieldD := andb b b; fieldE := testFoo true |}.
  Proof. record.simp. intros. srefl. Qed.

  Goal forall b, { { testFoo b with fieldA := 3 } with fieldA ::= Nat.add 4 }
                 = { testFoo b with fieldA := 4 + 3 }.
  Proof. record.simp. intros. srefl. Qed.

  Goal forall b, fieldB { testFoo b with fieldA ::= (Nat.add 12) } = eq_refl.
  Proof. record.simp. unfold testFoo. record.simp. intros. srefl. Qed.

  Goal forall b, fieldB (testFoo b) = eq_refl.
  Proof. unfold testFoo. record.simp. intros. srefl. Qed.

  Goal forall b, fieldB (testFoo b) <> eq_refl -> False.
  Proof. unfold testFoo. intros. record.simp. apply H. srefl. Qed.

  Goal forall b, fieldB (testFoo b) <> eq_refl -> False.
  Proof. unfold testFoo. record.simp. intros. apply H. srefl. Qed.
End RecordSetterTests.
