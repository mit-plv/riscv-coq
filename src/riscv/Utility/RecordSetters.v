Ltac eta X :=
  let s := constr:(ltac:(
        let x := fresh "x" in
        intro x; unshelve eexists;
        [ econstructor; destruct x | destruct x; reflexivity ])
    : forall x : X, { x' : X | x' = x }) in
  lazymatch s with
  (* `eval cbv beta` would get rid of superfluous eta expansions in each branch that
     were created by `destruct`, but we commment it out because `cbv beta` is called
     again in `setter` *)
  | fun x => exist _ (@?w x) _ => (* eval cbv beta in *) w
  end.

Ltac head t :=
  lazymatch t with
  | ?f _ => head f
  | _ => t
  end.

Ltac setter R E getter :=
  let h := head getter in
  let etaR := eta R in
  exact (fun (updateE: E -> E) (r: R) => ltac:(
    let b := eval cbv beta in (etaR r) in
    let g := eval cbv beta delta [h] in (getter r) in
    match b with
    (* Note: `context C[g]` without the constr_eq would work too, but g is printed
       as a destructuring let, whereas f and the anonymous getters in etaR are
       printed as matches, and we prefer to uniformly have matches everywhere *)
    | context C[?f] => constr_eq f g; let b' := context C[updateE f] in exact b'
    end
  )).

Definition Setter{R E: Type}(getter: R -> E): Type := (E -> E) -> R -> R.
Existing Class Setter.

Inductive update(R E: Type): Type :=
| mk_update(getter: R -> E)(setter: Setter getter)(transf: E -> E).

Definition apply_update{R E: Type}(u: update R E): R -> R :=
  match u with
  | mk_update _ _ getter setter transf => setter transf
  end.

Arguments mk_update {R E} getter {setter} transf.

Global Hint Extern 1 (@Setter ?R ?E ?getter) => setter R E getter : typeclass_instances.

(* Note: To update a field with a constant value (rather than by applying an
   transformer function to its old value), we could just use the constant function
   `fun _ => newValue`, but then `newValue` would appear under a binder, which
   causes some rewriting/simplification tactics which don't recurse under binders
   to miss opportunities for rewriting/simplification, so we use this explicit
   definition of `constant` instead.
   Note: There's already Coq.Program.Basics.const, but it's return type can differ
   from its argument type, which we don't want/need here. *)
Definition constant{E: Type}(newValue: E): E -> E := fun _ => newValue.

Module Export OCamlLikeNotations.
  Declare Scope ocaml_like_record_set.
  Open Scope ocaml_like_record_set.

  Declare Custom Entry field_update.
  Notation "proj := v" := (mk_update proj (constant v))
    (in custom field_update at level 1, proj constr at level 99, v constr at level 99,
     format "'[  ' proj  :=  '/' v ']'")
    : ocaml_like_record_set.
  Notation "proj ::= f" := (mk_update proj f)
    (in custom field_update at level 1, proj constr at level 99, f constr at level 99,
     format "'[  ' proj  ::=  '/' f ']'")
    : ocaml_like_record_set.

  Notation "{ x 'with' u }" := (apply_update u x)
     (at level 0, x at level 99, u custom field_update at level 1,
      format "{  '[hv  ' x  'with'  '/' u ']'  }") : ocaml_like_record_set.
  Notation "{ x 'with' u ; .. ; v ; w }" :=
     (apply_update w (apply_update v .. (apply_update u x) .. ))
     (at level 0, x at level 99, u custom field_update at level 1,
      v custom field_update at level 1, w custom field_update at level 1,
      format "{  '[hv  ' x  'with'  '/' u ;  '/' .. ;  '/' v ;  '/' w  ']' }")
      : ocaml_like_record_set.
End OCamlLikeNotations.

Require Coq.Program.Basics.
Notation compose := Coq.Program.Basics.compose. (* selective import *)

Module AdditionalNotations.
  Declare Scope record_set.
  Open Scope record_set.

  (* Note: coq-record-update uses level 12, but I prefer level 8:
      https://github.com/tchajed/coq-record-update/issues/14 *)
  Notation "x <| u |>" := (apply_update u x)
     (at level 8, u custom field_update at level 1, left associativity, format "x <| u |>")
     : record_set.

  Notation "'{!' u }" := (apply_update u)
     (at level 0, u custom field_update at level 1,
      format "'{!'  u  }")
    : record_set.

  Notation "'{!' u ; v ; .. ; w }" :=
     (compose (apply_update w) .. (compose (apply_update v) (apply_update u)) ..)
     (at level 0, u custom field_update at level 1, v custom field_update at level 1,
      w custom field_update at level 1,
      format "'{!'  '[' u ;  '/' v ;  '/' .. ;  '/' w  ']' }")
    : record_set.
End AdditionalNotations.

Require Import Ltac2.Ltac2.
Require Ltac2.Option.
Require Import Ltac2.Bool.
Require coqutil.Ltac2Lib.Constr.

Set Default Proof Mode "Classic".

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
    Constr.Unsafe.make (Constr.Unsafe.App (Env.instantiate reference:(Basics.compose)) args).

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

  Ltac2 t_apply_update(tR: constr)(tE: constr)(u: constr)(r: constr) :=
    let args := Array.make 4 tR in
    Array.set args 1 tE;
    Array.set args 2 u;
    Array.set args 3 r;
    Constr.Unsafe.make (Constr.Unsafe.App (Env.instantiate reference:(apply_update)) args).

  Ltac2 t_mk_update(tR: constr)(tE: constr)(g: constr)(s: constr)(t: constr) :=
    let args := Array.make 5 tR in
    Array.set args 1 tE;
    Array.set args 2 g;
    Array.set args 3 s;
    Array.set args 4 t;
    Constr.Unsafe.make (Constr.Unsafe.App (Env.instantiate reference:(mk_update)) args).

  Ltac2 t_const(tE: constr)(v: constr) :=
    let args := Array.make 2 tE in
    Array.set args 1 v;
    Constr.Unsafe.make (Constr.Unsafe.App (Env.instantiate reference:(constant)) args).

  (* upd: field update of type `update tR tE`, of form `@mk_update tR tE g s u`
     c: any constr
     If c is a series of setters setting g to some u_old, replaces u_old by u.
     If c is a series of setters not setting g and ending in a constructor,
     replaces the constructor argument corresponding to g by u.
     If (Some c') is returned, c' is convertible to c, but simpler.
     If None is returned, no simplification could be made, so the caller might
     be able to reuse an existing (tset (mk_gafu g u) c) term rather than
     allocating a new one. *)
  Ltac2 rec push_down_setter(upd: constr)(c: constr) :=
    log_call "push_down_setter" [upd; c];
    let c' :=
    lazy_match! upd with @mk_update ?tR ?tE ?g ?s ?u =>
    lazy_match! c with
    | @apply_update ?tR' ?tE' ?upd' ?r => lazy_match! upd' with @mk_update _ _ ?g' ?s' ?u' =>
        (* setter applied to setter *)
        if Constr.equal g g' then
          (* setter applied to same setter *)
          lazy_match! u with
          | constant _ => Some (t_apply_update tR tE upd r)
          | _ => let u_combined :=
                   lazy_match! u' with
                   | constant ?v' => t_const tE (simp_app_nonstrict u v')
                   | _ => right_leaning_compose tE tE tE u u'
                   end in
                 Some (t_apply_update tR tE (t_mk_update tR tE g s u_combined) r)
          end
        else (* setter applied to different setter *)
          match push_down_setter upd r with
          | Some r' => Some (t_apply_update tR' tE' upd' r')
          | None => None
          end
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
                       | constant ?v => v
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
    end end in
    log_ret "push_down_setter" [upd; c] c'

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
    | apply_update (mk_update ?g' ?u') ?r =>
        (* getter applied to setter *)
        if Constr.equal g g' then
          (* getter applied to same setter *)
          lazy_match! u' with
          | constant ?v' => Some v'
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
    | None => Constr.mkApp1 g r
    end

  with simp_app(f: constr)(a: constr) :=
    log_call "simp_app" [f; a];
    let c' := lazy_match! f with
    | @apply_update ?tR ?tE ?upd => push_down_setter upd a
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
    | None => Constr.mkApp1 f a
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
  Import AdditionalNotations.

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

  (*
  Check _<|S := 3|>.
  Fail Check (testFoo true)<|S := 3|>.
  Fail Goal forall (g: foo nat 2 -> nat), (testFoo true)<|g := 3|> = testFoo true.
  *)

  Goal forall b,
      { testFoo b with fieldC := true; fieldC := false; fieldA ::= Nat.add 2 } =
      { testFoo b with fieldA ::= Nat.add 1; fieldC := false; fieldA ::= Nat.add 1 }.
  Proof.
    intros. unfold apply_update. unfold constant. cbn. srefl.
  Qed.

  Check (fun b => {! fieldC := false } (testFoo b)).
  Check (fun b => {! fieldC := false; fieldC := true } (testFoo b)).
  Check (fun b => {! fieldC := false; fieldC := true; fieldA ::= Nat.add 2 } (testFoo b)).

  Goal forall b,
      {! fieldC := false; fieldC := true; fieldA ::= Nat.add 2 } (testFoo b) =
      {! fieldA ::= Nat.add 1; fieldC := true; fieldA ::= Nat.add 1 } (testFoo b).
  Proof.
    intros. unfold apply_update. unfold constant, compose. cbn. srefl.
  Qed.

  Goal forall r: foo (foo nat 4) 2,
  { r with fieldA ::= {! fieldA ::= Nat.add 1 } }.(fieldA).(fieldA) = S r.(fieldA).(fieldA).
  Proof. intros. reflexivity. Qed.

  Goal forall r: foo (foo nat 4) 2,
      { r with fieldA := { r.(fieldA) with fieldA ::= Nat.add 1 } }.(fieldA).(fieldA) =
        S r.(fieldA).(fieldA).
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
