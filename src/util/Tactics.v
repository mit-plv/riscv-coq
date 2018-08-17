Require Import Coq.ZArith.ZArith.

(* Like "pose proof" but only if we don't yet have this hypothesis *)
Tactic Notation "unique" "pose" "proof" constr(defn) :=
  let T := type of defn in
  match goal with
  | [ H : T |- _ ] => fail 1
  | _ => pose proof defn
  end.

(* Like "omega" but also knows about min and max *)
Ltac momega :=
  repeat match goal with
         | _: context[  min ?a ?b] |- _ => unique pose proof (Min.min_spec a b)
         |  |- context[  min ?a ?b]     => unique pose proof (Min.min_spec a b)
         | _: context[  max ?a ?b] |- _ => unique pose proof (Max.max_spec a b)
         |  |- context[  max ?a ?b]     => unique pose proof (Max.max_spec a b)
         | _: context[Z.min ?a ?b] |- _ => unique pose proof (  Z.min_spec a b)
         |  |- context[Z.min ?a ?b]     => unique pose proof (  Z.min_spec a b)
         | _: context[Z.max ?a ?b] |- _ => unique pose proof (  Z.max_spec a b)
         |  |- context[Z.max ?a ?b]     => unique pose proof (  Z.max_spec a b)
  end;
  omega.

Tactic Notation "so" tactic(f) :=
  match goal with
  | _: ?A |- _  => f A
  |       |- ?A => f A
  end.

Tactic Notation "forget" constr(X) "as" ident(y) := set (y:=X) in *; clearbody y.
