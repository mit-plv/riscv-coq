Require Import Coq.omega.Omega.

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
         | _: context[min ?a ?b] |- _ => unique pose proof (Min.min_spec a b)
         |  |- context[min ?a ?b]     => unique pose proof (Min.min_spec a b)
         | _: context[max ?a ?b] |- _ => unique pose proof (Max.max_spec a b)
         |  |- context[max ?a ?b]     => unique pose proof (Max.max_spec a b)
  end;
  omega.
