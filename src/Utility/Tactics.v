Require Import Coq.ZArith.ZArith.

(* Like "pose proof" but only if we don't yet have this hypothesis *)
Tactic Notation "unique" "pose" "proof" constr(defn) :=
  let T := type of defn in
  match goal with
  | [ H : T |- _ ] => fail 1
  | _ => pose proof defn
  end.

Tactic Notation "so" tactic(f) :=
  match goal with
  | _: ?A |- _  => f A
  |       |- ?A => f A
  end.

Tactic Notation "forget" constr(X) "as" ident(y) := set (y:=X) in *; clearbody y.
