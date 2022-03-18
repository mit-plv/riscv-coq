(* In the real library, `setter` is an implicit argument marked as a typeclass
   and inferred with a `Hint Extern`, but here, for simplicity, we write it out
   manually *)
Definition set{R E: Type}(getter: R -> E)(setter: (E -> E) -> R -> R) := setter.

Record X := mkX { fldA: nat; fldB : nat }.

(* inlined (anonymous) getters *)
Notation FldA x := (let (p, _) := x in p) (only parsing).
Notation FldB x := (let (_, p) := x in p) (only parsing).
(*
(* existing getters *)
Notation FldA := fldA (only parsing).
Notation FldB := fldB (only parsing).
*)

(* These two would be inferred by typeclasses + Ltac *)
Notation setterA := (fun (f: nat -> nat) (r: X) => mkX (f (FldA r)) (FldB r)) (only parsing).
Notation setterB := (fun (f: nat -> nat) (r: X) => mkX (FldA r) (f (FldB r))) (only parsing).

Fixpoint dblN(n: nat)(x: nat): nat :=
  match n with
  | O => x
  | S m => dblN m x + dblN m x
  end.

Notation updFldA := (set fldA setterA) (only parsing).
Notation updFldB := (set fldB setterB) (only parsing).

Lemma test(p: X)(s: nat):
  updFldA (dblN 11) (updFldB (fun _ => 1) (updFldA (fun _ => dblN 10 s) p)) =
  updFldB (fun _ => 1) (updFldA (fun _ => dblN 11 (dblN 10 s)) p).
Proof.
  reflexivity. (* much slower if we use existing getters instead of anonymous getters *)
Qed.
