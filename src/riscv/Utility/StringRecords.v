Require Import Coq.Strings.String. Open Scope string_scope.
Require Import Coq.Lists.List. Import ListNotations.

Local Set Universe Polymorphism.

Module record.
  Inductive record: list (string * Type) -> Type :=
  | Nil: record nil
  | Cons{V: Type}{T: list (string * Type)}(n: string)(v: V)(tail: record T): record ((n, V) :: T).

  Fixpoint get_type(T: list (string * Type))(n: string): Type :=
    match T with
    | nil => unit
    | (s, U) :: tail => if String.eqb n s then U else get_type tail n
    end.

  Fixpoint get{T: list (string * Type)}(r: record T)(n: string): get_type T n :=
    match r in (record l) return (get_type l n) with
    | Nil => tt
    | @Cons V U s v tail =>
      match String.eqb n s as b return (if b then V else get_type U n) with
      | true => v
      | false => get tail n
      end
    end.

  Definition destruct_types_rec(T: list (string * Type)): list (string * Type) -> list (string * Type) :=
    fix rec Suffix :=
      match Suffix with
      | nil => nil
      | (x, A) :: U => (x, get_type T x) :: rec U
      end.

  Definition destruct_types(T: list (string * Type)): list (string * Type) := destruct_types_rec T T.

  Goal False.
    let r := eval compute in (destruct_types [("a", nat: Type); ("b", string: Type); ("a", string: Type)])
      in pose r as x.
  Abort.

  Definition cast_get_type{n1 n2: string}(pf: (n1 =? n2) = true):
    forall (T: list (string * Type)), get_type T n1 -> get_type T n2.
    refine (fix rec T v := _).
    destruct T as [|[s A] U].
    - exact tt.
    - simpl in *.
      destruct (String.eqb n1 s) eqn: E1;
        destruct (String.eqb n2 s) eqn: E2.
      + exact v.
      + abstract (apply String.eqb_neq in E2; apply String.eqb_eq in E1; apply String.eqb_eq in pf; congruence).
      + abstract (apply String.eqb_neq in E1; apply String.eqb_eq in E2; apply String.eqb_eq in pf; congruence).
      + eapply rec. exact v.
  Defined.

  Definition set_rec{T: list (string * Type)}(r: record T)(n: string)(v: get_type T n):
    forall Suffix: list (string * Type), record (destruct_types_rec T Suffix).
    refine (fix rec Suffix {struct Suffix} := _).
    destruct Suffix as [|[x A] U].
    - exact Nil.
    - simpl.
      refine (Cons x _ (rec _)).
      destruct (String.eqb n x) eqn: E.
      + apply (cast_get_type E T v).
      + apply (get r x).
  Defined.

  Definition set{T: list (string * Type)}(r: record T)(n: string)(v: get_type T n): record (destruct_types T) :=
    set_rec r n v T.

  Ltac simp :=
    cbn [get_type get destruct_types_rec destruct_types cast_get_type set_rec set
         String.eqb Ascii.eqb Bool.eqb] in *.
End record.

Module RecordNotations.
  Import record.

  Declare Custom Entry type_entry.
  Notation "s : T" := (@pair string Type s T%type)
   (in custom type_entry at level 5, s constr at level 0, T constr at level 100, format "s :  T").
  Notation "[# x ]" := (record (@cons (string * Type) x)) (x custom type_entry at level 5): type_scope.
  Notation "[# x ; y ; .. ; z ]" :=
    (record (@cons (string * Type) x
            (@cons (string * Type) y
            ..
            (@cons (string * Type) z nil) ..)))
      (x custom type_entry at level 5, y custom type_entry at level 5, z custom type_entry at level 5,
       format "[#  x ;  y ;  .. ;  z  ]")
    : type_scope.

  Declare Custom Entry record_value.
  Notation "s := v" := (Cons s v Nil)
    (in custom record_value at level 5, s constr at level 0, v constr at level 100).
  Notation "s := v ; tail" := (Cons s v tail)
    (in custom record_value at level 5, s constr at level 0, v constr at level 100,
     tail custom record_value at level 5).
  Notation "{# x }" := x (x custom record_value at level 5, format "{#  x  }").

  Declare Scope record_scope.
  Notation "m # f" := (get m f) (left associativity, at level 8, format "m # f") : record_scope.
  Notation "m (# f := v )" := (set m f v) (left associativity, at level 8, format "m (# f  :=  v )")
    : record_scope.
  Open Scope record_scope.
End RecordNotations.

Import RecordNotations.

(* Note: Once https://github.com/coq/coq/issues/9518 is implemented,
   we can drop the quotes around the field names *)

Goal forall s: [# "a": nat * nat; "b": string; "c": list nat; "d": [# "fst": nat; "snd": nat ]], False.
  intros.
  pose s#"d"#"fst" as x.
  pose (s(#"b" := "hi")(#"a" := (1, 2))(#"c" := 1 :: s#"c")(#"b" := "new hi")) as y.
  record.simp.
  pose {# "a" := 1 ; "b" := {# "l" := true; "r" := false } } as z.
Abort.
