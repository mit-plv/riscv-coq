Require Import Coq.PArith.BinPos.
Require Import Coq.Lists.List. Import ListNotations.

Module natmap. Section __.
  Context {V: Type}.

  (* TODO if there are trailing None's map extensionality doesn't hold, can we fix that? *)
  Definition natmap := list (option V).

  Definition head(m: natmap): option V :=
    match m with
    | nil => None
    | o :: _ => o
    end.

  Definition tail: natmap -> natmap := @List.tail (option V).

  Fixpoint skip(n: nat)(m: natmap): natmap :=
    match n with
    | O => m
    | S n' => tail (skip n' m)
    end.

  Definition get(m: natmap)(n: nat): option V := head (skip n m).

  (* m2 overrides m1. Simplifies best if m2 is concrete *)
  Fixpoint merge(m1 m2: natmap): natmap :=
    match m2 with
    | nil => m1
    | cons h t => cons (match h with
                        | Some v => Some v
                        | None => head m1
                        end)
                       (merge (tail m1) t)
    end.

  Fixpoint singleton(k: nat)(v: V): natmap :=
    match k with
    | O => Some v :: nil
    | S n => None :: singleton n v
    end.

  Definition put(m: natmap)(k: nat)(v: V): natmap := merge m (singleton k v).

  Definition putmany: natmap -> list (nat * V) -> natmap :=
    List.fold_right (fun '(k, v) res => put res k v).

End __. End natmap.
Arguments natmap.natmap: clear implicits.
Notation natmap := natmap.natmap.

Definition forcetype(o: option Type): Type :=
  match o with
  | Some T => T
  | None => unit
  end.

Inductive hnatmap: natmap Type -> Type :=
| HNil: hnatmap nil
| HCons{OV: option Type}{T: natmap Type}(v: forcetype OV)(t: hnatmap T): hnatmap (cons OV T).

Module hnatmap.

  Definition head{T: natmap Type}(m: hnatmap T): forcetype (natmap.head T) :=
    match m with
    | HNil => tt
    | HCons v _ => v
    end.

  Definition tail{T: natmap Type}(m: hnatmap T): hnatmap (tail T) :=
    match m with
    | HNil => HNil
    | HCons _ t => t
    end.

  Fixpoint skip(n: nat){T: natmap Type}(m: hnatmap T): hnatmap (natmap.skip n T) :=
    match n with
    | 0 => m
    | S n' => tail (skip n' m)
    end.

  Definition get{T: natmap Type}(m: hnatmap T)(n: nat): forcetype (natmap.get T n) := head (skip n m).

  (* m2 overrides m1 *)
  Fixpoint merge{T1 T2: natmap Type}(m1: hnatmap T1)(m2: hnatmap T2): hnatmap (natmap.merge T1 T2).
    refine (match m2 with
            | HNil => m1
            | @HCons OV T2Tail v t => @HCons (match OV with
                                              | Some V => Some V
                                              | None => natmap.head T1
                                              end)
                                             (natmap.merge (natmap.tail T1) T2Tail)
                                             _
                                             (merge _ _ (tail m1) t)
            end).
    destruct OV as [V|].
    - exact v.
    - exact (head m1).
  Defined.

  Fixpoint singleton{V: Type}(k: nat)(v: V){struct k}: hnatmap (natmap.singleton k V) :=
    match k with
    | 0 => @HCons (Some V) [] v HNil
    | S n => @HCons None (natmap.singleton n V) tt (singleton n v)
    end.

  Definition put{T: natmap Type}(m: hnatmap T)(k: nat){V: Type}(v: V): hnatmap (natmap.put T k V) :=
    merge m (singleton k v).

End hnatmap.

Module HnatmapNotations.
  Declare Scope hnatmap_scope.
  Notation "m [ k := v ]" := (hnatmap.put m k v)
    (at level 8, left associativity, format "m [ k  :=  v ]") : hnatmap_scope.
  Notation "m [ k ]" := (hnatmap.get m k)
    (at level 8, left associativity, format "m [ k ]") : hnatmap_scope.
  (* this notation overrides the notation for applying a function m to the singleton list containing k,
     but that's so rare that it's fine *)
End HnatmapNotations.
