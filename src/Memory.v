Require Import bbv.Word.
Require Import riscv.Decidable.
Require Import Coq.Lists.List.

Section Memory.

  Variable w: nat. (* bit width of addresses and memory words *)

  Definition mem := word w -> option (word w).

  Definition read_mem(x: word w)(m: mem): option (word w) := m x.

  Definition write_mem(x: word w)(v: word w)(m: mem): option (mem) :=
    match m x with
    | Some old_value => Some (fun y => if dec (x = y) then Some v else m y)
    | None => None
    end.

  Definition no_mem: mem := fun x => None.

  Definition zeros_mem(upTo: word w): mem := fun x => if wlt_dec x upTo then Some $0 else None.

  Definition list_to_mem(l: list (word w)): mem := fun x => nth_error l (wordToNat x).

End Memory.

Arguments read_mem {_} _.
Arguments write_mem {_} _ _.
