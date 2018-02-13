Require Import Coq.ZArith.BinInt.
Require Import bbv.Word.
Require Import riscv.RiscvBitWidths.
Require Import riscv.NameWithEq.
Require Import riscv.Decode.

Section Riscv.

  Context {B: RiscvBitWidths}.

  Context {Name: NameWithEq}. (* register name *)
  Notation Reg := (@name Name).
  Existing Instance eq_name_dec.

  Class RiscvState(M: Type -> Type) := mkRiscvState {
    getRegister: Register -> M (word wXLEN);
    setRegister: Register -> (word wXLEN) -> M unit;

    loadWord: (word wXLEN) -> M (word wXLEN);
    storeWord: (word wXLEN) -> (word wXLEN) -> M unit;

    getPC: M Z;
    setPC: Z -> M unit;
  }.

End Riscv.
