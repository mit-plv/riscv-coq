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
    loadInst: (word wXLEN) -> M Instruction; (* decode already included *)
    (* not yet:
    loadWord: (word wXLEN) -> M (word wXLEN);
    storeWord: (word wXLEN) -> (word wXLEN) -> M unit;
    *)
    getPC: M (word wXLEN);
    setPC: word wXLEN -> M unit;
  }.

End Riscv.
