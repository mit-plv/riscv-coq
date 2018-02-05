Require Import Coq.omega.Omega.
Require Import riscv.RiscvBitWidths.

(* TODO Doesn't work at the moment because of "wXLEN_wInstr: wXLEN = wInstr"
Instance RiscvBitWidths64: RiscvBitWidths := {|
  wXLEN := 64;
  log2wXLEN := 6;
  wInstr := 32;
  wimm := 12;
  wupper := 20;
|}.
  all: try reflexivity.
  all: abstract omega.
Defined.
*)
