Require Import Coq.Lists.List. Import ListNotations.
Require Import Coq.ZArith.ZArith. Open Scope Z_scope.
Require Import coqutil.Datatypes.List.
Require Import riscv.Utility.InstructionCoercions. Open Scope ilist_scope.
Require Import riscv.Spec.CSR.
Require Import riscv.Spec.Decode.
Require Import riscv.Spec.PseudoInstructions.
Require Import riscv.Utility.RegisterNames.


(* a3 := a1 * a2
   without using mul, but with a naive loop:
   a3 := 0;
   while (0 != a1) {
     a3 := a3 + a2;
     a1 := a1 - 1;
   } *)
Definition softmul_insts := [[
  Addi a3 zero 0;
  Beq zero a1 16;
  Add a3 a3 a2;
  Addi a1 a1 (-1);
  J (-12)
]].

Definition save_regs3to31 :=
  @List.map Register Instruction (fun r => Sw sp r (4 * r)) (List.unfoldn (Z.add 1) 29 3).
Definition restore_regs3to31 :=
  @List.map Register Instruction (fun r => Lw r sp (4 * r)) (List.unfoldn (Z.add 1) 29 3).

(* TODO write encoder (so far there's only a decoder called CSR.lookupCSR) *)
Definition MTVal    := 835.  Remark MTVal_correct   : CSR.lookupCSR MTVal    = CSR.MTVal.    reflexivity. Qed.
Definition MEPC     := 833.  Remark MEPC_correct    : CSR.lookupCSR MEPC     = CSR.MEPC.     reflexivity. Qed.
Definition MScratch := 832.  Remark MScratch_correct: CSR.lookupCSR MScratch = CSR.MScratch. reflexivity. Qed.

Definition handler_insts := [[
  Csrrw sp sp MScratch;
  Sw sp zero 0;
  Sw sp ra 4;
  Csrr ra MScratch;
  Sw sp ra 8
  ]] ++ save_regs3to31 ++ [[
  Csrr t1 MTVal                    ; (* t1 := the invalid instruction i that caused the exception *)
  Srli t1 t1 5                     ; (* t1 := t1 >> 5                                             *)
  Andi s3 t1 (31*4)                ; (* s3 := i[7:12]<<2   // (rd of the MUL)*4                   *)
  Srli t1 t1 8                     ; (* t1 := t1 >> 8                                             *)
  Andi s1 t1 (31*4)                ; (* s1 := i[15:20]<<2  // (rs1 of the MUL)*4                  *)
  Srli t1 t1 5                     ; (* t1 := t1 >> 5                                             *)
  Andi s2 t1 (31*4)                ; (* s2 := i[20:25]<<2  // (rs2 of the MUL)*4                  *)
  Add s1 s1 sp                     ; (* s1 := s1 + stack_start                                    *)
  Add s2 s2 sp                     ; (* s2 := s2 + stack_start                                    *)
  Add s3 s3 sp                     ; (* s3 := s3 + stack_start                                    *)
  Lw a1 s1 0                       ; (* a1 := stack[s1]                                           *)
  Lw a2 s2 0                         (* a2 := stack[s2]                                           *)
  ]] ++ softmul_insts ++ [[          (* a3 := softmul(a1, a2)                                     *)
  Sw s3 a3 0                       ; (* stack[s3] := a3                                           *)
  Csrr t1 MEPC                     ;
  Addi t1 t1 4                     ;
  Csrw t1 MEPC                       (* MEPC := MEPC + 4                                          *)
  ]] ++ restore_regs3to31 ++ [[
  Lw ra sp 4;
  Csrr sp MScratch;
  Mret
  ]].
