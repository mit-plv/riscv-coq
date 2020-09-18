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

(* We also save the constant register 0 on the stack, so that we can conveniently index into an
   array of all registers *)
Definition all_reg_names: list Register := List.unfoldn (Z.add 1) 32 0.

Definition save_regs_insts(addr: Z) :=
  @List.map Register Instruction (fun r => Sw zero r (addr + 4 * r)) all_reg_names.
Definition restore_regs_insts(addr: Z) :=
  @List.map Register Instruction (fun r => Lw r zero (addr + 4 * r)) all_reg_names.

(* TODO write encoder (so far there's only a decoder called CSR.lookupCSR) *)
Definition MTVal: Z := 835.
Remark MTVal_correct: CSR.lookupCSR MTVal = CSR.MTVal. reflexivity. Qed.
Definition MEPC: Z := 833.
Remark MEPC_correct: CSR.lookupCSR MEPC = CSR.MEPC. reflexivity. Qed.

Definition handler_insts(handler_stack_start: Z) :=
  save_regs_insts handler_stack_start ++ [[
  Csrr t1 MTVal                    ; (* t1 := the invalid instruction i that caused the exception *)
  Srli t1 t1 5                     ; (* t1 := t1 >> 5                                             *)
  Andi s3 t1 (31*4)                ; (* s3 := i[7:12]<<2   // (rd of the MUL)*4                   *)
  Srli t1 t1 8                     ; (* t1 := t1 >> 8                                             *)
  Andi s1 t1 (31*4)                ; (* s1 := i[15:20]<<2  // (rs1 of the MUL)*4                  *)
  Srli t1 t1 5                     ; (* t1 := t1 >> 5                                             *)
  Andi s2 t1 (31*4)                ; (* s2 := i[20:25]<<2  // (rs2 of the MUL)*4                  *)
  Lw a1 s1 handler_stack_start     ; (* a1 := stack[s1]                                           *)
  Lw a2 s2 handler_stack_start       (* a2 := stack[s2]                                           *)
  ]] ++ softmul_insts ++ [[          (* a3 := softmul(a1, a2)                                     *)
  Sw s3 a3 handler_stack_start       (* stack[s3] := a3                                           *)
  ]] ++ restore_regs_insts handler_stack_start ++ [[
  Csrr t1 MEPC                     ;
  Addi t1 t1 4                     ;
  Csrw t1 MEPC                     ; (* MEPC := MEPC + 4                                          *)
  Mret
  ]].
