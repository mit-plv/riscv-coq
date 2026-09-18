(* Test program for the trap-entry mstatus update and the misaligned-store
   exception code (mit-plv/riscv-coq#61).

   Program 1 enables mstatus.MIE, takes a trap (ecall) into a handler that
   returns with mret, and then reads mstatus back.  The privileged spec says a
   trap sets MPIE := MIE and MIE := 0, and mret sets MIE := MPIE, so MIE must
   be set again after mret.

   Program 2 stores to a misaligned address on a machine whose translate does
   alignment checks; the exception code must be 6 (store/AMO address
   misaligned), not 4 (load address misaligned). *)

Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.ZArith.BinInt. Local Open Scope Z_scope.
Require Import coqutil.Map.Interface.
Require Import coqutil.Map.Memory.
Require Import coqutil.Word.LittleEndianList.
Require Import coqutil.Map.Z_keyed_SortedListMap.
Require Import riscv.Utility.Utility.
Require Import riscv.Utility.Monads. Import StateAbortFailOperations.
Require Import riscv.Utility.MkMachineWidth.
Require Import riscv.Utility.Words32Naive.
Require Import riscv.Utility.DefaultMemImpl32.
Require Import riscv.Utility.Encode.
Require Import riscv.Utility.ExtensibleRecords.
Require Import riscv.Spec.Decode.
Require Import riscv.Spec.Machine.
Require Import riscv.Spec.CSRField.
Require Import riscv.Spec.CSRFile.
Require Import riscv.Platform.MinimalCSRsDet.
Require Import riscv.Platform.Run.

Import HnatmapNotations. Local Open Scope hnatmap_scope.

(* MinimalCSRsDet with no extra fields, RV32, sorted-list maps *)
Local Notation State := (@MinimalCSRsDet.State 32 _ Mem (Zkeyed_map (bits 32)) nil).

#[local] Instance WithLeakage:
  RiscvProgramWithLeakage (StateAbortFail State) (bits 32) := {|
  RVP := IsRiscvMachine nil;
  leakEvent _ := Return tt;
|}.

(* every CSR field present and zero, so that reads never fail *)
Definition all_fields: list CSRField := [
  MXL; Extensions; SXL; UXL; TSR; TW; TVM; MXR; SUM; MPRV; XS; FS; MPP; SPP; MPIE;
  SPIE; UPIE; MIE; SIE; UIE; SD; MTVecBase; MTVecMode; MEDeleg; MIDeleg; MEIP; SEIP;
  UEIP; MTIP; STIP; UTIP; MSIP; SSIP; USIP; MEIE; SEIE; UEIE; MTIE; STIE; UTIE; MSIE;
  SSIE; USIE; MCycle; MInstRet; MHPM; MIR; MTM; MCY; MScratch; MEPC; MCauseInterrupt;
  MCauseCode; MTVal; STVecBase; STVecMode; SHPM; SIR; STM; SCY; SScratch; SEPC;
  SCauseInterrupt; SCauseCode; STVal; MODE; ASID; PPN; FFlags; FRM ].

Definition zeroCSRs: CSRFile := map.of_list (List.map (fun f => (f, 0)) all_fields).

Definition initialState(prog: list Instruction): State :=
  HNil[csrs := zeroCSRs]
      [log := (nil : list RiscvMachine.LogItem)]
      [mem := unchecked_store_bytes (map.empty : Mem) (ZToReg 0)
                (List.flat_map (le_split 4) (List.map encode prog))]
      [nextPc := ZToReg 4]
      [pc := ZToReg 0]
      [regs := (map.empty : Zkeyed_map (bits 32))].

(* run n instructions; an exception (abort) is a completed instruction, a
   failure stops the run *)
Fixpoint run{RVS: RiscvMachine (StateAbortFail State) (bits 32)}
  (fuel: nat)(s: State): State :=
  match fuel with
  | O => s
  | S fuel' => match run1 (RVS := RVS) RV32IM s with
               | (None, s') => s'
               | (Some _, s') => run fuel' s'
               end
  end.

Definition mstatus := 0x300.
Definition mtvec := 0x305.
Definition mepc := 0x341.
Definition t0 := 5. Definition t1 := 6. Definition t2 := 7.

(* Program 1: the handler starts at byte 24 (mtvec = 24, direct mode). *)
Definition trap_prog: list Instruction := [
  (*  0 *) IInstruction (Addi t0 0 24);         (* t0 := handler address *)
  (*  4 *) CSRInstruction (Csrrw 0 t0 mtvec);   (* mtvec := t0 *)
  (*  8 *) CSRInstruction (Csrrsi 0 8 mstatus); (* mstatus.MIE := 1 *)
  (* 12 *) CSRInstruction Ecall;                (* trap to the handler *)
  (* 16 *) CSRInstruction (Csrrs t1 0 mstatus); (* t1 := mstatus, after return from the trap *)
  (* 20 *) IInstruction (Jal 0 0);              (* loop forever *)
  (* 24 *) CSRInstruction (Csrrs t2 0 mepc);    (* handler: mepc := mepc + 4 *)
  (* 28 *) IInstruction (Addi t2 t2 4);
  (* 32 *) CSRInstruction (Csrrw 0 t2 mepc);
  (* 36 *) CSRInstruction Mret
].

(* 9 instructions: the 5 before the loop plus the 4 of the handler *)
Definition trap_final: State := run 9 (initialState trap_prog).

(* MIE is set again after mret ... *)
Lemma mstatus_MIE_restored_after_mret:
  map.get trap_final[csrs] MIE = Some 1.
Proof. vm_compute. reflexivity. Qed.

(* ... and the program sees it in the mstatus value it read back (bit 3) *)
Lemma program_reads_MIE_set:
  match map.get trap_final[regs] t1 with
  | Some v => Z.testbit (Zmod.unsigned v) 3
  | None => false
  end = true.
Proof. vm_compute. reflexivity. Qed.

(* the trap was really taken: the cause is 11 (environment call from M-mode) *)
Lemma trap_was_taken:
  map.get trap_final[csrs] MCauseCode = Some 11.
Proof. vm_compute. reflexivity. Qed.

(* Program 2: a store to a misaligned address, with alignment checking *)
#[local] Instance AlignmentCheckingRiscvState:
  RiscvMachine (StateAbortFail State) (bits 32) := {|
  translate := translate_with_alignment_check;
  flushTLB := Return tt;
  getCSR_InstRet := raiseException (ZToReg 0) (ZToReg 2);
  getCSR_Time    := raiseException (ZToReg 0) (ZToReg 2);
  getCSR_Cycle   := raiseException (ZToReg 0) (ZToReg 2);
|}.

Definition misaligned_store_prog: list Instruction := [
  (*  0 *) IInstruction (Addi t0 0 2);          (* t0 := 2, not 4-byte aligned *)
  (*  4 *) IInstruction (Sw t0 0 0)             (* mem[t0] := 0 *)
].

Definition misaligned_store_final: State :=
  run (RVS := AlignmentCheckingRiscvState) 2 (initialState misaligned_store_prog).

(* exception code 6 is "store/AMO address misaligned" *)
Lemma misaligned_store_cause_is_6:
  map.get misaligned_store_final[csrs] MCauseCode = Some 6.
Proof. vm_compute. reflexivity. Qed.
