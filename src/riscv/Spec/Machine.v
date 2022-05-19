Require Import Coq.ZArith.ZArith.
Require Import riscv.Utility.Monads.
Require riscv.Utility.MonadNotations.
Require Import riscv.Utility.Utility.
Require Import riscv.Spec.Decode.
Require Import riscv.Spec.CSRField.
Local Open Scope Z_scope.

(* Note that this is ordered: User < Supervisor < Machine *)
Inductive PrivMode: Type := User | Supervisor | Machine.

Definition decodePrivMode(m: MachineInt): PrivMode :=
  match m with
  | 0 => User
  | 1 => Supervisor
  | 3 => Machine
  | _ => User (* error "Invalid privilege mode" *)
  end.

Definition encodePrivMode(m: PrivMode): MachineInt :=
  match m with
  | User => 0
  | Supervisor => 1
  | Machine => 3
  end.

Definition PrivMode_eqb(m1 m2: PrivMode): bool := Z.eqb (encodePrivMode m1) (encodePrivMode m2).

Definition PrivMode_ltb(m1 m2: PrivMode): bool := Z.ltb (encodePrivMode m1) (encodePrivMode m2).

Inductive AccessType: Type := Instr | Load | Store.
Inductive SourceType: Type := VirtualMemory | Fetch | Execute.

Class RiscvProgram{M}{t}`{Monad M}`{MachineWidth t} := mkRiscvProgram {
  getRegister: Register -> M t;
  setRegister: Register -> t -> M unit;

  loadByte   : SourceType -> t -> M w8;
  loadHalf   : SourceType -> t -> M w16;
  loadWord   : SourceType -> t -> M w32;
  loadDouble : SourceType -> t -> M w64;

  storeByte   : SourceType -> t -> w8 -> M unit;
  storeHalf   : SourceType -> t -> w16 -> M unit;
  storeWord   : SourceType -> t -> w32 -> M unit;
  storeDouble : SourceType -> t -> w64 -> M unit;

  makeReservation  : t -> M unit;
  clearReservation : t -> M unit;
  checkReservation : t -> M bool;

  getCSRField : CSRField -> M MachineInt;
  setCSRField : CSRField -> MachineInt -> M unit;

  getPC: M t;
  setPC: t -> M unit;
  getPrivMode: M PrivMode;
  setPrivMode: PrivMode -> M unit;
  fence: MachineInt -> MachineInt -> M unit;

  (* Both of these update the PC at the end of a cycle.
     Every instance must support endCycleNormal.
     All operations following endCycleEarly are skipped.
     Some instances may not support endCycleEarly and fail instead. *)
  endCycleNormal: M unit;
  endCycleEarly: forall A, M A;
}.


Class RiscvMachine`{MP: RiscvProgram} := mkRiscvMachine {
  (* checks that addr is aligned, and translates the (possibly virtual) addr to a physical
     address, raising an exception if the address is invalid *)
  translate(accessType: AccessType)(alignment: t)(addr: t): M t;
  flushTLB: M unit;
  getCSR_InstRet: M MachineInt;
  getCSR_Time: M MachineInt;
  getCSR_Cycle: M MachineInt;
}.

Section Riscv.
  (* monad (will be instantiated with some kind of state monad) *)
  Context {M: Type -> Type}.
  Context {MM: Monad M}.

  (* type of register values *)
  Context {t: Type}.

  (* provides operations on t *)
  Context {MW: MachineWidth t}.

  Local Open Scope alu_scope.
  Local Open Scope Z_scope.

  Import MonadNotations.

  Context {MP: RiscvProgram}.

  Definition getXLEN: M MachineInt :=
    mxl <- getCSRField MXL;
    if Z.eqb mxl 1 then Return 32
    else if Z.eqb mxl 2 then Return 64
    else Return 0.

  Definition raiseExceptionWithInfo{A: Type}(isInterrupt exceptionCode info: t): M A :=
    pc <- getPC;
    (* here we hardcode that this simplified spec only supports machine mode and no interrupts *)
    addr <- getCSRField MTVecBase;
    setCSRField MTVal (regToZ_unsigned info);;
    (* these two need to be set just so that Mret will succeed at restoring them *)
    setCSRField MPP (encodePrivMode Machine);;
    setCSRField MPIE 0;;
    setCSRField MEPC (regToZ_unsigned pc);;
    setCSRField MCauseCode (regToZ_unsigned exceptionCode);;
    setPC (ZToReg (addr * 4));;
    @endCycleEarly M t MM MW MP A.

  Definition raiseException{A: Type}(isInterrupt: t)(exceptionCode: t): M A :=
    raiseExceptionWithInfo isInterrupt exceptionCode (ZToReg 0).

  (* in a system with virtual memory, this would also do the translation, but in our
     case, we only verify the alignment *)
  Definition translate_with_alignment_check
    (accessType: AccessType)(alignment: t)(addr: t): M t :=
    if remu addr alignment /= ZToReg 0
    then raiseException (ZToReg 0) (ZToReg 4)
    else Return addr.

  Instance DefaultRiscvState: RiscvMachine := {|
    (* riscv does allow misaligned memory access (but might emulate them in software),
       so for the compiler-facing side, we don't do alignment checks, but might add
       another riscv machine layer below to emulate turn misaligned accesses into two
       aligned accesses *)
    translate accessType alignment := @Return M MM t;
    flushTLB := Return tt;
    (* platform specific CSRs that we don't support at the moment: *)
    getCSR_InstRet := raiseException (ZToReg 0) (ZToReg 2);
    getCSR_Time    := raiseException (ZToReg 0) (ZToReg 2);
    getCSR_Cycle   := raiseException (ZToReg 0) (ZToReg 2);
  |}.

End Riscv.

Notation Register0 := 0%Z (only parsing).

Arguments RiscvProgram: clear implicits.
Arguments RiscvProgram (M) (t) {_} {_}.
Arguments RiscvMachine: clear implicits.
Arguments RiscvMachine (M) (t) {_} {_} {_}.

#[global] Existing Instance DefaultRiscvState.
