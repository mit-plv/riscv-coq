Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import riscv.Utility.Monads. Import StateAbortFailOperations.
Require Import riscv.Utility.MonadNotations.
Require Import riscv.Spec.Decode.
Require Import riscv.Spec.Machine.
Require Import riscv.Spec.CSRFile.
Require Import riscv.Utility.Utility.
Require Import riscv.Spec.Primitives.
Require Import riscv.Utility.ExtensibleRecords.
Require Import coqutil.Z.Lia.
Require Import coqutil.Map.Interface.
Require Import riscv.Platform.Sane.

Local Open Scope Z_scope.
Local Open Scope bool_scope.
Import ListNotations.

Definition regs: nat := 0.
Definition pc: nat := 1.
Definition nextPc: nat := 2.
Definition mem: nat := 3.
(* xAddrs : 4 *)
Definition log: nat := 5.
(* metrics: 6 *)
Definition csrs: nat := 7.

Section Riscv.
  Context {width: Z} {BW: Bitwidth width} {word: word width} {word_ok: word.ok word}.
  Context {Mem: map.map word byte}.
  Context {Registers: map.map Register word}.
  Context (UnknownFields: natmap Type).

  Definition Fields: natmap Type := natmap.putmany UnknownFields [
    (regs, Registers: Type);
    (pc, word: Type);
    (nextPc, word: Type);
    (mem, Mem: Type);
    (log, list RiscvMachine.LogItem: Type);
    (csrs, CSRFile: Type)
   ].

  Definition State: Type := hnatmap Fields.

  Import HnatmapNotations. Open Scope hnatmap_scope.

  Definition fail_if_None{R}(o: option R): StateAbortFail State R :=
    match o with
    | Some x => Return x
    | None => fail_hard
    end.

  Local Notation get := (@StateAbortFailOperations.get State). (* to improve type inference *)

  Definition loadN(n: nat)(kind: SourceType)(a: word): StateAbortFail State (HList.tuple byte n) :=
    mach <- get;
    v <- fail_if_None (Memory.load_bytes n mach[mem] a);
    Return v.

  Definition storeN(n: nat)(kind: SourceType)(a: word)(v: HList.tuple byte n): StateAbortFail State unit :=
    mach <- get;
    m <- fail_if_None (Memory.store_bytes n mach[mem] a v);
    put mach[mem := m].

  Definition updatePc(mach: State): State :=
    mach[pc := mach[nextPc]][nextPc := word.add mach[nextPc] (word.of_Z 4)].

  Instance IsRiscvMachine: RiscvProgram (StateAbortFail State) word := {
      getRegister reg :=
        if Z.eq_dec reg Register0 then
          Return (ZToReg 0)
        else
          if (0 <? reg) && (reg <? 32) then
            mach <- get;
            fail_if_None (map.get mach[regs] reg)
          else
            fail_hard;

      setRegister reg v :=
        if Z.eq_dec reg Register0 then
          Return tt
        else
          if (0 <? reg) && (reg <? 32) then
            mach <- get; put mach[regs := map.put mach[regs] reg v]
          else
            fail_hard;

      getPC := mach <- get; Return mach[pc];

      setPC newPC := mach <- get; put mach[nextPc := newPC];

      loadByte   := loadN 1;
      loadHalf   := loadN 2;
      loadWord   := loadN 4;
      loadDouble := loadN 8;

      storeByte   := storeN 1;
      storeHalf   := storeN 2;
      storeWord   := storeN 4;
      storeDouble := storeN 8;

      getCSRField f := mach <- get; fail_if_None (map.get mach[csrs] f);
      setCSRField f v := mach <- get; put mach[csrs := map.put mach[csrs] f v];

      makeReservation  addr := fail_hard;
      clearReservation addr := fail_hard;
      checkReservation addr := fail_hard;
      getPrivMode := Return Machine;
      setPrivMode mode :=
        match mode with
        | Machine => Return tt
        | User | Supervisor => fail_hard
        end;
      fence _ _ := fail_hard;

      endCycleNormal := mach <- get; put (updatePc mach);
      endCycleEarly{A: Type} := mach <- get; put (updatePc mach);; abort;
  }.

End Riscv.

(* needed because defined inside a Section *)
#[global] Existing Instance IsRiscvMachine.
