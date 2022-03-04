Require Import riscv.Utility.Monads.
Require Import riscv.Utility.FreeMonad.
Require Import riscv.Spec.Decode.
Require Import riscv.Spec.Machine.
Require Import riscv.Utility.MkMachineWidth.
Require Import riscv.Utility.Utility.

Section Riscv.
  Import free.

  Variant riscv_primitive{width}{BW: Bitwidth width}{word: word width}:=
  | GetRegister (_ : Register)
  | SetRegister (_ : Register) (_ : word)
  | LoadByte (_ : SourceType) (_ : word)
  | LoadHalf (_ : SourceType) (_ : word)
  | LoadWord (_ : SourceType) (_ : word)
  | LoadDouble (_ : SourceType) (_ : word)
  | StoreByte (_ : SourceType) (_ : word) (_ : w8)
  | StoreHalf (_ : SourceType) (_ : word) (_ : w16)
  | StoreWord (_ : SourceType) (_ : word) (_ : w32)
  | StoreDouble (_ : SourceType) (_ : word) (_ : w64)
  | MakeReservation (_ : word)
  | ClearReservation (_ : word)
  | CheckReservation (_ : word)
  | GetCSRField (_ : CSRField.CSRField)
  | SetCSRField (_ : CSRField.CSRField) (_ : MachineInt)
  | GetPrivMode
  | SetPrivMode (_ : PrivMode)
  | Fence (_ : MachineInt) (_ : MachineInt)
  | GetPC
  | SetPC (_ : word)
  | StartCycle
  | EndCycleNormal
  | EndCycleEarly (_ : Type)
  .

  Context {width} {BW: Bitwidth width} {word: word width}.

  Definition primitive_result (action : riscv_primitive) : Type :=
    match action with
    | GetRegister _ => word
    | SetRegister _ _ => unit
    | LoadByte _ _ => w8
    | LoadHalf _ _ => w16
    | LoadWord _ _ => w32
    | LoadDouble _ _ => w64
    | StoreByte _ _ _ | StoreHalf _ _ _ | StoreWord _ _ _ | StoreDouble _ _ _ => unit
    | MakeReservation _ | ClearReservation _ => unit
    | CheckReservation _ => bool
    | GetCSRField _ => MachineInt
    | SetCSRField _ _ => unit
    | GetPrivMode => PrivMode
    | SetPrivMode _ => unit
    | Fence _ _ => unit
    | GetPC => word
    | SetPC _ => unit
    | StartCycle => unit
    | EndCycleNormal => unit
    | EndCycleEarly T => T
    end.

  Global Instance Materialize: RiscvProgram (free riscv_primitive primitive_result) word := {|
    getRegister a := act (GetRegister a) ret;
    setRegister a b := act (SetRegister a b) ret;
    loadByte a b := act (LoadByte a b) ret;
    loadHalf a b := act (LoadHalf a b) ret;
    loadWord a b := act (LoadWord a b) ret;
    loadDouble a b := act (LoadDouble a b) ret;
    storeByte a b c := act (StoreByte a b c) ret;
    storeHalf a b c := act (StoreHalf a b c) ret;
    storeWord a b c := act (StoreWord a b c) ret;
    storeDouble a b c := act (StoreDouble a b c) ret;
    makeReservation a := act (MakeReservation a) ret;
    clearReservation a := act (ClearReservation a) ret;
    checkReservation a := act (CheckReservation a) ret;
    getCSRField f := act (GetCSRField f) ret;
    setCSRField f v := act (SetCSRField f v) ret;
    getPrivMode := act GetPrivMode ret;
    setPrivMode m := act (SetPrivMode m) ret;
    fence a b := act (Fence a b) ret;
    getPC := act GetPC ret;
    setPC a := act (SetPC a) ret;
    endCycleNormal := act EndCycleNormal ret;
    endCycleEarly A := act (EndCycleEarly A) ret;
  |}.

  (* Not (yet) in Riscv monad, but added here because it's useful to initialize
     nextPc to pc+4 at the beginning of each cycle instead of having to maintain
     a nextPc=pc+4 invariant everywhere *)
  Definition startCycle: FreeMonad.free riscv_primitive primitive_result unit :=
    FreeMonad.free.act StartCycle FreeMonad.free.ret.
End Riscv.
