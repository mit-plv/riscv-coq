Require Import Coq.ZArith.BinInt.
Require Import Coq.Strings.String.
Require Import riscv.Utility.Monads. Import OStateOperations.
Require Import riscv.Utility.MonadNotations.
Require Import riscv.Spec.Decode.
Require Import riscv.Platform.Memory. (* should go before Program because both define loadByte etc *)
Require Import riscv.Spec.Machine.
Require Import riscv.Spec.Execute.
Require Import riscv.Utility.PowerFunc.
Require Import riscv.Utility.Utility.
Require Import Coq.Lists.List. Import ListNotations.
Require Import riscv.Platform.Minimal.
Require Import coqutil.Map.Interface.


Section Riscv.
  Context {width: Z} {BW: Bitwidth width} {word: word width} {word_ok: word.ok word}.
  Context {Mem: map.map word byte}.
  Context {Registers: map.map Register word}.

  Local Notation empty_mem := (map.empty: Mem).

  Definition mkLogItemLoad(addr: word)(value: w32): LogItem :=
    ((empty_mem, "loadWord"%string, [addr]), (empty_mem, [int32ToReg value])).

  Definition mkLogItemStore(addr: word)(value: w32): LogItem :=
    ((empty_mem, "storeWord"%string, [addr; int32ToReg value]), (empty_mem, [])).

  Instance IsRiscvMachineL: RiscvProgram (OState RiscvMachine) word := {
      getRegister := getRegister;
      setRegister := setRegister;
      getPC := getPC;
      setPC := setPC;
      loadByte   := loadByte;
      loadHalf   := loadHalf;
      loadWord kind a :=
        Bind get
             (fun m =>
                Bind (Monad := (OState_Monad _)) (* why does Coq infer OStateND_Monad?? *)
                     (loadWord kind a)
                     (fun res =>
                        Bind (Monad := (OState_Monad _)) (* why does Coq infer OStateND_Monad?? *)
                             (put (withLogItem (mkLogItemLoad a res) m))
                             (fun _ => Return res)));
(*
        m <- get;
        res <- (loadWord kind a);
        put (withLogItem (mkLogItemLoad a res));;
        Return res;
*)

      loadDouble := loadDouble;
      storeByte   := storeByte;
      storeHalf   := storeHalf;

      storeWord kind a v :=
        Bind get
             (fun m =>
                Bind (Monad := (OState_Monad _)) (* why does Coq infer OStateND_Monad?? *)
                     (put (withLogItem (mkLogItemStore a v) m))
                     (fun (_: unit) =>
                        storeWord kind a v));

      storeDouble := storeDouble;
      makeReservation := makeReservation;
      clearReservation := clearReservation;
      checkReservation := checkReservation;
      getCSRField := getCSRField;
      setCSRField := setCSRField;
      getPrivMode := getPrivMode;
      setPrivMode := setPrivMode;
      fence := fence;

      endCycleNormal := endCycleNormal;
      endCycleEarly{A} := @endCycleEarly _ _ _ _ _ A;
  }.

End Riscv.

#[global] Existing Instance IsRiscvMachineL. (* needed because it was defined inside a Section *)
