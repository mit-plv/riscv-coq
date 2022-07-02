Require Import coqutil.Map.Interface.
Require Import coqutil.Word.Interface.
Require Import riscv.Utility.Utility.
Require Import riscv.Utility.Monads. Import OStateOperations.
Require Import riscv.Utility.MonadNotations.
Require Import riscv.Spec.Decode.
Require Import riscv.Spec.Machine.
Require Import riscv.Spec.Primitives.
Require Import riscv.Platform.AtomicRiscvMachine.
Require Import riscv.Platform.Minimal.

Section Riscv.
  Context {width: Z} {BW: Bitwidth width} {word: word width} {word_ok: word.ok word}.
  Context {Mem: map.map word byte}.
  Context {Registers: map.map Register word}.

  Definition liftL0{B: Type}(fr: option word -> option word)(f: OState RiscvMachine B):
    OState AtomicRiscvMachine B :=
    fun s => let (ob, s') := f s.(getMachine) in
             (ob, mkAtomicRiscvMachine s' (fr s.(getReservation))).

  Definition liftL1{A B: Type} fr (f: A -> OState RiscvMachine B) :=
    fun a => liftL0 fr (f a).

  Definition liftL2{A1 A2 B: Type} fl (f: A1 -> A2 -> OState RiscvMachine B) :=
    fun a1 a2 => liftL0 fl (f a1 a2).

  Definition liftL3{A1 A2 A3 B: Type} fl (f: A1 -> A2 -> A3 -> OState RiscvMachine B) :=
    fun a1 a2 a3 => liftL0 fl (f a1 a2 a3).

  Definition update(f: AtomicRiscvMachine -> AtomicRiscvMachine): OState AtomicRiscvMachine unit :=
    m <- get; put (f m).

  Instance IsAtomicRiscvMachine: RiscvProgram (OState AtomicRiscvMachine) word :=
    {
      getRegister := liftL1 id getRegister;
      setRegister := liftL2 id setRegister;
      getPC := liftL0 id getPC;
      setPC := liftL1 id setPC;
      loadByte := liftL2 id loadByte;
      loadHalf := liftL2 id loadHalf;
      loadWord := liftL2 id loadWord;
      loadDouble := liftL2 id loadDouble;
      storeByte := liftL3 id storeByte;
      storeHalf := liftL3 id storeHalf;
      storeWord := liftL3 id storeWord;
      storeDouble := liftL3 id storeDouble;
      makeReservation addr := update (fun mach => withReservation (Some addr) mach);
      clearReservation addr := update (fun mach => withReservation None mach);
      checkReservation addr :=
        mach <- get;
        match mach.(getReservation) with
        | None => Return false
        | Some addr' => Return (word.eqb addr addr')
        end;
      getCSRField := liftL1 id getCSRField;
      setCSRField := liftL2 id setCSRField;
      getPrivMode := liftL0 id getPrivMode;
      setPrivMode := liftL1 id setPrivMode;
      fence := liftL2 id fence;
      endCycleNormal := liftL0 id endCycleNormal;
      endCycleEarly{A} := liftL0 id (@endCycleEarly _ _ _ _ _ A);
    }.

  Instance AtomicMinimalPrimitivesParams: PrimitivesParams (OState AtomicRiscvMachine) AtomicRiscvMachine :=
    {
      Primitives.mcomp_sat := @OStateOperations.computation_with_answer_satisfies AtomicRiscvMachine;
      Primitives.is_initial_register_value := eq (word.of_Z 0);
      Primitives.nonmem_load n kind addr _ _ := False;
      Primitives.nonmem_store n kind addr v _ _ := False;
      Primitives.valid_machine mach := True;
    }.

End Riscv.

#[global] Existing Instance IsAtomicRiscvMachine.
