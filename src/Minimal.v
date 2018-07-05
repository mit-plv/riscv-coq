Require Import Coq.ZArith.BinInt.
Require Import Coq.omega.Omega.
Require Import bbv.WordScope.
Require Import riscv.util.BitWidths.
Require Import riscv.util.Monads.
Require Import riscv.Decode.
Require Import riscv.Memory. (* should go before Program because both define loadByte etc *)
Require Import riscv.Program.
Require Import riscv.Utility.
Require Import riscv.AxiomaticRiscv.
Require Export riscv.RiscvMachine.

Section Riscv.

  Context {B: BitWidths}.

  Context {Mem: Set}.

  Context {MemIsMem: Memory Mem wXLEN}.

  Context {mword: Set}.
  Context {MW: MachineWidth mword}.

  Context {RF: Type}.
  Context {RFI: RegisterFile RF Register mword}.

  Local Notation RiscvMachine := (@RiscvMachine B Mem RF).

  Definition liftLoad{R}(f: Mem -> mword -> R): mword -> OState RiscvMachine R :=
    fun a => m <- gets machineMem; Return (f m a).

  Definition liftStore{R}(f: Mem -> mword -> R -> Mem):
    mword -> R -> OState RiscvMachine unit :=
    fun a v => m <- get; put (with_machineMem (f m.(machineMem) a v) m).
  
  Instance IsRiscvMachine: RiscvProgram (OState RiscvMachine) mword :=
  {|
      getRegister reg :=
        if Z.eq_dec reg Register0 then
          Return $0
        else
          machine <- get;
          Return (getReg machine.(core).(registers) reg);

      setRegister reg v :=
        if Z.eq_dec reg Register0 then
          Return tt
        else
          machine <- get;
          let newRegs := setReg machine.(core).(registers) reg v in
          put (with_registers newRegs machine);

      getPC := machine <- get; Return machine.(core).(pc);

      setPC newPC :=
        machine <- get;
        put (with_nextPC newPC machine);

      loadByte   := liftLoad Memory.loadByte;
      loadHalf   := liftLoad Memory.loadHalf;
      loadWord   := liftLoad Memory.loadWord;
      loadDouble := liftLoad Memory.loadDouble;

      storeByte   := liftStore Memory.storeByte;
      storeHalf   := liftStore Memory.storeHalf;
      storeWord   := liftStore Memory.storeWord;
      storeDouble := liftStore Memory.storeDouble;

      step :=
        m <- get;
        put (with_nextPC (m.(core).(nextPC) ^+ $4) (with_pc m.(core).(nextPC) m));

      getCSRField_MTVecBase :=
        machine <- get;
        Return machine.(core).(exceptionHandlerAddr);

      endCycle A := Return None;
  |}.

  (* Puts given program at address 0, and makes pc point to beginning of program, i.e. 0.
     TODO maybe later allow any address?
     Note: Keeps the original exceptionHandlerAddr, and the values of the registers,
     which might contain any undefined garbage values, so the compiler correctness proof
     will show that the program is correct even then, i.e. no initialisation of the registers
     is needed. *)
  Definition putProgram(prog: list (word 32))(addr: mword)(ma: RiscvMachine): RiscvMachine :=
    (with_pc addr
    (with_nextPC (addr ^+ $4)
    (with_machineMem (store_word_list prog addr ma.(machineMem)) ma))).

  Ltac destruct_if :=
    match goal with
    | |- context [if ?x then _ else _] => destruct x
    end.

  Instance MinimalRiscvSatisfiesAxioms: @AxiomaticRiscv B RF RFI Mem MemIsMem IsRiscvMachine.
  Proof.
    constructor; intros; simpl; try reflexivity; destruct_if; try reflexivity;
      subst; unfold valid_register, Register0 in *; omega.
  Qed.
  
End Riscv.

(* needed because it was defined inside a Section *)
Existing Instance IsRiscvMachine.
Existing Instance MinimalRiscvSatisfiesAxioms.
