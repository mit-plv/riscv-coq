Require Import Coq.ZArith.BinInt.
Require Import bbv.WordScope.
Require Import bbv.DepEqNat.
Require Import riscv.util.NameWithEq.
Require Import riscv.RiscvBitWidths.
Require Import riscv.util.Monad.
Require Import riscv.util.StateMonad.
Require Import riscv.Decode.
Require Import riscv.Memory. (* should go before Program because both define loadByte etc *)
Require Import riscv.Program.
Require Import riscv.Execute.
Require Import riscv.util.PowerFunc.
Require Import riscv.Utility.
Require Import Coq.Lists.List.
Import ListNotations.

Section Riscv.

  Context {B: RiscvBitWidths}.

  Instance A: Alu (word wXLEN) (word wXLEN) := {|
    zero := $0;
    one := $1;
    add := @wplus wXLEN;
    sub := @wminus wXLEN;
    mul := @wmult wXLEN;
    div := @wdiv wXLEN;
    rem := @wmod wXLEN;
    signed_less_than a b := if wslt_dec a b then true else false;
    unsigned_less_than a (b: word wXLEN) := if wlt_dec a b then true else false;
    signed_eqb := @weqb wXLEN;
    shiftL w n := wlshift w (Z.to_nat n);
    signed_shiftR w n := wrshifta w (Z.to_nat n);
    unsigned_shiftR w n := wrshift w (Z.to_nat n);
    xor := @wxor wXLEN;
    or := @wor wXLEN;
    and := @wand wXLEN;
  |}.

  (* TODO this is not the way to do it *)

  Instance immmm: IntegralConversion MachineInt (word wXLEN).
    unfold MachineInt. constructor. apply ZToWord.
  Defined.
  Instance immmm': IntegralConversion (word wXLEN) MachineInt.
    unfold MachineInt. constructor. apply ZToWord || apply wordToZ.
  Defined.
  Instance c: Convertible (word wXLEN) (word wXLEN).
    unfold MachineInt. constructor; apply id || apply ZToWord || apply wordToZ.
  Defined.
  Instance ic8: IntegralConversion Int8 (word wXLEN).
    cbv -[wXLEN]. constructor. intro. destruct H.
    refine (nat_cast _ _ (sext w (wXLEN - 8))). abstract bitwidth_omega.
  Defined.
  Instance ic16: IntegralConversion Int16 (word wXLEN).
    cbv -[wXLEN]. constructor. intro. destruct H.
    refine (nat_cast _ _ (sext w (wXLEN - 16))). abstract bitwidth_omega.
  Defined.
  Instance ic32: IntegralConversion Int32 (word wXLEN).
    cbv -[wXLEN]. constructor. intro. destruct H.
    refine (nat_cast _ _ (sext w (wXLEN - 32))). abstract bitwidth_omega.
  Defined.
  Instance ic8': IntegralConversion (word wXLEN) Int8.
    cbv -[wXLEN]. constructor. intro. constructor.
    refine (split1 _ (wXLEN - 8) (nat_cast _ _ H)). abstract bitwidth_omega.
  Defined.
  Instance ic16': IntegralConversion (word wXLEN) Int16.
    cbv -[wXLEN]. constructor. intro. constructor.
    refine (split1 _ (wXLEN - 16) (nat_cast _ _ H)). abstract bitwidth_omega.
  Defined.
  Instance ic32': IntegralConversion (word wXLEN) Int32.
    cbv -[wXLEN]. constructor. intro. constructor.
    refine (split1 _ (wXLEN - 32) (nat_cast _ _ H)). abstract bitwidth_omega.
  Defined.
  Instance ic8u: IntegralConversion Word8 (word wXLEN).
    cbv -[wXLEN]. constructor. intro. destruct H.
    refine (nat_cast _ _ (zext w (wXLEN - 8))). abstract bitwidth_omega.
  Defined.
  Instance ic16u: IntegralConversion Word16 (word wXLEN).
    cbv -[wXLEN]. constructor. intro. destruct H.
    refine (nat_cast _ _ (zext w (wXLEN - 16))). abstract bitwidth_omega.
  Defined.
  Instance ic32u: IntegralConversion Word32 (word wXLEN).
    cbv -[wXLEN]. constructor. intro. destruct H.
    refine (nat_cast _ _ (zext w (wXLEN - 32))). abstract bitwidth_omega.
  Defined.
  Instance icZt: IntegralConversion Z (word wXLEN).
    unfold MachineInt. constructor. apply ZToWord.
  Defined.
  Instance icZu: IntegralConversion Z (word wXLEN).
    unfold MachineInt. constructor. apply ZToWord.
  Defined.
  Instance icut: IntegralConversion (word wXLEN) (word wXLEN).
    constructor. exact id.
  Defined.
  Instance ictu: IntegralConversion (word wXLEN) (word wXLEN).
    constructor. exact id.
  Defined.

  Definition MW: MachineWidth (word wXLEN) := MachineWidthInst (Z.of_nat log2wXLEN) (word wXLEN).

  Existing Instance MW.

  Definition Register := Z.

  Definition Register0: Register := 0%Z.

  Instance ZName: NameWithEq := {|
    name := Z
  |}.

  Definition run1{M: Type -> Type}{MM: Monad M}{RVS: RiscvState M}: M unit :=
    pc <- getPC;
    inst <- loadWord pc;
    execute (decode (Z.of_nat wXLEN) (Int32ToMachineInt inst));;
    step.

  Definition run{M: Type -> Type}{MM: Monad M}{RVS: RiscvState M}: nat -> M unit :=
    fun n => power_func (fun m => run1 ;; m) n (Return tt).

  Inductive TraceEvent: Set :=
  | TraceLoad(sz: nat)(addr: word wXLEN)(val: SignedWord sz)
  | TraceLoadFailure(addr: word wXLEN).

  Record RiscvMachine := mkRiscvMachine {
    machineMem: mem 8;
    registers: Register -> word wXLEN;
    pc: word wXLEN;
    nextPC: word wXLEN;
    exceptionHandlerAddr: word wXLEN;
    executionTrace: list TraceEvent;
  }.

  Definition with_machineMem me ma :=
    mkRiscvMachine me ma.(registers) ma.(pc) ma.(nextPC) ma.(exceptionHandlerAddr) ma.(executionTrace).
  Definition with_registers r ma :=
    mkRiscvMachine ma.(machineMem) r ma.(pc) ma.(nextPC) ma.(exceptionHandlerAddr) ma.(executionTrace).
  Definition with_pc p ma :=
    mkRiscvMachine ma.(machineMem) ma.(registers) p ma.(nextPC) ma.(exceptionHandlerAddr) ma.(executionTrace).
  Definition with_nextPC npc ma :=
    mkRiscvMachine ma.(machineMem) ma.(registers) ma.(pc) npc ma.(exceptionHandlerAddr) ma.(executionTrace).
  Definition with_exceptionHandlerAddr eh ma :=
    mkRiscvMachine ma.(machineMem) ma.(registers) ma.(pc) ma.(nextPC) eh ma.(executionTrace).
  Definition with_executionTrace t ma :=
    mkRiscvMachine ma.(machineMem) ma.(registers) ma.(pc) ma.(nextPC) ma.(exceptionHandlerAddr) t.

  Definition liftLoad{sz: nat}(f: mem 8 -> word wXLEN -> option (SignedWord sz))(a: word wXLEN)
    : State RiscvMachine (SignedWord sz) :=
    m <- get;
    match f m.(machineMem) a with
    | Some v =>
        put (with_executionTrace (m.(executionTrace) ++ [TraceLoad sz a v]) m);;
        Return v
    | None =>
        put (with_nextPC m.(exceptionHandlerAddr) m);;
        put (with_executionTrace (m.(executionTrace) ++ [TraceLoadFailure a]) m);;
        Return (mkSignedWord $0)
    end.

  Definition liftStore{sz: nat}(f: mem 8 -> word wXLEN -> SignedWord sz -> option (mem 8))
    (a: word wXLEN)(v: SignedWord sz) : State RiscvMachine unit :=
    m <- get;
    match f m.(machineMem) a v with
    | Some mem' => put (with_machineMem mem' m)
    | None => put (with_nextPC m.(exceptionHandlerAddr) m)
    end.

  Instance IsRiscvMachine: RiscvState (State RiscvMachine) :=
  {|
      getRegister := fun (reg: name) =>
        if dec (reg = Register0) then
          Return $0
        else
          machine <- get; Return (machine.(registers) reg);

      setRegister := fun s ic (reg: name) (v: s) =>
        if dec (reg = Register0) then
          Return tt
        else
          machine <- get;
          let newRegs := (fun reg2 => if dec (reg = reg2)
                                      then (fromIntegral v)
                                      else machine.(registers) reg2) in
          put (with_registers newRegs machine);

      getPC := gets pc;

      setPC := fun newPC =>
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
        put (with_nextPC (m.(nextPC) ^+ $4) (with_pc m.(nextPC) m));

      raiseException _ _ :=
        m <- get;
        put (with_nextPC m.(exceptionHandlerAddr) m);
  |}.

  Fixpoint storeWords(l: list (word 32))(a: word wXLEN)(m: mem 8): option (mem 8) :=
    match l with
    | nil => Some m
    | cons w l' =>
        match Memory.storeWord m a (mkSignedWord w) with
        | Some m' => storeWords l' (a ^+ $4) m'
        | None => None
        end
    end.

  Definition storeWords_if_mem_accepts(l: list (word 32))(m: mem 8): mem 8 :=
    match storeWords l $0 m with
    | Some m' => m'
    | None => m
    end.

  (* Puts given program at address 0, and makes pc point to beginning of program, i.e. 0.
     TODO maybe later allow any address?
     Note: Keeps the original exceptionHandlerAddr, and the values of the registers,
     which might contain any undefined garbage values, so the compiler correctness proof
     will show that the program is correct even then, i.e. no initialisation of the registers
     is needed. *)
  Definition putProgram(prog: list (word 32))(m: RiscvMachine): RiscvMachine :=
    match m with
    | mkRiscvMachine m regs _ _ eh tr =>
        mkRiscvMachine (storeWords_if_mem_accepts prog m) regs $0 $4 eh tr
    end.

End Riscv.

Existing Instance IsRiscvMachine. (* needed because it was defined inside a Section *)
