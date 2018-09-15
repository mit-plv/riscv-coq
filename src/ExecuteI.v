(* Default settings (from HsToCoq.Coq.Preamble) *)

Generalizable All Variables.

Unset Implicit Arguments.
Set Maximal Implicit Insertion.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Coq.Program.Tactics.
Require Coq.Program.Wf.

(* Preamble *)

Require Import Coq.ZArith.BinInt.
Local Open Scope Z.
Require Import Utility.
Local Open Scope alu_scope.

(* Converted imports: *)

Require Decode.
Require Import Monads.
Require Import Program.
Require Import Utility.

(* No type declarations to convert. *)
(* Converted value declarations: *)

Definition execute {p} {t} `{(RiscvState p t)}
   : Decode.InstructionI -> p unit :=
  fun arg_0__ =>
    match arg_0__ with
    | Decode.Lui rd imm20 => setRegister rd (fromImm imm20)
    | Decode.Auipc rd oimm20 =>
        Bind getPC (fun pc => setRegister rd (fromImm oimm20 + pc))
    | Decode.Jal rd jimm20 =>
        Bind getPC (fun pc =>
                let newPC := pc + fromImm jimm20 in
                if (remu newPC (ZToReg 4) /= ZToReg 0) : bool
                then raiseException (ZToReg 0) (ZToReg 0)
                else (Bind (setRegister rd (pc + ZToReg 4)) (fun _ => setPC newPC)))
    | Decode.Jalr rd rs1 oimm12 =>
        Bind (getRegister rs1) (fun x =>
                Bind getPC (fun pc =>
                        let newPC := and (x + fromImm oimm12) (lnot (ZToReg 1)) in
                        if (remu newPC (ZToReg 4) /= ZToReg 0) : bool
                        then raiseException (ZToReg 0) (ZToReg 0)
                        else (Bind (setRegister rd (pc + ZToReg 4)) (fun _ => setPC newPC))))
    | Decode.Beq rs1 rs2 sbimm12 =>
        Bind (getRegister rs1) (fun x =>
                Bind (getRegister rs2) (fun y =>
                        Bind getPC (fun pc =>
                                when (reg_eqb x y) (let newPC := (pc + fromImm sbimm12) in
                                                    if (remu newPC (ZToReg 4) /= ZToReg 0) : bool
                                                    then raiseException (ZToReg 0) (ZToReg 0)
                                                    else setPC newPC))))
    | Decode.Bne rs1 rs2 sbimm12 =>
        Bind (getRegister rs1) (fun x =>
                Bind (getRegister rs2) (fun y =>
                        Bind getPC (fun pc =>
                                when (x /= y) (let addr := (pc + fromImm sbimm12) in
                                               if (remu addr (ZToReg 4) /= ZToReg 0) : bool
                                               then raiseException (ZToReg 0) (ZToReg 0)
                                               else setPC addr))))
    | Decode.Blt rs1 rs2 sbimm12 =>
        Bind (getRegister rs1) (fun x =>
                Bind (getRegister rs2) (fun y =>
                        Bind getPC (fun pc =>
                                when (x < y) (let addr := (pc + fromImm sbimm12) in
                                              if (remu addr (ZToReg 4) /= ZToReg 0) : bool
                                              then raiseException (ZToReg 0) (ZToReg 0)
                                              else setPC addr))))
    | Decode.Bge rs1 rs2 sbimm12 =>
        Bind (getRegister rs1) (fun x =>
                Bind (getRegister rs2) (fun y =>
                        Bind getPC (fun pc =>
                                when (x >= y) (let addr := (pc + fromImm sbimm12) in
                                               if (remu addr (ZToReg 4) /= ZToReg 0) : bool
                                               then raiseException (ZToReg 0) (ZToReg 0)
                                               else setPC addr))))
    | Decode.Bltu rs1 rs2 sbimm12 =>
        Bind (getRegister rs1) (fun x =>
                Bind (getRegister rs2) (fun y =>
                        Bind getPC (fun pc =>
                                when ((ltu x y)) (let addr := (pc + fromImm sbimm12) in
                                                  if (remu addr (ZToReg 4) /= ZToReg 0) : bool
                                                  then raiseException (ZToReg 0) (ZToReg 0)
                                                  else setPC addr))))
    | Decode.Bgeu rs1 rs2 sbimm12 =>
        Bind (getRegister rs1) (fun x =>
                Bind (getRegister rs2) (fun y =>
                        Bind getPC (fun pc =>
                                when (negb (ltu x y)) (let addr := (pc + fromImm sbimm12) in
                                                       if (remu addr (ZToReg 4) /= ZToReg 0) : bool
                                                       then raiseException (ZToReg 0) (ZToReg 0)
                                                       else setPC addr))))
    | Decode.Lb rd rs1 oimm12 =>
        Bind (getRegister rs1) (fun a =>
                Bind (translate Load (ZToReg 1) (a + fromImm oimm12)) (fun addr =>
                        Bind (loadByte addr) (fun x => setRegister rd (int8ToReg x))))
    | Decode.Lh rd rs1 oimm12 =>
        Bind (getRegister rs1) (fun a =>
                Bind (translate Load (ZToReg 2) (a + fromImm oimm12)) (fun addr =>
                        Bind (loadHalf addr) (fun x => setRegister rd (int16ToReg x))))
    | Decode.Lw rd rs1 oimm12 =>
        Bind (getRegister rs1) (fun a =>
                Bind (translate Load (ZToReg 4) (a + fromImm oimm12)) (fun addr =>
                        Bind (loadWord addr) (fun x => setRegister rd (int32ToReg x))))
    | Decode.Lbu rd rs1 oimm12 =>
        Bind (getRegister rs1) (fun a =>
                Bind (translate Load (ZToReg 1) (a + fromImm oimm12)) (fun addr =>
                        Bind (loadByte addr) (fun x => setRegister rd (uInt8ToReg x))))
    | Decode.Lhu rd rs1 oimm12 =>
        Bind (getRegister rs1) (fun a =>
                Bind (translate Load (ZToReg 2) (a + fromImm oimm12)) (fun addr =>
                        Bind (loadHalf addr) (fun x => setRegister rd (uInt16ToReg x))))
    | Decode.Sb rs1 rs2 simm12 =>
        Bind (getRegister rs1) (fun a =>
                Bind (translate Store (ZToReg 1) (a + fromImm simm12)) (fun addr =>
                        Bind (getRegister rs2) (fun x => storeByte addr (regToInt8 x))))
    | Decode.Sh rs1 rs2 simm12 =>
        Bind (getRegister rs1) (fun a =>
                Bind (translate Store (ZToReg 2) (a + fromImm simm12)) (fun addr =>
                        Bind (getRegister rs2) (fun x => storeHalf addr (regToInt16 x))))
    | Decode.Sw rs1 rs2 simm12 =>
        Bind (getRegister rs1) (fun a =>
                Bind (translate Store (ZToReg 4) (a + fromImm simm12)) (fun addr =>
                        Bind (getRegister rs2) (fun x => storeWord addr (regToInt32 x))))
    | Decode.Addi rd rs1 imm12 =>
        Bind (getRegister rs1) (fun x => setRegister rd (x + fromImm imm12))
    | Decode.Slti rd rs1 imm12 =>
        Bind (getRegister rs1) (fun x =>
                let val := (if x < fromImm imm12 : bool then ZToReg 1 else ZToReg 0) in
                setRegister rd val)
    | Decode.Sltiu rd rs1 imm12 =>
        Bind (getRegister rs1) (fun x =>
                let val := (if (ltu x (fromImm imm12)) : bool then ZToReg 1 else ZToReg 0) in
                setRegister rd val)
    | Decode.Xori rd rs1 imm12 =>
        Bind (getRegister rs1) (fun x => setRegister rd (xor x (fromImm imm12)))
    | Decode.Ori rd rs1 imm12 =>
        Bind (getRegister rs1) (fun x => setRegister rd (or x (fromImm imm12)))
    | Decode.Andi rd rs1 imm12 =>
        Bind (getRegister rs1) (fun x => setRegister rd (and x (fromImm imm12)))
    | Decode.Slli rd rs1 shamt6 =>
        Bind (getRegister rs1) (fun x => setRegister rd (sll x shamt6))
    | Decode.Srli rd rs1 shamt6 =>
        Bind (getRegister rs1) (fun x => setRegister rd (srl x shamt6))
    | Decode.Srai rd rs1 shamt6 =>
        Bind (getRegister rs1) (fun x => setRegister rd (sra x shamt6))
    | Decode.Add rd rs1 rs2 =>
        Bind (getRegister rs1) (fun x =>
                Bind (getRegister rs2) (fun y => setRegister rd (x + y)))
    | Decode.Sub rd rs1 rs2 =>
        Bind (getRegister rs1) (fun x =>
                Bind (getRegister rs2) (fun y => setRegister rd (x - y)))
    | Decode.Sll rd rs1 rs2 =>
        Bind (getRegister rs1) (fun x =>
                Bind (getRegister rs2) (fun y => setRegister rd (sll x (regToShamt y))))
    | Decode.Slt rd rs1 rs2 =>
        Bind (getRegister rs1) (fun x =>
                Bind (getRegister rs2) (fun y =>
                        let val := if x < y : bool then ZToReg 1 else ZToReg 0 in setRegister rd val))
    | Decode.Sltu rd rs1 rs2 =>
        Bind (getRegister rs1) (fun x =>
                Bind (getRegister rs2) (fun y =>
                        let val := if ltu x y : bool then ZToReg 1 else ZToReg 0 in setRegister rd val))
    | Decode.Xor rd rs1 rs2 =>
        Bind (getRegister rs1) (fun x =>
                Bind (getRegister rs2) (fun y => setRegister rd (xor x y)))
    | Decode.Or rd rs1 rs2 =>
        Bind (getRegister rs1) (fun x =>
                Bind (getRegister rs2) (fun y => setRegister rd (or x y)))
    | Decode.Srl rd rs1 rs2 =>
        Bind (getRegister rs1) (fun x =>
                Bind (getRegister rs2) (fun y => setRegister rd (srl x (regToShamt y))))
    | Decode.Sra rd rs1 rs2 =>
        Bind (getRegister rs1) (fun x =>
                Bind (getRegister rs2) (fun y => setRegister rd (sra x (regToShamt y))))
    | Decode.And rd rs1 rs2 =>
        Bind (getRegister rs1) (fun x =>
                Bind (getRegister rs2) (fun y => setRegister rd (and x y)))
    | Decode.Fence pred succ => Return tt
    | Decode.Fence_i => Return tt
    | inst => Return tt
    end.

(* External variables:
     Bind Load Return RiscvState Store ZToReg and bool fromImm getPC getRegister
     int16ToReg int32ToReg int8ToReg lnot loadByte loadHalf loadWord ltu negb
     op_zgze__ op_zl__ op_zm__ op_zp__ op_zsze__ or raiseException regToInt16
     regToInt32 regToInt8 regToShamt reg_eqb remu setPC setRegister sll sra srl
     storeByte storeHalf storeWord translate tt uInt16ToReg uInt8ToReg unit when xor
     Decode.Add Decode.Addi Decode.And Decode.Andi Decode.Auipc Decode.Beq Decode.Bge
     Decode.Bgeu Decode.Blt Decode.Bltu Decode.Bne Decode.Fence Decode.Fence_i
     Decode.InstructionI Decode.Jal Decode.Jalr Decode.Lb Decode.Lbu Decode.Lh
     Decode.Lhu Decode.Lui Decode.Lw Decode.Or Decode.Ori Decode.Sb Decode.Sh
     Decode.Sll Decode.Slli Decode.Slt Decode.Slti Decode.Sltiu Decode.Sltu
     Decode.Sra Decode.Srai Decode.Srl Decode.Srli Decode.Sub Decode.Sw Decode.Xor
     Decode.Xori
*)
