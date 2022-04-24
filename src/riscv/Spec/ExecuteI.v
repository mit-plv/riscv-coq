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
Require Import riscv.Utility.Utility.
Local Open Scope alu_scope.

(* Converted imports: *)

Require Import Monads.
Require Spec.Decode.
Require Spec.Machine.
Require Spec.VirtualMemory.
Require Import Utility.
Require Utility.Utility.

(* No type declarations to convert. *)

(* Converted value declarations: *)

Definition execute {p : Type -> Type} {t : Type} `{Spec.Machine.RiscvMachine p
                                                                             t}
   : Spec.Decode.InstructionI -> p unit :=
  fun arg_0__ =>
    match arg_0__ with
    | Spec.Decode.Lui rd imm20 =>
        Spec.Machine.setRegister rd (Utility.Utility.fromImm imm20)
    | Spec.Decode.Auipc rd oimm20 =>
        Bind Spec.Machine.getPC (fun pc =>
                Spec.Machine.setRegister rd (Utility.Utility.fromImm oimm20 + pc))
    | Spec.Decode.Jal rd jimm20 =>
        Bind Spec.Machine.getPC (fun pc =>
                let newPC := pc + Utility.Utility.fromImm jimm20 in
                if (Utility.Utility.remu newPC (ZToReg 4) /= ZToReg 0) : bool
                then Spec.Machine.raiseExceptionWithInfo (ZToReg 0) (ZToReg 0) (id newPC)
                else (Bind (Spec.Machine.setRegister rd (pc + ZToReg 4)) (fun _ =>
                              Spec.Machine.setPC newPC)))
    | Spec.Decode.Jalr rd rs1 oimm12 =>
        Bind (Spec.Machine.getRegister rs1) (fun x =>
                Bind Spec.Machine.getPC (fun pc =>
                        let newPC := and (x + Utility.Utility.fromImm oimm12) (lnot (ZToReg 1)) in
                        if (Utility.Utility.remu newPC (ZToReg 4) /= ZToReg 0) : bool
                        then Spec.Machine.raiseExceptionWithInfo (ZToReg 0) (ZToReg 0) (id newPC)
                        else (Bind (Spec.Machine.setRegister rd (pc + ZToReg 4)) (fun _ =>
                                      Spec.Machine.setPC newPC))))
    | Spec.Decode.Beq rs1 rs2 sbimm12 =>
        Bind (Spec.Machine.getRegister rs1) (fun x =>
                Bind (Spec.Machine.getRegister rs2) (fun y =>
                        Bind Spec.Machine.getPC (fun pc =>
                                when (reg_eqb x y) (let newPC := (pc + Utility.Utility.fromImm sbimm12) in
                                                    if (Utility.Utility.remu newPC (ZToReg 4) /= ZToReg 0) : bool
                                                    then Spec.Machine.raiseExceptionWithInfo (ZToReg 0) (ZToReg 0) (id
                                                                                                                    newPC)
                                                    else Spec.Machine.setPC newPC))))
    | Spec.Decode.Bne rs1 rs2 sbimm12 =>
        Bind (Spec.Machine.getRegister rs1) (fun x =>
                Bind (Spec.Machine.getRegister rs2) (fun y =>
                        Bind Spec.Machine.getPC (fun pc =>
                                when (x /= y) (let addr := (pc + Utility.Utility.fromImm sbimm12) in
                                               if (Utility.Utility.remu addr (ZToReg 4) /= ZToReg 0) : bool
                                               then Spec.Machine.raiseExceptionWithInfo (ZToReg 0) (ZToReg 0) (id addr)
                                               else Spec.Machine.setPC addr))))
    | Spec.Decode.Blt rs1 rs2 sbimm12 =>
        Bind (Spec.Machine.getRegister rs1) (fun x =>
                Bind (Spec.Machine.getRegister rs2) (fun y =>
                        Bind Spec.Machine.getPC (fun pc =>
                                when (x < y) (let addr := (pc + Utility.Utility.fromImm sbimm12) in
                                              if (Utility.Utility.remu addr (ZToReg 4) /= ZToReg 0) : bool
                                              then Spec.Machine.raiseExceptionWithInfo (ZToReg 0) (ZToReg 0) (id addr)
                                              else Spec.Machine.setPC addr))))
    | Spec.Decode.Bge rs1 rs2 sbimm12 =>
        Bind (Spec.Machine.getRegister rs1) (fun x =>
                Bind (Spec.Machine.getRegister rs2) (fun y =>
                        Bind Spec.Machine.getPC (fun pc =>
                                when (x >= y) (let addr := (pc + Utility.Utility.fromImm sbimm12) in
                                               if (Utility.Utility.remu addr (ZToReg 4) /= ZToReg 0) : bool
                                               then Spec.Machine.raiseExceptionWithInfo (ZToReg 0) (ZToReg 0) (id addr)
                                               else Spec.Machine.setPC addr))))
    | Spec.Decode.Bltu rs1 rs2 sbimm12 =>
        Bind (Spec.Machine.getRegister rs1) (fun x =>
                Bind (Spec.Machine.getRegister rs2) (fun y =>
                        Bind Spec.Machine.getPC (fun pc =>
                                when ((Utility.Utility.ltu x y)) (let addr :=
                                                                    (pc + Utility.Utility.fromImm sbimm12) in
                                                                  if (Utility.Utility.remu addr (ZToReg 4) /=
                                                                      ZToReg 0) : bool
                                                                  then Spec.Machine.raiseExceptionWithInfo (ZToReg 0)
                                                                       (ZToReg 0) (id addr)
                                                                  else Spec.Machine.setPC addr))))
    | Spec.Decode.Bgeu rs1 rs2 sbimm12 =>
        Bind (Spec.Machine.getRegister rs1) (fun x =>
                Bind (Spec.Machine.getRegister rs2) (fun y =>
                        Bind Spec.Machine.getPC (fun pc =>
                                when (negb (Utility.Utility.ltu x y)) (let addr :=
                                                                         (pc + Utility.Utility.fromImm sbimm12) in
                                                                       if (Utility.Utility.remu addr (ZToReg 4) /=
                                                                           ZToReg 0) : bool
                                                                       then Spec.Machine.raiseExceptionWithInfo (ZToReg
                                                                                                                 0)
                                                                            (ZToReg 0) (id addr)
                                                                       else Spec.Machine.setPC addr))))
    | Spec.Decode.Lb rd rs1 oimm12 =>
        Bind (Spec.Machine.getRegister rs1) (fun a =>
                Bind (Spec.VirtualMemory.translate Spec.Machine.Load (ZToReg 1) (a +
                                                    Utility.Utility.fromImm oimm12)) (fun addr =>
                        Bind (Spec.Machine.loadByte Spec.Machine.Execute addr) (fun x =>
                                Spec.Machine.setRegister rd (Utility.Utility.int8ToReg x))))
    | Spec.Decode.Lh rd rs1 oimm12 =>
        Bind (Spec.Machine.getRegister rs1) (fun a =>
                Bind (Spec.VirtualMemory.translate Spec.Machine.Load (ZToReg 2) (a +
                                                    Utility.Utility.fromImm oimm12)) (fun addr =>
                        Bind (Spec.Machine.loadHalf Spec.Machine.Execute addr) (fun x =>
                                Spec.Machine.setRegister rd (Utility.Utility.int16ToReg x))))
    | Spec.Decode.Lw rd rs1 oimm12 =>
        Bind (Spec.Machine.getRegister rs1) (fun a =>
                Bind (Spec.VirtualMemory.translate Spec.Machine.Load (ZToReg 4) (a +
                                                    Utility.Utility.fromImm oimm12)) (fun addr =>
                        Bind (Spec.Machine.loadWord Spec.Machine.Execute addr) (fun x =>
                                Spec.Machine.setRegister rd (Utility.Utility.int32ToReg x))))
    | Spec.Decode.Lbu rd rs1 oimm12 =>
        Bind (Spec.Machine.getRegister rs1) (fun a =>
                Bind (Spec.VirtualMemory.translate Spec.Machine.Load (ZToReg 1) (a +
                                                    Utility.Utility.fromImm oimm12)) (fun addr =>
                        Bind (Spec.Machine.loadByte Spec.Machine.Execute addr) (fun x =>
                                Spec.Machine.setRegister rd (Utility.Utility.uInt8ToReg x))))
    | Spec.Decode.Lhu rd rs1 oimm12 =>
        Bind (Spec.Machine.getRegister rs1) (fun a =>
                Bind (Spec.VirtualMemory.translate Spec.Machine.Load (ZToReg 2) (a +
                                                    Utility.Utility.fromImm oimm12)) (fun addr =>
                        Bind (Spec.Machine.loadHalf Spec.Machine.Execute addr) (fun x =>
                                Spec.Machine.setRegister rd (Utility.Utility.uInt16ToReg x))))
    | Spec.Decode.Sb rs1 rs2 simm12 =>
        Bind (Spec.Machine.getRegister rs1) (fun a =>
                Bind (Spec.VirtualMemory.translate Spec.Machine.Store (ZToReg 1) (a +
                                                    Utility.Utility.fromImm simm12)) (fun addr =>
                        Bind (Spec.Machine.getRegister rs2) (fun x =>
                                Spec.Machine.storeByte Spec.Machine.Execute addr (Utility.Utility.regToInt8
                                                                                  x))))
    | Spec.Decode.Sh rs1 rs2 simm12 =>
        Bind (Spec.Machine.getRegister rs1) (fun a =>
                Bind (Spec.VirtualMemory.translate Spec.Machine.Store (ZToReg 2) (a +
                                                    Utility.Utility.fromImm simm12)) (fun addr =>
                        Bind (Spec.Machine.getRegister rs2) (fun x =>
                                Spec.Machine.storeHalf Spec.Machine.Execute addr (Utility.Utility.regToInt16
                                                                                  x))))
    | Spec.Decode.Sw rs1 rs2 simm12 =>
        Bind (Spec.Machine.getRegister rs1) (fun a =>
                Bind (Spec.VirtualMemory.translate Spec.Machine.Store (ZToReg 4) (a +
                                                    Utility.Utility.fromImm simm12)) (fun addr =>
                        Bind (Spec.Machine.getRegister rs2) (fun x =>
                                Spec.Machine.storeWord Spec.Machine.Execute addr (Utility.Utility.regToInt32
                                                                                  x))))
    | Spec.Decode.Addi rd rs1 imm12 =>
        Bind (Spec.Machine.getRegister rs1) (fun x =>
                Spec.Machine.setRegister rd (x + Utility.Utility.fromImm imm12))
    | Spec.Decode.Slti rd rs1 imm12 =>
        Bind (Spec.Machine.getRegister rs1) (fun x =>
                let val :=
                  (if x < Utility.Utility.fromImm imm12 : bool
                   then ZToReg 1
                   else ZToReg 0) in
                Spec.Machine.setRegister rd val)
    | Spec.Decode.Sltiu rd rs1 imm12 =>
        Bind (Spec.Machine.getRegister rs1) (fun x =>
                let val :=
                  (if (Utility.Utility.ltu x (Utility.Utility.fromImm imm12)) : bool
                   then ZToReg 1
                   else ZToReg 0) in
                Spec.Machine.setRegister rd val)
    | Spec.Decode.Xori rd rs1 imm12 =>
        Bind (Spec.Machine.getRegister rs1) (fun x =>
                Spec.Machine.setRegister rd (xor x (Utility.Utility.fromImm imm12)))
    | Spec.Decode.Ori rd rs1 imm12 =>
        Bind (Spec.Machine.getRegister rs1) (fun x =>
                Spec.Machine.setRegister rd (or x (Utility.Utility.fromImm imm12)))
    | Spec.Decode.Andi rd rs1 imm12 =>
        Bind (Spec.Machine.getRegister rs1) (fun x =>
                Spec.Machine.setRegister rd (and x (Utility.Utility.fromImm imm12)))
    | Spec.Decode.Slli rd rs1 shamt6 =>
        Bind (Spec.Machine.getRegister rs1) (fun x =>
                Spec.Machine.setRegister rd (Utility.Utility.sll x shamt6))
    | Spec.Decode.Srli rd rs1 shamt6 =>
        Bind (Spec.Machine.getRegister rs1) (fun x =>
                Spec.Machine.setRegister rd (Utility.Utility.srl x shamt6))
    | Spec.Decode.Srai rd rs1 shamt6 =>
        Bind (Spec.Machine.getRegister rs1) (fun x =>
                Spec.Machine.setRegister rd (Utility.Utility.sra x shamt6))
    | Spec.Decode.Add rd rs1 rs2 =>
        Bind (Spec.Machine.getRegister rs1) (fun x =>
                Bind (Spec.Machine.getRegister rs2) (fun y =>
                        Spec.Machine.setRegister rd (x + y)))
    | Spec.Decode.Sub rd rs1 rs2 =>
        Bind (Spec.Machine.getRegister rs1) (fun x =>
                Bind (Spec.Machine.getRegister rs2) (fun y =>
                        Spec.Machine.setRegister rd (x - y)))
    | Spec.Decode.Sll rd rs1 rs2 =>
        Bind (Spec.Machine.getRegister rs1) (fun x =>
                Bind (Spec.Machine.getRegister rs2) (fun y =>
                        Spec.Machine.setRegister rd (Utility.Utility.sll x (Utility.Utility.regToShamt
                                                                            y))))
    | Spec.Decode.Slt rd rs1 rs2 =>
        Bind (Spec.Machine.getRegister rs1) (fun x =>
                Bind (Spec.Machine.getRegister rs2) (fun y =>
                        let val := if x < y : bool then ZToReg 1 else ZToReg 0 in
                        Spec.Machine.setRegister rd val))
    | Spec.Decode.Sltu rd rs1 rs2 =>
        Bind (Spec.Machine.getRegister rs1) (fun x =>
                Bind (Spec.Machine.getRegister rs2) (fun y =>
                        let val := if Utility.Utility.ltu x y : bool then ZToReg 1 else ZToReg 0 in
                        Spec.Machine.setRegister rd val))
    | Spec.Decode.Xor rd rs1 rs2 =>
        Bind (Spec.Machine.getRegister rs1) (fun x =>
                Bind (Spec.Machine.getRegister rs2) (fun y =>
                        Spec.Machine.setRegister rd (xor x y)))
    | Spec.Decode.Or rd rs1 rs2 =>
        Bind (Spec.Machine.getRegister rs1) (fun x =>
                Bind (Spec.Machine.getRegister rs2) (fun y =>
                        Spec.Machine.setRegister rd (or x y)))
    | Spec.Decode.Srl rd rs1 rs2 =>
        Bind (Spec.Machine.getRegister rs1) (fun x =>
                Bind (Spec.Machine.getRegister rs2) (fun y =>
                        Spec.Machine.setRegister rd (Utility.Utility.srl x (Utility.Utility.regToShamt
                                                                            y))))
    | Spec.Decode.Sra rd rs1 rs2 =>
        Bind (Spec.Machine.getRegister rs1) (fun x =>
                Bind (Spec.Machine.getRegister rs2) (fun y =>
                        Spec.Machine.setRegister rd (Utility.Utility.sra x (Utility.Utility.regToShamt
                                                                            y))))
    | Spec.Decode.And rd rs1 rs2 =>
        Bind (Spec.Machine.getRegister rs1) (fun x =>
                Bind (Spec.Machine.getRegister rs2) (fun y =>
                        Spec.Machine.setRegister rd (and x y)))
    | Spec.Decode.Fence pred succ => Spec.Machine.fence pred succ
    | Spec.Decode.Fence_i => Return tt
    | inst => Return tt
    end.

(* External variables:
     Bind Return Type ZToReg and bool id lnot negb op_zgze__ op_zl__ op_zm__ op_zp__
     op_zsze__ or reg_eqb tt unit when xor Spec.Decode.Add Spec.Decode.Addi
     Spec.Decode.And Spec.Decode.Andi Spec.Decode.Auipc Spec.Decode.Beq
     Spec.Decode.Bge Spec.Decode.Bgeu Spec.Decode.Blt Spec.Decode.Bltu
     Spec.Decode.Bne Spec.Decode.Fence Spec.Decode.Fence_i Spec.Decode.InstructionI
     Spec.Decode.Jal Spec.Decode.Jalr Spec.Decode.Lb Spec.Decode.Lbu Spec.Decode.Lh
     Spec.Decode.Lhu Spec.Decode.Lui Spec.Decode.Lw Spec.Decode.Or Spec.Decode.Ori
     Spec.Decode.Sb Spec.Decode.Sh Spec.Decode.Sll Spec.Decode.Slli Spec.Decode.Slt
     Spec.Decode.Slti Spec.Decode.Sltiu Spec.Decode.Sltu Spec.Decode.Sra
     Spec.Decode.Srai Spec.Decode.Srl Spec.Decode.Srli Spec.Decode.Sub Spec.Decode.Sw
     Spec.Decode.Xor Spec.Decode.Xori Spec.Machine.Execute Spec.Machine.Load
     Spec.Machine.RiscvMachine Spec.Machine.Store Spec.Machine.fence
     Spec.Machine.getPC Spec.Machine.getRegister Spec.Machine.loadByte
     Spec.Machine.loadHalf Spec.Machine.loadWord Spec.Machine.raiseExceptionWithInfo
     Spec.Machine.setPC Spec.Machine.setRegister Spec.Machine.storeByte
     Spec.Machine.storeHalf Spec.Machine.storeWord Spec.VirtualMemory.translate
     Utility.Utility.fromImm Utility.Utility.int16ToReg Utility.Utility.int32ToReg
     Utility.Utility.int8ToReg Utility.Utility.ltu Utility.Utility.regToInt16
     Utility.Utility.regToInt32 Utility.Utility.regToInt8 Utility.Utility.regToShamt
     Utility.Utility.remu Utility.Utility.sll Utility.Utility.sra Utility.Utility.srl
     Utility.Utility.uInt16ToReg Utility.Utility.uInt8ToReg
*)
