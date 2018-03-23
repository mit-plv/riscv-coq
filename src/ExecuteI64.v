(* Default settings (from HsToCoq.Coq.Preamble) *)

Generalizable All Variables.

Unset Implicit Arguments.
Set Maximal Implicit Insertion.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Coq.Program.Tactics.
Require Coq.Program.Wf.

(* Preamble *)

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
   : Decode.InstructionI64 -> p unit :=
  fun arg_0__ =>
    match arg_0__ with
    | Decode.Lwu rd rs1 oimm12 =>
        Bind (getRegister rs1) (fun a =>
                Bind (translate Load four (a + fromImm oimm12)) (fun addr =>
                        Bind (loadWord addr) (fun x => setRegister rd (uInt32ToReg x))))
    | Decode.Ld rd rs1 oimm12 =>
        Bind (getRegister rs1) (fun a =>
                Bind (translate Load eight (a + fromImm oimm12)) (fun addr =>
                        Bind (loadDouble addr) (fun x => setRegister rd (int64ToReg x))))
    | Decode.Sd rs1 rs2 simm12 =>
        Bind (getRegister rs1) (fun a =>
                Bind (translate Store eight (a + fromImm simm12)) (fun addr =>
                        Bind (getRegister rs2) (fun x => storeDouble addr (regToInt64 x))))
    | Decode.Addiw rd rs1 imm12 =>
        Bind (getRegister rs1) (fun x => setRegister rd (s32 (x + fromImm imm12)))
    | Decode.Slliw rd rs1 shamt5 =>
        Bind (getRegister rs1) (fun x => setRegister rd (s32 (sll x shamt5)))
    | Decode.Srliw rd rs1 shamt5 =>
        Bind (getRegister rs1) (fun x => setRegister rd (s32 (srl (u32 x) shamt5)))
    | Decode.Sraiw rd rs1 shamt5 =>
        Bind (getRegister rs1) (fun x => setRegister rd (s32 (sra (s32 x) shamt5)))
    | Decode.Addw rd rs1 rs2 =>
        Bind (getRegister rs1) (fun x =>
                Bind (getRegister rs2) (fun y => setRegister rd (s32 (x + y))))
    | Decode.Subw rd rs1 rs2 =>
        Bind (getRegister rs1) (fun x =>
                Bind (getRegister rs2) (fun y => setRegister rd (s32 (x - y))))
    | Decode.Sllw rd rs1 rs2 =>
        Bind (getRegister rs1) (fun x =>
                Bind (getRegister rs2) (fun y => setRegister rd (s32 (sll x (regToShamt5 y)))))
    | Decode.Srlw rd rs1 rs2 =>
        Bind (getRegister rs1) (fun x =>
                Bind (getRegister rs2) (fun y =>
                        setRegister rd (s32 (srl (u32 x) (regToShamt5 y)))))
    | Decode.Sraw rd rs1 rs2 =>
        Bind (getRegister rs1) (fun x =>
                Bind (getRegister rs2) (fun y =>
                        setRegister rd (s32 (sra (s32 x) (regToShamt5 y)))))
    | inst => Return tt
    end.

(* Unbound variables:
     Bind Load Return RiscvState Store eight four fromImm getRegister int64ToReg
     loadDouble loadWord op_zm__ op_zp__ regToInt64 regToShamt5 s32 setRegister sll
     sra srl storeDouble translate tt u32 uInt32ToReg unit Decode.Addiw Decode.Addw
     Decode.InstructionI64 Decode.Ld Decode.Lwu Decode.Sd Decode.Slliw Decode.Sllw
     Decode.Sraiw Decode.Sraw Decode.Srliw Decode.Srlw Decode.Subw
*)
