Require Import bbv.WordScope.
Require Import bbv.DepEqNat.
Require Import riscv.NameWithEq.
Require Import riscv.RiscvBitWidths.
Require Import riscv.Monad.
Require Import riscv.Decode.
Require Import riscv.Program.

Require Import Sumbool.
(* Comments between ``double quotes'' are from quotes from
   The RISC-V Instruction Set Manual
   Volume I: User-Level ISA
   Document Version 2.2
*)

Section Riscv.

  Context {B: RiscvBitWidths}.

  Context {Name: NameWithEq}. (* register name *)
  Notation Reg := (@name Name).
  Existing Instance eq_name_dec.

  Definition signed_imm_to_word(v: word wimm): word wXLEN.
    refine (nat_cast word _ (sext v (wXLEN - wimm))). bitwidth_omega.
  Defined.

  Definition signed_jimm_to_word(v: word wupper): word wXLEN.
    refine (nat_cast word _ (sext (extz v 1) (wXLEN - wupper - 1))). bitwidth_omega.
  Defined.

  Definition signed_bimm_to_word(v: word wimm): word wXLEN.
    refine (nat_cast word _ (sext (extz v 1) (wXLEN - wimm - 1))). bitwidth_omega.
  Defined.

  Definition upper_imm_to_word(v: word wupper): word wXLEN.
    refine (nat_cast word _ (sext (extz v wimm) (wXLEN - wInstr))). bitwidth_omega.
  Defined.

  Axiom wneq: forall {sz:nat}, word sz -> word sz -> bool .
  Axiom raiseException: forall {M: Type -> Type}, word wXLEN -> word wXLEN -> M unit.
  Arguments sumbool_not {_} {_} (_).
  Print Return.
  Definition execute{M: Type -> Type}{MM: Monad M}{RVS: RiscvState M}(i: Instruction): M unit :=
    match i with
    | Lui rd imm20 =>
      ( ( setRegister rd ) imm20 )
    | Auipc rd oimm20 =>
      pc <- getPC;
        ( ( setRegister rd ) ((  oimm20 ) ^+ pc) )
    | Jal rd jimm20 =>
      pc <- getPC;
        let newPC := (pc ^+ (  jimm20 )) in
        (if (wneq ( ( wmod newPC ) $4 ) $0)
         then ( ( raiseException $0 ) $0 )
         else ( ( setRegister rd ) ((  pc ) ^+ $4) );;
                                                    ( setPC newPC ))
    | Jalr rd rs1 oimm12 =>
      x <- ( getRegister rs1 );
        pc <- getPC;
        let newPC := (x ^+ (  oimm12 )) in
        (if (wneq ( ( wmod newPC ) $4 ) $0)
         then ( ( raiseException $0 ) $0 )
         else ( ( setRegister rd ) ((  pc ) ^+ $4) );;
                                                    ( setPC newPC ))
    | Beq rs1 rs2 sbimm12 =>
      x <- ( getRegister rs1 );
        y <- ( getRegister rs2 );
        pc <- getPC;
        (if (weq x y)
         then let newPC := (pc ^+ (  sbimm12 )) in
              (if (wneq ( ( wmod newPC ) $4 ) $0)
               then ( ( raiseException $0 ) $0 )
               else ( setPC newPC ))
         else (Return tt))
    | Bne rs1 rs2 sbimm12 =>
      x <- ( getRegister rs1 );
        y <- ( getRegister rs2 );
        pc <- getPC;
        (if (wneq x y)
         then let addr := (pc ^+ (  sbimm12 )) in
              (if (wneq ( ( wmod addr ) $4 ) $0)
               then ( ( raiseException $0 ) $0 )
               else ( setPC addr ))
         else (Return tt))
    | Blt rs1 rs2 sbimm12 =>
      x <- ( getRegister rs1 );
        y <- ( getRegister rs2 );
        pc <- getPC;
        (if (wslt_dec x y)
         then let addr := (pc ^+ (  sbimm12 )) in
              (if (wneq ( ( wmod addr ) $4 ) $0)
               then ( ( raiseException $0 ) $0 )
               else ( setPC addr ))
         else (Return tt))
    | Bge rs1 rs2 sbimm12 =>
      x <- ( getRegister rs1 );
        y <- ( getRegister rs2 );
        pc <- getPC;
        (if (wsge_dec x y)
         then let addr := (pc ^+ (  sbimm12 )) in
              (if (wneq ( ( wmod addr ) $4 ) $0)
               then ( ( raiseException $0 ) $0 )
               else ( setPC addr ))
         else (Return tt))
    | Bltu rs1 rs2 sbimm12 =>
      x <- ( getRegister rs1 );
        y <- ( getRegister rs2 );
        pc <- getPC;
        (if ( ( wlt_dec x ) y )
         then let addr := (pc ^+ (  sbimm12 )) in
              (if (wneq ( ( wmod addr ) $4 ) $0)
               then ( ( raiseException $0 ) $0 )
               else ( setPC addr ))
         else (Return tt))
    | Bgeu rs1 rs2 sbimm12 =>
      x <- ( getRegister rs1 );
        y <- ( getRegister rs2 );
        pc <- getPC;
        (if ( Sumbool.sumbool_not ( ( wlt_dec x ) y ) )
         then let addr := (pc ^+ (  sbimm12 )) in
              (if (wneq ( ( wmod addr ) $4 ) $0)
               then ( ( raiseException $0 ) $0 )
               else ( setPC addr ))
         else (Return tt))
    (* | Lb rd rs1 oimm12 => *)
    (* a <- ( getRegister rs1 ); *)
    (* x <- ( loadByte (a ^+ (  oimm12 )) ); *)
    (* ( ( setRegister rd ) x ) *)
    (* | Lh rd rs1 oimm12 => *)
    (* a <- ( getRegister rs1 ); *)
    (* let addr := (a ^+ (  oimm12 )) in *)
    (* (if (wneq ( ( wmod addr ) $2 ) $0) *)
    (*  then ( ( raiseException $0 ) $4 ) *)
    (*  else x <- ( loadHalf addr ); *)
    (* ( ( setRegister rd ) x )) *)
    (* | Lw rd rs1 oimm12 => *)
    (* a <- ( getRegister rs1 ); *)
    (* let addr := (a ^+ (  oimm12 )) in *)
    (* (if (wneq ( ( wmod addr ) $4 ) $0) *)
    (*  then ( ( raiseException $0 ) $4 ) *)
    (*  else x <- ( loadWord addr ); *)
    (* ( ( setRegister rd ) x )) *)
    (* | Lbu rd rs1 oimm12 => *)
    (* a <- ( getRegister rs1 ); *)
    (* x <- ( loadByte (a ^+ (  oimm12 )) ); *)
    (* ( ( setRegister rd ) (  x ) ) *)
    (* | Lhu rd rs1 oimm12 => *)
    (* a <- ( getRegister rs1 ); *)
    (* let addr := (a ^+ (  oimm12 )) in *)
    (* (if (wneq ( ( wmod addr ) $2 ) $0) *)
    (*  then ( ( raiseException $0 ) $4 ) *)
    (*  else x <- ( loadHalf addr ); *)
    (* ( ( setRegister rd ) (  x ) )) *)
    (* | Sb rs1 rs2 simm12 => *)
    (* a <- ( getRegister rs1 ); *)
    (* x <- ( getRegister rs2 ); *)
    (* ( ( storeByte (a ^+ (  simm12 )) ) x ) *)
    (* | Sh rs1 rs2 simm12 => *)
    (* a <- ( getRegister rs1 ); *)
    (* let addr := (a ^+ (  simm12 )) in *)
    (* (if (wneq ( ( wmod addr ) $2 ) $0) *)
    (*  then ( ( raiseException $0 ) $6 ) *)
    (*  else x <- ( getRegister rs2 ); *)
    (* ( ( storeHalf addr ) x )) *)
    (* | Sw rs1 rs2 simm12 => *)
    (* a <- ( getRegister rs1 ); *)
    (* let addr := (a ^+ (  simm12 )) in *)
    (* (if (wneq ( ( wmod addr ) $4 ) $0) *)
    (*  then ( ( raiseException $0 ) $6 ) *)
    (*  else x <- ( getRegister rs2 ); *)
    (* ( ( storeWord addr ) x )) *)
    | Addi rd rs1 imm12 =>
      x <- ( getRegister rs1 );
        ( ( setRegister rd ) (x ^+ (  imm12 )) )
    | Slti rd rs1 imm12 =>
      x <- ( getRegister rs1 );
        ( ( setRegister rd ) (if (wslt_dec x (  imm12 ))
                              then $1
                              else $0) )
    | Sltiu rd rs1 imm12 =>
      x <- ( getRegister rs1 );
        ( ( setRegister rd ) (if ( ( wlt_dec x ) imm12 )
                              then $1
                              else $0) )
    | Xori rd rs1 imm12 =>
      x <- ( getRegister rs1 );
        ( ( setRegister rd ) ( ( wxor x ) (  imm12 ) ) )
    | Ori rd rs1 imm12 =>
      x <- ( getRegister rs1 );
        ( ( setRegister rd ) (wor x (  imm12 )) )
    | Andi rd rs1 imm12 =>
      x <- ( getRegister rs1 );
        ( ( setRegister rd ) (wand x (  imm12 )) )
    | Slli rd rs1 shamt6 =>
      x <- ( getRegister rs1 );
        ( ( setRegister rd ) ( ( wlshift x ) (wordToNat shamt6) ) )
    | Srli rd rs1 shamt6 =>
      x <- ( getRegister rs1 );
        ( ( setRegister rd ) ( ( wrshift x ) (wordToNat shamt6) ) )
    | Srai rd rs1 shamt6 =>
      x <- ( getRegister rs1 );
        ( ( setRegister rd ) ( ( wrshifta x ) (wordToNat shamt6) ) )
    | Add rd rs1 rs2 =>
      x <- ( getRegister rs1 );
        y <- ( getRegister rs2 );
        ( ( setRegister rd ) (x ^+ y) )
    | Sub rd rs1 rs2 =>
      x <- ( getRegister rs1 );
        y <- ( getRegister rs2 );
        ( ( setRegister rd ) (x ^- y) )
    | Sll rd rs1 rs2 =>
      x <- ( getRegister rs1 );
        y <- ( getRegister rs2 );
        ( ( setRegister rd ) ( ( wlshift x ) (wordToNat y) ) )
    | Slt rd rs1 rs2 =>
      x <- ( getRegister rs1 );
        y <- ( getRegister rs2 );
        ( ( setRegister rd ) (if (wslt_dec x y)
                              then $1
                              else $0) )
    | Sltu rd rs1 rs2 =>
      x <- ( getRegister rs1 );
        y <- ( getRegister rs2 );
        ( ( setRegister rd ) (if ( ( wlt_dec x ) y )
                              then $1
                              else $0) )
    | Xor rd rs1 rs2 =>
      x <- ( getRegister rs1 );
        y <- ( getRegister rs2 );
        ( ( setRegister rd ) ( ( wxor x ) y ) )
    | Or rd rs1 rs2 =>
      x <- ( getRegister rs1 );
        y <- ( getRegister rs2 );
        ( ( setRegister rd ) (wor x y) )
    | Srl rd rs1 rs2 =>
      x <- ( getRegister rs1 );
        y <- ( getRegister rs2 );
        ( ( setRegister rd ) ( ( wrshift x ) (wordToNat y) ) )
    | Sra rd rs1 rs2 =>
      x <- ( getRegister rs1 );
        y <- ( getRegister rs2 );
        ( ( setRegister rd ) ( ( wrshifta x ) (wordToNat y) ) )
    | And rd rs1 rs2 =>
      x <- ( getRegister rs1 );
        y <- ( getRegister rs2 );
        ( ( setRegister rd ) (wand x y) )
    | _ => Return tt
    end.


End Riscv.
