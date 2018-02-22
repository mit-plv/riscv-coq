Require Import Coq.ZArith.BinInt.
Require Import Coq.Bool.Sumbool.
Require Import bbv.WordScope.
Require Import bbv.DepEqNat.
Require Import riscv.util.NameWithEq.
Require Import riscv.RiscvBitWidths.
Require Import riscv.util.Monad.
Require Import riscv.Decode.
Require Import riscv.Program.

Arguments sumbool_not {_} {_} (_).

Open Scope Z_scope.

Section comparisons.

  Context {sz: nat}.
  Variable a b: word sz.

  (* a >= b <-> b <= a <-> ~ b > a <-> ~ a < b *)
  Definition wge_dec := sumbool_not (wlt_dec a b).

  (* a > b <-> b < a *)
  Definition wgt_dec := wlt_dec b a.

  (* a <= b <-> ~ b < a *)
  Definition wle_dec := sumbool_not (wlt_dec b a).

  (* a >= b <-> b <= a <-> ~ b > a <-> ~ a < b *)
  Definition wsge_dec := sumbool_not (wslt_dec a b).

  (* a > b <-> b < a *)
  Definition wsgt_dec := wslt_dec b a.

  (* a <= b <-> ~ b < a *)
  Definition wsle_dec := sumbool_not (wslt_dec b a).

End comparisons.


Section Riscv.

  Context {Name: NameWithEq}. (* register name *)
  Notation Register := (@name Name).
  Existing Instance eq_name_dec.

  Context {B: RiscvBitWidths}.

  Context {t Imm: Set}.

  Context {A: Alu t}.

  Context {c: IntegralConversion Imm t}.

  (* interpret this word as a signed number *)
  Definition signed: word wXLEN -> Z := @wordToZ wXLEN.

  (* interpret this word as an unsigned number *)
  Definition unsigned(w: word wXLEN): Z := Z.of_N (wordToN w).

  (* can be used for obtaining both signed and unsigned numbers *)
  Definition fromZ: Z -> word wXLEN := ZToWord wXLEN.

  (* Design note: PC is an unsigned number, but we often need to add a signed
     number to it, so we prefer using Z for everything (rather than also using N),
     but need a way to say that PC is to be interpreted as a signed number. *)

(*
  Definition toN: word wXLEN -> N := @wordToN wXLEN.

  Definition fromN: N -> word wXLEN := NToWord wXLEN.

  Definition treat_signed_as_unsigned(a: Z): N := match a with
    | Z0 => N0
    | Zpos p => Npos p
    | Zneg p => (Npow2 wXLEN - Npos p)%N
    end.
*)
  Definition treat_signed_as_unsigned(a: Z): Z := match a with
    | Z0 => Z0
    | Zpos p => Zpos p
    | Zneg p => (Zpower.two_power_nat wXLEN - Zpos p)
    end.

(*
  Definition fromByte(w: word 8): word wXLEN.
    refine (nat_cast _ _ (sext w (wXLEN - 8))). abstract bitwidth_omega.
  Defined.

  Definition fromHalf(w: word 16): word wXLEN.
    refine (nat_cast _ _ (sext w (wXLEN - 16))). abstract bitwidth_omega.
  Defined.

  Definition fromWord(w: word 32): word wXLEN.
    refine (nat_cast _ _ (sext w (wXLEN - 32))). abstract bitwidth_omega.
  Defined.

  Definition fromByteU(w: word 8): word wXLEN.
    refine (nat_cast _ _ (zext w (wXLEN - 8))). abstract bitwidth_omega.
  Defined.

  Definition fromHalfU(w: word 16): word wXLEN.
    refine (nat_cast _ _ (zext w (wXLEN - 16))). abstract bitwidth_omega.
  Defined.

  Definition fromWordU(w: word 32): word wXLEN.
    refine (nat_cast _ _ (zext w (wXLEN - 32))). abstract bitwidth_omega.
  Defined.

  Definition toByte(w: word wXLEN): word 8.
    refine (split_lower (wXLEN - 8) 8 (nat_cast _ _ w)). abstract bitwidth_omega.
  Defined.

  Definition toHalf(w: word wXLEN): word 16.
    refine (split_lower (wXLEN - 16) 16 (nat_cast _ _ w)). abstract bitwidth_omega.
  Defined.

  Definition toWord(w: word wXLEN): word 32.
    refine (split_lower (wXLEN - 32) 32 (nat_cast _ _ w)). abstract bitwidth_omega.
  Defined.
*)

  Context {ic8: IntegralConversion (word 8) t}.

  (* TODO *)
  Definition raiseException{M: Type -> Type}{MM: Monad M}(x1 x2: word wXLEN): M unit := Return tt.

  Definition execute{M: Type -> Type}{MM: Monad M}{RVS: RiscvState M}(i: Instruction Imm): M unit :=
    match i with
(*
    | Lui rd imm20 =>
      ( ( setRegister rd ) (fromZ imm20) )
    | Auipc rd oimm20 =>
      pc <- getPC;
        (* note: don't go directly from pc to Z, because pc cannot be negative *)
        ( ( setRegister rd ) (fromZ (oimm20 + unsigned pc)) )
    | Jal rd jimm20 =>
      pc <- getPC;
        let newPC := (unsigned pc + (  jimm20 )) in
        (if dec (Z.modulo newPC 4 <> 0)
         then ( ( raiseException $0 ) $0 )
         else ( ( setRegister rd ) (fromZ (unsigned pc + 4)));;
                                                    ( setPC (fromZ newPC) ))
    | Jalr rd rs1 oimm12 =>
      x <- ( getRegister rs1 );
        pc <- getPC;
        let newPC := (unsigned x + (  oimm12 )) in
        (if dec (Z.modulo newPC 4 <> 0)
         then ( ( raiseException $0 ) $0 )
         else ( ( setRegister rd ) (fromZ (unsigned pc + 4)));;
                                                    ( setPC (fromZ newPC) ))
    | Beq rs1 rs2 sbimm12 =>
      x <- ( getRegister rs1 );
        y <- ( getRegister rs2 );
        pc <- getPC;
        (if (weq x y)
         then let newPC := (unsigned pc + (  sbimm12 )) in
              (if dec (Z.modulo newPC 4 <> 0)
               then ( ( raiseException $0 ) $0 )
               else ( setPC (fromZ newPC) ))
         else (Return tt))
    | Bne rs1 rs2 sbimm12 =>
      x <- ( getRegister rs1 );
        y <- ( getRegister rs2 );
        pc <- getPC;
        (if dec (x <> y)
         then let addr := (unsigned pc + (  sbimm12 )) in
              (if dec (Z.modulo addr 4 <> 0)
               then ( ( raiseException $0 ) $0 )
               else ( setPC (fromZ addr) ))
         else (Return tt))
    | Blt rs1 rs2 sbimm12 =>
      x <- ( getRegister rs1 );
        y <- ( getRegister rs2 );
        pc <- getPC;
        (if (wslt_dec x y)
         then let addr := (unsigned pc + (  sbimm12 )) in
              (if dec (Z.modulo addr 4 <> 0)
               then ( ( raiseException $0 ) $0 )
               else ( setPC (fromZ addr) ))
         else (Return tt))
    | Bge rs1 rs2 sbimm12 =>
      x <- ( getRegister rs1 );
        y <- ( getRegister rs2 );
        pc <- getPC;
        (if (wsge_dec x y)
         then let addr := (unsigned pc + (  sbimm12 )) in
              (if dec (Z.modulo addr 4 <> 0)
               then ( ( raiseException $0 ) $0 )
               else ( setPC (fromZ addr) ))
         else (Return tt))
    | Bltu rs1 rs2 sbimm12 =>
      x <- ( getRegister rs1 );
        y <- ( getRegister rs2 );
        pc <- getPC;
        (if ( ( wlt_dec x ) y )
         then let addr := (unsigned pc + (  sbimm12 )) in
              (if dec (Z.modulo addr 4 <> 0)
               then ( ( raiseException $0 ) $0 )
               else ( setPC (fromZ addr) ))
         else (Return tt))
    | Bgeu rs1 rs2 sbimm12 =>
      x <- ( getRegister rs1 );
        y <- ( getRegister rs2 );
        pc <- getPC;
        (if ( Sumbool.sumbool_not ( ( wlt_dec x ) y ) )
         then let addr := (unsigned pc + (  sbimm12 )) in
              (if dec (Z.modulo addr 4 <> 0)
               then ( ( raiseException $0 ) $0 )
               else ( setPC (fromZ addr) ))
         else (Return tt))
*)

     | Lb rd rs1 oimm12 => 
         a <- getRegister rs1; 
         x <- loadByte (add a (fromIntegral oimm12)); 
         setRegister rd x
(*
     | Lh rd rs1 oimm12 => 
     a <- ( getRegister rs1 ); 
     let addr := (unsigned a + (  oimm12 )) in 
     (if dec (Z.modulo addr 2 <> 0)
      then ( ( raiseException $0 ) $4 ) 
      else x <- ( loadHalf addr ); 
     ( ( setRegister rd ) (fromHalf x) )) 
     | Lw rd rs1 oimm12 => 
     a <- ( getRegister rs1 ); 
     let addr := (unsigned a + (  oimm12 )) in 
     (if dec (Z.modulo addr 4 <> 0)
      then ( ( raiseException $0 ) $4 ) 
      else x <- ( loadWord addr ); 
     ( ( setRegister rd ) (fromWord x) )) 
     | Lbu rd rs1 oimm12 => 
     a <- ( getRegister rs1 ); 
     x <- ( loadByte (unsigned a + (  oimm12 )) ); 
     ( ( setRegister rd ) (fromByteU x ) ) 
     | Lhu rd rs1 oimm12 => 
     a <- ( getRegister rs1 ); 
     let addr := (unsigned a + (  oimm12 )) in 
     (if dec (Z.modulo addr 2 <> 0)
      then ( ( raiseException $0 ) $4 ) 
      else x <- ( loadHalf addr ); 
     ( ( setRegister rd ) (fromHalfU  x ) )) 
     | Sb rs1 rs2 simm12 => 
     a <- ( getRegister rs1 ); 
     x <- ( getRegister rs2 ); 
     ( ( storeByte (unsigned a + (  simm12 )) ) (toByte x) ) 
     | Sh rs1 rs2 simm12 => 
     a <- ( getRegister rs1 ); 
     let addr := (unsigned a + (  simm12 )) in 
     (if dec (Z.modulo addr 2 <> 0)
      then ( ( raiseException $0 ) $6 ) 
      else x <- ( getRegister rs2 ); 
     ( ( storeHalf addr ) (toHalf x) )) 
     | Sw rs1 rs2 simm12 => 
     a <- ( getRegister rs1 ); 
     let addr := (unsigned a + (  simm12 )) in 
     (if dec (Z.modulo addr 4 <> 0)
      then ( ( raiseException $0 ) $6 ) 
      else x <- ( getRegister rs2 ); 
     ( ( storeWord addr ) (toWord x) ))
    | Addi rd rs1 imm12 =>
      x <- ( getRegister rs1 );
        ( ( setRegister rd ) (fromZ (signed x + (  imm12 )) ))
         (* signed or unsigned doesn't matter here, meh *)
    | Slti rd rs1 imm12 =>
      x <- ( getRegister rs1 );
        ( ( setRegister rd ) (if dec (signed x < imm12)
                              then $1
                              else $0) )
    | Sltiu rd rs1 imm12 =>
      x <- ( getRegister rs1 );
        ( ( setRegister rd ) (if dec (unsigned x < treat_signed_as_unsigned imm12)%N
                              then $1
                              else $0) )
    | Xori rd rs1 imm12 =>
      x <- ( getRegister rs1 );
        (* signed should have the same result after casting back to word *)
        ( ( setRegister rd ) (fromZ (Z.lxor (unsigned x) imm12))) (* TODO that's awkward *)
    | Ori rd rs1 imm12 =>
      x <- ( getRegister rs1 );
        ( ( setRegister rd ) (fromZ (Z.lor (unsigned x) imm12)))
    | Andi rd rs1 imm12 =>
      x <- ( getRegister rs1 );
        ( ( setRegister rd ) (fromZ (Z.land (unsigned x) imm12)))
    | Slli rd rs1 shamt6 =>
      x <- ( getRegister rs1 );
        ( ( setRegister rd ) ( ( wlshift x ) shamt6 ) )
    | Srli rd rs1 shamt6 =>
      x <- ( getRegister rs1 );
        ( ( setRegister rd ) ( ( wrshift x ) shamt6 ) )
    | Srai rd rs1 shamt6 =>
      x <- ( getRegister rs1 );
        ( ( setRegister rd ) ( ( wrshifta x ) shamt6 ) )
    | Add rd rs1 rs2 =>
      x <- ( getRegister rs1 );
        y <- ( getRegister rs2 );
        ( ( setRegister rd ) (fromZ (unsigned x + unsigned y)) ) (* TODO or directly on word? *)
    | Sub rd rs1 rs2 =>
      x <- ( getRegister rs1 );
        y <- ( getRegister rs2 );
        ( ( setRegister rd ) (fromZ (unsigned x - unsigned y)) )
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
*)
    | _ => Return tt
    end.


End Riscv.

Close Scope Z_scope.
