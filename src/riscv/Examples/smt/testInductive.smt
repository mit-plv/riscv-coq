(declare-datatypes () ((unit tt)))
(declare-datatypes (T) ((option
  (Some (option_get T))
  None)))
(define-sort Z () Int)
(define-sort set (T) (Array T Bool))

; bitwidth-dependent word type
(define-sort word () (_ BitVec 32))

; bitwidth-independent word types
(define-sort w8 () (_ BitVec 8))
(define-sort w16 () (_ BitVec 16))
(define-sort w32 () (_ BitVec 32))
(define-sort w64 () (_ BitVec 64))

(define-sort ThreadId () Int)
(define-sort EventId () Int)

(declare-datatypes () ((Event
  (InitEvent (Loc_of_InitEvent word))
  (ThreadEvent (Tid_of_ThreadEvent ThreadId) (Iid_of_ThreadEvent EventId))
)))

(declare-datatypes () ((InstructionI
  (Lb (rd_of_Lb Z) (rs1_of_Lb Z) (oimm12_of_Lb Z))
  (Sb (rs1_of_Sb Z) (rs2_of_Sb Z) (simm12_of_Sb Z))
)))

; that's just the register name, needs to be between 0 and 32, value will be of type word
(define-sort Register () Int)
; register file:
(define-sort Registers () (Array Register word))

(declare-datatypes () ((ThreadState (mkThreadState
  (Regs Registers)
  (Pc word)
  (NextPc word)
  (Prog (Array Int InstructionI))
  (CurrentEvent Event)
  (Deps (Array Register (set Event)))
))))

(declare-datatypes () ((Label
  (ReadLabel (LabelReadLoc word))
  (WriteLabel (LabelWriteLoc word) (LabelVal w8))
  FenceLabel
  ErrorLabel)))

(declare-datatypes () ((Graph (mkGraph
  (Lab (Array Event (option Label)))
  (Rf (Array Event Event))
  (Addr (Array Event (set Event)))
  (Data (Array Event (set Event)))
  (Ctrl (Array Event (set Event)))
))))

(define-fun Loc00 ((G Graph) (e Event)) (option Label)
  (match (select (Lab G) e) (
    ((Some l) (match (Some l) (
                 ((Some ll) (Some ll))
                 (None None))))
    (None None))))

(define-fun LocOfLabel ((l Label)) (option word)
  (match l (
    ((ReadLabel x) (Some x))
    ((WriteLabel x v) (Some x))
    (FenceLabel (as None (option word)))
    (ErrorLabel (as None (option word))))))

(define-fun Loc001 ((G Graph) (e Event)) (option word)
  (match (select (Lab G) e) (
    ((Some theL) (LocOfLabel theL))
    (None None))))

(define-fun Loc ((G Graph) (e Event)) (option word)
  (match (select (Lab G) e) (
    ((Some ll) (match ll (
                ((ReadLabel x) (Some x))
                ((WriteLabel x v) (Some x))
                (FenceLabel None)
                (ErrorLabel None))))
    (None None))))

(declare-fun Val ((G Graph) (e Event)) (option w8)
  (match (select (Lab G) e) (
    ((Some l) (match l (
                ((ReadLabel x) None)
                ((WriteLabel x v) (Some v))
                (FenceLabel None)
                (ErrorLabel None))))
    (None None))))

(define-fun executeIsmall ((inst InstructionI) (s1 ThreadState) (s2 ThreadState)) bool
  (match inst (
    ((Lb rd rs1 oimm12) (= s1 s2))
    ((Sb rs1 rs2 simm12) (not (= s1 s2))))))

(declare-const nn Int)
(assert (exists ((a Int)) (and (< 2 a) (= nn (* a a)))))

(declare-const i1 InstructionI)
(declare-const i2 InstructionI)
(declare-const s ThreadState)
(assert (not (= i1 i2)))
(assert (executeIsmall i1 s s))

(define-fun getReg ((regs Registers) (reg Register)) word
  (ite (= reg 0) ((_ int2bv 32) 0) (select regs reg)))

(define-fun setReg ((regs Registers) (reg Register) (v word)) Registers
  (ite (= reg 0) regs (store regs reg v)))

(define-fun executeI ((G Graph) (inst InstructionI) (s1 ThreadState) (s2 ThreadState)) bool
  (match inst (   ( (Lb rd rs1
oimm12) (exists ( (_ unit)
         ) (and (= (select (Lab G) (CurrentEvent s1))
                 (Some (ReadLabel (bvadd (getReg (Regs s1) rs1) ((_ int2bv 32) oimm12)))))
            (exists ( (v0 w8)
             ) (and (= (Val G (select (Rf G) (CurrentEvent s1))) (Some v0))
                (and (=
                      (withRegs
                         (setReg (Regs s1) rd ((_ int2bv 32) (signExtend 8 (LittleEndian.combine 1 v0))))
                         (withCurrentEvent (NextEvent (CurrentEvent s1)) s1)) s2)
                 (= tt tt)))))))   ( (Lh _ _
_) (exists ( (_ unit)) (and (= (select (Lab G) (CurrentEvent s1)) (Some ErrorLabel)) (= s1 s2))))   ( (Lw _ _
_) (exists ( (_ unit)) (and (= (select (Lab G) (CurrentEvent s1)) (Some ErrorLabel)) (= s1 s2))))   ( (Lbu rd
rs1
oimm12) (exists ( (_ unit)
         ) (and (= (select (Lab G) (CurrentEvent s1))
                 (Some (ReadLabel (bvadd (getReg (Regs s1) rs1) ((_ int2bv 32) oimm12)))))
            (exists ( (v0 w8)
             ) (and (= (Val G (select (Rf G) (CurrentEvent s1))) (Some v0))
                (and (=
                      (withRegs (setReg (Regs s1) rd ((_ int2bv 32) (LittleEndian.combine 1 v0)))
                         (withCurrentEvent (NextEvent (CurrentEvent s1)) s1)) s2)
                 (= tt tt)))))))   ( (Lhu _ _
_) (exists ( (_ unit)) (and (= (select (Lab G) (CurrentEvent s1)) (Some ErrorLabel)) (= s1 s2))))   ( (Fence _
_) (and (= s1 s2) (= tt tt)))   ( (Fence_i ) (and (= s1 s2) (= tt tt)))   ( (Addi rd rs1
imm12) (and (= (withRegs (setReg (Regs s1) rd (bvadd (getReg (Regs s1) rs1) ((_ int2bv 32) imm12))) s1) s2)
        (= tt tt)))   ( (Slli rd rs1
shamt6) (and (= (withRegs (setReg (Regs s1) rd (word.slu (getReg (Regs s1) rs1) ((_ int2bv 32) shamt6))) s1)
              s2) (= tt tt)))   ( (Slti rd rs1
imm12) (and (=
             (withRegs
                (setReg (Regs s1) rd
                   (ite (bvlts (getReg (Regs s1) rs1) ((_ int2bv 32) imm12)) ((_ int2bv 32) 1)
                    ((_ int2bv 32) 0))) s1) s2) (= tt tt)))   ( (Sltiu rd rs1
imm12) (and (=
             (withRegs
                (setReg (Regs s1) rd
                   (ite (bvltu (getReg (Regs s1) rs1) ((_ int2bv 32) imm12)) ((_ int2bv 32) 1)
                    ((_ int2bv 32) 0))) s1) s2) (= tt tt)))   ( (Xori rd rs1
imm12) (and (= (withRegs (setReg (Regs s1) rd (bvxor (getReg (Regs s1) rs1) ((_ int2bv 32) imm12))) s1) s2)
        (= tt tt)))   ( (Ori rd rs1
imm12) (and (= (withRegs (setReg (Regs s1) rd (word.or (getReg (Regs s1) rs1) ((_ int2bv 32) imm12))) s1) s2)
        (= tt tt)))   ( (Andi rd rs1
imm12) (and (= (withRegs (setReg (Regs s1) rd (bvand (getReg (Regs s1) rs1) ((_ int2bv 32) imm12))) s1) s2)
        (= tt tt)))   ( (Srli rd rs1
shamt6) (and (= (withRegs (setReg (Regs s1) rd (word.sru (getReg (Regs s1) rs1) ((_ int2bv 32) shamt6))) s1)
              s2) (= tt tt)))   ( (Srai rd rs1
shamt6) (and (= (withRegs (setReg (Regs s1) rd (word.srs (getReg (Regs s1) rs1) ((_ int2bv 32) shamt6))) s1)
              s2) (= tt tt)))   ( (Auipc rd
oimm20) (and (= (withRegs (setReg (Regs s1) rd (bvadd ((_ int2bv 32) oimm20) (Pc s1))) s1) s2) (= tt tt)))
( (Sb rs1 rs2
simm12) (exists ( (_ unit)
         ) (and (= (select (Lab G) (CurrentEvent s1))
                 (Some
                    (WriteLabel (bvadd (getReg (Regs s1) rs1) ((_ int2bv 32) simm12))
                       (LittleEndian.split 1 (word.unsigned (getReg (Regs s1) rs2))))))
            (and (= (withCurrentEvent (NextEvent (CurrentEvent s1)) s1) s2) (= tt tt)))))   ( (Sh _ _
_) (exists ( (_ unit)) (and (= (select (Lab G) (CurrentEvent s1)) (Some ErrorLabel)) (= s1 s2))))   ( (Sw _ _
_) (exists ( (_ unit)) (and (= (select (Lab G) (CurrentEvent s1)) (Some ErrorLabel)) (= s1 s2))))   ( (Add rd
rs1
rs2) (and (= (withRegs (setReg (Regs s1) rd (bvadd (getReg (Regs s1) rs1) (getReg (Regs s1) rs2))) s1) s2)
      (= tt tt)))   ( (Sub rd rs1
rs2) (and (= (withRegs (setReg (Regs s1) rd (word.sub (getReg (Regs s1) rs1) (getReg (Regs s1) rs2))) s1) s2)
      (= tt tt)))   ( (Sll rd rs1
rs2) (and (=
           (withRegs
              (setReg (Regs s1) rd
                 (word.slu (getReg (Regs s1) rs1)
                    ((_ int2bv 32) (word.unsigned (getReg (Regs s1) rs2) mod 32)))) s1) s2)
      (= tt tt)))   ( (Slt rd rs1
rs2) (and (=
           (withRegs
              (setReg (Regs s1) rd
                 (ite (bvlts (getReg (Regs s1) rs1) (getReg (Regs s1) rs2)) ((_ int2bv 32) 1)
                  ((_ int2bv 32) 0))) s1) s2) (= tt tt)))   ( (Sltu rd rs1
rs2) (and (=
           (withRegs
              (setReg (Regs s1) rd
                 (ite (bvltu (getReg (Regs s1) rs1) (getReg (Regs s1) rs2)) ((_ int2bv 32) 1)
                  ((_ int2bv 32) 0))) s1) s2) (= tt tt)))   ( (Xor rd rs1
rs2) (and (= (withRegs (setReg (Regs s1) rd (bvxor (getReg (Regs s1) rs1) (getReg (Regs s1) rs2))) s1) s2)
      (= tt tt)))   ( (Srl rd rs1
rs2) (and (=
           (withRegs
              (setReg (Regs s1) rd
                 (word.sru (getReg (Regs s1) rs1)
                    ((_ int2bv 32) (word.unsigned (getReg (Regs s1) rs2) mod 32)))) s1) s2)
      (= tt tt)))   ( (Sra rd rs1
rs2) (and (=
           (withRegs
              (setReg (Regs s1) rd
                 (word.srs (getReg (Regs s1) rs1)
                    ((_ int2bv 32) (word.unsigned (getReg (Regs s1) rs2) mod 32)))) s1) s2)
      (= tt tt)))   ( (Or rd rs1
rs2) (and (= (withRegs (setReg (Regs s1) rd (word.or (getReg (Regs s1) rs1) (getReg (Regs s1) rs2))) s1) s2)
      (= tt tt)))   ( (And rd rs1
rs2) (and (= (withRegs (setReg (Regs s1) rd (bvand (getReg (Regs s1) rs1) (getReg (Regs s1) rs2))) s1) s2)
      (= tt tt)))   ( (Lui rd
imm20) (and (= (withRegs (setReg (Regs s1) rd ((_ int2bv 32) imm20)) s1) s2) (= tt tt)))   ( (Beq rs1 rs2
sbimm12) (ite (= (getReg (Regs s1) rs1) (getReg (Regs s1) rs2))
          (ite (negb (= (bvurem (bvadd (Pc s1) ((_ int2bv 32) sbimm12)) ((_ int2bv 32) 4)) ((_ int2bv 32) 0)))
           (exists ( (_ unit)) (and (= (select (Lab G) (CurrentEvent s1)) (Some ErrorLabel)) (= s1 s2)))
           (and (= (withNextPc (bvadd (Pc s1) ((_ int2bv 32) sbimm12)) s1) s2) (= tt tt)))
          (and (= s1 s2) (= tt tt))))   ( (Bne rs1 rs2
sbimm12) (ite (negb (= (getReg (Regs s1) rs1) (getReg (Regs s1) rs2)))
          (ite (negb (= (bvurem (bvadd (Pc s1) ((_ int2bv 32) sbimm12)) ((_ int2bv 32) 4)) ((_ int2bv 32) 0)))
           (exists ( (_ unit)) (and (= (select (Lab G) (CurrentEvent s1)) (Some ErrorLabel)) (= s1 s2)))
           (and (= (withNextPc (bvadd (Pc s1) ((_ int2bv 32) sbimm12)) s1) s2) (= tt tt)))
          (and (= s1 s2) (= tt tt))))   ( (Blt rs1 rs2
sbimm12) (ite (bvlts (getReg (Regs s1) rs1) (getReg (Regs s1) rs2))
          (ite (negb (= (bvurem (bvadd (Pc s1) ((_ int2bv 32) sbimm12)) ((_ int2bv 32) 4)) ((_ int2bv 32) 0)))
           (exists ( (_ unit)) (and (= (select (Lab G) (CurrentEvent s1)) (Some ErrorLabel)) (= s1 s2)))
           (and (= (withNextPc (bvadd (Pc s1) ((_ int2bv 32) sbimm12)) s1) s2) (= tt tt)))
          (and (= s1 s2) (= tt tt))))   ( (Bge rs1 rs2
sbimm12) (ite (negb (bvlts (getReg (Regs s1) rs1) (getReg (Regs s1) rs2)))
          (ite (negb (= (bvurem (bvadd (Pc s1) ((_ int2bv 32) sbimm12)) ((_ int2bv 32) 4)) ((_ int2bv 32) 0)))
           (exists ( (_ unit)) (and (= (select (Lab G) (CurrentEvent s1)) (Some ErrorLabel)) (= s1 s2)))
           (and (= (withNextPc (bvadd (Pc s1) ((_ int2bv 32) sbimm12)) s1) s2) (= tt tt)))
          (and (= s1 s2) (= tt tt))))   ( (Bltu rs1 rs2
sbimm12) (ite (bvltu (getReg (Regs s1) rs1) (getReg (Regs s1) rs2))
          (ite (negb (= (bvurem (bvadd (Pc s1) ((_ int2bv 32) sbimm12)) ((_ int2bv 32) 4)) ((_ int2bv 32) 0)))
           (exists ( (_ unit)) (and (= (select (Lab G) (CurrentEvent s1)) (Some ErrorLabel)) (= s1 s2)))
           (and (= (withNextPc (bvadd (Pc s1) ((_ int2bv 32) sbimm12)) s1) s2) (= tt tt)))
          (and (= s1 s2) (= tt tt))))   ( (Bgeu rs1 rs2
sbimm12) (ite (negb (bvltu (getReg (Regs s1) rs1) (getReg (Regs s1) rs2)))
          (ite (negb (= (bvurem (bvadd (Pc s1) ((_ int2bv 32) sbimm12)) ((_ int2bv 32) 4)) ((_ int2bv 32) 0)))
           (exists ( (_ unit)) (and (= (select (Lab G) (CurrentEvent s1)) (Some ErrorLabel)) (= s1 s2)))
           (and (= (withNextPc (bvadd (Pc s1) ((_ int2bv 32) sbimm12)) s1) s2) (= tt tt)))
          (and (= s1 s2) (= tt tt))))   ( (Jalr rd rs1
oimm12) (ite (negb
                (=
                 (bvurem (bvand (bvadd (getReg (Regs s1) rs1) ((_ int2bv 32) oimm12))
                          (bvxor ((_ int2bv 32) 1) ((_ int2bv 32) 4294967295))) ((_ int2bv 32) 4))
                 ((_ int2bv 32) 0)))
         (exists ( (_ unit)) (and (= (select (Lab G) (CurrentEvent s1)) (Some ErrorLabel)) (= s1 s2)))
         (and (=
               (withNextPc
                  (bvand (bvadd (getReg (Regs s1) rs1) ((_ int2bv 32) oimm12))
                   (bvxor ((_ int2bv 32) 1) ((_ int2bv 32) 4294967295)))
                  (withRegs (setReg (Regs s1) rd (bvadd (Pc s1) ((_ int2bv 32) 4))) s1)) s2)
          (= tt tt))))   ( (Jal rd
jimm20) (ite (negb (= (bvurem (bvadd (Pc s1) ((_ int2bv 32) jimm20)) ((_ int2bv 32) 4)) ((_ int2bv 32) 0)))
         (exists ( (_ unit)) (and (= (select (Lab G) (CurrentEvent s1)) (Some ErrorLabel)) (= s1 s2)))
         (and (=
               (withNextPc (bvadd (Pc s1) ((_ int2bv 32) jimm20))
                  (withRegs (setReg (Regs s1) rd (bvadd (Pc s1) ((_ int2bv 32) 4))) s1)) s2)
          (= tt tt))))   ( (InvalidI ) (and (= s1 s2) (= tt tt))))))

(check-sat)
(get-model)
