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

(define-fun NextEvent ((e Event)) Event
  (match e (
    ((InitEvent x) e)
    ((ThreadEvent t i) (ThreadEvent t (+ i 1))))))

(declare-datatypes () ((InstructionI
   (Lb (rd_Lb Z) (rs1_Lb Z) (oimm12_Lb Z))
   (Lh (rd_Lh Z) (rs1_Lh Z) (oimm12_Lh Z))
   (Lw (rd_Lw Z) (rs1_Lw Z) (oimm12_Lw Z))
   (Lbu (rd_Lbu Z) (rs1_Lbu Z) (oimm12_Lbu Z))
   (Lhu (rd_Lhu Z) (rs1_Lhu Z) (oimm12_Lhu Z))
   (Fence (pred_Fence Z) (succ_Fence Z))
   Fence_i
   (Addi (rd_Addi Z) (rs1_Addi Z) (imm12_Addi Z))
   (Slli (rd_Slli Z) (rs1_Slli Z) (shamt6_Slli Z))
   (Slti (rd_Slti Z) (rs1_Slti Z) (imm12_Slti Z))
   (Sltiu (rd_Sltiu Z) (rs1_Sltiu Z) (imm12_Sltiu Z))
   (Xori (rd_Xori Z) (rs1_Xori Z) (imm12_Xori Z))
   (Ori (rd_Ori Z) (rs1_Ori Z) (imm12_Ori Z))
   (Andi (rd_Andi Z) (rs1_Andi Z) (imm12_Andi Z))
   (Srli (rd_Srli Z) (rs1_Srli Z) (shamt6_Srli Z))
   (Srai (rd_Srai Z) (rs1_Srai Z) (shamt6_Srai Z))
   (Auipc (rd_Auipc Z) (oimm20_Auipc Z))
   (Sb (rs1_Sb Z) (rs2_Sb Z) (simm12_Sb Z))
   (Sh (rs1_Sh Z) (rs2_Sh Z) (simm12_Sh Z))
   (Sw (rs1_Sw Z) (rs2_Sw Z) (simm12_Sw Z))
   (Add (rd_Add Z) (rs1_Add Z) (rs2_Add Z))
   (Sub (rd_Sub Z) (rs1_Sub Z) (rs2_Sub Z))
   (Sll (rd_Sll Z) (rs1_Sll Z) (rs2_Sll Z))
   (Slt (rd_Slt Z) (rs1_Slt Z) (rs2_Slt Z))
   (Sltu (rd_Sltu Z) (rs1_Sltu Z) (rs2_Sltu Z))
   (Xor (rd_Xor Z) (rs1_Xor Z) (rs2_Xor Z))
   (Srl (rd_Srl Z) (rs1_Srl Z) (rs2_Srl Z))
   (Sra (rd_Sra Z) (rs1_Sra Z) (rs2_Sra Z))
   (Or (rd_Or Z) (rs1_Or Z) (rs2_Or Z))
   (And (rd_And Z) (rs1_And Z) (rs2_And Z))
   (Lui (rd_Lui Z) (imm20_Lui Z))
   (Beq (rs1_Beq Z) (rs2_Beq Z) (sbimm12_Beq Z))
   (Bne (rs1_Bne Z) (rs2_Bne Z) (sbimm12_Bne Z))
   (Blt (rs1_Blt Z) (rs2_Blt Z) (sbimm12_Blt Z))
   (Bge (rs1_Bge Z) (rs2_Bge Z) (sbimm12_Bge Z))
   (Bltu (rs1_Bltu Z) (rs2_Bltu Z) (sbimm12_Bltu Z))
   (Bgeu (rs1_Bgeu Z) (rs2_Bgeu Z) (sbimm12_Bgeu Z))
   (Jalr (rd_Jalr Z) (rs1_Jalr Z) (oimm12_Jalr Z))
   (Jal (rd_Jal Z) (jimm20_Jal Z))
   InvalidI
)))

; that's just the register name, needs to be between 0 and 32, value will be of type word
(define-sort Register () Int)
; register file:
(define-sort Registers () (Array Register word))

(declare-datatypes () ((ThreadState (mkThreadState
  (Regs Registers)
  (Pc word)
  (NextPc word)
  (Prog (Array word InstructionI))
  (CurrentEvent Event)
  (Deps (Array Register (set Event)))
))))

(define-fun withRegs         ((x Registers                   ) (s ThreadState)) ThreadState (mkThreadState x        (Pc s) (NextPc s) (Prog s) (CurrentEvent s) (Deps s)))
(define-fun withPc           ((x word                        ) (s ThreadState)) ThreadState (mkThreadState (Regs s) x      (NextPc s) (Prog s) (CurrentEvent s) (Deps s)))
(define-fun withNextPc       ((x word                        ) (s ThreadState)) ThreadState (mkThreadState (Regs s) (Pc s) x          (Prog s) (CurrentEvent s) (Deps s)))
(define-fun withProg         ((x (Array word InstructionI)    ) (s ThreadState)) ThreadState (mkThreadState (Regs s) (Pc s) (NextPc s) x        (CurrentEvent s) (Deps s)))
(define-fun withCurrentEvent ((x Event                       ) (s ThreadState)) ThreadState (mkThreadState (Regs s) (Pc s) (NextPc s) (Prog s) x                (Deps s)))
(define-fun withDeps         ((x (Array Register (set Event))) (s ThreadState)) ThreadState (mkThreadState (Regs s) (Pc s) (NextPc s) (Prog s) (CurrentEvent s) x       ))

(declare-datatypes () ((Label
  (ReadLabel (LabelReadLoc word))
  (WriteLabel (LabelWriteLoc word) (LabelVal w8))
  FenceLabel
  ErrorLabel
  AbsentLabel)))

(declare-datatypes () ((EventTyp ReadEvent WriteEvent FenceEvent ErrorEvent AbsentEvent)))

(define-fun LabelTyp ((l Label)) EventTyp
  (match l (
    ((ReadLabel _) ReadEvent)
    ((WriteLabel _ _) WriteEvent)
    (FenceLabel FenceEvent)
    (ErrorLabel ErrorEvent)
    (AbsentLabel AbsentEvent))))

(declare-datatypes () ((Graph (mkGraph
  (Lab (Array Event Label))
  (Rf (Array Event Event))
  (Addr (Array Event (set Event)))
  (Data (Array Event (set Event)))
  (Ctrl (Array Event (set Event)))
))))

(define-fun Typ ((G Graph) (e Event)) EventTyp (LabelTyp (select (Lab G) e)))

(declare-const G0 Graph)
(declare-const e0 Event)
(assert (= (select (Lab G0) e0) AbsentLabel))

(define-fun Loc ((G Graph) (e Event)) (option word)
  (match (select (Lab G) e) (
    ((ReadLabel x) (Some x))
    ((WriteLabel x v) (Some x))
    (FenceLabel (as None (option word)))
    (ErrorLabel (as None (option word)))
    (AbsentLabel (as None (option word))))))

(define-fun Val ((G Graph) (e Event)) w8
  (match (select (Lab G) e) (
    ((ReadLabel x) #x00)
    ((WriteLabel x v) v)
    (FenceLabel #x00)
    (ErrorLabel #x00)
    (AbsentLabel #x00))))

(declare-const nn Int)
(assert (exists ((a Int)) (and (< 2 a) (= nn (* a a)))))

(declare-const i1 InstructionI)
(declare-const i2 InstructionI)
(declare-const s ThreadState)
(assert (not (= i1 i2)))

(define-fun getReg ((regs Registers) (reg Register)) word
  (ite (= reg 0) ((_ int2bv 32) 0) (select regs reg)))

(define-fun setReg ((regs Registers) (reg Register) (v word)) Registers
  (ite (= reg 0) regs (store regs reg v)))

(define-const emptyEvents (set Event) ((as const (set Event)) false))
(define-const emptyDeps (Array Register (set Event)) ((as const (Array Register (set Event))) emptyEvents))

(define-fun getDeps ((D (Array Register (set Event))) (r Register)) (set Event)
  (ite (= r 0) emptyEvents (select D r)))

(define-fun setDeps ((D (Array Register (set Event))) (r Register) (s (set Event))) (Array Register (set Event))
  (ite (= r 0) D (store D r s)))

(define-const minusone Int (- 1))

(define-fun run1 ((G Graph) (s1 ThreadState) (s2 ThreadState)) bool
(match (select (Prog s1) (Pc s1)) (
((Lb rd rs1 oimm12) (and (and (= (select (Addr G) (CurrentEvent s1)) (getDeps (Deps s1) rs1))
                          (and (= (select (Data G) (CurrentEvent s1)) emptyEvents)
                           (= (select (Ctrl G) (CurrentEvent s1)) (getDeps (Deps s1) minusone))))
                     (and (and (= (select (Lab G) (CurrentEvent s1))
                                (ReadLabel (bvadd (getReg (Regs s1) rs1) ((_ int2bv 32) oimm12))))
                           (= (Typ G (select (Rf G) (CurrentEvent s1))) WriteEvent))
                      (and (=
                            (withPc (NextPc s1)
                               (withNextPc (bvadd (NextPc s1) ((_ int2bv 32) 4))
                                  (withDeps (Deps s1)
                                     (withRegs
                                        (setReg (Regs s1) rd
                                           ((_ sign_extend 24) (Val G (select (Rf G) (CurrentEvent s1)))))
                                        (withCurrentEvent (NextEvent (CurrentEvent s1)) s1))))) s2)
                       (= tt tt)))))
((Lh _ _ _) (and (= (select (Lab G) (CurrentEvent s1)) ErrorLabel) (= s1 s2)))
((Lw _ _ _) (and (= (select (Lab G) (CurrentEvent s1)) ErrorLabel) (= s1 s2)))
((Lbu rd rs1 oimm12) (and (and (= (select (Lab G) (CurrentEvent s1))
                                (ReadLabel (bvadd (getReg (Regs s1) rs1) ((_ int2bv 32) oimm12))))
                           (= (Typ G (select (Rf G) (CurrentEvent s1))) WriteEvent))
                      (and (=
                            (withPc (NextPc s1)
                               (withNextPc (bvadd (NextPc s1) ((_ int2bv 32) 4))
                                  (withDeps (Deps s1)
                                     (withRegs
                                        (setReg (Regs s1) rd
                                           ((_ zero_extend 24) (Val G (select (Rf G) (CurrentEvent s1)))))
                                        (withCurrentEvent (NextEvent (CurrentEvent s1)) s1))))) s2)
                       (= tt tt))))
((Lhu _ _ _) (and (= (select (Lab G) (CurrentEvent s1)) ErrorLabel) (= s1 s2)))
((Fence _ _) (and (=
                   (withPc (NextPc s1)
                      (withNextPc (bvadd (NextPc s1) ((_ int2bv 32) 4)) (withDeps (Deps s1) s1))) s2)
              (= tt tt)))
((Fence_i) (and (=
                 (withPc (NextPc s1)
                    (withNextPc (bvadd (NextPc s1) ((_ int2bv 32) 4)) (withDeps (Deps s1) s1))) s2)
            (= tt tt)))
((Addi rd rs1 imm12) (and (=
                           (withPc (NextPc s1)
                              (withNextPc (bvadd (NextPc s1) ((_ int2bv 32) 4))
                                 (withDeps (setDeps (Deps s1) rd (getDeps (Deps s1) rs1))
                                    (withRegs
                                       (setReg (Regs s1) rd
                                          (bvadd (getReg (Regs s1) rs1) ((_ int2bv 32) imm12))) s1)))) s2)
                      (= tt tt)))
((Slli rd rs1 shamt6) (and (=
                            (withPc (NextPc s1)
                               (withNextPc (bvadd (NextPc s1) ((_ int2bv 32) 4))
                                  (withDeps (setDeps (Deps s1) rd (getDeps (Deps s1) rs1))
                                     (withRegs
                                        (setReg (Regs s1) rd
                                           (bvshl (getReg (Regs s1) rs1) ((_ int2bv 32) shamt6))) s1)))) s2)
                       (= tt tt)))
((Slti rd rs1 imm12) (and (=
                           (withPc (NextPc s1)
                              (withNextPc (bvadd (NextPc s1) ((_ int2bv 32) 4))
                                 (withDeps (setDeps (Deps s1) rd (getDeps (Deps s1) rs1))
                                    (withRegs
                                       (setReg (Regs s1) rd
                                          (ite (bvslt (getReg (Regs s1) rs1) ((_ int2bv 32) imm12))
                                           ((_ int2bv 32) 1) ((_ int2bv 32) 0))) s1)))) s2)
                      (= tt tt)))
((Sltiu rd rs1 imm12) (and (=
                            (withPc (NextPc s1)
                               (withNextPc (bvadd (NextPc s1) ((_ int2bv 32) 4))
                                  (withDeps (setDeps (Deps s1) rd (getDeps (Deps s1) rs1))
                                     (withRegs
                                        (setReg (Regs s1) rd
                                           (ite (bvult (getReg (Regs s1) rs1) ((_ int2bv 32) imm12))
                                            ((_ int2bv 32) 1) ((_ int2bv 32) 0))) s1)))) s2)
                       (= tt tt)))
((Xori rd rs1 imm12) (and (=
                           (withPc (NextPc s1)
                              (withNextPc (bvadd (NextPc s1) ((_ int2bv 32) 4))
                                 (withDeps (setDeps (Deps s1) rd (getDeps (Deps s1) rs1))
                                    (withRegs
                                       (setReg (Regs s1) rd
                                          (bvxor (getReg (Regs s1) rs1) ((_ int2bv 32) imm12))) s1)))) s2)
                      (= tt tt)))
((Ori rd rs1 imm12) (and (=
                          (withPc (NextPc s1)
                             (withNextPc (bvadd (NextPc s1) ((_ int2bv 32) 4))
                                (withDeps (setDeps (Deps s1) rd (getDeps (Deps s1) rs1))
                                   (withRegs
                                      (setReg (Regs s1) rd (bvor (getReg (Regs s1) rs1) ((_ int2bv 32) imm12)))
                                      s1)))) s2) (= tt tt)))
((Andi rd rs1 imm12) (and (=
                           (withPc (NextPc s1)
                              (withNextPc (bvadd (NextPc s1) ((_ int2bv 32) 4))
                                 (withDeps (setDeps (Deps s1) rd (getDeps (Deps s1) rs1))
                                    (withRegs
                                       (setReg (Regs s1) rd
                                          (bvand (getReg (Regs s1) rs1) ((_ int2bv 32) imm12))) s1)))) s2)
                      (= tt tt)))
((Srli rd rs1 shamt6) (and (=
                            (withPc (NextPc s1)
                               (withNextPc (bvadd (NextPc s1) ((_ int2bv 32) 4))
                                  (withDeps (setDeps (Deps s1) rd (getDeps (Deps s1) rs1))
                                     (withRegs
                                        (setReg (Regs s1) rd
                                           (bvlshr (getReg (Regs s1) rs1) ((_ int2bv 32) shamt6))) s1)))) s2)
                       (= tt tt)))
((Srai rd rs1 shamt6) (and (=
                            (withPc (NextPc s1)
                               (withNextPc (bvadd (NextPc s1) ((_ int2bv 32) 4))
                                  (withDeps (setDeps (Deps s1) rd (getDeps (Deps s1) rs1))
                                     (withRegs
                                        (setReg (Regs s1) rd
                                           (bvashr (getReg (Regs s1) rs1) ((_ int2bv 32) shamt6))) s1)))) s2)
                       (= tt tt)))
((Auipc rd oimm20) (and (=
                         (withPc (NextPc s1)
                            (withNextPc (bvadd (NextPc s1) ((_ int2bv 32) 4))
                               (withDeps (setDeps (Deps s1) rd (getDeps (Deps s1) minusone))
                                  (withRegs (setReg (Regs s1) rd (bvadd ((_ int2bv 32) oimm20) (Pc s1))) s1))))
                         s2) (= tt tt)))
((Sb rs1 rs2 simm12) (and (and (= (select (Addr G) (CurrentEvent s1)) (getDeps (Deps s1) rs1))
                           (and (= (select (Data G) (CurrentEvent s1)) (getDeps (Deps s1) rs2))
                            (= (select (Ctrl G) (CurrentEvent s1)) (getDeps (Deps s1) minusone))))
                      (and (= (select (Lab G) (CurrentEvent s1))
                            (WriteLabel (bvadd (getReg (Regs s1) rs1) ((_ int2bv 32) simm12))
                               ((_ extract 7 0) (getReg (Regs s1) rs2))))
                       (and (=
                             (withPc (NextPc s1)
                                (withNextPc (bvadd (NextPc s1) ((_ int2bv 32) 4))
                                   (withDeps (Deps s1) (withCurrentEvent (NextEvent (CurrentEvent s1)) s1))))
                             s2) (= tt tt)))))
((Sh _ _ _) (and (= (select (Lab G) (CurrentEvent s1)) ErrorLabel) (= s1 s2)))
((Sw _ _ _) (and (= (select (Lab G) (CurrentEvent s1)) ErrorLabel) (= s1 s2)))
((Add rd rs1 rs2) (and (=
                        (withPc (NextPc s1)
                           (withNextPc (bvadd (NextPc s1) ((_ int2bv 32) 4))
                              (withDeps
                                 (setDeps (Deps s1) rd (union (getDeps (Deps s1) rs1) (getDeps (Deps s1) rs2)))
                                 (withRegs
                                    (setReg (Regs s1) rd (bvadd (getReg (Regs s1) rs1) (getReg (Regs s1) rs2)))
                                    s1)))) s2) (= tt tt)))
((Sub rd rs1 rs2) (and (=
                        (withPc (NextPc s1)
                           (withNextPc (bvadd (NextPc s1) ((_ int2bv 32) 4))
                              (withDeps
                                 (setDeps (Deps s1) rd (union (getDeps (Deps s1) rs1) (getDeps (Deps s1) rs2)))
                                 (withRegs
                                    (setReg (Regs s1) rd (bvsub (getReg (Regs s1) rs1) (getReg (Regs s1) rs2)))
                                    s1)))) s2) (= tt tt)))
((Sll rd rs1 rs2) (and (=
                        (withPc (NextPc s1)
                           (withNextPc (bvadd (NextPc s1) ((_ int2bv 32) 4))
                              (withDeps
                                 (setDeps (Deps s1) rd (union (getDeps (Deps s1) rs1) (getDeps (Deps s1) rs2)))
                                 (withRegs
                                    (setReg (Regs s1) rd
                                       (bvshl (getReg (Regs s1) rs1)
                                        ((_ int2bv 32) (mod ((_ bv2nat 32) (getReg (Regs s1) rs2)) 32)))) s1))))
                        s2) (= tt tt)))
((Slt rd rs1 rs2) (and (=
                        (withPc (NextPc s1)
                           (withNextPc (bvadd (NextPc s1) ((_ int2bv 32) 4))
                              (withDeps
                                 (setDeps (Deps s1) rd (union (getDeps (Deps s1) rs1) (getDeps (Deps s1) rs2)))
                                 (withRegs
                                    (setReg (Regs s1) rd
                                       (ite (bvslt (getReg (Regs s1) rs1) (getReg (Regs s1) rs2))
                                        ((_ int2bv 32) 1) ((_ int2bv 32) 0))) s1)))) s2)
                   (= tt tt)))
((Sltu rd rs1 rs2) (and (=
                         (withPc (NextPc s1)
                            (withNextPc (bvadd (NextPc s1) ((_ int2bv 32) 4))
                               (withDeps
                                  (setDeps (Deps s1) rd
                                     (union (getDeps (Deps s1) rs1) (getDeps (Deps s1) rs2)))
                                  (withRegs
                                     (setReg (Regs s1) rd
                                        (ite (bvult (getReg (Regs s1) rs1) (getReg (Regs s1) rs2))
                                         ((_ int2bv 32) 1) ((_ int2bv 32) 0))) s1)))) s2)
                    (= tt tt)))
((Xor rd rs1 rs2) (and (=
                        (withPc (NextPc s1)
                           (withNextPc (bvadd (NextPc s1) ((_ int2bv 32) 4))
                              (withDeps
                                 (setDeps (Deps s1) rd (union (getDeps (Deps s1) rs1) (getDeps (Deps s1) rs2)))
                                 (withRegs
                                    (setReg (Regs s1) rd (bvxor (getReg (Regs s1) rs1) (getReg (Regs s1) rs2)))
                                    s1)))) s2) (= tt tt)))
((Srl rd rs1 rs2) (and (=
                        (withPc (NextPc s1)
                           (withNextPc (bvadd (NextPc s1) ((_ int2bv 32) 4))
                              (withDeps
                                 (setDeps (Deps s1) rd (union (getDeps (Deps s1) rs1) (getDeps (Deps s1) rs2)))
                                 (withRegs
                                    (setReg (Regs s1) rd
                                       (bvlshr (getReg (Regs s1) rs1)
                                        ((_ int2bv 32) (mod ((_ bv2nat 32) (getReg (Regs s1) rs2)) 32)))) s1))))
                        s2) (= tt tt)))
((Sra rd rs1 rs2) (and (=
                        (withPc (NextPc s1)
                           (withNextPc (bvadd (NextPc s1) ((_ int2bv 32) 4))
                              (withDeps
                                 (setDeps (Deps s1) rd (union (getDeps (Deps s1) rs1) (getDeps (Deps s1) rs2)))
                                 (withRegs
                                    (setReg (Regs s1) rd
                                       (bvashr (getReg (Regs s1) rs1)
                                        ((_ int2bv 32) (mod ((_ bv2nat 32) (getReg (Regs s1) rs2)) 32)))) s1))))
                        s2) (= tt tt)))
((Or rd rs1 rs2) (and (=
                       (withPc (NextPc s1)
                          (withNextPc (bvadd (NextPc s1) ((_ int2bv 32) 4))
                             (withDeps
                                (setDeps (Deps s1) rd (union (getDeps (Deps s1) rs1) (getDeps (Deps s1) rs2)))
                                (withRegs
                                   (setReg (Regs s1) rd (bvor (getReg (Regs s1) rs1) (getReg (Regs s1) rs2)))
                                   s1)))) s2) (= tt tt)))
((And rd rs1 rs2) (and (=
                        (withPc (NextPc s1)
                           (withNextPc (bvadd (NextPc s1) ((_ int2bv 32) 4))
                              (withDeps
                                 (setDeps (Deps s1) rd (union (getDeps (Deps s1) rs1) (getDeps (Deps s1) rs2)))
                                 (withRegs
                                    (setReg (Regs s1) rd (bvand (getReg (Regs s1) rs1) (getReg (Regs s1) rs2)))
                                    s1)))) s2) (= tt tt)))
((Lui rd imm20) (and (=
                      (withPc (NextPc s1)
                         (withNextPc (bvadd (NextPc s1) ((_ int2bv 32) 4))
                            (withDeps (Deps s1) (withRegs (setReg (Regs s1) rd ((_ int2bv 32) imm20)) s1))))
                      s2) (= tt tt)))
((Beq rs1 rs2 sbimm12) (ite (= (getReg (Regs s1) rs1) (getReg (Regs s1) rs2))
                        (ite (not (= (bvurem (bvadd (Pc s1) ((_ int2bv 32) sbimm12)) ((_ int2bv 32) 4))
                                   ((_ int2bv 32) 0)))
                         (and (= (select (Lab G) (CurrentEvent s1)) ErrorLabel) (= s1 s2))
                         (and (=
                               (withPc (bvadd (Pc s1) ((_ int2bv 32) sbimm12))
                                  (withNextPc
                                     (bvadd (bvadd (Pc s1) ((_ int2bv 32) sbimm12)) ((_ int2bv 32) 4))
                                     (withDeps
                                        (setDeps (Deps s1) minusone
                                           (union (getDeps (Deps s1) minusone)
                                              (union (getDeps (Deps s1) rs1) (getDeps (Deps s1) rs2))))
                                        (withNextPc (bvadd (Pc s1) ((_ int2bv 32) sbimm12)) s1)))) s2)
                          (= tt tt)))
                        (and (=
                              (withPc (NextPc s1)
                                 (withNextPc (bvadd (NextPc s1) ((_ int2bv 32) 4))
                                    (withDeps
                                       (setDeps (Deps s1) minusone
                                          (union (getDeps (Deps s1) minusone)
                                             (union (getDeps (Deps s1) rs1) (getDeps (Deps s1) rs2)))) s1)))
                              s2) (= tt tt))))
((Bne rs1 rs2 sbimm12) (ite (not (= (getReg (Regs s1) rs1) (getReg (Regs s1) rs2)))
                        (ite (not (= (bvurem (bvadd (Pc s1) ((_ int2bv 32) sbimm12)) ((_ int2bv 32) 4))
                                   ((_ int2bv 32) 0)))
                         (and (= (select (Lab G) (CurrentEvent s1)) ErrorLabel) (= s1 s2))
                         (and (=
                               (withPc (bvadd (Pc s1) ((_ int2bv 32) sbimm12))
                                  (withNextPc
                                     (bvadd (bvadd (Pc s1) ((_ int2bv 32) sbimm12)) ((_ int2bv 32) 4))
                                     (withDeps
                                        (setDeps (Deps s1) minusone
                                           (union (getDeps (Deps s1) minusone)
                                              (union (getDeps (Deps s1) rs1) (getDeps (Deps s1) rs2))))
                                        (withNextPc (bvadd (Pc s1) ((_ int2bv 32) sbimm12)) s1)))) s2)
                          (= tt tt)))
                        (and (=
                              (withPc (NextPc s1)
                                 (withNextPc (bvadd (NextPc s1) ((_ int2bv 32) 4))
                                    (withDeps
                                       (setDeps (Deps s1) minusone
                                          (union (getDeps (Deps s1) minusone)
                                             (union (getDeps (Deps s1) rs1) (getDeps (Deps s1) rs2)))) s1)))
                              s2) (= tt tt))))
((Blt rs1 rs2 sbimm12) (ite (bvslt (getReg (Regs s1) rs1) (getReg (Regs s1) rs2))
                        (ite (not (= (bvurem (bvadd (Pc s1) ((_ int2bv 32) sbimm12)) ((_ int2bv 32) 4))
                                   ((_ int2bv 32) 0)))
                         (and (= (select (Lab G) (CurrentEvent s1)) ErrorLabel) (= s1 s2))
                         (and (=
                               (withPc (bvadd (Pc s1) ((_ int2bv 32) sbimm12))
                                  (withNextPc
                                     (bvadd (bvadd (Pc s1) ((_ int2bv 32) sbimm12)) ((_ int2bv 32) 4))
                                     (withDeps
                                        (setDeps (Deps s1) minusone
                                           (union (getDeps (Deps s1) minusone)
                                              (union (getDeps (Deps s1) rs1) (getDeps (Deps s1) rs2))))
                                        (withNextPc (bvadd (Pc s1) ((_ int2bv 32) sbimm12)) s1)))) s2)
                          (= tt tt)))
                        (and (=
                              (withPc (NextPc s1)
                                 (withNextPc (bvadd (NextPc s1) ((_ int2bv 32) 4))
                                    (withDeps
                                       (setDeps (Deps s1) minusone
                                          (union (getDeps (Deps s1) minusone)
                                             (union (getDeps (Deps s1) rs1) (getDeps (Deps s1) rs2)))) s1)))
                              s2) (= tt tt))))
((Bge rs1 rs2 sbimm12) (ite (not (bvslt (getReg (Regs s1) rs1) (getReg (Regs s1) rs2)))
                        (ite (not (= (bvurem (bvadd (Pc s1) ((_ int2bv 32) sbimm12)) ((_ int2bv 32) 4))
                                   ((_ int2bv 32) 0)))
                         (and (= (select (Lab G) (CurrentEvent s1)) ErrorLabel) (= s1 s2))
                         (and (=
                               (withPc (bvadd (Pc s1) ((_ int2bv 32) sbimm12))
                                  (withNextPc
                                     (bvadd (bvadd (Pc s1) ((_ int2bv 32) sbimm12)) ((_ int2bv 32) 4))
                                     (withDeps
                                        (setDeps (Deps s1) minusone
                                           (union (getDeps (Deps s1) minusone)
                                              (union (getDeps (Deps s1) rs1) (getDeps (Deps s1) rs2))))
                                        (withNextPc (bvadd (Pc s1) ((_ int2bv 32) sbimm12)) s1)))) s2)
                          (= tt tt)))
                        (and (=
                              (withPc (NextPc s1)
                                 (withNextPc (bvadd (NextPc s1) ((_ int2bv 32) 4))
                                    (withDeps
                                       (setDeps (Deps s1) minusone
                                          (union (getDeps (Deps s1) minusone)
                                             (union (getDeps (Deps s1) rs1) (getDeps (Deps s1) rs2)))) s1)))
                              s2) (= tt tt))))
((Bltu rs1 rs2 sbimm12) (ite (bvult (getReg (Regs s1) rs1) (getReg (Regs s1) rs2))
                         (ite (not (= (bvurem (bvadd (Pc s1) ((_ int2bv 32) sbimm12)) ((_ int2bv 32) 4))
                                    ((_ int2bv 32) 0)))
                          (and (= (select (Lab G) (CurrentEvent s1)) ErrorLabel) (= s1 s2))
                          (and (=
                                (withPc (bvadd (Pc s1) ((_ int2bv 32) sbimm12))
                                   (withNextPc
                                      (bvadd (bvadd (Pc s1) ((_ int2bv 32) sbimm12)) ((_ int2bv 32) 4))
                                      (withDeps
                                         (setDeps (Deps s1) minusone
                                            (union (getDeps (Deps s1) minusone)
                                               (union (getDeps (Deps s1) rs1) (getDeps (Deps s1) rs2))))
                                         (withNextPc (bvadd (Pc s1) ((_ int2bv 32) sbimm12)) s1)))) s2)
                           (= tt tt)))
                         (and (=
                               (withPc (NextPc s1)
                                  (withNextPc (bvadd (NextPc s1) ((_ int2bv 32) 4))
                                     (withDeps
                                        (setDeps (Deps s1) minusone
                                           (union (getDeps (Deps s1) minusone)
                                              (union (getDeps (Deps s1) rs1) (getDeps (Deps s1) rs2)))) s1)))
                               s2) (= tt tt))))
((Bgeu rs1 rs2 sbimm12) (ite (not (bvult (getReg (Regs s1) rs1) (getReg (Regs s1) rs2)))
                         (ite (not (= (bvurem (bvadd (Pc s1) ((_ int2bv 32) sbimm12)) ((_ int2bv 32) 4))
                                    ((_ int2bv 32) 0)))
                          (and (= (select (Lab G) (CurrentEvent s1)) ErrorLabel) (= s1 s2))
                          (and (=
                                (withPc (bvadd (Pc s1) ((_ int2bv 32) sbimm12))
                                   (withNextPc
                                      (bvadd (bvadd (Pc s1) ((_ int2bv 32) sbimm12)) ((_ int2bv 32) 4))
                                      (withDeps
                                         (setDeps (Deps s1) minusone
                                            (union (getDeps (Deps s1) minusone)
                                               (union (getDeps (Deps s1) rs1) (getDeps (Deps s1) rs2))))
                                         (withNextPc (bvadd (Pc s1) ((_ int2bv 32) sbimm12)) s1)))) s2)
                           (= tt tt)))
                         (and (=
                               (withPc (NextPc s1)
                                  (withNextPc (bvadd (NextPc s1) ((_ int2bv 32) 4))
                                     (withDeps
                                        (setDeps (Deps s1) minusone
                                           (union (getDeps (Deps s1) minusone)
                                              (union (getDeps (Deps s1) rs1) (getDeps (Deps s1) rs2)))) s1)))
                               s2) (= tt tt))))
((Jalr rd rs1 oimm12) (ite (not (=
                                 (bvurem (bvand (bvadd (getReg (Regs s1) rs1) ((_ int2bv 32) oimm12))
                                          (bvxor ((_ int2bv 32) 1) ((_ int2bv 32) 4294967295)))
                                  ((_ int2bv 32) 4)) ((_ int2bv 32) 0)))
                       (and (= (select (Lab G) (CurrentEvent s1)) ErrorLabel) (= s1 s2))
                       (and (=
                             (withPc
                                (bvand (bvadd (getReg (Regs s1) rs1) ((_ int2bv 32) oimm12))
                                 (bvxor ((_ int2bv 32) 1) ((_ int2bv 32) 4294967295)))
                                (withNextPc
                                   (bvadd (bvand (bvadd (getReg (Regs s1) rs1) ((_ int2bv 32) oimm12))
                                           (bvxor ((_ int2bv 32) 1) ((_ int2bv 32) 4294967295)))
                                    ((_ int2bv 32) 4))
                                   (withDeps
                                      (setDeps (setDeps (Deps s1) rd (getDeps (Deps s1) minusone)) minusone
                                         (union (getDeps (Deps s1) minusone) (getDeps (Deps s1) rs1)))
                                      (withNextPc
                                         (bvand (bvadd (getReg (Regs s1) rs1) ((_ int2bv 32) oimm12))
                                          (bvxor ((_ int2bv 32) 1) ((_ int2bv 32) 4294967295)))
                                         (withRegs (setReg (Regs s1) rd (bvadd (Pc s1) ((_ int2bv 32) 4))) s1)))))
                             s2) (= tt tt))))
((Jal rd jimm20) (ite (not (= (bvurem (bvadd (Pc s1) ((_ int2bv 32) jimm20)) ((_ int2bv 32) 4))
                            ((_ int2bv 32) 0)))
                  (and (= (select (Lab G) (CurrentEvent s1)) ErrorLabel) (= s1 s2))
                  (and (=
                        (withPc (bvadd (Pc s1) ((_ int2bv 32) jimm20))
                           (withNextPc (bvadd (bvadd (Pc s1) ((_ int2bv 32) jimm20)) ((_ int2bv 32) 4))
                              (withDeps (setDeps (Deps s1) rd (getDeps (Deps s1) minusone))
                                 (withNextPc (bvadd (Pc s1) ((_ int2bv 32) jimm20))
                                    (withRegs (setReg (Regs s1) rd (bvadd (Pc s1) ((_ int2bv 32) 4))) s1)))))
                        s2) (= tt tt))))
((InvalidI) (and (=
                  (withPc (NextPc s1)
                     (withNextPc (bvadd (NextPc s1) ((_ int2bv 32) 4)) (withDeps (Deps s1) s1))) s2)
             (= tt tt)))))
)

(declare-const G Graph)
(declare-const s1 ThreadState)
(declare-const s2 ThreadState)
(assert (run1 G s1 s2))
(check-sat)
(get-model)
