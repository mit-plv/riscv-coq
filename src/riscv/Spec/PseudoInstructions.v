Require Import riscv.Spec.Decode.
Require Import riscv.Spec.Machine.
Require Import Coq.ZArith.BinInt.

Open Scope Z_scope.

(* "Table 26.2: RISC-V pseudoinstructions" in the standard *)

Local Notation x0 := Register0.

Definition Nop := Addi x0 x0 0.
Definition Mov(rd: Register)(rs: Register) := Addi rd rs 0.
Definition Not(rd: Register)(rs: Register) := Xori rd rs (-1).
Definition Neg(rd: Register)(rs: Register) := Sub rd x0 rs.
Definition Negw(rd: Register)(rs: Register) := Subw rd x0 rs.
Definition Sextw(rd: Register)(rs: Register) := Addiw rd rs 0.
Definition Seqz(rd: Register)(rs: Register) := Sltiu rd rs 1.
Definition Snez(rd: Register)(rs: Register) := Sltu rd x0 rs.
Definition Sltz(rd: Register)(rs: Register) := Slt rd rs x0.
Definition Sgtz(rd: Register)(rs: Register) := Slt rd x0 rs.

Definition Beqz(rs: Register)(offset: Z) := Beq rs x0 offset.
Definition Bnez(rs: Register)(offset: Z) := Bne rs x0 offset.
Definition Blez(rs: Register)(offset: Z) := Bge x0 rs offset.
Definition Bgez(rs: Register)(offset: Z) := Bge rs x0 offset.
Definition Bltz(rs: Register)(offset: Z) := Blt rs x0 offset.
Definition Bgtz(rs: Register)(offset: Z) := Blt x0 rs offset.

Definition Bgt(rs: Register)(rt: Register)(offset: Z) := Blt rt rs offset.
Definition Ble(rs: Register)(rt: Register)(offset: Z) := Bge rt rs offset.
Definition Bgtu(rs: Register)(rt: Register)(offset: Z) := Bltu rt rs offset.
Definition Bleu(rs: Register)(rt: Register)(offset: Z) := Bgeu rt rs offset.

Definition J(offset: Z) := Jal x0 offset.
Definition Jr(rs: Register) := Jalr x0 rs 0.

(* "Table 26.3: Pseudoinstructions for accessing control and status registers" in the standard *)

Definition Csrr  rd  csr := Csrrs  rd x0 csr.
Definition Csrw  rs  csr := Csrrw  x0 rs csr.
Definition Csrs  rs  csr := Csrrs  x0 rs csr.
Definition Csrc  rs  csr := Csrrc  x0 rs csr.
Definition Csrwi imm csr := Csrrwi x0 imm csr.
Definition Csrsi imm csr := Csrrsi x0 imm csr.
Definition Csrci imm csr := Csrrci x0 imm csr.

#[export] Hint Unfold
    Nop
    Mov
    Not
    Neg
    Negw
    Sextw
    Seqz
    Snez
    Sltz
    Sgtz
    Beqz
    Bnez
    Blez
    Bgez
    Bltz
    Bgtz
    Bgt
    Ble
    Bgtu
    Bleu
    J
    Jr
    Csrr
    Csrw
    Csrs
    Csrc
    Csrwi
    Csrsi
    Csrci
  : unf_pseudo.
