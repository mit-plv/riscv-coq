Require Import Coq.ZArith.BinInt.

Open Scope Z_scope.

Lemma test: forall
  (opcode rs1 rs2 funct3 simm12
  inst q q0 r1 r2
  r r0 q1 q2 q3 r3 q4 r4 q5 r5 q6 r6 q7 r7 q8 r8 q9 r9 q10 r10 q11 r11 q12
  r12 q13 r13 q14 r14 q15 r15 q16 r16: Z),
    0 <= opcode < 128 /\ 0 <= rs1 < 32 /\ 0 <= rs2 < 32 /\
    0 <= funct3 < 8 /\ - (2048) <= simm12 < 2048
  -> opcode + r1 * 128 + funct3 * 4096 + rs1 * 32768 + rs2 * 1048576 + r2 * 33554432 = inst
  -> 0 <= r16 < 2
  -> q9 = 2 * q16 + r16
  -> 0 <= r15 < 32
  -> q6 = 32 * q15 + r15
  -> 0 <= r14 < 32
  -> q5 = 32 * q14 + r14
  -> 0 <= r13 < 8
  -> q4 = 8 * q13 + r13
  -> 0 <= r12 < 128
  -> q3 = 128 * q12 + r12
  -> 0 <= r11 < 32
  -> q8 = 32 * q11 + r11
  -> 0 <= r10 < 128
  -> q7 = 128 * q10 + r10
  -> 0 <= r9 < 2048
  -> r10 * 32 + r11 = 2048 * q9 + r9
  -> 0 <= r8 < 128
  -> inst = 128 * q8 + r8
  -> 0 <= r7 < 33554432
  -> inst = 33554432 * q7 + r7
  -> 0 <= r6 < 1048576
  -> inst = 1048576 * q6 + r6
  -> 0 <= r5 < 32768
  -> inst = 32768 * q5 + r5
  -> 0 <= r4 < 4096
  -> inst = 4096 * q4 + r4
  -> 0 <= r3 < 1
  -> inst = 1 * q3 + r3
  -> 0 <= r2 < 128
  -> q0 = 128 * q2 + r2
  -> 0 <= r1 < 32
  -> q = 32 * q1 + r1
  -> 0 <= r0 < 32
  -> simm12 = 32 * q0 + r0
  -> 0 <= r < 1
  -> simm12 = 1 * q + r
  -> opcode = r12 /\ funct3 = r13 /\ rs1 = r14
     /\ rs2 = r15 /\ simm12 = r10 * 32 + r11 - r16 * 4096.
Proof.
  intros.

  (* When your proof goal is about Z numbers and omega fails or takes forever, do this: *)

  Require Import riscv.util.smt.
  smt.

  (* Then append "(check-sat)" to the goal and feed it into Z3.
     unsat means your goal is true
     sat   means your goal is false *)
Abort.
