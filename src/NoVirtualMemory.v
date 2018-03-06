Require Import riscv.Utility.
Require Import riscv.Program.
Require Import riscv.util.Monad.
Require Import riscv.util.NameWithEq.

Inductive AccessType: Set := Instruction | Load | Store.

Local Open Scope alu_scope.

(* in a system with virtual memory, this would also do the translation, but in our
   case, we only verify the alignment *)
Definition withTranslation{N: NameWithEq}{t: Set}{MW: MachineWidth t}{M: Type -> Type}
  {MM: Monad M}{RVS: RiscvState M}
  (accessType: AccessType)(alignment: t)(addr: t)(memFunc: t -> M unit): M unit :=
  if rem addr alignment /= zero
  then raiseException zero four
  else memFunc addr.
