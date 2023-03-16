Require Import riscv.Spec.Decode.

Coercion IInstruction   : InstructionI   >-> Instruction.
Coercion MInstruction   : InstructionM   >-> Instruction.
Coercion AInstruction   : InstructionA   >-> Instruction.
Coercion FInstruction   : InstructionF   >-> Instruction.
Coercion I64Instruction : InstructionI64 >-> Instruction.
Coercion M64Instruction : InstructionM64 >-> Instruction.
Coercion A64Instruction : InstructionA64 >-> Instruction.
Coercion F64Instruction : InstructionF64 >-> Instruction.
Coercion CSRInstruction : InstructionCSR >-> Instruction.

(* separate notation to make sure coercions kick in *)
Declare Scope ilist_scope.
Notation "[[ ]]" := (@nil Instruction) (format "[[ ]]") : ilist_scope.
Notation "[[ x ]]" := (@cons Instruction x nil) : ilist_scope.
Notation "[[ x ; y ; .. ; z ]]" := (@cons Instruction x (@cons Instruction y .. (@cons Instruction z (@nil Instruction)) ..)) : ilist_scope.
