Require Export riscv.Decidable.

Class NameWithEq := mkNameWithEq {
  name: Set;
  eq_name_dec: DecidableEq name
}.
