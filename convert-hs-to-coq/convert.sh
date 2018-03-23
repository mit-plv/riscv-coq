#!/bin/sh

export STACK_YAML=../../hs-to-coq/stack.yaml

stack exec hs-to-coq -- -e ./Decode.edits  -p ./Decode_preamble.v  -e ./General.edits -e ./Base.edits -N -i ../../riscv-semantics/src -o ../src ../../riscv-semantics/src/Decode.hs
stack exec hs-to-coq -- -e ./Execute.edits -p ./Execute_preamble.v -e ./General.edits -e ./Base.edits -N -i ../../riscv-semantics/src -o ../src ../../riscv-semantics/src/ExecuteI.hs
stack exec hs-to-coq -- -e ./Execute.edits -p ./Execute_preamble.v -e ./General.edits -e ./Base.edits -N -i ../../riscv-semantics/src -o ../src ../../riscv-semantics/src/ExecuteI64.hs
stack exec hs-to-coq -- -e ./Execute.edits -p ./Execute_preamble.v -e ./General.edits -e ./Base.edits -N -i ../../riscv-semantics/src -o ../src ../../riscv-semantics/src/ExecuteM.hs
stack exec hs-to-coq -- -e ./Execute.edits -p ./Execute_preamble.v -e ./General.edits -e ./Base.edits -N -i ../../riscv-semantics/src -o ../src ../../riscv-semantics/src/ExecuteM64.hs
stack exec hs-to-coq -- -e ./Execute.edits -p ./Execute_preamble.v -e ./General.edits -e ./Base.edits -N -i ../../riscv-semantics/src -o ../src ../../riscv-semantics/src/ExecuteCSR.hs

