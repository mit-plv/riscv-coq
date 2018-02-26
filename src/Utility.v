Require Import Coq.ZArith.BinInt.

Class IntegralConversion(t1 t2: Set) := mkIntegralConversion {
  fromIntegral: t1 -> t2
}.

(* Meaning of MachineInt: an integer big enough to hold an integer of a RISCV machine,
   no matter whether it's a 32-bit or 64-bit machine. *)
Definition MachineInt := Z.

Definition bitSlice(x: Z)(start eend: Z): Z :=
  Z.land (Z.shiftr x start) (Z.lnot (Z.shiftl (-1) (eend - start))).

Definition signExtend(l: Z)(n: Z): Z :=
  if Z.testbit n (l-1) then (n - (Z.setbit 0 l)) else n.

Definition lower{a: Set}{ic: IntegralConversion a Z}(n: Z)(x: a): Z :=
  bitSlice (fromIntegral x) 0 n.

(*
combineBytes :: (Bits a, Integral a) => [Word8] -> a
combineBytes bytes = foldr (\(x,n) res -> res .|. shiftL (fromIntegral n) (8*x)) 0 $ zip [0..] bytes
*)

(*
splitBytes :: (Bits a, Integral a) => Int -> a -> [Word8]
splitBytes n w = map fromIntegral [bitSlice w p (p + 8) | p <- [0,8..n-1]]

splitHalf :: (Bits a, Integral a) => a -> [Word8]
splitHalf = splitBytes 16

splitWord :: (Bits a, Integral a) => a -> [Word8]
splitWord = splitBytes 32

splitDouble :: (Bits a, Integral a) => a -> [Word8]
splitDouble = splitBytes 64
*)

Class MachineWidth(t: Set) := mkMachineWidth {
  (* the bits of the "shift amount" field to be used for in a shift operation *)
  shiftBits: t -> Z;
  (* should select bits [2*XLEN-1 ... XLEN] *)
  highBits: Z -> t;
}.


Definition MachineWidthInst(log2XLEN: Z)(t: Set)
  {ic0: IntegralConversion Z t}{ic1: IntegralConversion t Z}:
MachineWidth t := {|
  shiftBits := lower log2XLEN;
  highBits n := fromIntegral (bitSlice n (2 ^ log2XLEN) (2 * 2 ^ log2XLEN));
|}.
