Require Import Coq.ZArith.BinInt.
Require Import bbv.Word.

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

(*
Inductive WordWithSignedness(sz: nat): Set :=
| SignedWord: word sz -> WordWithSignedness sz
| UnsignedWord: word sz -> WordWithSignedness sz.
*)

Inductive SignedWord(sz: nat): Set := mkSignedWord: word sz -> SignedWord sz.
Inductive UnsignedWord(sz: nat): Set := mkUnsignedWord: word sz -> UnsignedWord sz.

Arguments mkSignedWord {_} _.
Arguments mkUnsignedWord {_} _.

Definition Int8 : Set := SignedWord  8.
Definition Int16: Set := SignedWord 16.
Definition Int32: Set := SignedWord 32.
Definition Int64: Set := SignedWord 64.

Definition Word8 : Set := UnsignedWord  8.
Definition Word16: Set := UnsignedWord 16.
Definition Word32: Set := UnsignedWord 32.
Definition Word64: Set := UnsignedWord 64.

Class Convertible(s u: Set) := mkConvertible {
  unsigned: s -> u;
  signed: u -> s;
}.

Definition signed0{sz: nat}(w: UnsignedWord sz): SignedWord sz :=
  match w with
  | mkUnsignedWord x => mkSignedWord x
  end.

Definition unsigned0{sz: nat}(w: SignedWord sz): UnsignedWord sz :=
  match w with
  | mkSignedWord x => mkUnsignedWord x
  end.

Definition Convertible_Int_Word(sz: nat): Convertible (SignedWord sz) (UnsignedWord sz) := {|
  unsigned := unsigned0;
  signed := signed0;
|}.

Instance Convertible_Int8_Word8: Convertible Int8 Word8 := Convertible_Int_Word 8.
Instance Convertible_Int16_Word16: Convertible Int16 Word16 := Convertible_Int_Word 16.
Instance Convertible_Int32_Word32: Convertible Int32 Word32 := Convertible_Int_Word 32.
Instance Convertible_Int64_Word64: Convertible Int64 Word64 := Convertible_Int_Word 64.

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
