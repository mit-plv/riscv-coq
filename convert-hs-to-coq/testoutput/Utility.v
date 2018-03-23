(* Default settings (from HsToCoq.Coq.Preamble) *)

Generalizable All Variables.

Unset Implicit Arguments.
Set Maximal Implicit Insertion.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Coq.Program.Tactics.
Require Coq.Program.Wf.

(* Converted imports: *)

Require Control.Monad.Trans.State.Lazy.
Require Coq.Lists.List.
Require Data.Bits.
Require Data.Foldable.
Require GHC.Base.
Require GHC.Classes.
Require GHC.Enum.
Require GHC.Int.
Require GHC.Integer.Type.
Require GHC.List.
Require GHC.Num.
Require GHC.Real.
Require GHC.Types.
Require GHC.Word.
Import Data.Bits.Notations.
Import GHC.Base.Notations.
Import GHC.Classes.Notations.
Import GHC.Num.Notations.
Import GHC.Types.Notations.

(* Converted type declarations: *)

Definition MachineInt :=
  GHC.Int.Int64%type.

Record MachineWidth__Dict t := MachineWidth__Dict_Build {
  divu__ : t -> t -> t ;
  fromImm__ : MachineInt -> t ;
  highBits__ : GHC.Integer.Type.Integer -> t ;
  int16ToReg__ : GHC.Int.Int16 -> t ;
  int32ToReg__ : GHC.Int.Int32 -> t ;
  int64ToReg__ : GHC.Int.Int64 -> t ;
  int8ToReg__ : GHC.Int.Int8 -> t ;
  ltu__ : t -> t -> GHC.Types.Bool ;
  maxSigned__ : t ;
  maxUnsigned__ : t ;
  minSigned__ : t ;
  regToInt16__ : t -> GHC.Int.Int16 ;
  regToInt32__ : t -> GHC.Int.Int32 ;
  regToInt64__ : t -> GHC.Int.Int64 ;
  regToInt8__ : t -> GHC.Int.Int8 ;
  regToShamt__ : t -> GHC.Types.Int ;
  regToShamt5__ : t -> GHC.Types.Int ;
  regToZ_signed__ : t -> GHC.Integer.Type.Integer ;
  regToZ_unsigned__ : t -> GHC.Integer.Type.Integer ;
  remu__ : t -> t -> t ;
  sll__ : t -> GHC.Types.Int -> t ;
  sra__ : t -> GHC.Types.Int -> t ;
  srl__ : t -> GHC.Types.Int -> t ;
  uInt16ToReg__ : GHC.Int.Int16 -> t ;
  uInt32ToReg__ : GHC.Int.Int32 -> t ;
  uInt64ToReg__ : GHC.Int.Int64 -> t ;
  uInt8ToReg__ : GHC.Int.Int8 -> t }.

Definition MachineWidth t `{GHC.Real.Integral t} `{Data.Bits.Bits t} :=
  forall r, (MachineWidth__Dict t -> r) -> r.

Existing Class MachineWidth.

Definition divu `{g : MachineWidth t} : t -> t -> t :=
  g _ (divu__ t).

Definition fromImm `{g : MachineWidth t} : MachineInt -> t :=
  g _ (fromImm__ t).

Definition highBits `{g : MachineWidth t} : GHC.Integer.Type.Integer -> t :=
  g _ (highBits__ t).

Definition int16ToReg `{g : MachineWidth t} : GHC.Int.Int16 -> t :=
  g _ (int16ToReg__ t).

Definition int32ToReg `{g : MachineWidth t} : GHC.Int.Int32 -> t :=
  g _ (int32ToReg__ t).

Definition int64ToReg `{g : MachineWidth t} : GHC.Int.Int64 -> t :=
  g _ (int64ToReg__ t).

Definition int8ToReg `{g : MachineWidth t} : GHC.Int.Int8 -> t :=
  g _ (int8ToReg__ t).

Definition ltu `{g : MachineWidth t} : t -> t -> GHC.Types.Bool :=
  g _ (ltu__ t).

Definition maxSigned `{g : MachineWidth t} : t :=
  g _ (maxSigned__ t).

Definition maxUnsigned `{g : MachineWidth t} : t :=
  g _ (maxUnsigned__ t).

Definition minSigned `{g : MachineWidth t} : t :=
  g _ (minSigned__ t).

Definition regToInt16 `{g : MachineWidth t} : t -> GHC.Int.Int16 :=
  g _ (regToInt16__ t).

Definition regToInt32 `{g : MachineWidth t} : t -> GHC.Int.Int32 :=
  g _ (regToInt32__ t).

Definition regToInt64 `{g : MachineWidth t} : t -> GHC.Int.Int64 :=
  g _ (regToInt64__ t).

Definition regToInt8 `{g : MachineWidth t} : t -> GHC.Int.Int8 :=
  g _ (regToInt8__ t).

Definition regToShamt `{g : MachineWidth t} : t -> GHC.Types.Int :=
  g _ (regToShamt__ t).

Definition regToShamt5 `{g : MachineWidth t} : t -> GHC.Types.Int :=
  g _ (regToShamt5__ t).

Definition regToZ_signed `{g : MachineWidth t}
   : t -> GHC.Integer.Type.Integer :=
  g _ (regToZ_signed__ t).

Definition regToZ_unsigned `{g : MachineWidth t}
   : t -> GHC.Integer.Type.Integer :=
  g _ (regToZ_unsigned__ t).

Definition remu `{g : MachineWidth t} : t -> t -> t :=
  g _ (remu__ t).

Definition sll `{g : MachineWidth t} : t -> GHC.Types.Int -> t :=
  g _ (sll__ t).

Definition sra `{g : MachineWidth t} : t -> GHC.Types.Int -> t :=
  g _ (sra__ t).

Definition srl `{g : MachineWidth t} : t -> GHC.Types.Int -> t :=
  g _ (srl__ t).

Definition uInt16ToReg `{g : MachineWidth t} : GHC.Int.Int16 -> t :=
  g _ (uInt16ToReg__ t).

Definition uInt32ToReg `{g : MachineWidth t} : GHC.Int.Int32 -> t :=
  g _ (uInt32ToReg__ t).

Definition uInt64ToReg `{g : MachineWidth t} : GHC.Int.Int64 -> t :=
  g _ (uInt64ToReg__ t).

Definition uInt8ToReg `{g : MachineWidth t} : GHC.Int.Int8 -> t :=
  g _ (uInt8ToReg__ t).
(* Converted value declarations: *)

Local Definition MachineWidth__Int32_divu
   : GHC.Int.Int32 -> GHC.Int.Int32 -> GHC.Int.Int32 :=
  fun x y =>
    (GHC.Real.fromIntegral : GHC.Word.Word32 -> GHC.Int.Int32) (GHC.Real.rem
                                                                ((GHC.Real.fromIntegral : GHC.Int.Int32 ->
                                                                  GHC.Word.Word32) x)
                                                                ((GHC.Real.fromIntegral : GHC.Int.Int32 ->
                                                                  GHC.Word.Word32) y)).

Local Definition MachineWidth__Int32_fromImm : MachineInt -> GHC.Int.Int32 :=
  GHC.Real.fromIntegral.

Local Definition MachineWidth__Int32_int16ToReg
   : GHC.Int.Int16 -> GHC.Int.Int32 :=
  GHC.Real.fromIntegral.

Local Definition MachineWidth__Int32_int32ToReg
   : GHC.Int.Int32 -> GHC.Int.Int32 :=
  GHC.Real.fromIntegral.

Local Definition MachineWidth__Int32_int64ToReg
   : GHC.Int.Int64 -> GHC.Int.Int32 :=
  GHC.Real.fromIntegral.

Local Definition MachineWidth__Int32_int8ToReg
   : GHC.Int.Int8 -> GHC.Int.Int32 :=
  GHC.Real.fromIntegral.

Local Definition MachineWidth__Int32_ltu
   : GHC.Int.Int32 -> GHC.Int.Int32 -> GHC.Types.Bool :=
  fun x y =>
    ((GHC.Real.fromIntegral : GHC.Int.Int32 -> GHC.Word.Word32) x) GHC.Classes.<
    ((GHC.Real.fromIntegral : GHC.Int.Int32 -> GHC.Word.Word32) y).

Local Definition MachineWidth__Int32_maxSigned : GHC.Int.Int32 :=
  GHC.Enum.maxBound.

Local Definition MachineWidth__Int32_maxUnsigned : GHC.Int.Int32 :=
  (GHC.Real.fromIntegral : GHC.Word.Word32 -> GHC.Int.Int32)
  (GHC.Enum.maxBound : GHC.Word.Word32).

Local Definition MachineWidth__Int32_minSigned : GHC.Int.Int32 :=
  GHC.Enum.minBound.

Local Definition MachineWidth__Int32_regToInt16
   : GHC.Int.Int32 -> GHC.Int.Int16 :=
  GHC.Real.fromIntegral.

Local Definition MachineWidth__Int32_regToInt32
   : GHC.Int.Int32 -> GHC.Int.Int32 :=
  GHC.Real.fromIntegral.

Local Definition MachineWidth__Int32_regToInt64
   : GHC.Int.Int32 -> GHC.Int.Int64 :=
  GHC.Real.fromIntegral.

Local Definition MachineWidth__Int32_regToInt8
   : GHC.Int.Int32 -> GHC.Int.Int8 :=
  GHC.Real.fromIntegral.

Local Definition MachineWidth__Int32_regToZ_signed
   : GHC.Int.Int32 -> GHC.Integer.Type.Integer :=
  GHC.Real.fromIntegral.

Local Definition MachineWidth__Int32_regToZ_unsigned
   : GHC.Int.Int32 -> GHC.Integer.Type.Integer :=
  (GHC.Real.fromIntegral : GHC.Word.Word32 -> GHC.Integer.Type.Integer) GHC.Base.∘
  (GHC.Real.fromIntegral : GHC.Int.Int32 -> GHC.Word.Word32).

Local Definition MachineWidth__Int32_remu
   : GHC.Int.Int32 -> GHC.Int.Int32 -> GHC.Int.Int32 :=
  fun x y =>
    (GHC.Real.fromIntegral : GHC.Word.Word32 -> GHC.Int.Int32) (GHC.Real.rem
                                                                ((GHC.Real.fromIntegral : GHC.Int.Int32 ->
                                                                  GHC.Word.Word32) x)
                                                                ((GHC.Real.fromIntegral : GHC.Int.Int32 ->
                                                                  GHC.Word.Word32) y)).

Local Definition MachineWidth__Int32_sll
   : GHC.Int.Int32 -> GHC.Types.Int -> GHC.Int.Int32 :=
  Data.Bits.shiftL.

Local Definition MachineWidth__Int32_sra
   : GHC.Int.Int32 -> GHC.Types.Int -> GHC.Int.Int32 :=
  Data.Bits.shiftR.

Local Definition MachineWidth__Int32_srl
   : GHC.Int.Int32 -> GHC.Types.Int -> GHC.Int.Int32 :=
  fun x y =>
    (GHC.Real.fromIntegral : GHC.Word.Word32 -> GHC.Int.Int32) (Data.Bits.shiftR
                                                                ((GHC.Real.fromIntegral : GHC.Int.Int32 ->
                                                                  GHC.Word.Word32) x) y).

Local Definition MachineWidth__Int32_uInt16ToReg
   : GHC.Int.Int16 -> GHC.Int.Int32 :=
  fun x =>
    (GHC.Real.fromIntegral : GHC.Word.Word16 -> GHC.Int.Int32)
    ((GHC.Real.fromIntegral : GHC.Int.Int16 -> GHC.Word.Word16) x).

Local Definition MachineWidth__Int32_uInt32ToReg
   : GHC.Int.Int32 -> GHC.Int.Int32 :=
  fun x =>
    (GHC.Real.fromIntegral : GHC.Word.Word32 -> GHC.Int.Int32)
    ((GHC.Real.fromIntegral : GHC.Int.Int32 -> GHC.Word.Word32) x).

Local Definition MachineWidth__Int32_uInt64ToReg
   : GHC.Int.Int64 -> GHC.Int.Int32 :=
  fun x =>
    (GHC.Real.fromIntegral : GHC.Word.Word64 -> GHC.Int.Int32)
    ((GHC.Real.fromIntegral : GHC.Int.Int64 -> GHC.Word.Word64) x).

Local Definition MachineWidth__Int32_uInt8ToReg
   : GHC.Int.Int8 -> GHC.Int.Int32 :=
  fun x =>
    (GHC.Real.fromIntegral : GHC.Word.Word8 -> GHC.Int.Int32)
    ((GHC.Real.fromIntegral : GHC.Int.Int8 -> GHC.Word.Word8) x).

Local Definition MachineWidth__Int64_divu
   : GHC.Int.Int64 -> GHC.Int.Int64 -> GHC.Int.Int64 :=
  fun x y =>
    (GHC.Real.fromIntegral : GHC.Word.Word64 -> GHC.Int.Int64) (GHC.Real.rem
                                                                ((GHC.Real.fromIntegral : GHC.Int.Int64 ->
                                                                  GHC.Word.Word64) x)
                                                                ((GHC.Real.fromIntegral : GHC.Int.Int64 ->
                                                                  GHC.Word.Word64) y)).

Local Definition MachineWidth__Int64_fromImm : MachineInt -> GHC.Int.Int64 :=
  GHC.Real.fromIntegral.

Local Definition MachineWidth__Int64_int16ToReg
   : GHC.Int.Int16 -> GHC.Int.Int64 :=
  GHC.Real.fromIntegral.

Local Definition MachineWidth__Int64_int32ToReg
   : GHC.Int.Int32 -> GHC.Int.Int64 :=
  GHC.Real.fromIntegral.

Local Definition MachineWidth__Int64_int64ToReg
   : GHC.Int.Int64 -> GHC.Int.Int64 :=
  GHC.Real.fromIntegral.

Local Definition MachineWidth__Int64_int8ToReg
   : GHC.Int.Int8 -> GHC.Int.Int64 :=
  GHC.Real.fromIntegral.

Local Definition MachineWidth__Int64_ltu
   : GHC.Int.Int64 -> GHC.Int.Int64 -> GHC.Types.Bool :=
  fun x y =>
    ((GHC.Real.fromIntegral : GHC.Int.Int64 -> GHC.Word.Word64) x) GHC.Classes.<
    ((GHC.Real.fromIntegral : GHC.Int.Int64 -> GHC.Word.Word64) y).

Local Definition MachineWidth__Int64_maxSigned : GHC.Int.Int64 :=
  GHC.Enum.maxBound.

Local Definition MachineWidth__Int64_maxUnsigned : GHC.Int.Int64 :=
  (GHC.Real.fromIntegral : GHC.Word.Word64 -> GHC.Int.Int64)
  (GHC.Enum.maxBound : GHC.Word.Word64).

Local Definition MachineWidth__Int64_minSigned : GHC.Int.Int64 :=
  GHC.Enum.minBound.

Local Definition MachineWidth__Int64_regToInt16
   : GHC.Int.Int64 -> GHC.Int.Int16 :=
  GHC.Real.fromIntegral.

Local Definition MachineWidth__Int64_regToInt32
   : GHC.Int.Int64 -> GHC.Int.Int32 :=
  GHC.Real.fromIntegral.

Local Definition MachineWidth__Int64_regToInt64
   : GHC.Int.Int64 -> GHC.Int.Int64 :=
  GHC.Real.fromIntegral.

Local Definition MachineWidth__Int64_regToInt8
   : GHC.Int.Int64 -> GHC.Int.Int8 :=
  GHC.Real.fromIntegral.

Local Definition MachineWidth__Int64_regToZ_signed
   : GHC.Int.Int64 -> GHC.Integer.Type.Integer :=
  GHC.Real.fromIntegral.

Local Definition MachineWidth__Int64_regToZ_unsigned
   : GHC.Int.Int64 -> GHC.Integer.Type.Integer :=
  (GHC.Real.fromIntegral : GHC.Word.Word64 -> GHC.Integer.Type.Integer) GHC.Base.∘
  (GHC.Real.fromIntegral : GHC.Int.Int64 -> GHC.Word.Word64).

Local Definition MachineWidth__Int64_remu
   : GHC.Int.Int64 -> GHC.Int.Int64 -> GHC.Int.Int64 :=
  fun x y =>
    (GHC.Real.fromIntegral : GHC.Word.Word64 -> GHC.Int.Int64) (GHC.Real.rem
                                                                ((GHC.Real.fromIntegral : GHC.Int.Int64 ->
                                                                  GHC.Word.Word64) x)
                                                                ((GHC.Real.fromIntegral : GHC.Int.Int64 ->
                                                                  GHC.Word.Word64) y)).

Local Definition MachineWidth__Int64_sll
   : GHC.Int.Int64 -> GHC.Types.Int -> GHC.Int.Int64 :=
  Data.Bits.shiftL.

Local Definition MachineWidth__Int64_sra
   : GHC.Int.Int64 -> GHC.Types.Int -> GHC.Int.Int64 :=
  Data.Bits.shiftR.

Local Definition MachineWidth__Int64_srl
   : GHC.Int.Int64 -> GHC.Types.Int -> GHC.Int.Int64 :=
  fun x y =>
    (GHC.Real.fromIntegral : GHC.Word.Word64 -> GHC.Int.Int64) (Data.Bits.shiftR
                                                                ((GHC.Real.fromIntegral : GHC.Int.Int64 ->
                                                                  GHC.Word.Word64) x) y).

Local Definition MachineWidth__Int64_uInt16ToReg
   : GHC.Int.Int16 -> GHC.Int.Int64 :=
  fun x =>
    (GHC.Real.fromIntegral : GHC.Word.Word16 -> GHC.Int.Int64)
    ((GHC.Real.fromIntegral : GHC.Int.Int16 -> GHC.Word.Word16) x).

Local Definition MachineWidth__Int64_uInt32ToReg
   : GHC.Int.Int32 -> GHC.Int.Int64 :=
  fun x =>
    (GHC.Real.fromIntegral : GHC.Word.Word32 -> GHC.Int.Int64)
    ((GHC.Real.fromIntegral : GHC.Int.Int32 -> GHC.Word.Word32) x).

Local Definition MachineWidth__Int64_uInt64ToReg
   : GHC.Int.Int64 -> GHC.Int.Int64 :=
  fun x =>
    (GHC.Real.fromIntegral : GHC.Word.Word64 -> GHC.Int.Int64)
    ((GHC.Real.fromIntegral : GHC.Int.Int64 -> GHC.Word.Word64) x).

Local Definition MachineWidth__Int64_uInt8ToReg
   : GHC.Int.Int8 -> GHC.Int.Int64 :=
  fun x =>
    (GHC.Real.fromIntegral : GHC.Word.Word8 -> GHC.Int.Int64)
    ((GHC.Real.fromIntegral : GHC.Int.Int8 -> GHC.Word.Word8) x).

Definition bitSlice {a} `{Data.Bits.Bits a} `{GHC.Num.Num a}
   : a -> GHC.Types.Int -> GHC.Types.Int -> a :=
  fun x start end =>
    (Data.Bits.shiftR x start) Data.Bits..&.(**)
    (Data.Bits.complement GHC.Base.$
     Data.Bits.shiftL (GHC.Num.negate #1) (end GHC.Num.- start)).

Definition lower {a} {b} `{Data.Bits.Bits a} `{GHC.Real.Integral a}
  `{GHC.Num.Num b}
   : GHC.Types.Int -> a -> b :=
  fun n x => (GHC.Real.fromIntegral : a -> b) GHC.Base.$ bitSlice x #0 n.

Local Definition MachineWidth__Int64_regToShamt5
   : GHC.Int.Int64 -> GHC.Types.Int :=
  lower #5.

Local Definition MachineWidth__Int64_regToShamt
   : GHC.Int.Int64 -> GHC.Types.Int :=
  lower #6.

Local Definition MachineWidth__Int32_regToShamt5
   : GHC.Int.Int32 -> GHC.Types.Int :=
  lower #5.

Local Definition MachineWidth__Int32_regToShamt
   : GHC.Int.Int32 -> GHC.Types.Int :=
  lower #5.

Definition splitBytes {a} `{Data.Bits.Bits a} `{GHC.Real.Integral a}
   : GHC.Types.Int -> a -> list GHC.Word.Word8 :=
  fun n w =>
    GHC.Base.map (GHC.Real.fromIntegral : a -> GHC.Word.Word8)
    (Coq.Lists.List.flat_map (fun p => cons (bitSlice w p (p GHC.Num.+ #8)) nil)
                             (enumFromThenTo #0 #8 (n GHC.Num.- #1))).

Definition splitDouble {a} `{Data.Bits.Bits a} `{GHC.Real.Integral a}
   : a -> list GHC.Word.Word8 :=
  splitBytes #64.

Definition splitHalf {a} `{Data.Bits.Bits a} `{GHC.Real.Integral a}
   : a -> list GHC.Word.Word8 :=
  splitBytes #16.

Definition splitWord {a} `{Data.Bits.Bits a} `{GHC.Real.Integral a}
   : a -> list GHC.Word.Word8 :=
  splitBytes #32.

Local Definition MachineWidth__Int64_highBits
   : GHC.Integer.Type.Integer -> GHC.Int.Int64 :=
  fun n =>
    (GHC.Real.fromIntegral : GHC.Integer.Type.Integer -> GHC.Int.Int64) GHC.Base.$
    bitSlice n #64 #128.

Program Instance MachineWidth__Int64 : MachineWidth GHC.Int.Int64 :=
  fun _ k =>
    k {| divu__ := MachineWidth__Int64_divu ;
         fromImm__ := MachineWidth__Int64_fromImm ;
         highBits__ := MachineWidth__Int64_highBits ;
         int16ToReg__ := MachineWidth__Int64_int16ToReg ;
         int32ToReg__ := MachineWidth__Int64_int32ToReg ;
         int64ToReg__ := MachineWidth__Int64_int64ToReg ;
         int8ToReg__ := MachineWidth__Int64_int8ToReg ;
         ltu__ := MachineWidth__Int64_ltu ;
         maxSigned__ := MachineWidth__Int64_maxSigned ;
         maxUnsigned__ := MachineWidth__Int64_maxUnsigned ;
         minSigned__ := MachineWidth__Int64_minSigned ;
         regToInt16__ := MachineWidth__Int64_regToInt16 ;
         regToInt32__ := MachineWidth__Int64_regToInt32 ;
         regToInt64__ := MachineWidth__Int64_regToInt64 ;
         regToInt8__ := MachineWidth__Int64_regToInt8 ;
         regToShamt__ := MachineWidth__Int64_regToShamt ;
         regToShamt5__ := MachineWidth__Int64_regToShamt5 ;
         regToZ_signed__ := MachineWidth__Int64_regToZ_signed ;
         regToZ_unsigned__ := MachineWidth__Int64_regToZ_unsigned ;
         remu__ := MachineWidth__Int64_remu ;
         sll__ := MachineWidth__Int64_sll ;
         sra__ := MachineWidth__Int64_sra ;
         srl__ := MachineWidth__Int64_srl ;
         uInt16ToReg__ := MachineWidth__Int64_uInt16ToReg ;
         uInt32ToReg__ := MachineWidth__Int64_uInt32ToReg ;
         uInt64ToReg__ := MachineWidth__Int64_uInt64ToReg ;
         uInt8ToReg__ := MachineWidth__Int64_uInt8ToReg |}.

Local Definition MachineWidth__Int32_highBits
   : GHC.Integer.Type.Integer -> GHC.Int.Int32 :=
  fun n =>
    (GHC.Real.fromIntegral : GHC.Integer.Type.Integer -> GHC.Int.Int32) GHC.Base.$
    bitSlice n #32 #64.

Program Instance MachineWidth__Int32 : MachineWidth GHC.Int.Int32 :=
  fun _ k =>
    k {| divu__ := MachineWidth__Int32_divu ;
         fromImm__ := MachineWidth__Int32_fromImm ;
         highBits__ := MachineWidth__Int32_highBits ;
         int16ToReg__ := MachineWidth__Int32_int16ToReg ;
         int32ToReg__ := MachineWidth__Int32_int32ToReg ;
         int64ToReg__ := MachineWidth__Int32_int64ToReg ;
         int8ToReg__ := MachineWidth__Int32_int8ToReg ;
         ltu__ := MachineWidth__Int32_ltu ;
         maxSigned__ := MachineWidth__Int32_maxSigned ;
         maxUnsigned__ := MachineWidth__Int32_maxUnsigned ;
         minSigned__ := MachineWidth__Int32_minSigned ;
         regToInt16__ := MachineWidth__Int32_regToInt16 ;
         regToInt32__ := MachineWidth__Int32_regToInt32 ;
         regToInt64__ := MachineWidth__Int32_regToInt64 ;
         regToInt8__ := MachineWidth__Int32_regToInt8 ;
         regToShamt__ := MachineWidth__Int32_regToShamt ;
         regToShamt5__ := MachineWidth__Int32_regToShamt5 ;
         regToZ_signed__ := MachineWidth__Int32_regToZ_signed ;
         regToZ_unsigned__ := MachineWidth__Int32_regToZ_unsigned ;
         remu__ := MachineWidth__Int32_remu ;
         sll__ := MachineWidth__Int32_sll ;
         sra__ := MachineWidth__Int32_sra ;
         srl__ := MachineWidth__Int32_srl ;
         uInt16ToReg__ := MachineWidth__Int32_uInt16ToReg ;
         uInt32ToReg__ := MachineWidth__Int32_uInt32ToReg ;
         uInt64ToReg__ := MachineWidth__Int32_uInt64ToReg ;
         uInt8ToReg__ := MachineWidth__Int32_uInt8ToReg |}.

Definition combineBytes {a} `{Data.Bits.Bits a} `{GHC.Real.Integral a}
   : list GHC.Word.Word8 -> a :=
  fun bytes =>
    Data.Foldable.foldr (fun arg_0__ arg_1__ =>
                           match arg_0__, arg_1__ with
                           | pair x n, res =>
                               res Data.Bits..|.(**)
                               Data.Bits.shiftL ((GHC.Real.fromIntegral : GHC.Word.Word8 -> a) n) (#8 GHC.Num.*
                                                                                                   x)
                           end) #0 GHC.Base.$
    GHC.List.zip (enumFrom #0) bytes.

Definition liftState {m} {a} {b} `{(GHC.Base.Monad m)}
   : Control.Monad.Trans.State.Lazy.State a b ->
     Control.Monad.Trans.State.Lazy.StateT a m b :=
  Control.Monad.Trans.State.Lazy.mapStateT (GHC.Base.return_ GHC.Base.∘
                                            runIdentity).

Definition s16 {t} `{(GHC.Real.Integral t)} : t -> t :=
  fun n =>
    (GHC.Real.fromIntegral : GHC.Int.Int16 -> t) ((GHC.Real.fromIntegral : t ->
                                                   GHC.Int.Int16) n).

Definition s32 {t} `{(GHC.Real.Integral t)} : t -> t :=
  fun n =>
    (GHC.Real.fromIntegral : GHC.Int.Int32 -> t) ((GHC.Real.fromIntegral : t ->
                                                   GHC.Int.Int32) n).

Definition s8 {t} `{(GHC.Real.Integral t)} : t -> t :=
  fun n =>
    (GHC.Real.fromIntegral : GHC.Int.Int8 -> t) ((GHC.Real.fromIntegral : t ->
                                                  GHC.Int.Int8) n).

Definition setIndex {a} : GHC.Types.Int -> a -> list a -> list a :=
  fun i x l =>
    let 'pair left_ right_ := GHC.List.splitAt i l in
    left_ GHC.Base.++ (x GHC.Types.: (GHC.List.drop #1 right_)).

Definition u16 {t} `{(GHC.Real.Integral t)} : t -> t :=
  fun n =>
    (GHC.Real.fromIntegral : GHC.Word.Word16 -> t) ((GHC.Real.fromIntegral : t ->
                                                     GHC.Word.Word16) n).

Definition u32 {t} `{(GHC.Real.Integral t)} : t -> t :=
  fun n =>
    (GHC.Real.fromIntegral : GHC.Word.Word32 -> t) ((GHC.Real.fromIntegral : t ->
                                                     GHC.Word.Word32) n).

Definition u8 {t} `{(GHC.Real.Integral t)} : t -> t :=
  fun n =>
    (GHC.Real.fromIntegral : GHC.Word.Word8 -> t) ((GHC.Real.fromIntegral : t ->
                                                    GHC.Word.Word8) n).

(* Unbound variables:
     cons enumFrom enumFromThenTo list nil pair runIdentity
     Control.Monad.Trans.State.Lazy.State Control.Monad.Trans.State.Lazy.StateT
     Control.Monad.Trans.State.Lazy.mapStateT Coq.Lists.List.flat_map Data.Bits.Bits
     Data.Bits.complement Data.Bits.op_zizazi__ Data.Bits.op_zizbzi__
     Data.Bits.shiftL Data.Bits.shiftR Data.Foldable.foldr GHC.Base.Monad
     GHC.Base.map GHC.Base.op_z2218U__ GHC.Base.op_zd__ GHC.Base.op_zpzp__
     GHC.Base.return_ GHC.Classes.op_zl__ GHC.Enum.maxBound GHC.Enum.minBound
     GHC.Int.Int16 GHC.Int.Int32 GHC.Int.Int64 GHC.Int.Int8 GHC.Integer.Type.Integer
     GHC.List.drop GHC.List.splitAt GHC.List.zip GHC.Num.Num GHC.Num.fromInteger
     GHC.Num.negate GHC.Num.op_zm__ GHC.Num.op_zp__ GHC.Num.op_zt__ GHC.Real.Integral
     GHC.Real.fromIntegral GHC.Real.rem GHC.Types.Bool GHC.Types.Int
     GHC.Types.op_ZC__ GHC.Word.Word16 GHC.Word.Word32 GHC.Word.Word64 GHC.Word.Word8
*)
