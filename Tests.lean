--module

import AsimovWeights

set_option autoImplicit false

open Asimov

private def bf16Format : TwsFormat :=
  { elementFormat :=
      { weightFormat := .bf16
        subBlockSize := .none
        subBlockFormat := .scaleNone }
    blockFormat := .scaleNone
    activFormat := .bf16 }

private def p4_1Format : TwsFormat :=
  { elementFormat :=
      { weightFormat := .int4
        subBlockSize := .size16
        subBlockFormat := .scaleBiasFP16 }
    blockFormat := .scaleNone
    activFormat := .bf16 }

private def zeroBytes (size : Nat) : ByteArray :=
  ByteArray.mk (Array.replicate size 0)

private def setWord (bytes : ByteArray) (row memory value : Nat) : ByteArray :=
  let offset := 2 * (16 * row + memory)
  (bytes.set! offset (UInt8.ofNat value)).set! (offset + 1) (UInt8.ofNat (value / 256))

#guard match PackedWeights.expectedByteCount .normal512x128 bf16Format.elementFormat with
  | .ok count => count == 131072
  | .error _ => false
#guard match PackedWeights.expectedByteCount .normal512x128 p4_1Format.elementFormat with
  | .ok count => count == 49152
  | .error _ => false
#guard match PackedWeights.expectedByteCount .k128x512 p4_1Format.elementFormat with
  | .error _ => true
  | .ok _ => false

private def bf16OneImage : ByteArray :=
  setWord (zeroBytes 131072) 0 0 0x3f80

#guard match PackedWeights.toMatrix .normal512x128 bf16Format bf16OneImage with
  | .ok matrix =>
      matrix.rows == 512 && matrix.columns == 128 && matrix.values.size == 65536 &&
      matrix.values[0]! == .finite 1 0
  | .error _ => false

#guard match PackedWeights.toMatrix .normal512x128 bf16Format bf16OneImage with
  | .ok matrix => matrix.toElements[0][0] == .finite 1 0
  | .error _ => false

#guard match PackedWeights.toMatrix .normal512x128 bf16Format bf16OneImage with
  | .ok matrix =>
      PackedWeights.fromMatrix matrix == bf16OneImage &&
      match PackedWeights.toMatrix .normal512x128 matrix.format (PackedWeights.fromMatrix matrix) with
      | .ok decoded => decoded == matrix
      | .error _ => false
  | .error _ => false

#guard match PackedWeights.toMatrix .normal512x128 bf16Format bf16OneImage with
  | .ok matrix =>
      let changed : TwsMatrix 512 128 :=
        { matrix with packedWords := matrix.packedWords.set! 0 (0, 0x40) }
      changed.values[0]! == .finite 1 1 && PackedWeights.fromMatrix changed != bf16OneImage
  | .error _ => false

private def p4_1Image : ByteArray :=
  let bytes := zeroBytes 49152
  let bytes := setWord bytes 0 0 0x3c00
  setWord bytes 1 1 0x0007

#guard match PackedWeights.toMatrix .normal512x128 p4_1Format p4_1Image with
  | .ok matrix =>
      matrix.values[0]! == .finite 7 0
  | .error _ => false


private def mxfp4Bs32Format : TwsFormat :=
  { elementFormat :=
      { weightFormat := .e2m1
        subBlockSize := .size32
        subBlockFormat := .scaleE8 }
    blockFormat := .scaleNone
    activFormat := .bf16 }

private def mxfp4Bs32Image : ByteArray :=
  let bytes := zeroBytes 34816
  let bytes := setWord bytes 0 0 0x007f
  setWord bytes 1 1 0x0020

#guard match PackedWeights.toMatrix .normal512x128 mxfp4Bs32Format mxfp4Bs32Image with
  | .ok matrix =>
      matrix.values[16]! == .finite 1 0
  | .error _ => false
def main : IO Unit := pure ()
