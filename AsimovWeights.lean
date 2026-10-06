--module

import Asimov.Tws

/-!
# Packed TransWarp weight matrices

`PackedWeights.toMatrix` interprets one host-side packed TWS tile. The byte stream
is a sequence of groups. Each group is a sequence of 32-byte rows; each row holds
16 little-endian 16-bit WMem words. Groups, subblocks, and weights within a
subblock are in logical row-major order.

The layout arithmetic follows the `Blob` implementations in
`design/tws/models/rust/tws/src/blob/` and the read selection in
`design/tws/rtl/tws_element_format_control.sv`.
-/

set_option autoImplicit false

namespace Asimov

/-- Matrix shape selected at the TWS interface. -/
inductive TwsShape where
  | normal512x128
  | v512x128
  | k128x512
  deriving DecidableEq, Repr, Inhabited

/-- Logical matrix height. -/
def TwsShape.rows : TwsShape → Nat
  | .normal512x128 | .v512x128 => 512
  | .k128x512 => 128

/-- Logical matrix width. -/
def TwsShape.columns : TwsShape → Nat
  | .normal512x128 | .v512x128 => 128
  | .k128x512 => 512

/-- Exact value of a stored scalar. `finite c e` means `c * 2^e`. -/
inductive TwsScalar where
  | finite (coefficient : Int) (exponent : Int)
  | infinity (negative : Bool)
  | nan
  deriving DecidableEq, Repr, Inhabited

namespace TwsScalar

private def pow2 (n : Nat) : Int := (2 : Int) ^ n

/-- Canonical exact finite value. -/
def finiteNormalized (coefficient exponent : Int) : TwsScalar :=
  if coefficient == 0 then .finite 0 0
  else
    let zeros := coefficient.trailingZeros
    .finite (coefficient / pow2 zeros) (exponent + Int.ofNat zeros)

/-- Exact multiplication of values decoded from TWS formats. -/
def mul : TwsScalar → TwsScalar → TwsScalar
  | .nan, _ | _, .nan => .nan
  | .finite 0 _, .infinity _ | .infinity _, .finite 0 _ => .nan
  | .infinity a, .infinity b => .infinity (a != b)
  | .infinity a, .finite b _ | .finite b _, .infinity a =>
      .infinity (a != (b < 0))
  | .finite a ea, .finite b eb => finiteNormalized (a * b) (ea + eb)

/-- Exact addition of values decoded from TWS formats. -/
def add : TwsScalar → TwsScalar → TwsScalar
  | .nan, _ | _, .nan => .nan
  | .infinity a, .infinity b => if a == b then .infinity a else .nan
  | .infinity a, _ | _, .infinity a => .infinity a
  | .finite 0 _, x | x, .finite 0 _ => x
  | .finite a ea, .finite b eb =>
      if ea ≤ eb then finiteNormalized (a + b * pow2 (eb - ea).toNat) ea
      else finiteNormalized (a * pow2 (ea - eb).toNat + b) eb
end TwsScalar

/-- Two bytes of one physical WMem word, low byte first. -/
abbrev TwsPackedWord := UInt8 × UInt8

private def bytesToWords : List UInt8 → List TwsPackedWord
  | low :: high :: rest => (low, high) :: bytesToWords rest
  | _ => []

private def wordsToBytes : List TwsPackedWord → List UInt8
  | [] => []
  | (low, high) :: rest => low :: high :: wordsToBytes rest

private theorem wordsToBytes_bytesToWords (bytes : List UInt8)
    (h : bytes.length % 2 = 0) : wordsToBytes (bytesToWords bytes) = bytes := by
  cases bytes with
  | nil => rfl
  | cons low rest =>
      cases rest with
      | nil => simp at h
      | cons high rest =>
          simp only [bytesToWords, wordsToBytes, List.cons.injEq, true_and]
          apply wordsToBytes_bytesToWords rest
          simp only [List.length_cons] at h
          omega

private theorem bytesToWords_wordsToBytes (words : List TwsPackedWord) :
    bytesToWords (wordsToBytes words) = words := by
  induction words with
  | nil => rfl
  | cons word rest ih =>
      cases word
      simp [wordsToBytes, bytesToWords, ih]

private theorem wordsToBytes_length (words : List TwsPackedWord) :
    (wordsToBytes words).length = 2 * words.length := by
  induction words with
  | nil => rfl
  | cons word rest ih =>
      cases word
      simp [wordsToBytes, ih, Nat.mul_add]

private theorem byteWordRoundTrip (bytes : ByteArray)
    (h : bytes.size % 2 = 0) :
    ByteArray.mk (wordsToBytes (bytesToWords bytes.data.toList)).toArray = bytes := by
  cases bytes with
  | mk data =>
      apply ByteArray.ext
      cases data with
      | mk values =>
          change (wordsToBytes (bytesToWords values)).toArray = values.toArray
          rw [wordsToBytes_bytesToWords values]
          exact h

/-- Matrix format and reconstructible words, indexed by logical dimensions. -/
structure TwsMatrix (rows columns : Nat) where
  format : TwsFormat
  packedWords : Array TwsPackedWord
  deriving DecidableEq, Inhabited

/-- Statically indexed matrix height. -/
def TwsMatrix.rows {rows columns : Nat} (_ : TwsMatrix rows columns) : Nat := rows

/-- Statically indexed matrix width. -/
def TwsMatrix.columns {rows columns : Nat} (_ : TwsMatrix rows columns) : Nat := columns

/-- Why a packed tile cannot be interpreted. -/
inductive PackedWeights.Error where
  | invalidFormat (problems : List String)
  | unsupportedPairing (weight : TwsWeightFormat) (subblock : TwsSubBlockFormat)
  | compressedAttentionShape (shape : TwsShape)
  | wrongByteCount (expected actual : Nat)
  deriving DecidableEq, Repr

namespace PackedWeights

private structure Layout where
  weightBits : Nat
  blocksPerGroup : Nat
  weightsPerBlock : Nat
  rowsPerGroup : Nat
  deriving Repr

private def weightBits : TwsWeightFormat → Nat
  | .uint1 => 1
  | .int2 | .uint2 => 2
  | .int4 | .uint4 | .e2m1 => 4
  | .int8 | .uint8 | .e4m3 | .e5m2 => 8
  | .fp16 | .bf16 => 16

private def blocksPerGroup (format : TwsSubBlockFormat) : Nat :=
  if format.hasMetadata then 2 ^ format.lbSubBlocksPerGroup else 1

private def weightsPerBlock (format : TwsElementFormat) : Nat :=
  if format.subBlockFormat.hasMetadata then
    16 * 2 ^ format.subBlockSize.lbIndicesPerSubBlock
  else
    16 * 2 ^ format.weightFormat.lbIndicesPerWord

private def supported (format : TwsElementFormat) : Bool :=
  match format.subBlockFormat, weightBits format.weightFormat with
  | .scaleNone, 1 | .scaleNone, 16 | .scale2BiasMinusOne, 1 => true
  | .scaleFP16, 2 | .scaleFP16, 4 | .scaleFP16, 8
  | .scaleBF16, 2 | .scaleBF16, 4 | .scaleBF16, 8
  | .scaleBiasFP16, 2 | .scaleBiasFP16, 4 | .scaleBiasFP16, 8
  | .scaleBiasBF16, 2 | .scaleBiasBF16, 4 | .scaleBiasBF16, 8 => true
  | .scaleE5M2, 4 | .scaleE5M2, 8
  | .scaleE4M3, 4 | .scaleE4M3, 8
  | .scaleE8, 4 | .scaleE8, 8 => true
  | _, _ => false

private def layout (format : TwsElementFormat) : Except Error Layout :=
  let problems := format.problems "weights"
  if problems != [] then .error (.invalidFormat problems)
  else if !supported format then
    .error (.unsupportedPairing format.weightFormat format.subBlockFormat)
  else .ok
    { weightBits := weightBits format.weightFormat
      blocksPerGroup := blocksPerGroup format.subBlockFormat
      weightsPerBlock := weightsPerBlock format
      rowsPerGroup := format.wordsPerGroup }

private def byte (bytes : ByteArray) (index : Nat) : Nat :=
  bytes.get! index |>.toNat

private def word (bytes : ByteArray) (groupBase row memory : Nat) : UInt16 :=
  let offset := groupBase + 2 * (16 * row + memory)
  UInt16.ofNat (byte bytes offset + 256 * byte bytes (offset + 1))

private def field (value : UInt16) (shift width : Nat) : UInt16 :=
  UInt16.ofNat ((value.toNat / 2 ^ shift) % 2 ^ width)

private def signed (bits width : Nat) : Int :=
  if bits < 2 ^ (width - 1) then Int.ofNat bits
  else Int.ofNat bits - Int.ofNat (2 ^ width)

private def finite (negative : Bool) (coefficient : Nat) (exponent : Int) : TwsScalar :=
  .finiteNormalized (if negative then -Int.ofNat coefficient else Int.ofNat coefficient) exponent

private def decodeBinary (exponentBits fractionBits bias bits : Nat) : TwsScalar :=
  let fraction := bits % 2 ^ fractionBits
  let exponent := (bits / 2 ^ fractionBits) % 2 ^ exponentBits
  let negative := bits / 2 ^ (fractionBits + exponentBits) != 0
  if exponent == 2 ^ exponentBits - 1 then
    if fraction == 0 then .infinity negative else .nan
  else if exponent == 0 then
    finite negative fraction (1 - bias - fractionBits)
  else
    finite negative (2 ^ fractionBits + fraction)
      (Int.ofNat exponent - Int.ofNat bias - Int.ofNat fractionBits)

private def decodeE4M3 (bits : Nat) : TwsScalar :=
  let fraction := bits % 8
  let exponent := (bits / 8) % 16
  let negative := bits / 128 != 0
  if bits % 128 == 127 then .nan
  else if exponent == 0 then finite negative fraction (-9)
  else finite negative (8 + fraction) (Int.ofNat exponent - 10)

private def decodeWeight (format : TwsWeightFormat) (bits : UInt16) : TwsScalar :=
  let n := bits.toNat
  match format with
  | .uint1 | .uint2 | .uint4 | .uint8 => .finiteNormalized (Int.ofNat n) 0
  | .int2 => .finiteNormalized (signed n 2) 0
  | .int4 => .finiteNormalized (signed n 4) 0
  | .int8 => .finiteNormalized (signed n 8) 0
  | .e2m1 =>
      let magnitude := #[0, 1, 2, 3, 4, 6, 8, 12][n % 8]!
      finite (n / 8 != 0) magnitude (-1)
  | .e4m3 => decodeE4M3 n
  | .e5m2 => decodeBinary 5 2 15 n
  | .fp16 => decodeBinary 5 10 15 n
  | .bf16 => decodeBinary 8 7 127 n

private def decodeScale (format : TwsSubBlockFormat) (bits : UInt16) : TwsScalar :=
  match format with
  | .scaleE5M2 => decodeBinary 5 2 15 bits.toNat
  | .scaleE4M3 => decodeE4M3 bits.toNat
  | .scaleE8 => if bits.toNat == 0xff then .nan else .finite 1 (Int.ofNat bits.toNat - 127)
  | .scaleFP16 | .scaleBiasFP16 => decodeBinary 5 10 15 bits.toNat
  | .scaleBF16 | .scaleBiasBF16 => decodeBinary 8 7 127 bits.toNat
  | .scaleNone => .finite 1 0
  | .scale2BiasMinusOne => .finite 2 0

private def hasBias : TwsSubBlockFormat → Bool
  | .scaleBiasFP16 | .scaleBiasBF16 | .scale2BiasMinusOne => true
  | _ => false

private def metadata (bytes : ByteArray) (groupBase block : Nat)
    (format : TwsSubBlockFormat) : Option UInt16 × Option UInt16 :=
  match format with
  | .scaleNone => (none, none)
  | .scale2BiasMinusOne => (none, none)
  | .scaleE5M2 | .scaleE4M3 | .scaleE8 =>
      let packed := word bytes groupBase 0 (block / 2)
      (some (field packed (8 * (block % 2)) 8), none)
  | .scaleFP16 | .scaleBF16 => (some (word bytes groupBase 0 block), none)
  | .scaleBiasFP16 | .scaleBiasBF16 =>
      (some (word bytes groupBase 0 block),
       some (word bytes groupBase 0 (8 + block)))

private structure Location where
  row : Nat
  memory : Nat
  shift : Nat

private def hadamardLocation (weight : Nat) : Location :=
  { row := 0
    memory := ((weight / 2) % 8) * 2 + (weight / 16) % 2
    shift := (weight % 2) * 8 + weight / 32 }

private def mxLocation (layout : Layout) (block weight : Nat) : Location :=
  let indicesPerSubblock := layout.weightsPerBlock / 16
  let position := weight / 16
  let column := weight % 16
  let parity := 1 - (block / 2) % 2
  let is8 := layout.weightBits == 8
  let row := if is8 then
      1 + (block / 4) * 2 * indicesPerSubblock + (block % 2) * indicesPerSubblock + position
    else
      1 + (block / 4) * indicesPerSubblock +
        (block % 2) * (indicesPerSubblock / 2) + position / 2
  let shift := if is8 then 8 * (column % 2)
    else 4 * (2 * (column % 2) + if indicesPerSubblock == 1 then block % 2 else position % 2)
  { row, memory := 2 * (column / 2) + parity, shift }

private def ordinaryLocation (layout : Layout) (block weight : Nat) : Location :=
  let pairsPerWord := 8 / layout.weightBits
  let pairLane := (block / 2) % pairsPerWord
  let parity0 := 1 - block % 2
  let parity :=
    if layout.weightBits == 8 && (block == 2 || block == 3) && weight ≥ 4 then 1 - parity0
    else parity0
  { row := 1 + block / (16 / layout.weightBits)
    memory := parity + 2 * (weight / 2)
    shift := layout.weightBits * (pairLane + pairsPerWord * (weight % 2)) }

private def location (layout : Layout) (format : TwsElementFormat) (block weight : Nat) : Location :=
  if !format.subBlockFormat.hasMetadata then hadamardLocation weight
  else match format.subBlockFormat with
    | .scaleE5M2 | .scaleE4M3 | .scaleE8 => mxLocation layout block weight
    | _ => ordinaryLocation layout block weight

private def decodeOne (bytes : ByteArray) (groupBase : Nat) (layout : Layout)
    (format : TwsElementFormat) (block weight : Nat) : TwsScalar :=
  let loc := if layout.weightBits == 16 then { row := 0, memory := weight, shift := 0 }
    else location layout format block weight
  let weightRaw := field (word bytes groupBase loc.row loc.memory) loc.shift layout.weightBits
  let (scaleBits, biasBits) := metadata bytes groupBase block format.subBlockFormat
  let scale := match scaleBits with
    | some bits => decodeScale format.subBlockFormat bits
    | none => decodeScale format.subBlockFormat 0
  let bias := match biasBits with
    | some bits => decodeScale format.subBlockFormat bits
    | none => if hasBias format.subBlockFormat then .finite (-1) 0 else .finite 0 0
  (decodeWeight format.weightFormat weightRaw).mul scale |>.add bias

/-- Required byte count for one packed tile. -/
def expectedByteCount (shape : TwsShape) (format : TwsElementFormat) : Except Error Nat :=
  match layout format with
  | .error error => .error error
  | .ok layout =>
      if shape != .normal512x128 && layout.weightBits != 16 then
        .error (.compressedAttentionShape shape)
      else
        let scalarCount := shape.rows * shape.columns
        let scalarsPerGroup := layout.blocksPerGroup * layout.weightsPerBlock
        .ok (scalarCount / scalarsPerGroup * layout.rowsPerGroup * 32)

private theorem expectedByteCount_even {shape : TwsShape} {format : TwsElementFormat}
    {count : Nat} (h : expectedByteCount shape format = .ok count) : count % 2 = 0 := by
  simp only [expectedByteCount] at h
  split at h
  · contradiction
  split at h
  · contradiction
  · cases h
    omega

private def decodeValues (rows columns : Nat) (format : TwsElementFormat)
    (bytes : ByteArray) (layout : Layout) : Array TwsScalar := Id.run do
  let scalarCount := rows * columns
  let scalarsPerGroup := layout.blocksPerGroup * layout.weightsPerBlock
  let groups := scalarCount / scalarsPerGroup
  let groupBytes := layout.rowsPerGroup * 32
  let mut values := Array.mkEmpty scalarCount
  for group in [0:groups] do
    let base := group * groupBytes
    for block in [0:layout.blocksPerGroup] do
      for weight in [0:layout.weightsPerBlock] do
        values := values.push (decodeOne bytes base layout format block weight)
  return values

/-- Interpret one host-packed TWS tile as an exact, row-major matrix. -/
def toMatrix (shape : TwsShape) (format : TwsFormat) (bytes : ByteArray) :
    Except Error (TwsMatrix shape.rows shape.columns) :=
  match layout format.elementFormat with
  | .error error => .error error
  | .ok _ =>
      match expectedByteCount shape format.elementFormat with
      | .error error => .error error
      | .ok expected =>
          if bytes.size = expected then .ok
            { format, packedWords := (bytesToWords bytes.data.toList).toArray }
          else .error (.wrongByteCount expected bytes.size)

/-- Recover exact host-packed bytes retained by matrix interpretation. -/
def fromMatrix {rows columns : Nat} (matrix : TwsMatrix rows columns) : ByteArray :=
  ByteArray.mk (wordsToBytes matrix.packedWords.toList).toArray

/-- Row-major scalar view computed from matrix physical words. -/
def _root_.Asimov.TwsMatrix.values {rows columns : Nat}
    (matrix : TwsMatrix rows columns) : Array TwsScalar :=
  match layout matrix.format.elementFormat with
  | .error _ => #[]
  | .ok layout =>
      decodeValues rows columns matrix.format.elementFormat (fromMatrix matrix) layout

/-- Read one scalar from matrix view. -/
def _root_.Asimov.TwsMatrix.get? {rows columns : Nat}
    (matrix : TwsMatrix rows columns) (row column : Nat) : Option TwsScalar :=
  if row < rows && column < columns then
    matrix.values[row * columns + column]?
  else none

/-- Scalar matrix as statically sized rows and columns. -/
def _root_.Asimov.TwsMatrix.toElements {rows columns : Nat}
    (matrix : TwsMatrix rows columns) : Vector (Vector TwsScalar columns) rows :=
  let values := matrix.values
  Vector.ofFn fun row =>
    Vector.ofFn fun column => values[row.val * columns + column.val]!

/-- Successful interpretation followed by packing returns original bytes. -/
theorem fromMatrix_toMatrix {shape : TwsShape} {format : TwsFormat}
    {bytes : ByteArray} {matrix : TwsMatrix shape.rows shape.columns}
    (h : toMatrix shape format bytes = .ok matrix) :
    fromMatrix matrix = bytes := by
  cases hLayout : layout format.elementFormat with
  | error error => simp [toMatrix, hLayout] at h
  | ok layout =>
      cases hCount : expectedByteCount shape format.elementFormat with
      | error error => simp [toMatrix, hLayout, hCount] at h
      | ok count =>
          by_cases hSize : bytes.size = count
          · have countEven := expectedByteCount_even hCount
            have bytesEven : bytes.size % 2 = 0 := by omega
            simp [toMatrix, hLayout, hCount, hSize] at h
            cases h
            exact byteWordRoundTrip bytes bytesEven
          · simp [toMatrix, hLayout, hCount, hSize] at h

/-- Packing then interpreting any correctly sized matrix preserves it. -/
theorem toMatrix_fromMatrix_of_size (shape : TwsShape)
    (matrix : TwsMatrix shape.rows shape.columns)
    (hCount : expectedByteCount shape matrix.format.elementFormat =
      .ok (2 * matrix.packedWords.size)) :
    toMatrix shape matrix.format (fromMatrix matrix) = .ok matrix := by
  cases hLayout : layout matrix.format.elementFormat with
  | error error => simp [expectedByteCount, hLayout] at hCount
  | ok layout =>
      have hSize : (fromMatrix matrix).size = 2 * matrix.packedWords.size := by
        change (wordsToBytes matrix.packedWords.toList).length =
          2 * matrix.packedWords.toList.length
        exact wordsToBytes_length matrix.packedWords.toList
      have hWords : bytesToWords (fromMatrix matrix).data.toList = matrix.packedWords.toList := by
        change bytesToWords (wordsToBytes matrix.packedWords.toList) = matrix.packedWords.toList
        exact bytesToWords_wordsToBytes matrix.packedWords.toList
      simp [toMatrix, hLayout, hCount, hSize, hWords]

/-- Repacking and interpreting any successfully decoded matrix preserves matrix. -/
theorem toMatrix_fromMatrix {shape : TwsShape} {format : TwsFormat}
    {bytes : ByteArray} {matrix : TwsMatrix shape.rows shape.columns}
    (h : toMatrix shape format bytes = .ok matrix) :
    toMatrix shape matrix.format (fromMatrix matrix) = .ok matrix := by
  have original := h
  have bytesEq := fromMatrix_toMatrix h
  rw [bytesEq]
  simp only [toMatrix] at h
  split at h
  all_goals try split at h
  all_goals try split at h
  all_goals try contradiction
  all_goals cases h
  exact original

end PackedWeights
end Asimov
