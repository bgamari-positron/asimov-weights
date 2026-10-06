# asimov-weights

Lean model for host-packed TransWarp weight tiles.

```lean
PackedWeights.toMatrix
  (shape : TwsShape)
  (format : TwsFormat)
  (bytes : ByteArray) :
  Except PackedWeights.Error (TwsMatrix shape.rows shape.columns)
```

Input uses packed group order: 32-byte WMem rows, 16 little-endian words per
row. `TwsMatrix rows columns` is indexed by logical dimensions and stores format
plus physical words. `TwsMatrix.toElements` computes
`Vector (Vector TwsScalar columns) rows`; no raw scalar fields are duplicated.
`PackedWeights.fromMatrix` serializes physical words back to bytes.

Lean proves both directions with `PackedWeights.fromMatrix_toMatrix`,
`PackedWeights.toMatrix_fromMatrix`, and the general correctly-sized-matrix
theorem `PackedWeights.toMatrix_fromMatrix_of_size`.

Enter pinned Lean 4.32.2 shell and test:

```sh
nix develop
lake test
```
