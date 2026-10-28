module

public import Theory.SpecificGroups.ONan.MatrixData

/-!
# Base-seven row encoding for finite matrix certificates

A row is stored as the natural number whose little-endian base-seven digits
are its 45 entries. Decoding is an ordinary Lean definition, so every use of
a table entry is subject to kernel reduction. This reduces data elaboration
without changing the matrix-valued certificate interfaces.
-/

namespace ONan.Simplicity.TwoCertificate.FusionData

/-- Decode the first 45 base-seven digits of each numerical row. -/
@[expose] public def decodeRows (rows : Fin 45 → ℕ) :
    Matrix (Fin 45) (Fin 45) (ZMod 7) :=
  fun i j => (rows i / 7 ^ j.val % 7 : ℕ)

end ONan.Simplicity.TwoCertificate.FusionData
