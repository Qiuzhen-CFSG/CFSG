module

public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degree220Pair.NativeActions.ExteriorCoordinates.Evaluation

/-!
# A packed circuit for five-by-five binary determinants

The smaller Laplace minors are shared in this fixed-size circuit. Bit extraction
commutes with its AND and XOR operations, so each bit is exactly the existing
`binaryDet` of the corresponding five-by-five Boolean matrix. In particular,
the circuit can certify 462 minor columns at once, without an abstract matrix
or field computation during reduction.

This is the evaluator used for the first native generator in `../First.lean`.
Source convention: James, J. Algebra 27 (1973), 57–111; GM02 Proposition 5.1;
`NativeActions/source/README.md`.
-/

@[expose] public section
namespace Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degree220Pair.NativeActions.ExteriorCoordinates.First

/-- The fixed five-dimensional Laplace circuit shares its smaller minors. -/
def packedFive (m : Fin 5 → Fin 5 → ℕ) : ℕ :=
  let d01 := (m 3 0 &&& m 4 1) ^^^ ((m 3 1 &&& m 4 0))
  let d02 := (m 3 0 &&& m 4 2) ^^^ ((m 3 2 &&& m 4 0))
  let d03 := (m 3 0 &&& m 4 3) ^^^ ((m 3 3 &&& m 4 0))
  let d04 := (m 3 0 &&& m 4 4) ^^^ ((m 3 4 &&& m 4 0))
  let d12 := (m 3 1 &&& m 4 2) ^^^ ((m 3 2 &&& m 4 1))
  let d13 := (m 3 1 &&& m 4 3) ^^^ ((m 3 3 &&& m 4 1))
  let d14 := (m 3 1 &&& m 4 4) ^^^ ((m 3 4 &&& m 4 1))
  let d23 := (m 3 2 &&& m 4 3) ^^^ ((m 3 3 &&& m 4 2))
  let d24 := (m 3 2 &&& m 4 4) ^^^ ((m 3 4 &&& m 4 2))
  let d34 := (m 3 3 &&& m 4 4) ^^^ ((m 3 4 &&& m 4 3))
  let d012 := (m 2 0 &&& d12) ^^^ ((m 2 1 &&& d02) ^^^ ((m 2 2 &&& d01)))
  let d013 := (m 2 0 &&& d13) ^^^ ((m 2 1 &&& d03) ^^^ ((m 2 3 &&& d01)))
  let d014 := (m 2 0 &&& d14) ^^^ ((m 2 1 &&& d04) ^^^ ((m 2 4 &&& d01)))
  let d023 := (m 2 0 &&& d23) ^^^ ((m 2 2 &&& d03) ^^^ ((m 2 3 &&& d02)))
  let d024 := (m 2 0 &&& d24) ^^^ ((m 2 2 &&& d04) ^^^ ((m 2 4 &&& d02)))
  let d034 := (m 2 0 &&& d34) ^^^ ((m 2 3 &&& d04) ^^^ ((m 2 4 &&& d03)))
  let d123 := (m 2 1 &&& d23) ^^^ ((m 2 2 &&& d13) ^^^ ((m 2 3 &&& d12)))
  let d124 := (m 2 1 &&& d24) ^^^ ((m 2 2 &&& d14) ^^^ ((m 2 4 &&& d12)))
  let d134 := (m 2 1 &&& d34) ^^^ ((m 2 3 &&& d14) ^^^ ((m 2 4 &&& d13)))
  let d234 := (m 2 2 &&& d34) ^^^ ((m 2 3 &&& d24) ^^^ ((m 2 4 &&& d23)))
  let d0123 := (m 1 0 &&& d123) ^^^ ((m 1 1 &&& d023) ^^^ ((m 1 2 &&& d013) ^^^ ((m 1 3 &&& d012))))
  let d0124 := (m 1 0 &&& d124) ^^^ ((m 1 1 &&& d024) ^^^ ((m 1 2 &&& d014) ^^^ ((m 1 4 &&& d012))))
  let d0134 := (m 1 0 &&& d134) ^^^ ((m 1 1 &&& d034) ^^^ ((m 1 3 &&& d014) ^^^ ((m 1 4 &&& d013))))
  let d0234 := (m 1 0 &&& d234) ^^^ ((m 1 2 &&& d034) ^^^ ((m 1 3 &&& d024) ^^^ ((m 1 4 &&& d023))))
  let d1234 := (m 1 1 &&& d234) ^^^ ((m 1 2 &&& d134) ^^^ ((m 1 3 &&& d124) ^^^ ((m 1 4 &&& d123))))
  (m 0 0 &&& d1234) ^^^ ((m 0 1 &&& d0234) ^^^ ((m 0 2 &&& d0134) ^^^ ((m 0 3 &&& d0124) ^^^ ((m 0 4 &&& d0123)))))

lemma packedFive_bit (m : Fin 5 → Fin 5 → ℕ) (j : ℕ) :
    (packedFive m).testBit j = binaryDet 5 (fun a b => (m a b).testBit j) := by
  simp [packedFive, Nat.testBit_and, Nat.testBit_xor, binaryDet, List.ofFn_succ]
  rfl

end Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degree220Pair.NativeActions.ExteriorCoordinates.First
