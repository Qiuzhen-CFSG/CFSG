module

public import Theory.SpecificGroups.BabyMonster.Order.LowerBound.ImageSize.Reduction
public import Theory.SpecificGroups.BabyMonster.Order.LowerBound.ImageSize.Conjugacy.Data

/-!
# Matrix certificates for the recovered generators

Breuer–Magaard–Wilson, *Verification of the ordinary character table of the
Baby Monster*, §3.4, https://arxiv.org/abs/1902.07758, compare standard bases
for the original and recovered pairs. With right conjugation, the certificate
equations are `atlasA * Q = Q * A` and `atlasB * Q = Q * B`.

The assembly below constructs the ambient unit directly from a matrix and
its checked inverse. Multiplication by that inverse turns the intertwining
equations into simultaneous conjugacy. No membership of `Q` in the generated
subgroup is required. The concrete evaluations and matrix equations remain
explicit premises until the numerical certificates have been proved.
-/

@[expose] public section

namespace BabyMonster.OrderLowerBound

/-- An invertible intertwiner and evaluations of the two recovered words
suffice to certify simultaneous conjugacy in the ambient matrix group. -/
theorem matrix_recovered_conjugacy_of_intertwiner
    (ha : atlasA ^ 2 = 1) (hb : atlasB ^ 3 = 1)
    (Q R A B : AtlasMatrix)
    (hQR : Q * R = 1) (hRQ : R * Q = 1)
    (hA : atlasA * Q = Q * A) (hB : atlasB * Q = Q * B)
    (hA' : A = (↑(recoveredA (matrixGenerators ha hb)) : AtlasMatrix))
    (hB' : B = (↑(recoveredB (matrixGenerators ha hb)) : AtlasMatrix)) :
    ∃ u : MatrixGroup,
      wordConjugate (standardA ha) u = recoveredA (matrixGenerators ha hb) ∧
      wordConjugate (standardB hb) u = recoveredB (matrixGenerators ha hb) := by
  let u : MatrixGroup := ⟨Q, R, hQR, hRQ⟩
  refine ⟨u, ?_, ?_⟩
  · apply Units.ext
    change R * atlasA * Q = _
    rw [mul_assoc, hA, ← mul_assoc, hRQ, one_mul, hA']
  · apply Units.ext
    change R * atlasB * Q = _
    rw [mul_assoc, hB, ← mul_assoc, hRQ, one_mul, hB']

end BabyMonster.OrderLowerBound
