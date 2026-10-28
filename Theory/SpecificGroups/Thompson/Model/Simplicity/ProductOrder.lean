module

public import Theory.SpecificGroups.Thompson.Model.GeneratorCertificates
public import Theory.SpecificGroups.Thompson.Model.Simplicity.ProductOrder.Certificates

/-!
# The Thompson generator product has nineteenth power one

The packed product certificates supply matrices along the addition chain
1, 2, 4, 8, 9, 18, 19. Abstract monoid algebra assembles them without unfolding
concrete matrix multiplication. Faithfulness transfers the matrix relation
to the two generators of the fixed group carrier.

Source: the standard-generator relation on the ATLAS Thompson group page,
https://brauer.maths.qmul.ac.uk/Atlas/v3/spor/Th/ (R. A. Wilson,
S. J. Nickerson and J. N. Bray). Matrix provenance is in
`Model/source/README.md`; kernel-checked witnesses are in
`ProductOrder/Certificates.lean`.
-/

namespace Thompson

private theorem pow_nineteen_of_chain {M : Type*} [Monoid M]
    (x x2 x4 x8 x9 x18 : M)
    (h2 : x * x = x2) (h4 : x2 * x2 = x4) (h8 : x4 * x4 = x8)
    (h9 : x8 * x = x9) (h18 : x9 * x9 = x18) (h19 : x18 * x = 1) :
    x ^ 19 = 1 := by
  have hx2 : x ^ 2 = x2 := by simpa only [pow_two] using h2
  have hx4 : x ^ 4 = x4 := by
    calc
      x ^ 4 = x ^ 2 * x ^ 2 := pow_add x 2 2
      _ = x4 := by rw [hx2]; exact h4
  have hx8 : x ^ 8 = x8 := by
    calc
      x ^ 8 = x ^ 4 * x ^ 4 := pow_add x 4 4
      _ = x8 := by rw [hx4]; exact h8
  have hx9 : x ^ 9 = x9 := by
    calc
      x ^ 9 = x ^ 8 * x := pow_succ x 8
      _ = x9 := by rw [hx8]; exact h9
  have hx18 : x ^ 18 = x18 := by
    calc
      x ^ 18 = x ^ 9 * x ^ 9 := pow_add x 9 9
      _ = x18 := by rw [hx9]; exact h18
  calc
    x ^ 19 = x ^ 18 * x := pow_succ x 18
    _ = 1 := by rw [hx18]; exact h19

/-- The concrete ATLAS generator product has nineteenth power one. -/
public theorem atlasAB_pow_nineteen : (atlasA * atlasB) ^ 19 = 1 := by
  obtain ⟨x1, x2, x4, x8, x9, x18, h1, h2, h4, h8, h9, h18, h19⟩ :=
    atlasAB_power_chain
  rw [h1]
  exact pow_nineteen_of_chain x1 x2 x4 x8 x9 x18 h2 h4 h8 h9 h18 h19

/-- The two certified Thompson generators satisfy the ATLAS product relation. -/
public theorem generatorAB_pow_nineteen : (generatorA * generatorB) ^ 19 = 1 := by
  apply matrixHom_injective
  rw [map_pow, map_mul, matrixHom_generatorA, matrixHom_generatorB, map_one,
    atlasAB_pow_nineteen]

end Thompson
