module

public import Theory.SpecificGroups.ONan.MatrixModel
public import Theory.SpecificGroups.ONan.ProjectiveSimplicity.RelationData
public import Theory.SpecificGroups.ONan.ProjectiveSimplicity.PrimeNormalGeneration.NineteenData

/-!
# The nineteenth-power relation for the O'Nan generators

The actual linear matrices satisfy `(A * B²)¹⁹ = I`, hence the same relation
holds projectively. Explicit intermediate matrices separate the kernel checks
for the products in a repeated-squaring chain. No presentation assumption or
external computation is used as a proof.

Source matrices: ATLAS of Finite Group Representations, preserved and
attributed in `refs/original/onan/README.md`.
-/

namespace ONan.Simplicity

open PrimeNormalData

set_option maxRecDepth 4096
set_option maxHeartbeats 0

private theorem b_sq : matrixB * matrixB = SimplicityData.b2 := by
  apply Matrix.ext
  unfold SimplicityData.b2
  decide +kernel

private theorem d_eq : matrixA * SimplicityData.b2 = d := by
  apply Matrix.ext
  unfold SimplicityData.b2 d
  decide +kernel

private theorem d_sq : d * d = d2 := by
  apply Matrix.ext
  unfold d d2
  decide +kernel

private theorem d2_sq : d2 * d2 = d4 := by
  apply Matrix.ext
  unfold d2 d4
  decide +kernel

private theorem d4_sq : d4 * d4 = d8 := by
  apply Matrix.ext
  unfold d4 d8
  decide +kernel

private theorem d8_sq : d8 * d8 = d16 := by
  apply Matrix.ext
  unfold d8 d16
  decide +kernel

private theorem d16_mul_d2 : d16 * d2 = d18 := by
  apply Matrix.ext
  unfold d16 d2 d18
  decide +kernel

private theorem d18_mul_d : d18 * d = 1 := by
  apply Matrix.ext
  simp only [Matrix.one_apply]
  unfold d18 d
  decide +kernel

/-- The nineteenth power is already the identity on the linear cover. -/
public theorem matrixAB2_pow_nineteen : (matrixA * matrixB ^ 2) ^ 19 = 1 := by
  have h2 : d ^ 2 = d2 := (pow_two d).trans d_sq
  have h4 : d ^ 4 = d4 := by
    calc
      d ^ 4 = d ^ 2 * d ^ 2 := pow_add d 2 2
      _ = d4 := by rw [h2, d2_sq]
  have h8 : d ^ 8 = d8 := by
    calc
      d ^ 8 = d ^ 4 * d ^ 4 := pow_add d 4 4
      _ = d8 := by rw [h4, d4_sq]
  have h16 : d ^ 16 = d16 := by
    calc
      d ^ 16 = d ^ 8 * d ^ 8 := pow_add d 8 8
      _ = d16 := by rw [h8, d8_sq]
  rw [pow_two matrixB, b_sq, d_eq]
  calc
    d ^ 19 = (d ^ 16 * d ^ 2) * d := by rw [← pow_add, ← pow_succ]
    _ = 1 := by rw [h16, h2, d16_mul_d2, d18_mul_d]

end ONan.Simplicity

namespace ONan

/-- The standard word labelled 19ABC has nineteenth power one. -/
public theorem generatorAB2_pow_nineteen : (generatorA * generatorB ^ 2) ^ 19 = 1 := by
  have h : (linearA * linearB ^ 2) ^ 19 = 1 :=
    Units.ext Simplicity.matrixAB2_pow_nineteen
  apply Subtype.ext
  change (projectiveA * projectiveB ^ 2) ^ 19 = 1
  simpa only [projectiveA, projectiveB, map_pow, map_mul, map_one] using
    congrArg Matrix.ProjGenLinGroup.mk h

end ONan
