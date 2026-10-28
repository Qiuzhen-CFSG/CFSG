module
public import Theory.SpecificGroups.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Short.LocalA5.SourceConstruction.Geometry.Extension.RootJ2Alignment.SubgroupPlacement.CubicGeometry.RootModel.ReferenceCentralizer.Volume.BlockImage.ModularCoordinates.FiniteCalculation.Transport
public import Theory.SpecificGroups.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Short.LocalA5.SourceConstruction.Geometry.Extension.RootJ2Alignment.SubgroupPlacement.CubicGeometry.RootModel.ReferenceCentralizer.Volume.BlockImage.ModularCoordinates.FiniteCalculation.Scalars.Units
public import Theory.SpecificGroups.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Short.LocalA5.SourceConstruction.Geometry.Extension.RootJ2Alignment.SubgroupPlacement.CubicGeometry.RootModel.ReferenceCentralizer.Volume.BlockImage.ModularCoordinates.FiniteCalculation.Scalars.Tables

/-!
# Actual rational scalar actions on the quaternion-fixed binary space

Every rational icosian unit is a signed axis or a Hurwitz half-unit. The
literal sign quotient distinguishes the projective square-one and cubic
cases. The checked integral basis identities, followed by the existing
inverse-right transport, identify their actions on all binary vectors fixed
by the three axes. Central signs disappear modulo two; the parity of the
normalized imaginary signs distinguishes the two half-unit orientations.

This proves the complete ScalarComparison record. Its coordinate application
discharges the scalar premise and leaves only the independent GoldenCoordinates
witnesses to the embedding producer and final assembly owner.

Source consumer: Aschbacher, Sporadic Groups (1994), 49.5, pp.283–284.
The construction retains John Bray's ATLAS matrices and Gerald Höhn's icosian
comparison, under the ATLAS Research and Attribution License 1.0; see
LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/

@[expose] public noncomputable section
open Atlas.Conway Atlas.Algebra Atlas.Lattices Atlas.Codes Matrix
open scoped MatrixGroups
namespace Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.LocalA5.SourceConstruction.RootModel
open scoped Long
namespace ReferenceBlock.ModularCoordinates.FiniteCalculation.Scalars
open Long.Block Long.Block.Realization

/-- Coefficients in the integral span of 1,i,j,k and (1+i+j+k)/2. -/
def hurwitzCoefficients : HurwitzIndex → Fin 5 → ℤ
  | .inl p => ![if p.1 = 0 then icosianCoordinateSign p.2 else 0,
      if p.1 = 1 then icosianCoordinateSign p.2 else 0,
      if p.1 = 2 then icosianCoordinateSign p.2 else 0,
      if p.1 = 3 then icosianCoordinateSign p.2 else 0, 0]
  | .inr p => ![0,
      if p 1 = p 0 then 0 else -icosianCoordinateSign (p 0),
      if p 2 = p 0 then 0 else -icosianCoordinateSign (p 0),
      if p 3 = p 0 then 0 else -icosianCoordinateSign (p 0),
      icosianCoordinateSign (p 0)]

local instance : DecidableEq IcosianQuaternion := fun x y =>
  decidable_of_iff (x.re = y.re ∧ x.imI = y.imI ∧ x.imJ = y.imJ ∧ x.imK = y.imK)
    QuaternionAlgebra.ext_iff.symm

private theorem coefficients_quaternion : ∀ i,
    let c := hurwitzCoefficients i
    hurwitzQuaternion i = scalarQuaternion
      ((c 0 : ℚ) + (c 4 : ℚ)/2) ((c 1 : ℚ) + (c 4 : ℚ)/2)
      ((c 2 : ℚ) + (c 4 : ℚ)/2) ((c 3 : ℚ) + (c 4 : ℚ)/2) := by
  decide +kernel

/-- After normalizing the real sign, the parity of the three imaginary signs
selects the second orientation. -/
def halfOpposite (p : Fin 4 → Bit) : Bool := decide (p 0 + p 1 + p 2 + p 3 = 1)

private theorem axis_coefficients : ∀ p : Fin 4 × Bit,
    let c := hurwitzCoefficients (.inl p)
    ((c 0 + c 1 + c 2 + c 3 : ℤ) : Bit) = 1 ∧ (c 4 : Bit) = 0 := by
  decide +kernel

private theorem half_coefficients : ∀ p : Fin 4 → Bit,
    let c := hurwitzCoefficients (.inr p)
    ((c 0 + c 1 + c 2 + c 3 : ℤ) : Bit) = (if halfOpposite p then 1 else 0) ∧
      (c 4 : Bit) = 1 := by
  decide +kernel

private theorem scalar_basis (u : rationalScalarUnits) (i : HurwitzIndex)
    (hi : (u⁻¹).val.val.val = hurwitzQuaternion i) :
    scalarMatrix u * basisMatrix =
      basisMatrix * (tableCombination (hurwitzCoefficients i)).map (Int.castRingHom ℚ) := by
  rw [scalarMatrix, hi, coefficients_quaternion]
  exact combination_coordinates (hurwitzCoefficients i)

private theorem combination_fixed (c : Fin 5 → ℤ) (v : Binary) (hv : AxisFixed v) :
    (tableCombination c).map (Int.castRingHom Bit) *ᵥ v =
      ((c 0 + c 1 + c 2 + c 3 : ℤ) : Bit) • v +
        (c 4 : Bit) • (rightHalfTable.map (Int.castRingHom Bit) *ᵥ v) := by
  change ((Int.castRingHom Bit).mapMatrix (tableCombination c)) *ᵥ v = _
  simp only [tableCombination, map_add, map_zsmul, map_one,
    Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec]
  have h0 : rightAxis0Table.map (Int.castRingHom Bit) *ᵥ v = v := hv 0
  have h1 : rightAxis1Table.map (Int.castRingHom Bit) *ᵥ v = v := hv 1
  have h2 : rightAxis2Table.map (Int.castRingHom Bit) *ᵥ v = v := hv 2
  change c 0 • v + c 1 • (rightAxis0Table.map (Int.castRingHom Bit) *ᵥ v) +
    c 2 • (rightAxis1Table.map (Int.castRingHom Bit) *ᵥ v) +
    c 3 • (rightAxis2Table.map (Int.castRingHom Bit) *ᵥ v) +
    c 4 • (rightHalfTable.map (Int.castRingHom Bit) *ᵥ v) = _
  rw [h0, h1, h2, ← add_smul, ← add_smul, ← add_smul]
  simp only [Int.cast_smul_eq_zsmul]

theorem axisFixed_scalarFixed (v : Binary) (hv : AxisFixed v) : ScalarFixed v := by
  intro u hu
  obtain ⟨p, hp⟩ := square_inverse_axis u hu
  rw [scalarAction_of_basis u _ (scalar_basis u (.inl p) hp), combination_fixed _ v hv]
  rw [(axis_coefficients p).1, (axis_coefficients p).2]
  simp

theorem cubic_scalar_orientation (u : rationalScalarUnits)
    (hu : orderOf (rationalScalarToFive u) = 3) :
    ∃ opposite : Bool, ∀ v, AxisFixed v → scalarAction u v = orientationAction opposite v := by
  obtain ⟨p, hp⟩ := cubic_inverse_half u hu
  refine ⟨halfOpposite p, ?_⟩
  intro v hv
  rw [scalarAction_of_basis u _ (scalar_basis u (.inr p) hp), combination_fixed _ v hv]
  rw [(half_coefficients p).1, (half_coefficients p).2]
  cases halfOpposite p <;> simp [orientationAction, add_comm]

end ReferenceBlock.ModularCoordinates.FiniteCalculation.Scalars
namespace ReferenceBlock.ModularCoordinates.FiniteCalculation

/-- The actual rational scalar action agrees with the finite quaternion model. -/
theorem scalarComparison : ScalarComparison :=
  ⟨Scalars.axisFixed_scalarFixed, Scalars.cubic_scalar_orientation⟩

end ReferenceBlock.ModularCoordinates.FiniteCalculation
namespace ReferenceBlock.ModularCoordinates

/-- The scalar calculation discharges the entire rational-unit premise of the
finite coordinate construction. Only the independent golden embeddings remain. -/
theorem finiteCoordinates_of_goldenCoordinates
    (hc : ∀ inverse opposite : Bool, Nonempty (FiniteCalculation.GoldenCoordinates inverse opposite))
    (inverse : Bool) (u : Long.Block.Realization.rationalScalarUnits)
    (hu : orderOf (Long.Block.Realization.rationalScalarToFive u) = 3) :
    Nonempty (FiniteCoordinates inverse u) :=
  finiteCoordinates_of_comparisons FiniteCalculation.scalarComparison hc inverse u hu

end ReferenceBlock.ModularCoordinates
end Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.LocalA5.SourceConstruction.RootModel
