module
public import Theory.SpecificGroups.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Long.Subgroup.Lattice.Block.Realization.Comparison
public import Theory.SpecificGroups.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Long.Subgroup.Lattice.Block.Realization.ScalarInterface

/-!
# Marked integral transport to the exact Leech and scalar quotients

Compose the explicit quaternion-lattice comparison with the existing icosian
comparison. This gives genuine integral Leech isometries and detects precisely
the two central signs. Right rational-quaternion linearity gives integral
commutation with the actual rational norm-one scalars. Their literal image
in A₅ therefore gives the commutation clause consumed by
`Block.latticeBlockOfMatrix`, using exactly `leechCentralProjection`.

The two independent premises are an actual marked lattice comparison and an
A₄ parametrization of the rational scalar image. They are not asserted here.
The final realization task must discharge both before defining its unconditional
`matrixToLeech` and `matrixMarking`.

Source: Aschbacher, *Sporadic Groups* (1994), 49.2 and 49.5, for the marked
block contract. The integral comparison and scalar actions are the attributed
ATLAS ports of Gerald Höhn; the block matrices are John Bray's `6L34G1-Ar6aB0`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Matrix Atlas.Algebra Atlas.Lattices Atlas.Conway Atlas.LinearAlgebra
namespace Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Long.Block.Realization

variable (e : Space ≃ₗ[ℚ] IcosianRationalCoordinates)
  (heForm : ∀ x y, icosianBilinear (e x) (e y) = form x y)
  (heLattice : ∀ x, x ∈ lattice ↔ e x ∈ rationalIcosianLattice)
  (heRight : ∀ (a b c d : ℚ) (x : Space),
    e (rightScalar a b c d *ᵥ x) = icosianRightMul (e x) (scalarQuaternion a b c d))

include heForm in
theorem leechComparison_form (x y : Space) :
    rationalForm ((e.trans icosianComparison) x) ((e.trans icosianComparison) y) = form x y := by
  change rationalForm (icosianComparison (e x)) (icosianComparison (e y)) = _
  rw [icosianComparison_isometry, heForm]

include heLattice in
theorem leechComparison_lattice (x : Space) :
    x ∈ lattice ↔ (e.trans icosianComparison) x ∈ rationalLeech :=
  (heLattice x).trans (icosianComparison_lattice_iff (e x))

/-- Conditional transport through the actual existing icosian integral comparison. -/
def toLeechOfIcosianComparison : matrixGroup →* LeechIsometryGroup :=
  toLeechOfComparison (e.trans icosianComparison)
    (leechComparison_form e heForm) (leechComparison_lattice e heLattice)

theorem toLeechOfIcosianComparison_injective :
    Function.Injective (toLeechOfIcosianComparison e heForm heLattice) :=
  toLeechOfComparison_injective _ _ _

theorem toLeechOfIcosianComparison_signs :
    leechCentralSigns.comap (toLeechOfIcosianComparison e heForm heLattice) = matrixSigns :=
  toLeechOfComparison_signs _ _ _

include heRight in
theorem toLeechOfIcosianComparison_scalar (g : matrixGroup) (u : rationalScalarUnits) :
    Commute (toLeechOfIcosianComparison e heForm heLattice g) (icosianScalarsToCo0 u.val) := by
  have h := (comparedAction_commute_scalar e heRight g u).map
    (linearAutomorphismCongr icosianComparison).toMonoidHom
  apply fullIsometryEquiv.injective
  rw [map_mul, map_mul]
  apply Subtype.ext
  change (fullIsometryEquiv (toLeechOfIcosianComparison e heForm heLattice g)).val *
      (fullIsometryEquiv (icosianScalarsToCo0 u.val)).val =
    (fullIsometryEquiv (icosianScalarsToCo0 u.val)).val *
      (fullIsometryEquiv (toLeechOfIcosianComparison e heForm heLattice g)).val
  rw [toLeechOfIcosianComparison, toLeechOfComparison_extension,
    icosianScalarsToCo0_extension]
  exact h.eq

include heRight in
/-- The finite scalar marking discharges the literal commutation clause of
`Block.latticeBlockOfMatrix`, once the independent lattice comparison is supplied. -/
theorem toLeechOfIcosianComparison_commute
    (j : alternatingGroup fourPoints →* alternatingGroup (Fin 5))
    (hj : j.range = rationalScalarToFive.range)
    (a : alternatingGroup fourPoints) (g : matrixGroup) :
    Commute (scalarFive (j a))
      (leechCentralProjection (toLeechOfIcosianComparison e heForm heLattice g)) := by
  have ha : j a ∈ rationalScalarToFive.range := hj ▸ (show j a ∈ j.range from ⟨a, rfl⟩)
  obtain ⟨u,hu⟩ := ha
  rw [← hu, rationalScalarToFive_projection]
  exact ((toLeechOfIcosianComparison_scalar e heForm heLattice heRight g u).symm).map
    leechCentralProjection

end Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Long.Block.Realization
