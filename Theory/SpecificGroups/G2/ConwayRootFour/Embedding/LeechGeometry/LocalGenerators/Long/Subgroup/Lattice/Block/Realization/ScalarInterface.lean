module
public import Theory.SpecificGroups.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Long.Subgroup.Lattice.Block.Realization.RightScalars

/-!
# The actual rational scalar subgroup and its five-point image

Restrict the retained norm-one icosian group to quaternions whose four golden
coefficients are rational. Its five-point map is the actual scalar sign
quotient followed by the existing alternating-group equivalence. No abstract
A₄ identification is inferred from this definition.

A rational right-quaternion-linear comparison intertwines these concrete
scalars with the explicit right multiplication matrices. Their commutation
with the faithful matrix action supplies the marked comparison consumer.
The finite A₄ parametrization of this image remains an independent obligation.

The icosian carrier, sign quotient and five-point equivalence are the attributed
ATLAS ports of Gerald Höhn, revision 8eabb35afe2b5e45bf913a2d05c53e558d2e2917.
The rational-coordinate restriction and transport lemmas are proved here.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Matrix Atlas.Algebra Atlas.Lattices Atlas.Conway
namespace Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Long.Block.Realization

/-- A rational Hamilton quaternion inside the retained golden quaternion algebra. -/
def scalarQuaternion (a b c d : ℚ) : IcosianQuaternion :=
  ⟨⟨a,0⟩,⟨b,0⟩,⟨c,0⟩,⟨d,0⟩⟩

/-- The actual rational norm-one scalars in the integral icosian order. -/
def rationalScalarUnits : Subgroup icosianNormOneGroup where
  carrier := {u | u.val.val.re.im = 0 ∧ u.val.val.imI.im = 0 ∧
    u.val.val.imJ.im = 0 ∧ u.val.val.imK.im = 0}
  one_mem' := by exact ⟨rfl,rfl,rfl,rfl⟩
  mul_mem' := by
    rintro u v ⟨hu0,hu1,hu2,hu3⟩ ⟨hv0,hv1,hv2,hv3⟩
    change ((u.val.val*v.val.val).re.im=0) ∧ ((u.val.val*v.val.val).imI.im=0) ∧
      ((u.val.val*v.val.val).imJ.im=0) ∧ ((u.val.val*v.val.val).imK.im=0)
    simp [Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul,
      hu0,hu1,hu2,hu3,hv0,hv1,hv2,hv3]
  inv_mem' := by
    rintro u ⟨hu0,hu1,hu2,hu3⟩
    change ((star u.val.val).re.im=0) ∧ ((star u.val.val).imI.im=0) ∧
      ((star u.val.val).imJ.im=0) ∧ ((star u.val.val).imK.im=0)
    simp [hu0,hu1,hu2,hu3]

theorem rationalScalarUnits_value (u : rationalScalarUnits) :
    u.val.val.val = scalarQuaternion u.val.val.val.re.re u.val.val.val.imI.re
      u.val.val.val.imJ.re u.val.val.val.imK.re := by
  obtain ⟨h0,h1,h2,h3⟩ := u.property
  ext <;> simp [scalarQuaternion, h0,h1,h2,h3]

/-- Its literal projective image in the already retained scalar A₅. -/
def rationalScalarToFive : rationalScalarUnits →* alternatingGroup (Fin 5) :=
  icosianScalarProjectiveAlternating.toMonoidHom.comp
    ((QuotientGroup.mk' icosianNormOneReduction.ker).comp rationalScalarUnits.subtype)

theorem rationalScalarToFive_projection (u : rationalScalarUnits) :
    scalarFive (rationalScalarToFive u) = leechCentralProjection (icosianScalarsToCo0 u.val) := by
  change icosianScalarProjectiveToCo1 (icosianScalarProjectiveAlternating.symm
    (icosianScalarProjectiveAlternating (QuotientGroup.mk' icosianNormOneReduction.ker u.val))) = _
  rw [MulEquiv.symm_apply_apply]
  rfl

/-- Inverse right multiplication, matching the existing scalar representation convention. -/
def scalarMatrix (u : rationalScalarUnits) : RealMatrix :=
  let q := (u⁻¹).val.val.val
  rightScalar q.re.re q.imI.re q.imJ.re q.imK.re

variable (e : Space ≃ₗ[ℚ] IcosianRationalCoordinates)
  (heRight : ∀ (a b c d : ℚ) (x : Space),
    e (rightScalar a b c d *ᵥ x) = icosianRightMul (e x) (scalarQuaternion a b c d))

include heRight in
theorem scalar_intertwines (u : rationalScalarUnits) (x : Space) :
    icosianScalarRepresentation u.val (e x) = e (scalarMatrix u *ᵥ x) := by
  change icosianRightMul (e x) (u⁻¹).val.val.val = _
  rw [rationalScalarUnits_value (u⁻¹)]
  exact (heRight _ _ _ _ x).symm

include heRight in
/-- Rational right-linearity is exactly the scalar compatibility needed by the consumer. -/
theorem comparedAction_commute_scalar (g : matrixGroup) (u : rationalScalarUnits) :
    Commute (Atlas.LinearAlgebra.linearAutomorphismCongr e (linearAction g))
      (icosianScalarRepresentation u.val) := by
  apply LinearEquiv.ext
  intro y
  obtain ⟨x,rfl⟩ := e.surjective y
  change e (linearAction g (e.symm (icosianScalarRepresentation u.val (e x)))) =
    icosianScalarRepresentation u.val (e (linearAction g (e.symm (e x))))
  rw [scalar_intertwines e heRight, e.symm_apply_apply, e.symm_apply_apply,
    scalar_intertwines e heRight]
  congr 1
  exact linearAction_rightScalar _ _ _ _ _ _

end Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Long.Block.Realization
