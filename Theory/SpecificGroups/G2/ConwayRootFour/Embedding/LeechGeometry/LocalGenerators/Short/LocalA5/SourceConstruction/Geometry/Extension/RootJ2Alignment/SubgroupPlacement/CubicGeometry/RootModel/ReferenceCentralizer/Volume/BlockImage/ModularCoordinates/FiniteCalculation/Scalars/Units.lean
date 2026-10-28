module
public import Theory.SpecificGroups.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Short.LocalA5.SourceConstruction.Geometry.Extension.RootJ2Alignment.SubgroupPlacement.CubicGeometry.RootModel.ReferenceCentralizer.Volume.BlockImage.ModularCoordinates.FiniteCalculation.Transport

/-!
# Rational-unit exhaustion and the literal scalar sign quotient

The retained icosian norm-one coordinate exhaustion leaves exactly the signed
axes and the half-integral Hurwitz possibilities for a rational unit. The
actual five-point map kills exactly the two central signs. Consequently a
projective element squaring to one comes from an axis, while a projective
element of order three comes from a half-unit. We enumerate the inverse unit
to match the inverse-right convention of the scalar representation.

The coordinate argument extends the private enumeration in
Realization.TetrahedralMarking.RationalUnits without changing that module.
The retained exhaustion and reduction are Gerald Höhn's ATLAS ports, revision
8eabb35afe2b5e45bf913a2d05c53e558d2e2917. See LICENSES/ATLAS.txt and
LICENSES/ATLAS-CITATION.cff. Source consumer: Aschbacher, Sporadic Groups
(1994), 49.5, pp.283–284.
-/

@[expose] public noncomputable section
open Atlas.Conway Atlas.Algebra Atlas.Lattices Atlas.Codes Matrix
open scoped MatrixGroups
namespace Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.LocalA5.SourceConstruction.RootModel
open scoped Long
namespace ReferenceBlock.ModularCoordinates.FiniteCalculation.Scalars
open Long.Block Long.Block.Realization

local instance : DecidableEq IcosianQuaternion := fun x y =>
  decidable_of_iff (x.re = y.re ∧ x.imI = y.imI ∧ x.imJ = y.imJ ∧ x.imK = y.imK)
    QuaternionAlgebra.ext_iff.symm

abbrev HurwitzIndex := (Fin 4 × Bit) ⊕ (Fin 4 → Bit)

def hurwitzCoordinates : HurwitzIndex → IcosianIntegerCoordinates
  | .inl p => icosianAxisCoordinates (⟨2 * p.1.val, by omega⟩, p.2)
  | .inr p => icosianTetradCoordinates (13, p)

def hurwitzQuaternion (i : HurwitzIndex) : IcosianQuaternion :=
  icosianCoordinatesQuaternion (hurwitzCoordinates i)

private def rationalCoordinates (v : IcosianIntegerCoordinates) : Prop :=
  v 1 = 0 ∧ v 3 = 0 ∧ v 5 = 0 ∧ v 7 = 0

private instance (v : IcosianIntegerCoordinates) : Decidable (rationalCoordinates v) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _))

private theorem rationalCoordinates_exhaust (v : IcosianIntegerCoordinates)
    (hv : v ∈ icosianNormOneCoordinates) (hr : rationalCoordinates v) :
    ∃ i, hurwitzCoordinates i = v := by
  rcases Finset.mem_union.mp (Finset.mem_filter.mp hv).1 with ha | ht
  · obtain ⟨p, _, rfl⟩ := Finset.mem_image.mp ha
    have h : ∀ p : Fin 8 × Bit, rationalCoordinates (icosianAxisCoordinates p) →
        ∃ i : Fin 4 × Bit, hurwitzCoordinates (.inl i) = icosianAxisCoordinates p := by
      decide +kernel
    obtain ⟨i, hi⟩ := h p hr
    exact ⟨.inl i, hi⟩
  · obtain ⟨p, _, rfl⟩ := Finset.mem_image.mp ht
    have h : ∀ p : Fin 14 × (Fin 4 → Bit),
        rationalCoordinates (icosianTetradCoordinates p) → p.1 = 13 := by
      decide +kernel
    refine ⟨.inr p.2, ?_⟩
    change icosianTetradCoordinates (13, p.2) = icosianTetradCoordinates p
    rw [← h p hr]

private theorem coordinates_rational_iff (v : {v // v ∈ icosianNormOneCoordinates}) :
    icosianNormOneCoordinatesEquiv v ∈ rationalScalarUnits ↔ rationalCoordinates v.val := by
  change ((v.val 1 : ℚ)/2 = 0 ∧ (v.val 3 : ℚ)/2 = 0 ∧
    (v.val 5 : ℚ)/2 = 0 ∧ (v.val 7 : ℚ)/2 = 0) ↔ _
  norm_num [rationalCoordinates]

theorem rationalUnit_exhaust (u : rationalScalarUnits) :
    ∃ i, u.val.val.val = hurwitzQuaternion i := by
  obtain ⟨v, hv⟩ := icosianNormOneCoordinatesEquiv.surjective u.val
  have hr := (coordinates_rational_iff v).mp (hv.symm ▸ u.property)
  obtain ⟨i, hi⟩ := rationalCoordinates_exhaust v.val v.property hr
  refine ⟨i, ?_⟩
  rw [← hv]
  change icosianCoordinatesQuaternion v.val = icosianCoordinatesQuaternion (hurwitzCoordinates i)
  rw [hi]

theorem projective_eq_one_iff (u : rationalScalarUnits) :
    rationalScalarToFive u = 1 ↔ u.val.val.val = 1 ∨ u.val.val.val = -1 := by
  change icosianScalarProjectiveAlternating
    (QuotientGroup.mk' icosianNormOneReduction.ker u.val) = 1 ↔ _
  rw [MulEquiv.map_eq_one_iff]
  change (u.val : IcosianScalarProjectiveModel) = 1 ↔ _
  rw [QuotientGroup.eq_one_iff, icosianNormOneReduction_kernel_iff]
  constructor
  · rintro (h | h)
    · exact Or.inl (congrArg (fun x : icosianNormOneGroup => x.val.val) h)
    · exact Or.inr (congrArg (fun x : icosianNormOneGroup => x.val.val) h)
  · rintro (h | h)
    · exact Or.inl (icosianNormOne_value_injective h)
    · exact Or.inr (icosianNormOne_value_injective h)

theorem projective_square_iff (u : rationalScalarUnits) :
    rationalScalarToFive u ^ 2 = 1 ↔
      u.val.val.val ^ 2 = 1 ∨ u.val.val.val ^ 2 = -1 := by
  rw [← map_pow, projective_eq_one_iff]
  rfl

private theorem axis_square : ∀ p : Fin 4 × Bit,
    hurwitzQuaternion (.inl p) ^ 2 = 1 ∨ hurwitzQuaternion (.inl p) ^ 2 = -1 := by
  decide +kernel

private theorem half_not_square : ∀ p : Fin 4 → Bit,
    ¬ (hurwitzQuaternion (.inr p) ^ 2 = 1 ∨ hurwitzQuaternion (.inr p) ^ 2 = -1) := by
  decide +kernel

theorem square_inverse_axis (u : rationalScalarUnits)
    (hu : rationalScalarToFive u ^ 2 = 1) :
    ∃ p : Fin 4 × Bit, (u⁻¹).val.val.val = hurwitzQuaternion (.inl p) := by
  have hinv : rationalScalarToFive u⁻¹ ^ 2 = 1 := by
    rw [map_inv, inv_pow, hu, inv_one]
  obtain ⟨p, hp⟩ := rationalUnit_exhaust u⁻¹
  cases p with
  | inl p => exact ⟨p, hp⟩
  | inr p =>
    have h := (projective_square_iff u⁻¹).mp hinv
    rw [hp] at h
    exact (half_not_square p h).elim

theorem cubic_inverse_half (u : rationalScalarUnits)
    (hu : orderOf (rationalScalarToFive u) = 3) :
    ∃ p : Fin 4 → Bit, (u⁻¹).val.val.val = hurwitzQuaternion (.inr p) := by
  obtain ⟨p, hp⟩ := rationalUnit_exhaust u⁻¹
  cases p with
  | inr p => exact ⟨p, hp⟩
  | inl p =>
    have h : rationalScalarToFive u⁻¹ ^ 2 = 1 :=
      (projective_square_iff _).mpr (hp ▸ axis_square p)
    have hd := orderOf_dvd_of_pow_eq_one h
    rw [map_inv, orderOf_inv, hu] at hd
    norm_num at hd

end ReferenceBlock.ModularCoordinates.FiniteCalculation.Scalars
end Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.LocalA5.SourceConstruction.RootModel
