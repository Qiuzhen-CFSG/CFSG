module

public import Theory.SpecificGroups.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Long.Subgroup.Lattice.Block.Realization.ScalarInterface

/-!
# Rational norm-one icosians and their actual projective image

The rational elements of the retained norm-one icosian group are exactly the
24 Hurwitz units: eight signed quaternion axes and sixteen half-integral units.
We parametrize them in the existing doubled golden-coordinate convention.
The existing norm-one exhaustion reduces completeness to the axis and tetrad
families; small kernel-checked calculations select precisely the rational ones.

The literal map `rationalScalarToFive` has the same two signs as the retained
icosian reduction. Its image therefore has order twelve. This count feeds the
unconditional tetrahedral marking, rather than assuming an abstract A₄ image.

The coordinate enumeration, exhaustion, and scalar reduction are the attributed
ATLAS ports of Gerald Höhn, revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`; see `LICENSES/ATLAS.txt` and
`LICENSES/ATLAS-CITATION.cff`. The marked block application is Aschbacher,
*Sporadic Groups* (1994), 49.2 and 49.5.
-/

@[expose] public noncomputable section
open Atlas.Algebra Atlas.Conway
namespace Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Long.Block.Realization

private abbrev HurwitzIndex := (Fin 4 × Atlas.Codes.Bit) ⊕ (Fin 4 → Atlas.Codes.Bit)

/-- The eight signed axes and the sixteen half-integral Hurwitz units,
expressed in the existing doubled golden-coordinate convention. -/
private def hurwitzCoordinates : HurwitzIndex → IcosianIntegerCoordinates
  | .inl p => icosianAxisCoordinates (⟨2 * p.1.val, by omega⟩, p.2)
  | .inr p => icosianTetradCoordinates (13, p)

private def rationalCoordinates (v : IcosianIntegerCoordinates) : Prop :=
  v 1 = 0 ∧ v 3 = 0 ∧ v 5 = 0 ∧ v 7 = 0

private instance (v : IcosianIntegerCoordinates) : Decidable (rationalCoordinates v) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _))

private theorem hurwitzCoordinates_injective : Function.Injective hurwitzCoordinates := by
  decide +kernel

private theorem hurwitzCoordinates_rational : ∀ i, rationalCoordinates (hurwitzCoordinates i) := by
  decide +kernel

private theorem hurwitzCoordinates_tau : ∀ i, icosianCoordinateTau (hurwitzCoordinates i) = 0 := by
  decide +kernel

private theorem hurwitzCoordinates_mem (i : HurwitzIndex) :
    hurwitzCoordinates i ∈ icosianNormOneCoordinates := by
  apply Finset.mem_filter.mpr
  refine ⟨?_, hurwitzCoordinates_tau i⟩
  cases i with
  | inl p => exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨_, Finset.mem_univ _, rfl⟩)
  | inr p => exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨_, Finset.mem_univ _, rfl⟩)

private theorem rationalCoordinates_exhaust (v : IcosianIntegerCoordinates)
    (hv : v ∈ icosianNormOneCoordinates) (hr : rationalCoordinates v) :
    ∃ i, hurwitzCoordinates i = v := by
  rcases Finset.mem_union.mp (Finset.mem_filter.mp hv).1 with ha | ht
  · obtain ⟨p, _, rfl⟩ := Finset.mem_image.mp ha
    have h : ∀ p : Fin 8 × Atlas.Codes.Bit, rationalCoordinates (icosianAxisCoordinates p) →
        ∃ i : Fin 4 × Atlas.Codes.Bit, hurwitzCoordinates (.inl i) = icosianAxisCoordinates p := by
      decide +kernel
    obtain ⟨i, hi⟩ := h p hr
    exact ⟨.inl i, hi⟩
  · obtain ⟨p, _, rfl⟩ := Finset.mem_image.mp ht
    have h : ∀ p : Fin 14 × (Fin 4 → Atlas.Codes.Bit),
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

private noncomputable def hurwitzUnitsEquiv : HurwitzIndex ≃ rationalScalarUnits :=
  Equiv.ofBijective (fun i =>
    ⟨icosianNormOneCoordinatesEquiv ⟨hurwitzCoordinates i, hurwitzCoordinates_mem i⟩,
      (coordinates_rational_iff _).mpr (hurwitzCoordinates_rational i)⟩) (by
    constructor
    · intro i j h
      apply hurwitzCoordinates_injective
      have heq := icosianNormOneCoordinatesEquiv.injective
        (congrArg (fun u : rationalScalarUnits => u.val) h)
      exact congrArg (fun x : {v // v ∈ icosianNormOneCoordinates} => x.val) heq
    · intro u
      obtain ⟨v, hv⟩ := icosianNormOneCoordinatesEquiv.surjective u.val
      have hr := (coordinates_rational_iff v).mp (hv.symm ▸ u.property)
      obtain ⟨i, hi⟩ := rationalCoordinates_exhaust v.val v.property hr
      refine ⟨i, Subtype.ext ((congrArg icosianNormOneCoordinatesEquiv (Subtype.ext hi)).trans hv)⟩)

/-- The rational subgroup of the existing norm-one icosians has 24 elements. -/
theorem rationalScalarUnits_card : Nat.card rationalScalarUnits = 24 := by
  rw [← Nat.card_congr hurwitzUnitsEquiv]
  norm_num [Nat.card_eq_fintype_card, HurwitzIndex, Atlas.Codes.Bit]

private theorem reduction_kernel_le_rational :
    icosianNormOneReduction.ker ≤ rationalScalarUnits := by
  intro u hu
  rcases (icosianNormOneReduction_kernel_iff u).mp hu with rfl | rfl
  · exact rationalScalarUnits.one_mem
  · exact ⟨rfl, rfl, rfl, rfl⟩

private theorem rationalScalarToFive_ker :
    rationalScalarToFive.ker = icosianNormOneReduction.ker.subgroupOf rationalScalarUnits := by
  ext u
  change icosianScalarProjectiveAlternating
    (QuotientGroup.mk' icosianNormOneReduction.ker u.val) = 1 ↔
      u.val ∈ icosianNormOneReduction.ker
  rw [MulEquiv.map_eq_one_iff]
  exact QuotientGroup.eq_one_iff _

/-- The kernel of the literal five-point map consists of the two central signs. -/
theorem rationalScalarToFive_kernel_card : Nat.card rationalScalarToFive.ker = 2 := by
  rw [rationalScalarToFive_ker,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe reduction_kernel_le_rational).toEquiv]
  exact icosianNormOneReduction_kernel_card

/-- The actual rational scalar image in the retained A₅ has order twelve. -/
theorem rationalScalarToFive_range_card : Nat.card rationalScalarToFive.range = 12 := by
  have h := rationalScalarToFive.ker.card_mul_index
  rw [Subgroup.index_ker, rationalScalarToFive_kernel_card, rationalScalarUnits_card] at h
  omega

end Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Long.Block.Realization
