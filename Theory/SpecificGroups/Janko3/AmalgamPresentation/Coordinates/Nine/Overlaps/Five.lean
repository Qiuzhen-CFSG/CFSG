module
public import Theory.SpecificGroups.Janko3.AmalgamPresentation.Coordinates.Nine.Overlaps.Cardinalities
public import Theory.SpecificGroups.AlternatingSix.FivePointCoordinates

/-!
# Native A₅ recognition of the literal third overlap

The two actual projective generators lie in PSL₂(9). The exact order-sixty
subgroup is carried into A₆ by the existing exceptional isomorphism. Its
six-coset action identifies that same subgroup with a point stabilizer,
producing an actual A₅ equivalence for the retained complement.
-/
public noncomputable section
namespace Sporadic.Janko3.AmalgamPresentation.NineCoordinates
open Subgroup OverlapTables SourceRecognition.CubicNormalizerModel
open Atlas.Comparisons.Exceptional GorensteinWalter

private theorem field_odd : IsOddPrimePower (Nat.card F) := by
  rw [Nine.card]
  exact ⟨3,2,by decide,by decide,by decide,by decide⟩
private theorem field_large : 3 < Nat.card F := by rw [Nine.card]; decide

private theorem derived_eq : derived = Matrix.ProjectiveSpecialLinearGroup.toPGL.range :=
  pgl2_commutator_eq_psl2_range_of_card_gt_three F field_odd field_large

/-- The actual order-sixty projective subgroup lies in the derived group. -/
theorem rawThirdProjection_le_derived : Third.subgroup ≤ derived := by
  apply (closure_le _).mpr
  rintro _ ⟨b,rfl⟩
  rw [derived_eq]
  apply (GorensteinWalter.pgl2_mk_mem_psl2_range_iff_det_isSquare _).mpr
  change ∃ x : F, (overlapMatrix (if b then 3 else 2)).det.val = x*x
  cases b <;> decide +kernel

private def derivedSixEquiv : derived ≃* alternatingGroup (Fin 6) :=
  (MulEquiv.subgroupCongr derived_eq).trans
    ((psl2EquivToPGLRange F).symm.trans psl2NineCoordinatesEquivAlt6)

/-- The literal projective image is an actual A₅, through its native six-point action. -/
def rawThirdProjectionEquiv : Third.subgroup ≃* alternatingGroup (Fin 5) := by
  apply Classical.choice
  let H := Third.subgroup.subgroupOf derived
  let K := H.map derivedSixEquiv.toMonoidHom
  let e₀ : Third.subgroup ≃* H := (subgroupOfEquivOfLe rawThirdProjection_le_derived).symm
  let e₁ : H ≃* K := H.equivMapOfInjective derivedSixEquiv.toMonoidHom derivedSixEquiv.injective
  have hc : Nat.card K = 60 := by
    rw [←Nat.card_congr (e₀.trans e₁).toEquiv]
    exact Third.subgroup_card
  obtain ⟨α,i,hK⟩ := AlternatingSix.FivePointCoordinates.exists_marked_point_automorphism K hc
  exact ⟨(e₀.trans e₁).trans
    ((K.equivMapOfInjective α.toMonoidHom α.injective).trans
      ((MulEquiv.subgroupCongr hK).trans (AlternatingSix.SmallIndex.pointEquiv (n := 5) i)))⟩

/-- The retained complement inside the full order-180 raw overlap is A₅. -/
theorem rawThird_complement_equiv :
    Nonempty ((rawThird ⊓ (SemidirectProduct.inr : P →* Canonical).range : Subgroup Canonical) ≃*
      alternatingGroup (Fin 5)) :=
  ⟨rawThirdComplementEquiv.trans rawThirdProjectionEquiv⟩

end Sporadic.Janko3.AmalgamPresentation.NineCoordinates
