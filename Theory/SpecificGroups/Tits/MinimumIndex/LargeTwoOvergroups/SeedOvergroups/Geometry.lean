module

public import Theory.SpecificGroups.Tits.MinimumIndex.LargeTwoOvergroups.SeedOvergroups.FiniteCover
public import Theory.SpecificGroups.Tits.MinimumIndex.LargeTwoOvergroups.SeedOvergroups.Geometry.Membership
public import Theory.SpecificGroups.Tits.MinimumIndex.LargeTwoOvergroups.SeedOvergroups.Geometry.MaskChecks
public import Theory.SpecificGroups.Tits.MinimumIndex.LargeTwoOvergroups.SeedOvergroups.Geometry.TwoPlaces
public import Theory.SpecificGroups.Tits.MinimumIndex.LargeTwoOvergroups.SeedOvergroups.Geometry.CommonFactorCover
public import Theory.SpecificGroups.Tits.MinimumIndex.LargeTwoOvergroups.SeedOvergroups.Geometry.RepresentativeMasks
public import Theory.SpecificGroups.Tits.MinimumIndex.LargeTwoOvergroups.SeedOvergroups.Geometry.RepresentativeProducts

/-!
# Assembly of concrete place geometry from representative certificates

The certified common-factor covers, representative membership masks and
disjoint-product exclusions prove both geometry contracts for all eighteen
literal place patterns. Leaf-support checks give successive intersection
containments. Writing x = q*a and y⁻¹ = q'*b reduces product compatibility
to the exclusion of a*b⁻¹ when the representative supports are disjoint.
Pattern 9 uses the direct two-subgroup argument in TwoPlaces.

The final exports discharge every finite certificate premise and show that
a subgroup covered by a seed's listed places lies in one of them. The
separate extension obstruction still supplies that coverage in the full
seed-overgroup placement theorem. Source: Parrott (1972), section 5, p.683,
and SeedOvergroups/source/README.md.
-/

@[expose] public section
namespace Tits.MinimumIndex.LargeTwoOvergroups.SeedOvergroups
open Geometry

private theorem representative_membership (t : Fin 18)
    (hmasks : ∀ r ∈ rows t, ∀ j ∈ placePattern t,
      placeTest (rowPerm r) j = rowMember r j) :
    ∀ r ∈ rows t, ∀ j ∈ placePattern t,
      rowElement r ∈ place j ↔ rowMember r j = true := by
  intro r hr j hj
  rw [← placeTest_iff, ← rowPerm_eq, hmasks r hr j hj]

/-- The intersection contract, with its finite coverage and mask premises explicit. -/
theorem placePattern_leafIntersections_of_representative_certificates (t : Fin 18)
    (hcommon : ∀ q ∈ factors t, ∀ j ∈ placePattern t, q ∈ place j)
    (hcover : ∀ x : Atlas1600Group, (∃ j ∈ placePattern t, x ∈ place j) →
      ∃ q ∈ factors t, ∃ r ∈ rows t, x = q * rowElement r)
    (hmasks : ∀ r ∈ rows t, ∀ j ∈ placePattern t,
      placeTest (rowPerm r) j = rowMember r j) :
    LeafIntersections ((placePattern t).map place) :=
  leafIntersections_of_support place (rows t) rowMember (placePattern t) (parents t)
    (union_support_of_common_factors place (placePattern t) (factors t) (rows t)
      rowElement rowMember hcommon hcover (representative_membership t hmasks))
    (leafCheck_checked t)

/-- The product contract, with its finite coverage, masks and exclusions explicit. -/
theorem placePattern_productCompatible_of_representative_certificates (t : Fin 18)
    (hcommon : ∀ q ∈ factors t, ∀ j ∈ placePattern t, q ∈ place j)
    (hcover : ∀ x : Atlas1600Group, (∃ j ∈ placePattern t, x ∈ place j) →
      ∃ q ∈ factors t, ∃ r ∈ rows t, x = q * rowElement r)
    (hmasks : ∀ r ∈ rows t, ∀ j ∈ placePattern t,
      placeTest (rowPerm r) j = rowMember r j)
    (hproducts : ∀ a ∈ rows t, ∀ b ∈ rows t, sharesPlace t a b = false →
      ∀ j ∈ placePattern t, placeTest (rowPerm a * (rowPerm b)⁻¹) j = false) :
    ProductCompatible ((placePattern t).map place) := by
  apply productCompatible_of_common_factors place (placePattern t) (factors t) (rows t)
    rowElement rowMember hcommon hcover (representative_membership t hmasks)
  intro a ha b hb hab j hj hmem
  have ht := (placeTest_iff (rowElement a * (rowElement b)⁻¹) j).mpr hmem
  change placeTest ((rowElement a).val * ((rowElement b).val)⁻¹) j = true at ht
  rw [← rowPerm_eq, ← rowPerm_eq, hproducts a ha b hb hab j hj] at ht
  contradiction

/-- Application to the literal union in the seed-overgroup consumer. The
assembly owner must supply the three finite certificate families. -/
theorem placePattern_le_of_representative_certificates (t : Fin 18)
    (hcommon : ∀ q ∈ factors t, ∀ j ∈ placePattern t, q ∈ place j)
    (hcover : ∀ x : Atlas1600Group, (∃ j ∈ placePattern t, x ∈ place j) →
      ∃ q ∈ factors t, ∃ r ∈ rows t, x = q * rowElement r)
    (hmasks : ∀ r ∈ rows t, ∀ j ∈ placePattern t,
      placeTest (rowPerm r) j = rowMember r j)
    (hproducts : ∀ a ∈ rows t, ∀ b ∈ rows t, sharesPlace t a b = false →
      ∀ j ∈ placePattern t, placeTest (rowPerm a * (rowPerm b)⁻¹) j = false)
    (K : Subgroup Atlas1600Group)
    (hK : ∀ x ∈ K, ∃ P ∈ (placePattern t).map place, x ∈ P) :
    ∃ P ∈ (placePattern t).map place, K ≤ P :=
  le_of_union (placePattern_leafIntersections_of_representative_certificates
    t hcommon hcover hmasks)
    (placePattern_productCompatible_of_representative_certificates
      t hcommon hcover hmasks hproducts) K hK

/-- Uniform assembly needs certificates only for the other seventeen patterns. -/
theorem placePattern_geometry_of_representative_certificates
    (hcommon : ∀ t : Fin 18, t ≠ 9 →
      ∀ q ∈ factors t, ∀ j ∈ placePattern t, q ∈ place j)
    (hcover : ∀ t : Fin 18, t ≠ 9 →
      ∀ x : Atlas1600Group, (∃ j ∈ placePattern t, x ∈ place j) →
        ∃ q ∈ factors t, ∃ r ∈ rows t, x = q * rowElement r)
    (hmasks : ∀ t : Fin 18, t ≠ 9 →
      ∀ r ∈ rows t, ∀ j ∈ placePattern t,
        placeTest (rowPerm r) j = rowMember r j)
    (hproducts : ∀ t : Fin 18, t ≠ 9 →
      ∀ a ∈ rows t, ∀ b ∈ rows t, sharesPlace t a b = false →
        ∀ j ∈ placePattern t, placeTest (rowPerm a * (rowPerm b)⁻¹) j = false)
    (t : Fin 18) : LeafIntersections ((placePattern t).map place) ∧
      ProductCompatible ((placePattern t).map place) := by
  by_cases ht : t = 9
  · subst t
    exact ⟨placePattern_nine_leafIntersections, placePattern_nine_productCompatible⟩
  · exact ⟨placePattern_leafIntersections_of_representative_certificates
      t (hcommon t ht) (hcover t ht) (hmasks t ht),
      placePattern_productCompatible_of_representative_certificates
        t (hcommon t ht) (hcover t ht) (hmasks t ht) (hproducts t ht)⟩

/-- Every literal place pattern has the successive leaf-parent intersection
containments, with all coverage and membership certificates discharged. -/
theorem placePattern_leafIntersections (t : Fin 18) :
    LeafIntersections ((placePattern t).map place) := by
  by_cases ht : t = 9
  · subst t
    exact placePattern_nine_leafIntersections
  · exact placePattern_leafIntersections_of_representative_certificates t
      (factors_mem_places t) (commonFactorCover t ht) (representative_masks t ht)

/-- If x, y and x*y lie in a literal place union, some listed place contains
both x and y. All finite certificate premises are discharged. -/
theorem placePattern_productCompatible (t : Fin 18) :
    ProductCompatible ((placePattern t).map place) := by
  by_cases ht : t = 9
  · subst t
    exact placePattern_nine_productCompatible
  · exact placePattern_productCompatible_of_representative_certificates t
      (factors_mem_places t) (commonFactorCover t ht) (representative_masks t ht)
      (disjoint_representative_products t ht)

/-- A subgroup covered by any of the eighteen place unions lies in one place. -/
theorem placePattern_le_of_union (t : Fin 18) (K : Subgroup Atlas1600Group)
    (hcover : ∀ x ∈ K, ∃ P ∈ (placePattern t).map place, x ∈ P) :
    ∃ P ∈ (placePattern t).map place, K ≤ P :=
  le_of_union (placePattern_leafIntersections t) (placePattern_productCompatible t) K hcover

/-- Application to the seed-overgroup consumer's exact list. Only elementwise
coverage remains, supplied there by the independent extension obstruction. -/
theorem places_le_of_union (i : Fin 122) (K : Subgroup Atlas1600Group)
    (hcover : ∀ x ∈ K, ∃ P ∈ places i, x ∈ P) :
    ∃ P ∈ places i, K ≤ P :=
  placePattern_le_of_union (seedPattern i) K hcover

end Tits.MinimumIndex.LargeTwoOvergroups.SeedOvergroups
