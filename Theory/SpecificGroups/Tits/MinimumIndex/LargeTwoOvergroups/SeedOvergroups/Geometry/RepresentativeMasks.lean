module

public import Theory.SpecificGroups.Tits.MinimumIndex.LargeTwoOvergroups.SeedOvergroups.Geometry.RepresentativeMasks.Checks
public import Theory.SpecificGroups.Tits.MinimumIndex.LargeTwoOvergroups.SeedOvergroups.Geometry.Membership

/-!
# Correctness of the representative place-membership masks

All stored support bits used by patterns other than 9 are certified for the
literal representative words. The proof combines bounded kernel computations
through point-action identities, then transports them to actual subgroup
membership. The final application supplies the support premise of the common
factor reduction. Coverage and common-factor membership remain the separate
source inputs owned by the geometry assembly; this module asserts neither.

Source: Parrott (1972), section 5, p.683; Geometry/source/README.md and
SeedOvergroups/source/geometry-representatives.json.
-/

namespace Tits.MinimumIndex.LargeTwoOvergroups.SeedOvergroups.Geometry

/-- The candidate support bits are exactly the original executable place tests. -/
public theorem representative_masks (t : Fin 18) (ht : t ≠ 9) :
    ∀ r ∈ rows t, ∀ j ∈ placePattern t, placeTest (rowPerm r) j = rowMember r j :=
  RepresentativeMasks.of_checks t (RepresentativeMasks.checked t ht)

/-- Each certified bit describes membership in the literal conjugate parabolic. -/
public theorem representative_membership_iff (t : Fin 18) (ht : t ≠ 9)
    (r : Row) (hr : r ∈ rows t) (j : Fin 38) (hj : j ∈ placePattern t) :
    rowElement r ∈ place j ↔ rowMember r j = true := by
  rw [← placeTest_iff, ← rowPerm_eq, representative_masks t ht r hr j hj]

/-- Application to the actual common-factor reduction, discharging its mask
premise. The common-factor and coverage premises have independent producers. -/
public theorem union_support_of_representative_masks (t : Fin 18) (ht : t ≠ 9)
    (hcommon : ∀ q ∈ factors t, ∀ j ∈ placePattern t, q ∈ place j)
    (hcover : ∀ x : Atlas1600Group, (∃ j ∈ placePattern t, x ∈ place j) →
      ∃ q ∈ factors t, ∃ r ∈ rows t, x = q * rowElement r) :
    ∀ x : Atlas1600Group, (∃ j ∈ placePattern t, x ∈ place j) →
      ∃ r ∈ rows t, ∀ j ∈ placePattern t, x ∈ place j ↔ rowMember r j = true :=
  union_support_of_common_factors place (placePattern t) (factors t) (rows t)
    rowElement rowMember hcommon hcover (representative_membership_iff t ht)

end Tits.MinimumIndex.LargeTwoOvergroups.SeedOvergroups.Geometry
