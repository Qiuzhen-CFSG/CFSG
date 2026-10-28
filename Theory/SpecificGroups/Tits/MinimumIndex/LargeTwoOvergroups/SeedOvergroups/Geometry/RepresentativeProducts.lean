module

public import Theory.SpecificGroups.Tits.MinimumIndex.LargeTwoOvergroups.SeedOvergroups.Geometry.RepresentativeProducts.Certificates
public import Theory.SpecificGroups.Tits.MinimumIndex.LargeTwoOvergroups.SeedOvergroups.Geometry.RepresentativeProducts.Pattern0
public import Theory.SpecificGroups.Tits.MinimumIndex.LargeTwoOvergroups.SeedOvergroups.Geometry.RepresentativeProducts.Pattern1
public import Theory.SpecificGroups.Tits.MinimumIndex.LargeTwoOvergroups.SeedOvergroups.Geometry.RepresentativeProducts.Pattern2
public import Theory.SpecificGroups.Tits.MinimumIndex.LargeTwoOvergroups.SeedOvergroups.Geometry.RepresentativeProducts.Pattern3
public import Theory.SpecificGroups.Tits.MinimumIndex.LargeTwoOvergroups.SeedOvergroups.Geometry.RepresentativeProducts.Pattern4
public import Theory.SpecificGroups.Tits.MinimumIndex.LargeTwoOvergroups.SeedOvergroups.Geometry.RepresentativeProducts.Pattern5
public import Theory.SpecificGroups.Tits.MinimumIndex.LargeTwoOvergroups.SeedOvergroups.Geometry.RepresentativeProducts.Pattern6
public import Theory.SpecificGroups.Tits.MinimumIndex.LargeTwoOvergroups.SeedOvergroups.Geometry.RepresentativeProducts.Pattern7
public import Theory.SpecificGroups.Tits.MinimumIndex.LargeTwoOvergroups.SeedOvergroups.Geometry.RepresentativeProducts.Pattern8
public import Theory.SpecificGroups.Tits.MinimumIndex.LargeTwoOvergroups.SeedOvergroups.Geometry.RepresentativeProducts.Pattern10
public import Theory.SpecificGroups.Tits.MinimumIndex.LargeTwoOvergroups.SeedOvergroups.Geometry.RepresentativeProducts.Pattern11
public import Theory.SpecificGroups.Tits.MinimumIndex.LargeTwoOvergroups.SeedOvergroups.Geometry.RepresentativeProducts.Pattern12
public import Theory.SpecificGroups.Tits.MinimumIndex.LargeTwoOvergroups.SeedOvergroups.Geometry.RepresentativeProducts.Pattern13
public import Theory.SpecificGroups.Tits.MinimumIndex.LargeTwoOvergroups.SeedOvergroups.Geometry.RepresentativeProducts.Pattern14
public import Theory.SpecificGroups.Tits.MinimumIndex.LargeTwoOvergroups.SeedOvergroups.Geometry.RepresentativeProducts.Pattern15
public import Theory.SpecificGroups.Tits.MinimumIndex.LargeTwoOvergroups.SeedOvergroups.Geometry.RepresentativeProducts.Pattern16
public import Theory.SpecificGroups.Tits.MinimumIndex.LargeTwoOvergroups.SeedOvergroups.Geometry.RepresentativeProducts.Pattern17
import Mathlib.Tactic.FinCases

/-!
# Disjoint representative products for all required place patterns

The shared invariant and selector checks reduce the required quadratic exclusion
to one checked support bit per row and place. The seventeen pattern certificates
prove the uniform exclusion of `a * b⁻¹` for disjoint stored masks. This supplies
the product-exclusion premise of the geometry assembly without any cover or
mask-membership assumption. The `ProductCompatible` application retains those
two independently owned premises. Pattern 9 has its separate two-place proof.

Source: the Parrott (1972), §5, p.683 words in Geometry.Data, with the exact
centralizer/normalizer conventions certified in Geometry.Membership.
-/

@[expose] public section
namespace Tits.MinimumIndex.LargeTwoOvergroups.SeedOvergroups.Geometry

/-- The complete four-place pattern supplies the literal representative-product
premise of the seed-overgroup geometry consumer. -/
theorem disjoint_representative_products_four :
    ∀ a ∈ rows 4, ∀ b ∈ rows 4, sharesPlace 4 a b = false →
      ∀ j ∈ placePattern 4, placeTest (rowPerm a * (rowPerm b)⁻¹) j = false :=
  RepresentativeProducts.excludes_of_checks 4
    RepresentativeProducts.Pattern4.selector RepresentativeProducts.Pattern4.checked

/-- For every pattern other than the separate two-place case, disjoint stored
masks exclude the literal product `a * b⁻¹` from every listed place. -/
theorem disjoint_representative_products :
    ∀ t : Fin 18, t ≠ 9 → ∀ a ∈ rows t, ∀ b ∈ rows t,
      sharesPlace t a b = false →
      ∀ j ∈ placePattern t, placeTest (rowPerm a * (rowPerm b)⁻¹) j = false := by
  intro t ht
  fin_cases t
  · exact RepresentativeProducts.Pattern0.excludes
  · exact RepresentativeProducts.Pattern1.excludes
  · exact RepresentativeProducts.Pattern2.excludes
  · exact RepresentativeProducts.Pattern3.excludes
  · exact disjoint_representative_products_four
  · exact RepresentativeProducts.Pattern5.excludes
  · exact RepresentativeProducts.Pattern6.excludes
  · exact RepresentativeProducts.Pattern7.excludes
  · exact RepresentativeProducts.Pattern8.excludes
  · exact (ht rfl).elim
  · exact RepresentativeProducts.Pattern10.excludes
  · exact RepresentativeProducts.Pattern11.excludes
  · exact RepresentativeProducts.Pattern12.excludes
  · exact RepresentativeProducts.Pattern13.excludes
  · exact RepresentativeProducts.Pattern14.excludes
  · exact RepresentativeProducts.Pattern15.excludes
  · exact RepresentativeProducts.Pattern16.excludes
  · exact RepresentativeProducts.Pattern17.excludes

/-- Consumer application: the representative-product premise is discharged for
every required pattern. The common-factor cover and mask correctness are the
independent inputs retained by the full geometry assembly. -/
theorem placePattern_productCompatible_of_cover_and_masks (t : Fin 18) (ht : t ≠ 9)
    (hcommon : ∀ q ∈ factors t, ∀ j ∈ placePattern t, q ∈ place j)
    (hcover : ∀ x : Atlas1600Group, (∃ j ∈ placePattern t, x ∈ place j) →
      ∃ q ∈ factors t, ∃ r ∈ rows t, x = q * rowElement r)
    (hmasks : ∀ r ∈ rows t, ∀ j ∈ placePattern t,
      placeTest (rowPerm r) j = rowMember r j) :
    ProductCompatible ((placePattern t).map place) := by
  apply productCompatible_of_common_factors place (placePattern t) (factors t) (rows t)
    rowElement rowMember hcommon hcover
  · intro r hr j hj
    rw [← placeTest_iff, ← rowPerm_eq, hmasks r hr j hj]
  · intro a ha b hb hab j hj hmem
    have hp := (placeTest_iff (rowElement a * (rowElement b)⁻¹) j).mpr hmem
    change placeTest ((rowElement a).val * ((rowElement b).val)⁻¹) j = true at hp
    rw [← rowPerm_eq, ← rowPerm_eq,
      disjoint_representative_products t ht a ha b hb hab j hj] at hp
    exact Bool.noConfusion hp

/-- Consumer application: pattern 4's product-exclusion premise is discharged.
The common-factor cover and mask correctness remain the independent premises
owned by the full geometry assembly. -/
theorem placePattern_four_productCompatible_of_cover_and_masks
    (hcommon : ∀ q ∈ factors 4, ∀ j ∈ placePattern 4, q ∈ place j)
    (hcover : ∀ x : Atlas1600Group, (∃ j ∈ placePattern 4, x ∈ place j) →
      ∃ q ∈ factors 4, ∃ r ∈ rows 4, x = q * rowElement r)
    (hmasks : ∀ r ∈ rows 4, ∀ j ∈ placePattern 4,
      placeTest (rowPerm r) j = rowMember r j) :
    ProductCompatible ((placePattern 4).map place) := by
  apply productCompatible_of_common_factors place (placePattern 4) (factors 4) (rows 4)
    rowElement rowMember hcommon hcover
  · intro r hr j hj
    rw [← placeTest_iff, ← rowPerm_eq, hmasks r hr j hj]
  · intro a ha b hb hab j hj hmem
    have ht := (placeTest_iff (rowElement a * (rowElement b)⁻¹) j).mpr hmem
    change placeTest ((rowElement a).val * ((rowElement b).val)⁻¹) j = true at ht
    rw [← rowPerm_eq, ← rowPerm_eq,
      disjoint_representative_products_four a ha b hb hab j hj] at ht
    exact Bool.noConfusion ht

/-- Uniform assembly from any family of checked selectors. The concrete family
is discharged in `disjoint_representative_products`. -/
theorem disjoint_representative_products_of_selector_certificates
    (select : Fin 18 → Fin 38 → Nat → Fin 38)
    (hcheck : ∀ t : Fin 18, t ≠ 9 →
      (rows t).all (RepresentativeProducts.rowCheck t (select t)) = true) :
    ∀ t : Fin 18, t ≠ 9 → ∀ a ∈ rows t, ∀ b ∈ rows t,
      sharesPlace t a b = false →
      ∀ j ∈ placePattern t, placeTest (rowPerm a * (rowPerm b)⁻¹) j = false := by
  intro t ht
  exact RepresentativeProducts.excludes_of_checks t (select t) (hcheck t ht)

end Tits.MinimumIndex.LargeTwoOvergroups.SeedOvergroups.Geometry
