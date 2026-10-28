module

public import Theory.SpecificGroups.Tits.MinimumIndex.LargeTwoOvergroups.SeedOvergroups.Geometry.RepresentativeProducts.Key
public import Theory.SpecificGroups.Tits.MinimumIndex.LargeTwoOvergroups.SeedOvergroups.Geometry.RepresentativeProducts.Fast
public import Theory.SpecificGroups.Tits.MinimumIndex.LargeTwoOvergroups.SeedOvergroups.Geometry.Reduction

/-!
# Linear certificates for disjoint representative products

The executable fingerprint agrees with the invariant proved in `Key`.
For each place and each representative, a certificate selects a listed place
whose bit is set in that representative's stored mask. The selected place
depends only on the fingerprint. Consequently rows with disjoint masks cannot
have a product `a * b⁻¹` in any listed place.

No assertion about the correctness of the masks as memberships is used.
Those independent certificates are required by the final geometry assembly.
Source: Parrott (1972), §5, p.683, with Geometry.Data's literal conventions.
-/

@[expose] public section
namespace Tits.MinimumIndex.LargeTwoOvergroups.SeedOvergroups.Geometry.RepresentativeProducts

/-- The optimized evaluator computes the proved conjugation invariant. -/
theorem key_eq (r : Row) (j : Fin 38) : key r j = cosetKey (rowPerm r) j := by
  simp only [key, cosetKey, centerKey, representative_eq, conjugator_eq, assignment_eq]
  by_cases hj : j.val < 17
  · simp only [hj, if_true, Nat.not_le.mpr hj, decide_false, Bool.false_eq_true, if_false]
    rfl
  · simp only [hj, if_false, Nat.le_of_not_gt hj, decide_true, if_true]
    rfl

/-- Check the selected support bit for every listed place of one stored row. -/
def rowCheck (t : Fin 18) (select : Fin 38 → Nat → Fin 38) (r : Row) : Bool :=
  (placePattern t).all fun j =>
    let k := select j (key r j)
    decide (k ∈ placePattern t) && rowMember r k

/-- A checked selector supplies the exact product-exclusion premise used by
`placePattern_productCompatible_of_representative_certificates`. -/
theorem excludes_of_checks (t : Fin 18) (select : Fin 38 → Nat → Fin 38)
    (hcheck : (rows t).all (rowCheck t select) = true) :
    ∀ a ∈ rows t, ∀ b ∈ rows t, sharesPlace t a b = false →
      ∀ j ∈ placePattern t, placeTest (rowPerm a * (rowPerm b)⁻¹) j = false := by
  apply excludes_of_selector t select
  intro r hr j hj
  have hrow := List.all_eq_true.mp hcheck r hr
  have h := List.all_eq_true.mp hrow j hj
  simp only [Bool.and_eq_true, decide_eq_true_eq, key_eq] at h
  exact h

end Tits.MinimumIndex.LargeTwoOvergroups.SeedOvergroups.Geometry.RepresentativeProducts
