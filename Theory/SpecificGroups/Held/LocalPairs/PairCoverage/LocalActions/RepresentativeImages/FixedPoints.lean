module

public import Theory.SpecificGroups.Held.LocalPairs.PairCoverage.LocalActions.RepresentativeImages.Planes

/-!
# The mixed Held plane axes cannot be exchanged by a permutation

At both j=1 candidates the first marked generator fixes a letter, whereas
the second has no fixed letter. Conjugating a permutation carries its fixed
letters bijectively to those of its conjugate, so no permutation exchanges
these generators. This will distinguish the diagonal and monomial full
images once the inner coordinate image has been certified.

Sources: the literal ATLAS HeG1-p2058B0 action, with the candidate words in
Candidates; GLS3 Table 5.3p and Aschbacher–Smith, printed pp.509–511.
-/

@[expose] public section
namespace Held.LocalPairs.PairCoverage.LocalActions.RepresentativeImages

theorem mixed_first_axis_has_fixed_point (i : Bool) :
    ∃ x : Fin 2058, representation (basisGenerator i 1 0) x = x := by
  cases i
  · change ∃ x : Fin 2058, representation (oddGenerator false 1 0) x = x
    rw [← Pair01.odd0_eq]
    exact Pair01.odd0_has_fixed_point
  · change ∃ x : Fin 2058, representation (oddGenerator true 1 0) x = x
    rw [← Pair11.odd0_eq]
    exact Pair11.odd0_has_fixed_point

theorem mixed_second_axis_has_no_fixed_point (i : Bool) (x : Fin 2058) :
    representation (basisGenerator i 1 1) x ≠ x := by
  cases i
  · change representation (oddGenerator false 1 1) x ≠ x
    rw [← Pair01.odd1_eq]
    exact Pair01.odd1_has_no_fixed_point x
  · change representation (oddGenerator true 1 1) x ≠ x
    rw [← Pair11.odd1_eq]
    exact Pair11.odd1_has_no_fixed_point x

/-- In the mixed representatives, no ambient permutation exchanges the marked generators. -/
theorem mixed_axes_not_conjugate (i : Bool) (σ : Equiv.Perm (Fin 2058)) :
    σ * representation (basisGenerator i 1 0) * σ⁻¹ ≠
      representation (basisGenerator i 1 1) := by
  intro he
  obtain ⟨x, hx⟩ := mixed_first_axis_has_fixed_point i
  apply mixed_second_axis_has_no_fixed_point i (σ x)
  rw [← he]
  change σ (representation (basisGenerator i 1 0) (σ.symm (σ x))) = σ x
  rw [σ.symm_apply_apply, hx]

end Held.LocalPairs.PairCoverage.LocalActions.RepresentativeImages
