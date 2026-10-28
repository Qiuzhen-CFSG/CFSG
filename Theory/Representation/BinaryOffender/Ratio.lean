module
public import Theory.Representation.BinaryOffender.Basic
public import Mathlib.Order.ConditionallyCompleteLattice.Finset

/-!
# Attainment of the quadratic action ratio

There are only finitely many subgroups of a finite group, so a finite quadratic
ratio is attained by an actual nontrivial quadratic elementary subgroup. This
supplies the implication B.1.4(5)(iii) ⇒ (i) without Thompson replacement.
The opposite implication still needs the replacement theorem.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*,
1 March 2004, B.1.1 and B.1.4, pp. 67–69.
-/

public section
namespace Representation.BinaryOffender
open scoped ENNReal
variable {G V : Type*} [Group G] [Finite G] [AddCommGroup V]
  [Module (ZMod 2) V] (ρ : Representation (ZMod 2) G V)

/-- A finite upper bound on the global quadratic ratio is attained by a subgroup. -/
theorem quadraticRatio_le_iff {r : ℝ≥0∞} (hr : r ≠ ⊤) :
    quadraticRatio ρ ≤ r ↔
      ∃ A, IsElementaryTwo A ∧ IsQuadratic ρ A ∧ actionRatio ρ A ≤ r := by
  classical
  constructor
  · intro h
    let S := {A : Subgroup G // IsElementaryTwo A ∧ IsQuadratic ρ A}
    by_cases hS : Nonempty S
    · let : Nonempty S := hS
      obtain ⟨A, hA⟩ := exists_eq_ciInf_of_finite
        (f := fun A : S => actionRatio ρ A.val)
      rw [iInf_subtype] at hA
      exact ⟨A.val, A.property.1, A.property.2, hA.trans_le h⟩
    · have htop : quadraticRatio ρ = ⊤ := by
        apply iInf_eq_top.mpr
        intro A
        apply iInf_eq_top.mpr
        intro hA
        exact (hS ⟨⟨A, hA⟩⟩).elim
      exact (hr (top_le_iff.mp (htop ▸ h))).elim
  · rintro ⟨A, hA, hq, hle⟩
    exact (iInf_le_of_le A (iInf_le_of_le ⟨hA, hq⟩ le_rfl)).trans hle

/-- Ratio at most one means that a quadratic offender actually exists. -/
theorem quadraticRatio_le_one_iff : quadraticRatio ρ ≤ 1 ↔
    ∃ A, IsOffender ρ A ∧ IsQuadratic ρ A := by
  rw [quadraticRatio_le_iff ρ (by simp : (1 : ℝ≥0∞) ≠ ⊤)]
  constructor
  · rintro ⟨A, hA, hq, hr⟩
    exact ⟨A, ⟨hA, (actionRatio_le_one_iff ρ hA).mp hr⟩, hq⟩
  · rintro ⟨A, ⟨hA, hr⟩, hq⟩
    exact ⟨A, hA, hq, (actionRatio_le_one_iff ρ hA).mpr hr⟩

/-- B.1.4(5)(iii) ⇒ (i), including exclusion of the empty-index case. -/
theorem isFFModule_of_quadraticRatio_le_one (h : quadraticRatio ρ ≤ 1) :
    IsFFModule ρ := by
  obtain ⟨A, hA, _⟩ := (quadraticRatio_le_one_iff ρ).mp h
  exact ⟨A, hA⟩

end Representation.BinaryOffender
