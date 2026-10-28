module

public import Theory.Representation.BinaryOffender.CommutatorRank
public import Theory.Representation.BinaryOffender.RestrictionComparison

/-!
# Elementary actors with a common fixed space

If every nonidentity element of an elementary abelian two-group has the
same fixed space as the whole group, the action is quadratic. Indeed the
displacement of an involution lies in its fixed space in characteristic two.
Equality of the fixed-space codimensions suffices in finite dimension.

This is the linear step in Aschbacher–Smith, H.11.1(3), printed p.393
(combined manuscript of 1 March 2004).
-/

public section
namespace Representation.BinaryOffender

variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]

/-- A common fixed space for the nonidentity elements forces quadratic action. -/
theorem isQuadratic_of_common_fixedSpace (ρ : Representation (ZMod 2) G V)
    {A : Subgroup G} [IsElementaryAbelian 2 A]
    (hfix : ∀ a ∈ A, a ≠ 1 → fixedSpace ρ A = fixedSpace ρ (Subgroup.zpowers a)) :
    IsQuadratic ρ A := by
  intro a ha b hb v
  by_cases hb1 : b = 1
  · subst b
    simp
  have hbb : b * b = 1 := by
    simpa only [pow_two] using elemPow_eq_one_of_isElementaryAbelian (p := 2) b hb
  have hv : ρ b (ρ b v) = v := by
    rw [← Module.End.mul_apply, ← map_mul, hbb, map_one, Module.End.one_apply]
  have hneg (w : V) : -w = w := by
    have hw : w + w = 0 := by
      simpa only [add_smul, one_smul, zero_smul] using
        congrArg (fun c : ZMod 2 => c • w) (by decide : (1 : ZMod 2) + 1 = 0)
    exact neg_eq_of_add_eq_zero_left hw
  have hmem : ρ b v - v ∈ fixedSpace ρ (Subgroup.zpowers b) := by
    rw [mem_fixedSpace_zpowers_iff, map_sub, hv]
    simp only [sub_eq_add_neg, hneg, add_comm]
  rw [← hfix b hb hb1] at hmem
  exact hmem ⟨a, ha⟩

/-- In finite dimension, equality of codimensions gives the common fixed space. -/
theorem fixedSpace_eq_of_fixedCodim_eq [FiniteDimensional (ZMod 2) V]
    (ρ : Representation (ZMod 2) G V) {A B : Subgroup G} (hBA : B ≤ A)
    (hd : fixedCodim ρ A = fixedCodim ρ B) : fixedSpace ρ A = fixedSpace ρ B := by
  apply Submodule.eq_of_le_of_finrank_eq (fixedSpace_antitone ρ hBA)
  have hA := fixedCodim_add_finrank ρ A
  have hB := fixedCodim_add_finrank ρ B
  omega

/-- Uniform element codimensions give quadratic action without replacement. -/
theorem isQuadratic_of_common_fixedCodim [FiniteDimensional (ZMod 2) V]
    (ρ : Representation (ZMod 2) G V) {A : Subgroup G} [IsElementaryAbelian 2 A]
    (hd : ∀ a ∈ A, a ≠ 1 → fixedCodim ρ A = fixedCodim ρ (Subgroup.zpowers a)) :
    IsQuadratic ρ A := by
  apply isQuadratic_of_common_fixedSpace ρ
  intro a ha ha1
  exact fixedSpace_eq_of_fixedCodim_eq ρ (Subgroup.zpowers_le.mpr ha) (hd a ha ha1)

end Representation.BinaryOffender
