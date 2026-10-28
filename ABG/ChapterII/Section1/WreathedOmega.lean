module
public import ABG.ChapterII.Section1.WreathedInvolutions
public import Theory.GroupTheory.PGroup.Omega
public import Mathlib.GroupTheory.QuotientGroup.Basic
public import Mathlib.GroupTheory.SpecificGroups.Cyclic.Basic

/-!
# The omega subgroup of a wreathed group

For a chosen wreathed presentation of height at least two, the first omega
subgroup is `T ⊔ Y` and its quotient is cyclic. This is ABG Chapter II §1
Lemma 2(viii), article p.10, with the notation fixed on article p.9.

The square-one classification puts every generator of omega either in the
base four subgroup T or in the form r^i*z; both lie in T ⊔ Y since z=x₂⁻¹*d.
Conversely, x₂, x₃, z, and r*z have square one, so the omega subgroup contains
T and the generators r,d of Y. Finally the generator-change theorem says
that Y together with sz generates S. Killing Y in the omega quotient leaves
the image of sz as a single generator. The local characteristic instance
supplies the quotient group structure without assuming additional normality.
-/

namespace ABG.Wreathed.Presentation
variable {S : Type*} [Group S] {n : ℕ} (P : Presentation S n)

private theorem square_mem_omega {g : S} (h : g ^ 2 = 1) :
    g ∈ omega₁ S (p := 2) := by
  exact Subgroup.subset_closure (by simpa only [pow_one, Set.mem_ofPred_eq] using h)

private theorem lower :
    P.T ⊔ P.Y ≤ omega₁ S (p := 2) := by
  let O := omega₁ S (p := 2)
  have hz : P.z ∈ O := square_mem_omega P.z_sq
  have h₂ : P.x₂ ∈ O := square_mem_omega P.x₂_sq
  have h₃ : P.x₃ ∈ O := square_mem_omega P.x₃_sq
  have hrz : (P.r * P.z) ^ 2 = 1 := by
    calc
      (P.r * P.z) ^ 2 = P.r * (P.z * P.r * P.z⁻¹) := by simp only [P.z_inv, pow_two, mul_assoc]
      _ = 1 := by rw [P.z_conj_r, mul_inv_cancel]
  have hr : P.r ∈ O := by
    have hm := O.mul_mem (square_mem_omega hrz) (O.inv_mem hz)
    simpa only [mul_inv_cancel_right] using hm
  refine sup_le ?_ ?_
  · apply (Subgroup.closure_le _).mpr
    intro g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hg with rfl | rfl | rfl
    · rw [P.x_eq_x₂_mul_x₃]; exact O.mul_mem h₂ h₃
    · exact h₂
    · exact h₃
  · apply (Subgroup.closure_le _).mpr
    intro g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hg with rfl | rfl
    · exact hr
    · exact O.mul_mem h₂ hz

private theorem upper
    (hclass : ∀ g : S, g ^ 2 = 1 → g ∈ P.T ∨ ∃ i : ℕ, g = P.r ^ i * P.z) :
    omega₁ S (p := 2) ≤ P.T ⊔ P.Y := by
  let H := P.T ⊔ P.Y
  have hr : P.r ∈ H := (show P.Y ≤ H from le_sup_right)
    (Subgroup.subset_closure (by simp))
  have hd : P.d ∈ H := (show P.Y ≤ H from le_sup_right)
    (Subgroup.subset_closure (by simp))
  have h₂ : P.x₂ ∈ H := (show P.T ≤ H from le_sup_left)
    (Subgroup.subset_closure (by simp))
  have hz : P.z ∈ H := by
    have hh := H.mul_mem (H.inv_mem h₂) hd
    simpa only [d, inv_mul_cancel_left] using hh
  apply (Subgroup.closure_le _).mpr
  intro g hg
  have hg' : g ^ 2 = 1 := by simpa only [pow_one, Set.mem_ofPred_eq] using hg
  rcases hclass g hg' with ht | ⟨i, rfl⟩
  · exact (show P.T ≤ P.T ⊔ P.Y from le_sup_left) ht
  · exact H.mul_mem (H.pow_mem hr i) hz

include P in
private theorem cyclic :
    letI : (omega₁ S (p := 2)).Characteristic := omega₁_characteristic S
    IsCyclic (S ⧸ omega₁ S (p := 2)) := by
  let : (omega₁ S (p := 2)).Characteristic := omega₁_characteristic S
  let q := QuotientGroup.mk' (omega₁ S (p := 2))
  apply isCyclic_iff_exists_zpowers_eq_top.mpr
  refine ⟨q (P.s * P.z), ?_⟩
  have hmap : P.Y.map q = ⊥ := by
    apply (Subgroup.map_eq_bot_iff _).mpr
    simpa only [q, QuotientGroup.ker_mk'] using (le_sup_right.trans P.lower : P.Y ≤ omega₁ S (p := 2))
  have hh := congrArg (Subgroup.map q) P.generator_change.2
  rw [Subgroup.map_sup, hmap, bot_sup_eq, MonoidHom.map_zpowers,
    Subgroup.map_top_of_surjective q (QuotientGroup.mk'_surjective _)] at hh
  exact hh

public theorem omega_structure :
    letI : (omega₁ S (p := 2)).Characteristic := omega₁_characteristic S
    omega₁ S (p := 2) = P.T ⊔ P.Y ∧ IsCyclic (S ⧸ omega₁ S (p := 2)) := by
  classical
  refine ⟨le_antisymm (P.upper ?_) P.lower, P.cyclic⟩
  intro g hg
  by_cases hu : g ∈ P.U
  · left
    rcases P.base_involution_cases hu hg with rfl | rfl | rfl | rfl
    · exact P.T.one_mem
    · exact Subgroup.subset_closure (by simp)
    · exact Subgroup.subset_closure (by simp)
    · exact Subgroup.subset_closure (by simp)
  · exact Or.inr (P.outer_involution_form hu hg)
end ABG.Wreathed.Presentation
